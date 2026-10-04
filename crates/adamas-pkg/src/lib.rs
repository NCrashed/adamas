//! Проект Adamas: манифест, git-зависимости, lockfile (§7.1, §7.3).
//!
//! §7.3 отводит Фазе 9 git-based пакетный менеджер: зависимость есть git URL
//! плюс коммит или тег, централизованного реестра нет. §7.1 требует сверх того
//! lockfile и воспроизводимость сборки. Этот крейт - и то и другое, и ничего
//! сверх.
//!
//! # Что где
//!
//! - [`manifest`] - `adamas.toml` и почему он TOML.
//! - [`lock`] - `adamas.lock` и почему он вообще нужен при подвижном теге.
//! - [`fetch`] - зеркало и чекаут, и когда сеть не трогается.
//! - [`sources`] - реализация [`Sources`](adamas_elab::program::Sources),
//!   отдающая путь модуля тому пакету, чей префикс его накрывает.
//!
//! # Чего здесь нет
//!
//! - **Content addressing** (§7.3, Фаза 10+). Из трёх его условий здесь
//!   закладывается второе - явные зависимости: модуль приходит из пакета,
//!   названного в манифесте, и больше ниоткуда.
//! - **Централизованный реестр.** §7.3 решает это прямо.
//!
//! # Транзитивные зависимости (§10 вопрос 179)
//!
//! Граф обходится от корня, и **копия** пакета - это префикс, URL и коммит.
//! Копия, нужная двоим, достаётся один раз. Разные коммиты одного префикса
//! уживаются: у каждой копии свои модули под своим путём (`Std@0123abcd4567`,
//! если копий больше одной), а какую из них значит `import Std.Prelude`, решает
//! манифест пакета, где импорт написан. Безопасно это для когерентности ровно
//! потому, что инстанс когерентного класса стоит в файле класса или головы
//! (§3.5, пункт 2): копия несёт его на своих типах. Цена - тип одной копии не
//! совместим с тем же типом другой; сводить совместимые коммиты в одну копию
//! нечем, пока у git-зависимости нет версий.

pub mod error;
pub mod fetch;
pub mod lock;
pub mod manifest;
pub mod sources;

use std::path::{Path, PathBuf};

pub use error::PkgError;
pub use fetch::Store;
pub use lock::{Lock, Pinned};
pub use manifest::{Dependency, Manifest, Requirement};
pub use sources::{Package, Workspace};

use adamas_elab::program::Directory;

/// Копия пакета графа, лежащая на диске.
#[derive(Clone, Debug)]
pub struct Resolved {
    /// Префикс путей модулей.
    pub prefix: String,
    /// Путь, под которым объявлены модули копии (§10 вопрос 179).
    pub canonical: String,
    /// Коммит, на котором стоит чекаут.
    pub rev: String,
    /// Корень поиска модулей внутри чекаута.
    pub root: PathBuf,
    /// Ходили ли за ней к источнику в эту сборку.
    pub refreshed: bool,
}

/// Открытый проект: манифест разобран, зависимости на диске, замок записан.
#[derive(Debug)]
pub struct Project {
    /// Разобранный `adamas.toml`.
    pub manifest: Manifest,
    /// Копии графа в порядке обхода: сначала зависимости манифеста.
    pub resolved: Vec<Resolved>,
    /// Был ли `adamas.lock` переписан этой сборкой.
    pub relocked: bool,
    /// Корни поиска модулей - это и есть замена `Directory` у драйвера.
    pub sources: Workspace,
}

impl Project {
    /// Читает манифест, достаёт зависимости, пишет замок.
    ///
    /// Порядок именно такой: замок читается **до** достачи и определяет, какой
    /// коммит брать; пишется **после** и фиксирует, какой взяли.
    ///
    /// # Errors
    ///
    /// Манифеста нет или он собран не так - у проекта или у пакета графа;
    /// `git` не достал зависимость; замок не пишется.
    pub fn open(dir: &Path) -> Result<Self, PkgError> {
        let manifest = Manifest::open(dir)?;
        let previous = Lock::open(dir)?;
        let store = Store::new(dir);

        // Обход в ширину от корня. Узел - копия пакета: префикс, URL и коммит.
        // Одна и та же копия, нужная двоим, достаётся один раз.
        let mut nodes: Vec<Node> = Vec::new();
        let mut roots = Vec::new();
        let mut queue: std::collections::VecDeque<(Option<usize>, Dependency)> = manifest
            .dependencies
            .iter()
            .map(|dependency| (None, dependency.clone()))
            .collect();
        while let Some((requirer, dependency)) = queue.pop_front() {
            let tag = match &dependency.want {
                Requirement::Tag(tag) => Some(tag.as_str()),
                Requirement::Rev(_) => None,
            };
            let pinned = previous.pinned(&dependency.prefix, &dependency.git, tag);
            let fetched = store.provide(&dependency, pinned)?;
            let known = nodes.iter().position(|node| {
                node.prefix == dependency.prefix
                    && node.git == dependency.git
                    && node.rev == fetched.rev
            });
            let index = if let Some(index) = known {
                nodes[index].refreshed |= fetched.refreshed;
                index
            } else {
                let inner = Manifest::open(&fetched.dir)?;
                let index = nodes.len();
                queue.extend(
                    inner
                        .dependencies
                        .iter()
                        .map(|it| (Some(index), it.clone())),
                );
                nodes.push(Node {
                    prefix: dependency.prefix.clone(),
                    git: dependency.git.clone(),
                    tag: tag.map(str::to_owned),
                    rev: fetched.rev,
                    root: inner.root,
                    exports: inner.exports,
                    refreshed: fetched.refreshed,
                    dependencies: Vec::new(),
                });
                index
            };
            match requirer {
                Some(requirer) => nodes[requirer]
                    .dependencies
                    .push((dependency.prefix.clone(), index)),
                None => roots.push((dependency.prefix.clone(), index)),
            }
        }

        let canonical = canonical(&nodes);
        let mut sources = Workspace::new(&manifest.root);
        for (prefix, index) in &roots {
            sources = sources.requiring(prefix, &canonical[*index]);
        }
        let mut resolved = Vec::new();
        let mut packages = Vec::new();
        for (index, node) in nodes.into_iter().enumerate() {
            sources = sources.with(Package {
                canonical: canonical[index].clone(),
                prefix: node.prefix.clone(),
                directory: Directory::new(&node.root),
                exports: node.exports,
                dependencies: node
                    .dependencies
                    .iter()
                    .map(|(prefix, index)| (prefix.clone(), canonical[*index].clone()))
                    .collect(),
            });
            packages.push(Pinned {
                prefix: node.prefix.clone(),
                git: node.git,
                rev: node.rev.clone(),
                tag: node.tag,
            });
            resolved.push(Resolved {
                prefix: node.prefix,
                canonical: canonical[index].clone(),
                rev: node.rev,
                root: node.root,
                refreshed: node.refreshed,
            });
        }

        let relocked = Lock { packages }.save(dir)?;
        Ok(Self {
            manifest,
            resolved,
            relocked,
            sources,
        })
    }

    /// Файл модуля-входа.
    #[must_use]
    pub fn entry_file(&self) -> PathBuf {
        self.manifest.entry_file()
    }
}

/// Копия пакета по ходу обхода графа.
struct Node {
    prefix: String,
    git: String,
    /// Тег требования, у записанного коммитом - `None`.
    tag: Option<String>,
    rev: String,
    root: PathBuf,
    exports: Option<Vec<String>>,
    refreshed: bool,
    /// Зависимости копии: написанный префикс и номер узла.
    dependencies: Vec<(String, usize)>,
}

/// Пути, под которыми объявлены копии: префикс, а при нескольких копиях
/// префикса - префикс с коммитом.
fn canonical(nodes: &[Node]) -> Vec<String> {
    nodes
        .iter()
        .map(|node| {
            let copies = nodes.iter().filter(|it| it.prefix == node.prefix).count();
            if copies == 1 {
                node.prefix.clone()
            } else {
                format!("{}@{}", node.prefix, &node.rev[..node.rev.len().min(12)])
            }
        })
        .collect()
}
