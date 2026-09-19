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
//! - **Транзитивные зависимости.** Зависимость с собственным
//!   `[dependencies]` отвергается названной причиной, а не подключается
//!   наполовину: единый граф требует правила разрешения версий, а версий у
//!   git-зависимости нет - есть коммиты.

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
pub use sources::Workspace;

/// Зависимость, лежащая на диске.
#[derive(Clone, Debug)]
pub struct Resolved {
    /// Префикс путей модулей.
    pub prefix: String,
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
    /// Зависимости в порядке манифеста.
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
    /// Манифеста нет или он собран не так; `git` не достал зависимость;
    /// зависимость сама имеет зависимости; замок не пишется.
    pub fn open(dir: &Path) -> Result<Self, PkgError> {
        let manifest = Manifest::open(dir)?;
        let previous = Lock::open(dir)?;
        let store = Store::new(dir);

        let mut resolved = Vec::new();
        let mut packages = Vec::new();
        let mut sources = Workspace::new(&manifest.root);
        for dependency in &manifest.dependencies {
            let pinned = previous.pinned(&dependency.prefix, &dependency.git);
            let fetched = store.provide(dependency, pinned)?;
            let inner = Manifest::open(&fetched.dir)?;
            if !inner.dependencies.is_empty() {
                return Err(PkgError::shape(
                    &fetched.dir.join(manifest::MANIFEST),
                    format!(
                        "у зависимости `{}` есть свои зависимости; транзитивные не поддержаны (§7.3: реестра нет, разрешать версии нечем)",
                        dependency.prefix
                    ),
                ));
            }
            sources = sources.with_package(&dependency.prefix, &inner.root);
            packages.push(Pinned {
                prefix: dependency.prefix.clone(),
                git: dependency.git.clone(),
                rev: fetched.rev.clone(),
            });
            resolved.push(Resolved {
                prefix: dependency.prefix.clone(),
                rev: fetched.rev,
                root: inner.root,
                refreshed: fetched.refreshed,
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
