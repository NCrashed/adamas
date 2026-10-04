//! Поиск модулей по манифесту: [`Workspace`] вместо
//! [`Directory`](adamas_elab::program::Directory).
//!
//! Шов оставлен треком A волны 2: корень поиска у драйвера был один каталог, а
//! [`Sources`] - трейт. Манифест заменяет реализацию, и больше в элаборации не
//! меняется ничего: `import Std.Prelude` разбирается тем же кодом и
//! квалифицируется тем же путём, а откуда пришёл текст - её дело не касается.
//!
//! # Правило маршрута
//!
//! Путь модуля отдаётся пакету, чей префикс его накрывает: `Std` накрывает
//! `Std` и всё, что начинается на `Std.`. Не накрытый никем путь ищется в
//! корне самого проекта. Побеждает **длиннейший** префикс - иначе `Data` и
//! `Data.Map` нельзя было бы держать в разных пакетах.
//!
//! Внутри пакета путь **не укорачивается**: `Std.Prelude` - это
//! `<чекаут>/<корень пакета>/Std/Prelude.adamas`. Так один и тот же файл лежит
//! под одним и тем же именем и в своём репозитории, и в чужом проекте, и
//! менять `import`'ы при переезде не приходится.
//!
//! # Копии пакета и чей манифест решает (§10 вопрос 179)
//!
//! Пакет, попавший в граф несколькими коммитами, объявлен по копии на коммит
//! под своим путём (`Std@0123abcd4567.Prelude`); единственная копия
//! объявлена под префиксом. Написанный путь переводится в путь копии
//! манифестом пакета **подключающего**: свой префикс - своя копия, префикс
//! зависимости - копия, которую назвал его манифест. Не накрытое ничем у
//! проекта - его собственный модуль, у пакета - отказ: он подключает только
//! объявленное.
//!
//! # Публичное у пакета - то, что он экспортирует
//!
//! §4.8 даёт инкапсуляцию **вложенному** модулю, а файл ничем не объемлется
//! (`Enclosing::file`), и скрывать ему нечем. Граница поэтому живёт у пакета:
//! `exports` его манифеста перечисляет публичные префиксы (§10 вопрос 180).
//! Модуль пакета подключается **снаружи** - из проекта или другого пакета, -
//! только если его накрывает экспорт; **изнутри**, из модуля под тем же
//! префиксом, - всякий: `Std.Prelude` вправе подключать `Std.Internal`. Без
//! `exports` открыто всё, как было.

use std::path::Path;

use adamas_elab::program::{Directory, Sources};

/// Пакет графа зависимостей.
#[derive(Clone, Debug)]
pub struct Package {
    /// Путь, под которым объявлены его модули: префикс, а у пакета, попавшего
    /// в граф несколькими коммитами, - префикс с коммитом (`Std@0123abcd4567`).
    pub canonical: String,
    /// Префикс, которым его модули пишутся - в нём самом и у подключающих.
    pub prefix: String,
    /// Корень поиска модулей в чекауте.
    pub directory: Directory,
    /// Публичные префиксы (§10 вопрос 180); `None` - открыто всё.
    pub exports: Option<Vec<String>>,
    /// Его зависимости: написанный префикс и каноническое имя копии.
    pub dependencies: Vec<(String, String)>,
}

/// Корни поиска модулей: свой и по одному на пакет графа.
#[derive(Clone, Debug)]
pub struct Workspace {
    local: Directory,
    packages: Vec<Package>,
    /// Зависимости самого проекта: написанный префикс и каноническое имя.
    dependencies: Vec<(String, String)>,
}

impl Workspace {
    /// Корень собственных модулей проекта.
    #[must_use]
    pub fn new(local: &Path) -> Self {
        Self {
            local: Directory::new(local),
            packages: Vec::new(),
            dependencies: Vec::new(),
        }
    }

    /// Добавляет зависимость проекта, единственную копию своего префикса.
    #[must_use]
    pub fn with_package(self, prefix: &str, root: &Path) -> Self {
        self.with(Package {
            canonical: prefix.to_owned(),
            prefix: prefix.to_owned(),
            directory: Directory::new(root),
            exports: None,
            dependencies: Vec::new(),
        })
        .requiring(prefix, prefix)
    }

    /// Добавляет пакет графа.
    #[must_use]
    pub fn with(mut self, package: Package) -> Self {
        self.packages.push(package);
        // Длиннейший впереди: `Data.Map` обязан побеждать `Data`.
        self.packages
            .sort_by_key(|package| std::cmp::Reverse(package.canonical.len()));
        self
    }

    /// Объявляет зависимость самого проекта: префикс и копию, которую он
    /// значит.
    #[must_use]
    pub fn requiring(mut self, prefix: &str, canonical: &str) -> Self {
        self.dependencies
            .push((prefix.to_owned(), canonical.to_owned()));
        self
    }

    /// Пакет, объявивший модуль под этим путём; `None` - сам проект.
    fn owner(&self, path: &str) -> Option<&Package> {
        self.packages
            .iter()
            .find(|package| covers(&package.canonical, path))
    }

    /// Файловый путь модуля: в чекауте он лежит под префиксом, а не под
    /// каноническим именем копии.
    fn located(&self, path: &str) -> (&Directory, String) {
        match self.owner(path) {
            Some(package) => (
                &package.directory,
                rebased(path, &package.canonical, &package.prefix),
            ),
            None => (&self.local, path.to_owned()),
        }
    }
}

impl Sources for Workspace {
    fn text(&self, path: &str) -> Option<String> {
        let (directory, written) = self.located(path);
        directory.text(&written)
    }

    fn private(&self, from: Option<&str>, path: &str) -> Option<String> {
        let package = self.owner(path)?;
        // Изнутри пакета видно всё: служебный модуль заводят ради своих.
        if from.is_some_and(|from| covers(&package.canonical, from)) {
            return None;
        }
        let exports = package.exports.as_ref()?;
        let written = rebased(path, &package.canonical, &package.prefix);
        (!exports.iter().any(|export| covers(export, &written))).then(|| package.prefix.clone())
    }

    fn canonical(&self, from: Option<&str>, path: &str) -> Option<String> {
        if path == adamas_elab::program::PRELUDE {
            return Some(path.to_owned());
        }
        let importer = from.and_then(|from| self.owner(from));
        if let Some(package) = importer {
            if covers(&package.prefix, path) {
                return Some(rebased(path, &package.prefix, &package.canonical));
            }
        }
        let dependencies = importer.map_or(&self.dependencies, |package| &package.dependencies);
        let found = dependencies
            .iter()
            .filter(|(prefix, _)| covers(prefix, path))
            .max_by_key(|(prefix, _)| prefix.len());
        match (found, importer) {
            (Some((prefix, canonical)), _) => Some(rebased(path, prefix, canonical)),
            // Не накрытый зависимостью путь проекта - его собственный модуль.
            (None, None) => Some(path.to_owned()),
            (None, Some(_)) => None,
        }
    }

    fn looked(&self, path: &str) -> String {
        let (directory, written) = self.located(path);
        directory.looked(&written)
    }
}

/// Путь под префиксом `from`, переписанный под префикс `to`.
fn rebased(path: &str, from: &str, to: &str) -> String {
    format!("{to}{}", &path[from.len()..])
}

/// Накрывает ли префикс путь: сам префикс и всё, что под ним.
///
/// Сравнение посегментное, а не по началу строки: `Std` не накрывает `Stdlib`.
fn covers(prefix: &str, path: &str) -> bool {
    path == prefix
        || (path.len() > prefix.len()
            && path.starts_with(prefix)
            && path.as_bytes()[prefix.len()] == b'.')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_prefix_covers_itself_and_what_is_under_it() {
        assert!(covers("Std", "Std"));
        assert!(covers("Std", "Std.Prelude"));
        assert!(covers("Data.Map", "Data.Map.Internal"));
    }

    /// Сравнение по началу строки отдало бы `Stdlib` пакету `Std`.
    #[test]
    fn a_prefix_does_not_cover_a_longer_word() {
        assert!(!covers("Std", "Stdlib"));
        assert!(!covers("Std", "Stdlib.Prelude"));
        assert!(!covers("Data.Map", "Data.Maple"));
    }

    #[test]
    fn the_longest_prefix_wins() {
        let workspace = Workspace::new(Path::new("/проект/src"))
            .with_package("Data", Path::new("/пакеты/data"))
            .with_package("Data.Map", Path::new("/пакеты/map"));
        assert_eq!(
            workspace.looked("Data.Map.Internal"),
            Path::new("/пакеты/map/Data/Map/Internal.adamas")
                .display()
                .to_string()
        );
        assert_eq!(
            workspace.looked("Data.Set"),
            Path::new("/пакеты/data/Data/Set.adamas")
                .display()
                .to_string()
        );
        assert_eq!(
            workspace.looked("Own.Module"),
            Path::new("/проект/src/Own/Module.adamas")
                .display()
                .to_string()
        );
    }
}
