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

use std::path::Path;

use adamas_elab::program::{Directory, Sources};

/// Корни поиска модулей: свой и по одному на зависимость.
#[derive(Clone, Debug)]
pub struct Workspace {
    local: Directory,
    packages: Vec<(String, Directory)>,
}

impl Workspace {
    /// Корень собственных модулей проекта.
    #[must_use]
    pub fn new(local: &Path) -> Self {
        Self {
            local: Directory::new(local),
            packages: Vec::new(),
        }
    }

    /// Добавляет пакет, обслуживающий префикс.
    #[must_use]
    pub fn with_package(mut self, prefix: &str, root: &Path) -> Self {
        self.packages
            .push((prefix.to_owned(), Directory::new(root)));
        // Длиннейший префикс впереди: `Data.Map` обязан побеждать `Data`.
        self.packages
            .sort_by_key(|(prefix, _)| std::cmp::Reverse(prefix.len()));
        self
    }

    /// Кто отвечает за этот путь.
    fn route(&self, path: &str) -> &Directory {
        self.packages
            .iter()
            .find(|(prefix, _)| covers(prefix, path))
            .map_or(&self.local, |(_, directory)| directory)
    }
}

impl Sources for Workspace {
    fn text(&self, path: &str) -> Option<String> {
        self.route(path).text(path)
    }

    fn looked(&self, path: &str) -> String {
        self.route(path).looked(path)
    }
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
