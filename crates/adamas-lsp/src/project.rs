//! Проект в редакторе: открытый буфер главнее файла на диске (§7.2, §7.3).
//!
//! Драйвер читает подключаемые модули с диска ([`Directory`]), и этого ему
//! довольно: `adamas check` запускается над сохранённым деревом. Редактору
//! этого мало - человек правит файл и **не сохраняет** его, а зависящий буфер
//! обязан подчёркиваться по тому, что человек видит перед собой, а не по тому,
//! что лежит в файловой системе.
//!
//! Отсюда [`Buffers`]: путь модуля разрешается в файл тем же правилом, что у
//! драйвера (`Data.Map` - это `<корень>/Data/Map.adamas`), но текст берётся у
//! открытого буфера, если такой есть. Правило раскладки одно на обоих, и
//! второй его записи не заводится: [`Directory::file_of`] зовут оба.
//!
//! Корень поиска - каталог входного файла, то есть того буфера, который сейчас
//! проверяется. Манифест (трек C волны, §7.3) заменит его собой.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::str::FromStr as _;

use adamas_elab::program::{Directory, Sources};
use lsp_types::Uri;

/// Путь файла, на который указывает `file:`-URI. `None` - URI не про файл.
///
/// Проценты раскодируются: редактор шлёт `file:///%D0%B0.adamas` там, где на
/// диске лежит `а.adamas`, и без раскодирования модуль искался бы по
/// написанию, которого в файловой системе нет.
#[must_use]
pub fn path_of(uri: &Uri) -> Option<PathBuf> {
    let scheme = uri.scheme()?;
    if !scheme.as_str().eq_ignore_ascii_case("file") {
        return None;
    }
    let path = uri.path();
    if !path.is_absolute() {
        return None;
    }
    let decoded = path.as_estr().decode().into_string_lossy().into_owned();
    Some(PathBuf::from(decoded))
}

/// `file:`-URI файла на диске. `None` - путь не строка UTF-8 либо URI не
/// разобрался обратно.
///
/// Кодируется всё, чего RFC 3986 не разрешает в пути без процентов, кроме
/// самого разделителя: иначе пробел или кириллица в пути давали бы URI, который
/// редактор не примет.
#[must_use]
pub fn uri_of(path: &Path) -> Option<Uri> {
    let mut out = String::from("file://");
    for byte in path.to_str()?.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                out.push(char::from(byte));
            }
            // Запись в `String` не отказывает: `fmt::Error` здесь недостижим.
            _ => drop(write!(out, "%{byte:02X}")),
        }
    }
    Uri::from_str(&out).ok()
}

/// Тексты модулей проекта: сперва открытые буферы, затем диск.
#[derive(Debug)]
pub struct Buffers<'a> {
    /// Раскладка модулей по файлам - та же, что у драйвера.
    directory: Directory,
    /// Открытые буферы по пути файла.
    open: HashMap<PathBuf, &'a str>,
}

impl<'a> Buffers<'a> {
    /// Проект с корнем в этом каталоге и этими открытыми буферами.
    #[must_use]
    pub fn new(root: impl Into<PathBuf>, open: HashMap<PathBuf, &'a str>) -> Self {
        Self {
            directory: Directory::new(root),
            open,
        }
    }

    /// Проект без единого открытого буфера - всё читается с диска.
    #[must_use]
    pub fn on_disk(root: impl Into<PathBuf>) -> Self {
        Self::new(root, HashMap::new())
    }
}

impl Sources for Buffers<'_> {
    fn text(&self, path: &str) -> Option<String> {
        let file = self.directory.file_of(path);
        if let Some(text) = self.open.get(&file) {
            return Some((*text).to_owned());
        }
        std::fs::read_to_string(&file).ok()
    }

    fn looked(&self, path: &str) -> String {
        self.directory.file_of(path).display().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::{Uri, path_of, uri_of};
    use std::path::{Path, PathBuf};
    use std::str::FromStr as _;

    #[test]
    fn a_file_uri_becomes_its_path() {
        let uri = Uri::from_str("file:///home/u/Std/Map.adamas").expect("URI разбирается");
        assert_eq!(path_of(&uri), Some(PathBuf::from("/home/u/Std/Map.adamas")));
    }

    /// Проценты в URI - это байты пути, а не его написание.
    #[test]
    fn percents_are_decoded_back_into_bytes() {
        let uri = Uri::from_str("file:///%D0%BF%D1%83%D1%82%D1%8C/%D0%B0.adamas")
            .expect("URI разбирается");
        assert_eq!(path_of(&uri), Some(PathBuf::from("/путь/а.adamas")));
    }

    /// И обратно: путь с кириллицей даёт URI, который разбирается в него же.
    #[test]
    fn a_path_round_trips_through_its_uri() {
        let path = Path::new("/путь с пробелом/а.adamas");
        let uri = uri_of(path).expect("путь UTF-8 переводится в URI");
        assert_eq!(
            uri.as_str(),
            "file:///%D0%BF%D1%83%D1%82%D1%8C%20%D1%81%20%D0%BF%D1%80%D0%BE%D0%B1%D0%B5%D0%BB%D0%BE%D0%BC/%D0%B0.adamas"
        );
        assert_eq!(path_of(&uri).as_deref(), Some(path));
    }

    /// URI не про файл путём не притворяется.
    #[test]
    fn a_non_file_uri_has_no_path() {
        let uri = Uri::from_str("untitled:Untitled-1").expect("URI разбирается");
        assert_eq!(path_of(&uri), None);
    }
}
