//! Lockfile: `adamas.lock` (§7.1, «Lockfile + воспроизводимые сборки»).
//!
//! # Зачем он вообще
//!
//! §7.3 разрешает записать зависимость тегом, а **тег в git подвижен**: в
//! репозитории-источнике его переставляют на другой коммит одной командой.
//! Манифест с тегом поэтому описывает не сборку, а намерение; сборку описывает
//! коммит, в который тег разрешился **в первый раз**, и хранится он здесь.
//!
//! Из этого следует и граница пользы: при `rev = "<коммит>"` lockfile не
//! добавляет к воспроизводимости ничего - манифест уже неподвижен. Он остаётся
//! кешем разрешения, не более.
//!
//! # Формат
//!
//! ```toml
//! # adamas.lock — создан `adamas`. Правится инструментом, а не рукой.
//! version = 1
//!
//! [[package]]
//! prefix = "Std"
//! git = "file:///std"
//! rev = "0123456789abcdef0123456789abcdef01234567"
//! ```
//!
//! Тот же TOML, что у манифеста, и по той же причине: второй формат в проекте
//! никому не нужен. Пишется вручную форматированием, а не сериализатором -
//! `serde` в зависимости не взят (см. [`crate::manifest`]), а форма файла
//! фиксированная.

use std::path::Path;

use toml::de::DeTable;

use crate::error::PkgError;

/// Имя файла.
pub const LOCKFILE: &str = "adamas.lock";

/// Версия формата. Несовпадение - отказ, а не молчаливое чтение.
const VERSION: u64 = 1;

/// Одна запертая зависимость.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pinned {
    /// Префикс путей модулей - тот же ключ, что в манифесте.
    pub prefix: String,
    /// URL, из которого коммит достали. Сменился - запись не годится.
    pub git: String,
    /// Полный хеш коммита.
    pub rev: String,
}

/// Содержимое `adamas.lock`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lock {
    /// Записи в порядке префиксов.
    pub packages: Vec<Pinned>,
}

impl Lock {
    /// Читает `<dir>/adamas.lock`. Файла нет - пустой замок.
    ///
    /// # Errors
    ///
    /// Файл есть, но не читается, не разбирается или собран не так.
    pub fn open(dir: &Path) -> Result<Self, PkgError> {
        let path = dir.join(LOCKFILE);
        if !path.is_file() {
            return Ok(Self::default());
        }
        let text = std::fs::read_to_string(&path).map_err(|source| PkgError::Read {
            path: path.clone(),
            source,
        })?;
        Self::parse(&path, &text)
    }

    /// Разбирает текст замка. `path` идёт только в сообщения.
    ///
    /// # Errors
    ///
    /// TOML не разобрался, версия не та или поля собраны не так.
    pub fn parse(path: &Path, text: &str) -> Result<Self, PkgError> {
        let document = DeTable::parse(text).map_err(|error| PkgError::Syntax {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        let document = document.get_ref();
        let version = document
            .get("version")
            .and_then(|it| it.get_ref().as_integer())
            .and_then(|it| it.as_str().parse::<u64>().ok())
            .ok_or_else(|| PkgError::shape(path, "нет поля `version`"))?;
        if version != VERSION {
            return Err(PkgError::shape(
                path,
                format!(
                    "версия формата {version}, инструмент понимает {VERSION}: удалите файл, он будет создан заново"
                ),
            ));
        }

        let mut packages = Vec::new();
        if let Some(array) = document.get("package") {
            let array = array
                .get_ref()
                .as_array()
                .ok_or_else(|| PkgError::shape(path, "`package` - не массив таблиц"))?;
            for entry in &**array {
                let table = entry
                    .get_ref()
                    .as_table()
                    .ok_or_else(|| PkgError::shape(path, "элемент `package` - не таблица"))?;
                let field = |key: &str| -> Result<String, PkgError> {
                    table
                        .get(key)
                        .and_then(|it| it.get_ref().as_str())
                        .map(str::to_owned)
                        .ok_or_else(|| {
                            PkgError::shape(path, format!("в `[[package]]` нет `{key}`"))
                        })
                };
                packages.push(Pinned {
                    prefix: field("prefix")?,
                    git: field("git")?,
                    rev: field("rev")?,
                });
            }
        }
        Ok(Self { packages })
    }

    /// Коммит, запертый за этим префиксом при **этом же** URL.
    ///
    /// URL сверяется намеренно: переехавшая зависимость - другая зависимость,
    /// и старый коммит от неё не годится.
    #[must_use]
    pub fn pinned(&self, prefix: &str, git: &str) -> Option<&str> {
        self.packages
            .iter()
            .find(|it| it.prefix == prefix && it.git == git)
            .map(|it| it.rev.as_str())
    }

    /// Текст файла.
    #[must_use]
    pub fn rendered(&self) -> String {
        let mut out = String::from(
            "# adamas.lock — создан `adamas`. Правится инструментом, а не рукой.\nversion = 1\n",
        );
        let mut packages = self.packages.clone();
        packages.sort_by(|left, right| left.prefix.cmp(&right.prefix));
        for package in packages {
            out.push_str("\n[[package]]\nprefix = ");
            out.push_str(&quoted(&package.prefix));
            out.push_str("\ngit = ");
            out.push_str(&quoted(&package.git));
            out.push_str("\nrev = ");
            out.push_str(&quoted(&package.rev));
            out.push('\n');
        }
        out
    }

    /// Пишет `<dir>/adamas.lock`, если текст изменился.
    ///
    /// Возвращает `true`, если файл был записан. Сверка с прежним текстом - не
    /// оптимизация: перезапись без изменений трогает mtime и сбивает всякого,
    /// кто по нему судит о работе.
    ///
    /// Проекту без зависимостей файл не заводится: запирать в нём нечего, а
    /// лишний файл в каталоге всякого, кто просто проверил программу, -
    /// мусор. Уже заведённый при этом обновляется и пустым: последняя
    /// зависимость, убранная из манифеста, обязана уйти и отсюда.
    ///
    /// # Errors
    ///
    /// Файл не пишется.
    pub fn save(&self, dir: &Path) -> Result<bool, PkgError> {
        let path = dir.join(LOCKFILE);
        if self.packages.is_empty() && !path.exists() {
            return Ok(false);
        }
        let text = self.rendered();
        if std::fs::read_to_string(&path).is_ok_and(|old| old == text) {
            return Ok(false);
        }
        std::fs::write(&path, text).map_err(|source| PkgError::Write {
            path: path.clone(),
            source,
        })?;
        Ok(true)
    }
}

/// Строка в TOML basic-string. URL приходит из чужого файла, и кавычка с
/// обратным слешем в нём законны.
fn quoted(text: &str) -> String {
    use std::fmt::Write as _;

    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for symbol in text.chars() {
        match symbol {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            it if (it as u32) < 0x20 || it as u32 == 0x7f => {
                let _ = write!(out, "\\u{:04X}", it as u32);
            }
            it => out.push(it),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pinned(prefix: &str, git: &str, rev: &str) -> Pinned {
        Pinned {
            prefix: prefix.to_owned(),
            git: git.to_owned(),
            rev: rev.to_owned(),
        }
    }

    /// Круг «записали - прочитали» держит и на URL с кавычкой: экранирование
    /// пишется руками, и проверять его надо тем же путём, каким его сломают.
    #[test]
    fn a_written_lock_reads_back() {
        let lock = Lock {
            packages: vec![
                pinned("Std", "file:///std", "a".repeat(40).as_str()),
                pinned("Data", "https://host/it\\\"quoted\".git", &"b".repeat(40)),
            ],
        };
        let text = lock.rendered();
        let back = Lock::parse(Path::new("adamas.lock"), &text).expect("замок");
        let mut expected = lock.packages;
        expected.sort_by(|left, right| left.prefix.cmp(&right.prefix));
        assert_eq!(back.packages, expected);
    }

    /// Пустой замок не заводится, а заведённый - опустошается.
    #[test]
    fn an_empty_lock_is_written_only_over_an_existing_one() {
        let scratch = tempfile::tempdir().expect("каталог");
        let dir = scratch.path();

        assert!(!Lock::default().save(dir).expect("запись"));
        assert!(!dir.join(LOCKFILE).exists(), "файл заведён на пустом месте");

        let filled = Lock {
            packages: vec![pinned("Std", "file:///std", &"d".repeat(40))],
        };
        assert!(filled.save(dir).expect("запись"));
        assert!(Lock::default().save(dir).expect("запись"));
        assert!(
            Lock::open(dir).expect("чтение").packages.is_empty(),
            "убранная зависимость осталась в замке"
        );
    }

    #[test]
    fn a_missing_version_is_refused() {
        let error = Lock::parse(Path::new("adamas.lock"), "[[package]]\n")
            .expect_err("без версии обязан быть отказ");
        assert!(format!("{error}").contains("`version`"), "{error}");
    }

    #[test]
    fn a_future_version_is_refused_by_name() {
        let error = Lock::parse(Path::new("adamas.lock"), "version = 99\n")
            .expect_err("чужая версия обязана быть названа");
        assert!(format!("{error}").contains("удалите файл"), "{error}");
    }

    /// Переехавший URL - другая зависимость, и прежний коммит к ней не
    /// относится.
    #[test]
    fn a_pin_belongs_to_its_url() {
        let lock = Lock {
            packages: vec![pinned("Std", "file:///std", &"c".repeat(40))],
        };
        assert!(lock.pinned("Std", "file:///std").is_some());
        assert!(lock.pinned("Std", "file:///other").is_none());
        assert!(lock.pinned("Other", "file:///std").is_none());
    }
}
