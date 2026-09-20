//! Отказы пакетного менеджера.
//!
//! Все они - пользовательские: кривой манифест, недостижимый репозиторий,
//! несуществующий тег. Паники здесь нет ни одной, потому что каждый из них
//! приходит от написанного человеком файла или от чужого репозитория
//! (CLAUDE.md, «Panic на user-facing путях»).

use std::path::PathBuf;

/// Что помешало открыть проект.
#[derive(Debug, thiserror::Error)]
pub enum PkgError {
    /// Манифеста нет там, где его искали.
    #[error("манифест не найден: {0}")]
    NoManifest(PathBuf),

    /// Файл не читается.
    #[error("не удалось прочитать {path}: {source}")]
    Read {
        /// Что читали.
        path: PathBuf,
        /// Почему не вышло.
        source: std::io::Error,
    },

    /// Файл не пишется.
    #[error("не удалось записать {path}: {source}")]
    Write {
        /// Что писали.
        path: PathBuf,
        /// Почему не вышло.
        source: std::io::Error,
    },

    /// TOML не разобрался.
    #[error("{path}: {message}")]
    Syntax {
        /// Файл.
        path: PathBuf,
        /// Сообщение разборщика TOML.
        message: String,
    },

    /// Поле не на месте: нет, не того типа, пустое.
    #[error("{path}: {message}")]
    Shape {
        /// Файл.
        path: PathBuf,
        /// Что именно не так.
        message: String,
    },

    /// `git` не запустился или ушёл с ненулевым кодом.
    #[error("git {command}: {message}")]
    Git {
        /// Команда без пути к бинарю.
        command: String,
        /// `stderr` вместе с кодом возврата.
        message: String,
    },
}

impl PkgError {
    /// Отказ формы с готовым текстом.
    pub(crate) fn shape(path: &std::path::Path, message: impl Into<String>) -> Self {
        Self::Shape {
            path: path.to_path_buf(),
            message: message.into(),
        }
    }
}
