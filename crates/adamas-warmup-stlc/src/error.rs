//! Ошибки всех стадий - один enum на весь конвейер.

use adamas_core::source::{SourceFile, Span};

/// Ошибка компиляции или вычисления.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Лексер встретил символ, не начинающий ни один токен.
    #[error("неизвестный символ {ch:?}")]
    UnexpectedChar {
        /// Сам символ.
        ch: char,
        /// Где он находится.
        span: Span,
    },

    /// Целочисленный литерал не помещается в `i64`.
    #[error("целочисленный литерал не помещается в Int")]
    IntTooLarge {
        /// Спан литерала.
        span: Span,
    },

    /// Парсер ожидал одно, а увидел другое.
    // Двоеточия, а не "ожидался/ожидалось": подставляемые описания имеют
    // разный род, и согласовать шаблон с ними нельзя.
    #[error("ожидалось: {expected}; найдено: {found}")]
    UnexpectedToken {
        /// Человекочитаемое описание ожидаемого.
        expected: String,
        /// Что встретилось вместо этого.
        found: String,
        /// Спан встреченного токена.
        span: Span,
    },

    /// Вложенность выражений или типов превысила предел парсера.
    #[error("слишком глубокая вложенность, предел {limit}")]
    TooDeep {
        /// Предел, который был исчерпан.
        limit: u32,
        /// Спан токена, на котором это случилось.
        span: Span,
    },

    /// Имя не связано ни `let`, ни лямбдой.
    #[error("переменная `{name}` не определена")]
    UnboundVariable {
        /// Имя переменной.
        name: String,
        /// Спан вхождения.
        span: Span,
    },

    /// Унификация двух типов провалилась.
    #[error("несовпадение типов: ожидался {expected}, получен {found}")]
    Mismatch {
        /// Тип, которого требовал контекст.
        expected: String,
        /// Тип, который получился на самом деле.
        found: String,
        /// Спан выражения, на котором сломалось.
        span: Span,
    },

    /// Метапеременная встречается внутри типа, которым её пытаются решить.
    /// Классический признак самоприменения вроде `\x -> x x`.
    #[error("бесконечный тип: {meta} встречается в {ty}")]
    OccursCheck {
        /// Имя метапеременной в печатном виде.
        meta: String,
        /// Тип, в который она пыталась подставиться.
        ty: String,
        /// Спан выражения.
        span: Span,
    },

    /// Вычисление не уложилось в лимит шагов.
    #[error("превышен лимит шагов вычисления ({limit})")]
    StepLimit {
        /// Лимит, который был исчерпан.
        limit: u32,
    },

    /// Целочисленное переполнение во время вычисления.
    ///
    /// Без спана - и это цена разделения surface/core: [`crate::core`] спанов
    /// не хранит, а ошибка возникает уже там. В настоящем компиляторе такие
    /// ошибки либо ловятся статически, либо core тащит спаны дальше.
    #[error("целочисленное переполнение")]
    Overflow,
}

impl Error {
    /// Спан, к которому привязана ошибка. У [`Error::StepLimit`] его нет:
    /// шаги кончаются не в конкретной точке программы.
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        match *self {
            Self::UnexpectedChar { span, .. }
            | Self::IntTooLarge { span }
            | Self::UnexpectedToken { span, .. }
            | Self::TooDeep { span, .. }
            | Self::UnboundVariable { span, .. }
            | Self::Mismatch { span, .. }
            | Self::OccursCheck { span, .. } => Some(span),
            Self::StepLimit { .. } | Self::Overflow => None,
        }
    }

    /// Рендерит ошибку с привязкой к исходнику: `имя:строка:колонка`, текст
    /// ошибки, сама строка и подчёркивание под спаном.
    ///
    /// Настоящая диагностика Adamas (§7.4) будет строиться на `ariadne` или
    /// `miette`; здесь ровно столько, чтобы snapshot-тесты ошибок читались
    /// глазами и чтобы [`adamas_core::source`] был проверен в деле.
    #[must_use]
    pub fn render(&self, source: &SourceFile) -> String {
        use std::fmt::Write as _;

        let Some(span) = self.span() else {
            return format!("error: {self}\n");
        };
        let Some(start) = source.location(span.start()) else {
            return format!("error: {self}\n");
        };

        let mut out = format!("{}:{start}: error: {self}\n", source.name());
        if let Some(line) = source.line_text(start.line) {
            let _ = writeln!(out, "  {line}");
            let width = source.snippet(span).map_or(1, |s| s.chars().count().max(1));
            let _ = writeln!(
                out,
                "  {:pad$}{:^<width$}",
                "",
                "",
                pad = start.column - 1,
                width = width
            );
        }
        out
    }
}
