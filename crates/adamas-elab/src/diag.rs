//! Диагностика значением: позиция отдельно от текста (§7.2, §7.4).
//!
//! До этого модуля отказ превращался в строку сразу - [`crate::report`] отдавал
//! готовый блок «позиция, строка исходника, каретка», и другого доступа к
//! тексту сообщения не было. Редактору нужен тот же текст **без** этого блока:
//! позицию он рисует сам, а строку исходника у него и так видно. Собрать текст
//! второй раз значило бы завести вторую запись каждого сообщения, и она
//! разъехалась бы с первой - проект платил за такие пары четырежды за две
//! волны.
//!
//! Поэтому источник один: [`Diagnostic`] собирается из отказа один раз, драйвер
//! печатает её [`Diagnostic::rendered`], сервер шлёт [`Diagnostic::message`] с
//! позицией. Совпадение проверяется прогоном - `crates/adamas-cli/tests/lsp.rs`
//! собирает вывод драйвера обратно из того, что ушло бы в редактор.
//!
//! # Форма
//!
//! Сообщение делится на три части, и делится оно так, потому что в терминале
//! между ними стоит исходник:
//!
//! ```text
//! файл:20:18: ожидалась функция, получено значение типа `Nat`   <- headline
//!   двойка = {- 😀 -} Succ Zero Zero
//!                    ^^^^^^^^^^^^^^
//!   путь: тело `двойка`                                         <- detail
//! ```
//!
//! [`Diagnostic::related`] - другие места того же отказа; в терминале они идут
//! своим блоком, в LSP - `relatedInformation`.

use adamas_core::sig::Signature;
use adamas_core::source::{SourceFile, Span};
use adamas_parser::ast::Module;

use crate::error::ElabError;
use crate::warn::Warning;

/// Насколько серьёзно.
///
/// Двух градаций хватает: компилятор отвечает отказом либо предупреждением, а
/// `Information`/`Hint` LSP появятся вместе с подсказками §7.2 (FBIP,
/// аллокации), которых сегодня нет.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    /// Программа отвергнута.
    Error,
    /// Программа принята с оговоркой.
    Warning,
}

/// Место со своей подписью: вторая точка, на которую смотрит отказ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Related {
    /// Где.
    pub span: Span,
    /// Что там написано.
    pub message: String,
}

/// Отказ или предупреждение как данные.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// Отказ или оговорка.
    pub severity: Severity,
    /// Место, которое подчёркивается.
    pub span: Span,
    /// Первая строка сообщения. Однострочна по построению: в терминале сразу
    /// за ней идёт исходник.
    pub headline: String,
    /// Хвост сообщения - телескоп и маршрут. Пуст либо начинается с перевода
    /// строки.
    pub detail: String,
    /// Прочие места того же сообщения.
    pub related: Vec<Related>,
}

impl Diagnostic {
    /// Отказ разбора: текста сверх своей строки у него нет.
    #[must_use]
    pub fn of_parse(error: &adamas_parser::Error) -> Self {
        Self {
            severity: Severity::Error,
            span: error.span(),
            headline: error.to_string(),
            detail: String::new(),
            related: Vec::new(),
        }
    }

    /// Отказ элаборации или проверки типов.
    #[must_use]
    pub fn of_error(error: &ElabError) -> Self {
        Self {
            severity: Severity::Error,
            span: error.span(),
            headline: crate::render::headline(error),
            detail: crate::render::detail(error),
            related: crate::render::related(error),
        }
    }

    /// Предупреждение.
    #[must_use]
    pub fn of_warning(warning: &Warning) -> Self {
        Self {
            severity: Severity::Warning,
            span: warning.span(),
            headline: warning.to_string(),
            detail: String::new(),
            related: Vec::new(),
        }
    }

    /// Текст сообщения целиком, без позиции и без исходника: то, что видит
    /// читатель в редакторе.
    #[must_use]
    pub fn message(&self) -> String {
        format!("{}{}", self.headline, self.detail)
    }

    /// Текст для терминала: позиция, строка исходника с кареткой, связанные
    /// места и хвост.
    #[must_use]
    pub fn rendered(&self, file: &SourceFile) -> String {
        let mut out = crate::render::located(file, self.span, &self.headline);
        for related in &self.related {
            out.push('\n');
            out.push_str(&crate::render::located(
                file,
                related.span,
                &related.message,
            ));
        }
        out.push_str(&self.detail);
        out
    }
}

/// Что известно о файле после полного прохода.
///
/// Полный проход, а не инкрементальный: замер волны 1 Фазы 9 дал 36 мс на
/// капстоуне в 944 строки при бюджете интерактивности порядка 100 мс, и граф
/// зависимостей за эти деньги не покупается.
#[derive(Debug)]
pub struct Analysis {
    /// Дерево поверхностного языка. Есть, если текст разобрался.
    pub module: Option<Module>,
    /// Что успело объявиться. Есть, если текст разобрался; полна, если
    /// программа принята.
    ///
    /// Частичная сигнатура нужна редактору (§7.2): буфер под курсором не
    /// проверяется почти никогда - слово дописывается посередине, - а тип
    /// имени, объявленного **выше** места отказа, известен и показывать его
    /// нечему помешать. Содержимое её от этого не портится: `declare`
    /// добавляет группу целиком и только проверенную, а та, на которой проход
    /// остановился, в сигнатуру не попадает.
    pub signature: Option<Signature>,
    /// Отказы и предупреждения в порядке появления.
    pub diagnostics: Vec<Diagnostic>,
}

impl Analysis {
    /// Первый отказ, если он был.
    #[must_use]
    pub fn error(&self) -> Option<&Diagnostic> {
        self.diagnostics
            .iter()
            .find(|it| it.severity == Severity::Error)
    }
}

/// Текст файла целиком: разбор, элаборация, проверка типов.
///
/// Общая половина драйвера (`adamas check`) и сервера: оба обязаны отвечать
/// одно и то же, и держится это тем, что путь один.
///
/// Отказ у прохода не более одного: компилятор останавливается на первом, и
/// восстановления после ошибки сегодня нет. Предупреждения приходят только с
/// принятой программой - по той же причине.
#[must_use]
pub fn analyze(text: &str) -> Analysis {
    let module = match adamas_parser::parse(text) {
        Ok(module) => module,
        Err(error) => {
            return Analysis {
                module: None,
                signature: None,
                diagnostics: vec![Diagnostic::of_parse(&error)],
            };
        }
    };
    let (signature, outcome) = crate::elaborated(&module);
    Analysis {
        module: Some(module),
        signature: Some(signature),
        diagnostics: match outcome {
            Ok(warnings) => warnings.iter().map(Diagnostic::of_warning).collect(),
            Err(error) => vec![Diagnostic::of_error(&error)],
        },
    }
}
