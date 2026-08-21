//! Warm-up Фазы 0: STLC + Hindley-Milner на bidirectional-элаборации.
//!
//! Разминка перед Фазой 1, а не часть будущего компилятора: `adamas-core` об
//! этом крейте не знает. Почему выбраны bidirectional-вывод, метаконтекст с
//! уровнями и подстановочный интерпретатор - в `docs/warmup-retrospective.md`.
//!
//! # Пример
//!
//! ```
//! use adamas_core::source::SourceFile;
//! use adamas_warmup_stlc::{run, Value};
//!
//! let file = SourceFile::new("fact.stlc", "
//!     let rec fact = \\n -> if n < 1 then 1 else n * fact (n - 1) in
//!     fact 10
//! ");
//! let outcome = run(&file).expect("программа корректна");
//! assert_eq!(outcome.ty.to_string(), "Int");
//! assert_eq!(outcome.value, Value::Int(3_628_800));
//! ```

mod core;
mod error;
mod eval;
mod infer;
mod lexer;
mod parser;
mod syntax;
mod types;
mod unify;

use adamas_core::source::SourceFile;

pub use crate::error::Error;
pub use crate::eval::Value;
pub use crate::types::Type;

/// Результат полного прогона: тип программы и её значение.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// Выведенный тип программы, уже без неразрешённых метапеременных.
    pub ty: Type,
    /// Значение, к которому программа вычислилась.
    pub value: Value,
}

/// Лексирует, парсит и типизирует программу, не вычисляя её.
///
/// Аналог `adamas check` (§7.1): быстрая обратная связь без исполнения.
///
/// # Errors
///
/// Любая ошибка любой стадии - со спаном, указывающим на место в `source`.
pub fn check(source: &SourceFile) -> Result<Type, Error> {
    let tokens = lexer::tokenize(source.text())?;
    let term = parser::parse(&tokens)?;
    infer::infer_program(&term)
}

/// Прогоняет программу целиком: типизация, затем вычисление.
///
/// # Errors
///
/// Ошибка любой стадии. Вычисление начинается только после успешной
/// типизации, поэтому "застрявших" термов здесь быть не может - кроме
/// исчерпания лимита шагов на незавершающейся программе.
pub fn run(source: &SourceFile) -> Result<Outcome, Error> {
    let tokens = lexer::tokenize(source.text())?;
    let term = parser::parse(&tokens)?;
    let ty = infer::infer_program(&term)?;
    let expr = core::lower(&term);
    let value = eval::eval(&expr)?;
    Ok(Outcome { ty, value })
}
