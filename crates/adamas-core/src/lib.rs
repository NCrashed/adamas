//! Ядро компилятора Adamas: core language, elaborator, type checker.
//!
//! Спецификация - `adamas-design.md` §3.
//!
//! # Состояние (Фаза 1)
//!
//! Готово ядро вычислений: термы ([`term`]) с кратностями ([`mult`]) и
//! алгебраическими уровнями ([`level`]), `NbE` ([`eval`]) и проверка
//! конвертируемости ([`conv`]).
//!
//! Ещё нет: bidirectional-проверки типов, учёта использований по QTT,
//! метапеременных и universe polymorphism, индуктивных типов, зависимых пар.
//! Кратности при этом уже в представлении и различают типы функций при
//! проверке конвертируемости.

pub mod conv;
pub mod eval;
pub mod level;
pub mod mult;
pub mod source;
pub mod term;
pub mod value;
