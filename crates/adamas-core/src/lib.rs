//! Ядро компилятора Adamas: core language, elaborator, type checker.
//!
//! Спецификация - `adamas-design.md` §3.
//!
//! # Состояние (Фаза 1)
//!
//! Готово: термы ([`term`]) с кратностями ([`mult`]) и алгебраическими
//! уровнями ([`level`]), `NbE` ([`eval`]), проверка конвертируемости
//! ([`conv`]) с δ-разворотом, bidirectional-проверка типов с учётом
//! использований QTT ([`check`] поверх [`ctx`]), определения верхнего уровня
//! с universe polymorphism ([`sig`]).
//!
//! Universe polymorphism пока **явная**: аргументы уровня в местах
//! использования пишутся руками. Вывод их через level-метапеременные -
//! следующий срез, представление от него не изменится.
//!
//! Ещё нет: метапеременных, индуктивных типов, зависимых пар, pattern
//! matching, проверки тотальности.
//!
//! Пока нет индуктивных типов, **`Type 0` необитаем**: `Pi` живёт в `max`
//! уровней своих частей, и опуститься до нуля неоткуда.

pub mod check;
pub mod conv;
pub mod ctx;
pub mod eval;
pub mod level;
pub mod mult;
pub mod sig;
pub mod source;
pub mod term;
pub mod value;
