//! Исполнение термов ядра: интерпретатор с хендлерами эффектов (§9 Фаза 5).
//!
//! **Вычислителей два, и это названная цена.** Первый - [`adamas_core::eval`]:
//! он обслуживает конвертируемость, про эффекты не знает ничего, и `#handle.L`
//! для него постулат, то есть нейтраль. Второй - этот: он исполняет, эффекты
//! производит, а типов не считает вовсе. Разойтись им есть где: `handle`,
//! посчитанный здесь, в типах остаётся собой.
//!
//! Довод в пользу двух - §3.4: рантайм-остаток эффекта вводится **понижением**,
//! а не связыванием ядра. Продолжение - не операция над термами, и завести его
//! в ядре значило бы протащить самую нетривиальную часть рантайма в TCB ради
//! редукции, которой в типах никто не просит.
//!
//! Стирания здесь нет: типы доходят до исполнения наравне со значениями. Оно
//! придёт с понижением, а понижения пока нет - есть машина над самим термом.

mod effect;
mod machine;
mod outcome;
mod scope;

pub use machine::Machine;
pub use outcome::{Cont, Outcome, Performed};

use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_core::value::Env;

/// Чем исполнение может кончиться помимо значения.
#[derive(Debug, thiserror::Error)]
pub enum RunError {
    /// Операция дошла до верха, не встретив своего хендлера.
    ///
    /// Проверка типов такого не пропускает - погашение требует, чтобы row
    /// определения была пуста, - так что случай этот означает расхождение
    /// машины с правилом, а не ошибку автора.
    #[error("операция `{operation}` метки `{effect}` осталась без хендлера")]
    Unhandled {
        /// Метка операции.
        effect: String,
        /// Сама операция.
        operation: String,
    },
}

/// Исполняет замкнутый терм и читает результат обратно в терм.
///
/// # Errors
///
/// [`RunError::Unhandled`] - операция дошла до верха.
pub fn run(signature: &Signature, term: &Term) -> Result<Term, RunError> {
    let machine = Machine::new(signature);
    let value = match machine.eval(&Env::default(), term) {
        Outcome::Done(value) => value,
        Outcome::Performed(performed) => return Err(unhandled(&performed)),
    };
    machine
        .read(value)
        .map_err(|performed| unhandled(&performed))
}

/// Операция, не встретившая хендлера.
fn unhandled(performed: &Performed) -> RunError {
    RunError::Unhandled {
        effect: performed.effect.to_string(),
        operation: performed.operation.to_string(),
    }
}
