//! Исход вычисления: значение или произведённая операция.
//!
//! Это резумпционная монада. Обычный вычислитель отдаёт значение и на том
//! кончается; этот отдаёт **либо** значение, **либо** операцию вместе с тем,
//! чем занять её место. Второе и есть продолжение, и никакой другой формы у
//! него быть не может: продолжение обязано пережить возврат из вычисления,
//! которое его породило, а стек Rust этого не переживает.

use std::fmt;
use std::rc::Rc;

use adamas_core::term::Name;
use adamas_core::value::Value;

use crate::machine::Machine;

/// Продолжение: чем занять место произведённой операции.
///
/// `Fn`, а не `FnOnce`: `handleMulti` зовёт резумпцию сколько угодно раз
/// (§3.4), и различает две формы хендлера ровно кратность резумпции.
pub type Cont = Rc<dyn Fn(&Machine<'_>, Rc<Value>) -> Outcome>;

/// Чем кончилось вычисление.
pub enum Outcome {
    /// Значением.
    Done(Rc<Value>),
    /// Операцией, ждущей хендлера.
    Performed(Performed),
}

impl fmt::Debug for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Done(value) => f.debug_tuple("Done").field(value).finish(),
            Self::Performed(performed) => f.debug_tuple("Performed").field(performed).finish(),
        }
    }
}

/// Произведённая операция вместе с продолжением.
pub struct Performed {
    /// Метка, чью операцию произвели.
    pub effect: Name,
    /// Сама операция.
    pub operation: Name,
    /// Её аргументы целиком - вместе с параметрами метки и триггером.
    ///
    /// Резать их - дело хендлера: ветка связывает не всё, что операция
    /// принимает, а знание о том, что именно, живёт в типе элиминатора.
    pub arguments: Vec<Rc<Value>>,
    /// Чем занять место операции.
    pub resumption: Cont,
    /// Деструкторы scope'ов, из которых операция вышла, - изнутри наружу.
    ///
    /// Копятся, пока исход идёт наружу, и нужны ровно на случай, когда ветка
    /// хендлера продолжение **не** зовёт: тогда `let`, стоявший в нём, уезжает
    /// вместе с ним, а закрыть ресурс всё равно надо (§3.3). Возобновлённое
    /// продолжение их не трогает - `#closing` перевзводит себя само.
    pub pending: Vec<Rc<Value>>,
}

impl fmt::Debug for Performed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Performed")
            .field("effect", &self.effect)
            .field("operation", &self.operation)
            .field("arguments", &self.arguments)
            .finish_non_exhaustive()
    }
}

impl Performed {
    /// Дописывает работу к продолжению: сперва оно, потом `step`.
    ///
    /// Так собирается продолжение при возврате наружу. Кадр, увидевший
    /// операцию под собой, знает **свой** остаток работы и приписывает его -
    /// не выполняя. Сумма таких приписываний и есть контекст, в котором
    /// операция стояла.
    #[must_use]
    pub fn after(self, step: Cont) -> Self {
        Self {
            resumption: composed(self.resumption, step),
            ..self
        }
    }

    /// То же, но каждый исход по дороге уносит **долг** - деструкторы, которые
    /// запустит тот, кто это продолжение оборвёт.
    ///
    /// Приписать долг одному исходу мало: продолжение перевзводится, и
    /// следующая операция на том же пути даёт новый исход с собственным
    /// пустым списком. Оборви её - и долг некому платить. Поэтому он едет со
    /// всей цепочкой, пока она жива.
    ///
    /// Дважды долг не платится: отложенное читает только оборвавший, а обрыв
    /// на цепочке случается один раз - дальше неё продолжения нет.
    #[must_use]
    pub fn owing(mut self, owed: Rc<[Rc<Value>]>, step: Cont) -> Self {
        self.pending.extend(owed.iter().map(Rc::clone));
        Self {
            resumption: indebted(self.resumption, owed, step),
            ..self
        }
    }
}

/// Продолжение из двух, несущее долг на всех исходах по дороге.
fn indebted(first: Cont, owed: Rc<[Rc<Value>]>, then: Cont) -> Cont {
    Rc::new(move |machine, value| match first(machine, value) {
        Outcome::Done(value) => then(machine, value),
        Outcome::Performed(performed) => {
            Outcome::Performed(performed.owing(Rc::clone(&owed), Rc::clone(&then)))
        }
    })
}

/// Продолжение из двух: сперва первое, потом второе.
///
/// Первое само вправе произвести операцию - тогда второе приписывается уже её
/// продолжению, и так до тех пор, пока значение не появится.
fn composed(first: Cont, then: Cont) -> Cont {
    Rc::new(move |machine, value| match first(machine, value) {
        Outcome::Done(value) => then(machine, value),
        Outcome::Performed(performed) => Outcome::Performed(performed.after(Rc::clone(&then))),
    })
}

/// Продолжение, которое ничего не делает: место операции и есть ответ.
#[must_use]
pub(crate) fn identity() -> Cont {
    Rc::new(|_, value| Outcome::Done(value))
}
