//! Scope, держащий ресурс: `#closing` и раскрутка при обрыве (§3.3).
//!
//! Вставленный `drop` стоит в точке выхода из scope. На нормальном выходе этого
//! довольно: тело кончилось значением, деструктор идёт следом. На выходе через
//! операцию - нет: остаток тела уезжает в продолжение, и если ветка хендлера
//! продолжение не зовёт, `drop` уезжает вместе с ним.
//!
//! Поэтому scope наблюдаем: элаборация ставит `#closing`, и машина видит, что
//! вошла в него. Операция, вышедшая наружу, уносит деструктор **отложенным**;
//! возобновление перевзводит `#closing` на себе, а обрыв запускает отложенное.

use std::rc::Rc;

use adamas_core::value::Value;

use crate::machine::Machine;
use crate::outcome::Outcome;

impl Machine<'_> {
    /// Запускает тело под scope'ом, держащим ресурс.
    ///
    /// Аргументы - типы тела и деструктора, затем оба приостановленных
    /// вычисления. Типы здесь не нужны: они стёрты и стоят ради проверки.
    pub(crate) fn closing(&self, arguments: &[Rc<Value>]) -> Outcome {
        let [_, _, body, close] = arguments else {
            unreachable!("`#closing` объявлен четырёхместным");
        };
        let Some(unit) = self.unit() else {
            unreachable!("`#closing` объявляется только вместе с единицей");
        };
        let outcome = self.apply(body, unit);
        self.guarded(outcome, close)
    }

    /// Разбирает исход тела, стоящего под `#closing`.
    pub(crate) fn guarded(&self, outcome: Outcome, close: &Rc<Value>) -> Outcome {
        let mut performed = match outcome {
            // Нормальный выход: деструктор, потом значение тела.
            Outcome::Done(value) => return self.closed(close, value),
            Outcome::Performed(performed) => performed,
        };
        // Операция ушла наружу. Деструктор откладывается - вдруг продолжение
        // выбросят, - и перевзводится на самом продолжении: возобновившееся
        // тело обязано снова оказаться под этим scope'ом.
        performed.pending.push(Rc::clone(close));
        let close = Rc::clone(close);
        let inner = Rc::clone(&performed.resumption);
        performed.resumption =
            Rc::new(move |machine, value| machine.guarded(inner(machine, value), &close));
        Outcome::Performed(performed)
    }

    /// Запускает деструктор и отдаёт значение тела.
    fn closed(&self, close: &Rc<Value>, value: Rc<Value>) -> Outcome {
        let Some(unit) = self.unit() else {
            return Outcome::Done(value);
        };
        match self.apply(close, unit) {
            Outcome::Done(_) => Outcome::Done(value),
            // Деструктор эффектен сам: его row - окружающая scope'а (§10
            // вопрос 75, вариант (б)), и произвести он вправе. Значение тела
            // ждёт, пока он закончит.
            Outcome::Performed(performed) => Outcome::Performed(
                performed.after(Rc::new(move |_, _| Outcome::Done(Rc::clone(&value)))),
            ),
        }
    }

    /// Запускает отложенные деструкторы и отдаёт значение ветки.
    ///
    /// Порядок - тот, в котором они копились: изнутри наружу, то есть LIFO по
    /// связываниям, как обещает §3.3.
    ///
    /// Деструктор здесь работает **вне** снявшего метку хендлера: тот уже
    /// ответил. Операция из деструктора поэтому уходит наружу; случай узкий -
    /// деструктор, производящий ровно ту метку, обрыв которой его и вызвал, - и
    /// пока он назван, а не решён.
    pub(crate) fn unwound(&self, pending: &[Rc<Value>], from: usize, value: &Rc<Value>) -> Outcome {
        let Some(unit) = self.unit() else {
            return Outcome::Done(Rc::clone(value));
        };
        for index in from..pending.len() {
            match self.apply(&pending[index], Rc::clone(&unit)) {
                Outcome::Done(_) => {}
                Outcome::Performed(performed) => {
                    let (pending, value) = (pending.to_vec(), Rc::clone(value));
                    return Outcome::Performed(performed.after(Rc::new(move |machine, _| {
                        machine.unwound(&pending, index + 1, &value)
                    })));
                }
            }
        }
        Outcome::Done(Rc::clone(value))
    }
}
