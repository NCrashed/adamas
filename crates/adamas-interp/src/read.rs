//! Обратное чтение значения в терм - тоже без рекурсии по кадрам Rust.
//!
//! Читает **машина**, а не `conv`: значение, которое просто вернули, до сих пор
//! не разворачивалось - разворот стоит у применения, разбора и проекции, а
//! `Cons answer Nil` не делает ни того, ни другого, ни третьего. Дочитывало его
//! обратное чтение ядра, и хендлер под ним оставался нейтралью.
//!
//! Глубина здесь - глубина **данных**, и она бывает не меньше вычислительной:
//! список в сто тысяч звеньев столько же и весит.

use std::rc::Rc;

use adamas_core::eval::quote;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Elim, Head, Value};

use crate::RunError;
use crate::machine::{Machine, constructor};

/// Отложенная работа обратного чтения.
enum Pending {
    /// Прочитать значение.
    Read(Rc<Value>),
    /// Собрать конструктор из уже прочитанных аргументов.
    Constructor(Term, usize),
    /// Собрать запись из уже прочитанных полей.
    Object(Rc<[Name]>),
}

impl Machine<'_> {
    /// Читает значение в терм, досчитывая его насквозь.
    ///
    /// # Errors
    ///
    /// Операция, дошедшая до чтения, хендлера не встретила: возобновлять её
    /// некуда, чтение и есть конец программы.
    pub fn read(&self, value: Rc<Value>) -> Result<Term, RunError> {
        let mut work = vec![Pending::Read(value)];
        let mut done: Vec<Term> = Vec::new();
        while let Some(next) = work.pop() {
            match next {
                Pending::Read(value) => self.reading(value, &mut work, &mut done)?,
                Pending::Constructor(base, arity) => {
                    let arguments = done.split_off(done.len() - arity);
                    done.push(arguments.into_iter().fold(base, |callee, argument| {
                        Term::App(Rc::new(callee), Rc::new(argument))
                    }));
                }
                Pending::Object(names) => {
                    let values = done.split_off(done.len() - names.len());
                    done.push(Term::Object(
                        names
                            .iter()
                            .cloned()
                            .zip(values.into_iter().map(Rc::new))
                            .collect(),
                    ));
                }
            }
        }
        match done.pop() {
            Some(term) => Ok(term),
            None => unreachable!("чтение оставило пустой ответ"),
        }
    }

    /// Один шаг чтения: значение приводится к головной форме и раскладывается.
    fn reading(
        &self,
        value: Rc<Value>,
        work: &mut Vec<Pending>,
        done: &mut Vec<Term>,
    ) -> Result<(), RunError> {
        // Досчитывается тем же циклом, что и всё прочее: разворот определения -
        // обычный пользовательский код.
        let value = self.forced(value)?;
        match &*value {
            Value::Neutral(head @ Head::Global(name, ..), spine) if applications(spine) => {
                let base = quote(0, &Rc::new(Value::Neutral(head.clone(), Vec::new())));
                // Голова - **любое** имя, а не только конструктор. Пока условие
                // спрашивало конструктора, всё прочее уходило в рекурсивный
                // `quote`, и постулат над цепочкой из семнадцати тысяч звеньев
                // ронял процесс переполнением стека - при том что те же сто
                // тысяч звеньев без постулата считались и печатались (ревью
                // 2026-09-07). Предел возвращался туда, откуда его убрали
                // вопросами 89, 92 и 93.
                let built = constructor(self.signature(), name);
                // Стёртые аргументы **конструктора** не печатаются: их в
                // значении нет - на их месте стоит маркер, а вычислено не было
                // ничего (§3.3). Печатать маркер значило бы показывать место,
                // которого нет. У прочих имён спайн печатается целиком, как
                // печатал его `quote`: сужать здесь нечего, а разойтись с
                // прежним выводом было бы правкой сверх дефекта.
                let live: Vec<&Rc<Value>> = spine
                    .iter()
                    .filter_map(|elim| match elim {
                        Elim::App(argument)
                            if !(built && matches!(&**argument, Value::Erased)) =>
                        {
                            Some(argument)
                        }
                        _ => None,
                    })
                    .collect();
                work.push(Pending::Constructor(base, live.len()));
                // Аргументы читаются слева направо, поэтому в стек кладутся
                // справа налево.
                for argument in live.into_iter().rev() {
                    work.push(Pending::Read(Rc::clone(argument)));
                }
            }
            Value::Object(fields) => {
                work.push(Pending::Object(
                    fields.iter().map(|(name, _)| Rc::clone(name)).collect(),
                ));
                for (_, field) in fields.iter().rev() {
                    work.push(Pending::Read(Rc::clone(field)));
                }
            }
            _ => done.push(quote(0, &value)),
        }
        Ok(())
    }
}

/// Все ли элиминаторы спайна - применения.
fn applications(spine: &[Elim]) -> bool {
    spine.iter().all(|elim| matches!(elim, Elim::App(_)))
}
