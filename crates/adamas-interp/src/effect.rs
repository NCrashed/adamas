//! Операции, хендлеры и scope: где вычисление обрывается и кто его подхватывает.
//!
//! Операция обрывает вычисление тогда, когда получила аргумент, на стрелке
//! которого стоит row. Позиция эта не соглашение машины, а то самое место, где
//! объявление проверило форму операции (§3.4).
//!
//! **Хендлер ищется ближайший по стеку, и это совпадает с проверкой типов.**
//! Правило погашения `ε' ≡ ε ++ Λ` отдаёт вызываемому внутреннее вхождение
//! метки (§3.4, лог 2026-09-04), значит смещение вектора evidence всегда нуль -
//! искать по стеку и есть верный ответ, а не приближение к нему.
//!
//! Хендлер **глубокий**: сегмент резумпции включает сам кадр хендлера, поэтому
//! возобновление ставит его обратно, и операция после возобновления попадает
//! тому же хендлеру. §3.4 выбирает глубокий прямо - на нём стоит модель
//! стоимости.
//!
//! # Раскрутка видна в сегменте, а не ведётся рядом
//!
//! Деструктор ждёт выхода из scope кадром [`Frame::Closing`]. Когда ветка
//! хендлера не зовёт резумпцию, её сегмент выброшен - и всё, что надо
//! запустить, стоит **в нём**: обход находит и `Closing`, и вложенные
//! `Branch`, чьи собственные сегменты тоже брошены. Списка отложенного рядом со
//! стеком больше нет, а с ним и возможности разъехаться - на чём этот код
//! ловился трижды.

use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::DefinitionKind;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Elim, Value};

use crate::RunError;
use crate::frame::{Frame, Handler, Kont};
use crate::machine::{Machine, Step};

/// Невыразимые имена элиминаторов - те же, что ставит элаборация.
const HANDLE: &str = "#handle.";
const MULTI: &str = "#handleMulti.";
const CLOSING: &str = "#closing";

/// Имя единицы: приостановленное вычисление запускается её значением.
const UNIT: &str = "Unit";

impl Machine<'_> {
    /// Насыщенное имя, у которого есть эффектный смысл. `None` - обычное.
    ///
    /// # Errors
    ///
    /// Операция, не встретившая хендлера.
    pub(crate) fn effectful(
        &self,
        name: &Name,
        spine: &[Elim],
        kont: &mut Kont,
    ) -> Result<Option<Step>, RunError> {
        if &**name == CLOSING {
            let arguments = applied(spine);
            if arguments.len() < 4 {
                return Ok(None);
            }
            return Ok(Some(self.entering(&arguments, kont)?));
        }
        if let Some(definition) = self.signature().lookup(name)
            && let DefinitionKind::Operation { effect } = &definition.kind
        {
            let Some(arity) = performing(&definition.ty) else {
                return Ok(None);
            };
            let arguments = applied(spine);
            if arguments.len() < arity {
                return Ok(None);
            }
            return self.performed(effect, name, &arguments, kont).map(Some);
        }
        let Some(handler) = self.shape(name) else {
            return Ok(None);
        };
        let arguments = applied(spine);
        // Параметры метки, `a`, `b`, вычисление, `return` и ветки.
        let arity = handler.params + 4 + handler.operations.len();
        if arguments.len() < arity {
            return Ok(None);
        }
        Ok(Some(self.installed(handler, &arguments, kont)?))
    }

    /// Форма элиминатора: параметры метки, операции и арности веток.
    fn shape(&self, name: &Name) -> Option<Handler> {
        let effect = name
            .strip_prefix(MULTI)
            .or_else(|| name.strip_prefix(HANDLE))?;
        let definition = self.signature().lookup(effect)?;
        let DefinitionKind::Effect { operations, params } = &definition.kind else {
            return None;
        };
        let params = *params as usize;
        // Ветка получает не всё, что принимает операция: параметры метки она не
        // связывает, а синтезированный сахаром триггер - тем более. Сколько
        // именно - написано в типе элиминатора, где ветка стоит доменом.
        let eliminator = self.signature().lookup(name)?;
        let mut written = Vec::with_capacity(operations.len());
        for slot in 0..operations.len() {
            let branch = domain(&eliminator.ty, params + 4 + slot)?;
            written.push(binders(branch).checked_sub(1)?);
        }
        Some(Handler {
            effect: Rc::from(effect),
            params,
            operations: operations.iter().cloned().collect(),
            written: written.into(),
            // Ветки снимаются со спайна в `installed`.
            branches: Rc::from([]),
            returned: Rc::new(Value::Object(Rc::from([]))),
        })
    }

    /// Ставит хендлер и запускает под ним вычисление.
    fn installed(
        &self,
        shape: Handler,
        arguments: &[Rc<Value>],
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        let params = shape.params;
        let handler = Rc::new(Handler {
            branches: arguments[params + 4..params + 4 + shape.operations.len()]
                .iter()
                .map(Rc::clone)
                .collect(),
            returned: Rc::clone(&arguments[params + 3]),
            ..shape
        });
        let unit = self.unit()?;
        kont.push(Frame::Handler(handler));
        // Вычисление приостановлено: `{ε} A` есть нульместная функция.
        Ok(Step::Apply(Rc::clone(&arguments[params + 2]), unit))
    }

    /// Вычисление под хендлером кончилось значением - его принимает `return`.
    pub(crate) fn handled(value: Rc<Value>, handler: &Rc<Handler>) -> Step {
        Step::Apply(Rc::clone(&handler.returned), value)
    }

    /// Операция: ищет свой хендлер по стеку и снимает сегмент до него.
    fn performed(
        &self,
        effect: &Name,
        operation: &Name,
        arguments: &[Rc<Value>],
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        let found = kont.iter().enumerate().rev().find_map(|(index, frame)| {
            let Frame::Handler(handler) = frame else {
                return None;
            };
            if handler.effect != *effect {
                return None;
            }
            let slot = handler.operations.iter().position(|it| it == operation)?;
            Some((index, Rc::clone(handler), slot))
        });
        let Some((index, handler, slot)) = found else {
            return Err(RunError::Unhandled {
                effect: effect.to_string(),
                operation: operation.to_string(),
            });
        };
        // Сегмент включает сам кадр хендлера: возобновление ставит его обратно,
        // и это и значит «глубокий».
        let segment: Rc<[Frame]> = kont.drain(index..).collect();
        let (resume, ticket) = self.resumption(segment);
        let mut given: Vec<Rc<Value>> = arguments
            [handler.params..handler.params + handler.written[slot]]
            .iter()
            .map(Rc::clone)
            .collect();
        given.push(resume);
        let branch = Rc::clone(&handler.branches[slot]);
        kont.push(Frame::Branch(ticket));
        Ok(Machine::passing(branch, &given.into(), 0, kont))
    }

    /// Ветка договорила: жив ли остаток вычисления.
    ///
    /// Резумпцию не позвали - продолжение мертво, и всё, что оно было должно,
    /// стоит в его сегменте.
    pub(crate) fn settled(&self, ticket: usize, value: Rc<Value>, kont: &mut Kont) -> Step {
        if self.invoked(ticket) {
            return Step::Return(value);
        }
        let Some(segment) = self.segment(ticket) else {
            return Step::Return(value);
        };
        self.unwinding(&segment, segment.len(), value, kont)
    }

    /// Раскрутка выброшенного сегмента: сверху вниз, то есть изнутри наружу.
    ///
    /// `index` - сколько кадров ещё не пройдено. Обход находит и деструкторы
    /// этого сегмента, и брошенные ветки внутри него: их сегменты тоже мертвы.
    pub(crate) fn unwinding(
        &self,
        segment: &Rc<[Frame]>,
        index: usize,
        held: Rc<Value>,
        kont: &mut Kont,
    ) -> Step {
        let mut index = index;
        while index > 0 {
            index -= 1;
            match &segment[index] {
                Frame::Closing(close) => {
                    let Ok(unit) = self.unit() else {
                        continue;
                    };
                    let close = Rc::clone(close);
                    kont.push(Frame::Unwinding(Rc::clone(segment), index, held));
                    return Step::Apply(close, unit);
                }
                // Раскрутка, недобежавшая своё: её остаток брошен вместе с
                // этим сегментом. Случается, когда деструктор сам произвёл
                // операцию, а её оборвали.
                Frame::Unwinding(inner, at, _) => {
                    let (inner, at) = (Rc::clone(inner), *at);
                    kont.push(Frame::Unwinding(Rc::clone(segment), index, held));
                    return self.unwinding(&inner, at, self.trivial(), kont);
                }
                // Ветка внутри сегмента, чью резумпцию не позвали: её
                // собственный сегмент брошен вместе с этим.
                Frame::Branch(ticket) if !self.invoked(*ticket) => {
                    let Some(inner) = self.segment(*ticket) else {
                        continue;
                    };
                    kont.push(Frame::Unwinding(Rc::clone(segment), index, held));
                    let length = inner.len();
                    return self.unwinding(&inner, length, self.trivial(), kont);
                }
                _ => {}
            }
        }
        Step::Return(held)
    }

    /// Входит в scope, держащий ресурс: деструктор ждёт выхода кадром.
    fn entering(&self, arguments: &[Rc<Value>], kont: &mut Kont) -> Result<Step, RunError> {
        let [_, _, body, close] = arguments else {
            unreachable!("`#closing` объявлен четырёхместным");
        };
        let unit = self.unit()?;
        kont.push(Frame::Closing(Rc::clone(close)));
        Ok(Step::Apply(Rc::clone(body), unit))
    }

    /// Значение единицы - единственный конструктор `Unit`.
    ///
    /// # Errors
    ///
    /// Единицы в сигнатуре нет либо конструктор у неё не один: без неё
    /// приостановленного вычисления не существует, а значит и звать было нечего.
    pub(crate) fn unit(&self) -> Result<Rc<Value>, RunError> {
        let Some([only]) = self.signature().constructors(UNIT) else {
            return Err(RunError::NoUnit);
        };
        let Some(definition) = self.signature().lookup(only) else {
            return Err(RunError::NoUnit);
        };
        let levels: Vec<Level> = (0..definition.level_arity)
            .map(|_| Level::number(0))
            .collect();
        Ok(Value::constant(
            Rc::clone(only),
            &levels,
            Rc::from([] as [Row<Rc<Value>>; 0]),
        ))
    }

    /// Значение, которым раскрутка отчитывается: её ответа никто не читает.
    fn trivial(&self) -> Rc<Value> {
        self.unit()
            .unwrap_or_else(|_| Rc::new(Value::Object(Rc::from([]))))
    }
}

/// Аргументы из спайна. Прочие элиминаторы у насыщенного имени не встречаются.
fn applied(spine: &[Elim]) -> Vec<Rc<Value>> {
    spine
        .iter()
        .filter_map(|elim| match elim {
            Elim::App(argument) => Some(Rc::clone(argument)),
            _ => None,
        })
        .collect()
}

/// На каком по счёту аргументе операция производит. `None` - row нигде нет.
fn performing(ty: &Term) -> Option<usize> {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, _, _, row, codomain) = current {
        count += 1;
        if !row.labels().is_empty() {
            return Some(count);
        }
        current = codomain;
    }
    None
}

/// Сколько связываний у типа подряд.
fn binders(ty: &Term) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, _, _, _, codomain) = current {
        count += 1;
        current = codomain;
    }
    count
}

/// Домен связывания под номером `index`.
fn domain(ty: &Term, index: usize) -> Option<&Term> {
    let mut current = ty;
    for _ in 0..index {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    match current {
        Term::Pi(_, _, domain, _, _) => Some(domain),
        _ => None,
    }
}
