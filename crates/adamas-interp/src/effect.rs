//! Операции и хендлеры: где вычисление обрывается и кто его подхватывает.
//!
//! Операция обрывает вычисление тогда, когда получила аргумент, на стрелке
//! которого стоит row. Позиция эта не соглашение машины, а то самое место, где
//! объявление проверило форму операции (§3.4): row обязана стоять где-то в
//! типе, и стоит она ровно на последней стрелке.
//!
//! Хендлер **глубокий**: резумпция переустанавливает его на себе, поэтому
//! операция, произведённая после возобновления, попадает тому же хендлеру.
//! §3.4 выбирает глубокий прямо - на нём стоит модель стоимости
//! («tail-resumptive → inline без overhead»).
//!
//! **Хендлер ищется ближайший по стеку, и это совпадает с проверкой типов.**
//! Правило погашения `ε' ≡ ε ++ Λ` отдаёт вызываемому **внутреннее** вхождение
//! метки (§3.4, лог 2026-09-04), значит смещение вектора evidence всегда нуль -
//! искать по стеку и есть верный ответ, а не приближение к нему. Прежняя
//! ориентация `Λ ++ ε` расходилась с этим поиском на вложенных хендлерах одной
//! метки, и разворот правила расхождение снял.
//!
//! Осталась от evidence-трансляции половина стоимостная: явный вектор вместо
//! динамического проброса наружу. Потребитель у неё - codegen (§9 Фаза 6).

use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::DefinitionKind;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Elim, Value};

use crate::machine::Machine;
use crate::outcome::{Cont, Outcome, Performed, identity};

/// Невыразимые имена элиминаторов - те же, что ставит элаборация.
const HANDLE: &str = "#handle.";
const MULTI: &str = "#handleMulti.";

/// Имя единицы: вычисление под хендлером запускается её значением.
const UNIT: &str = "Unit";

/// Невыразимое имя элиминатора scope - то же, что ставит элаборация.
const CLOSING: &str = "#closing";

/// Форма элиминатора: всё, что читается из сигнатуры, а не со спайна.
struct Shape {
    /// Метка, которую он снимает.
    effect: Name,
    /// Сколько ведущих аргументов операции - параметры метки.
    params: usize,
    /// Операции метки в порядке объявления - он же порядок веток.
    operations: Rc<[Name]>,
    /// Сколько аргументов связывает ветка каждой операции.
    written: Rc<[usize]>,
}

/// Хендлер: форма вместе с ветками, снятыми со спайна.
struct Handler {
    shape: Shape,
    /// Ветви в порядке операций.
    branches: Rc<[Rc<Value>]>,
    /// Ветвь `return`.
    returned: Rc<Value>,
}

impl Machine<'_> {
    /// Насыщенное имя, у которого есть эффектный смысл. `None` - обычное.
    pub(crate) fn effectful(&self, name: &Name, spine: &[Elim]) -> Option<Outcome> {
        // Scope, держащий ресурс: тело под ним запускает машина, чтобы видеть,
        // что из него вышли (§3.3).
        if &**name == CLOSING {
            let arguments = applied(spine);
            return (arguments.len() >= 4).then(|| self.closing(&arguments));
        }
        if let Some(definition) = self.signature().lookup(name)
            && let DefinitionKind::Operation { effect } = &definition.kind
        {
            let arity = performing(&definition.ty)?;
            let arguments = applied(spine);
            return (arguments.len() >= arity).then(|| {
                Outcome::Performed(Performed {
                    effect: Rc::clone(effect),
                    operation: Rc::clone(name),
                    arguments,
                    resumption: identity(),
                    pending: Vec::new(),
                })
            });
        }

        let shape = self.shape(name)?;
        let arguments = applied(spine);
        // Параметры метки, `a`, `b`, вычисление, `return` и ветки.
        let arity = shape.params + 4 + shape.operations.len();
        (arguments.len() >= arity).then(|| self.install(name, shape, &arguments))
    }

    /// Форма элиминатора: параметры метки, операции и арности веток.
    ///
    /// `None` - имя не элиминатор. Различаются они по имени, потому что и
    /// заводит их элаборация именем: тела у элиминатора нет, ролью в сигнатуре
    /// он постулат, и отличить его от всякого другого постулата больше нечем.
    fn shape(&self, name: &Name) -> Option<Shape> {
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
        Some(Shape {
            effect: Rc::from(effect),
            params,
            operations: operations.iter().cloned().collect(),
            written: written.into(),
        })
    }

    /// Ставит хендлер и запускает под ним вычисление.
    fn install(&self, name: &Name, shape: Shape, arguments: &[Rc<Value>]) -> Outcome {
        let params = shape.params;
        let handler = Rc::new(Handler {
            branches: arguments[params + 4..params + 4 + shape.operations.len()]
                .iter()
                .map(Rc::clone)
                .collect(),
            returned: Rc::clone(&arguments[params + 3]),
            shape,
        });
        let Some(unit) = self.unit() else {
            unreachable!("элиминатор `{name}` объявлен, а единицы в сигнатуре нет");
        };
        // Вычисление приостановлено: `{ε} A` есть нульместная функция, и
        // запускает её единица (§3.4).
        let outcome = self.apply(&arguments[params + 2], unit);
        self.handled(outcome, &handler)
    }

    /// Разбирает исход вычисления, стоящего под хендлером.
    fn handled(&self, outcome: Outcome, handler: &Rc<Handler>) -> Outcome {
        let performed = match outcome {
            // Вычисление кончилось значением - его принимает `return`.
            Outcome::Done(value) => return self.apply(&handler.returned, value),
            Outcome::Performed(performed) => performed,
        };
        let Some(slot) = handler
            .shape
            .operations
            .iter()
            .position(|operation| *operation == performed.operation)
            .filter(|_| performed.effect == handler.shape.effect)
        else {
            // Чужая метка идёт наружу, а хендлер переустанавливается на
            // продолжении: возобновлённое вычисление обязано снова оказаться
            // под ним. Это и значит «глубокий».
            let handler = Rc::clone(handler);
            let inner = Rc::clone(&performed.resumption);
            return Outcome::Performed(Performed {
                resumption: Rc::new(move |machine, value| {
                    machine.handled(inner(machine, value), &handler)
                }),
                ..performed
            });
        };

        let written = handler.shape.written[slot];
        let branch = Rc::clone(&handler.branches[slot]);
        let mut given: Vec<Rc<Value>> = performed.arguments
            [handler.shape.params..handler.shape.params + written]
            .iter()
            .map(Rc::clone)
            .collect();
        let (resume, slot) = self.resumption(resuming(&performed.resumption, handler));
        given.push(resume);
        let outcome = self.pass(branch, &given, 0);
        self.settled(outcome, slot, &performed.pending)
    }

    /// Ветка договорила: пора решать, жив ли остаток вычисления.
    ///
    /// Пока ветка сама производит операции, решать рано - `resume` она вправе
    /// позвать и после них.
    fn settled(&self, outcome: Outcome, slot: usize, pending: &[Rc<Value>]) -> Outcome {
        let performed = match outcome {
            Outcome::Done(value) if self.invoked(slot) => return Outcome::Done(value),
            // Продолжение выброшено вместе со всем, что в нём стояло, - а
            // деструкторы там стояли (§3.3).
            Outcome::Done(value) => return self.unwound(pending, 0, &value),
            Outcome::Performed(performed) => performed,
        };
        // Ветка сама произвела операцию, и оборвать её вправе уже снаружи -
        // не эту, так следующую на том же пути. Выброшенным тогда окажется
        // **это** продолжение вместе с отложенными деструкторами, и запустить
        // их будет некому. Они и есть долг: едет он со всей цепочкой, и платит
        // его тот, кто её оборвал.
        let owed: Rc<[Rc<Value>]> = pending.into();
        let pending = pending.to_vec();
        Outcome::Performed(performed.owing(
            owed,
            Rc::new(move |machine, value| machine.settled(Outcome::Done(value), slot, &pending)),
        ))
    }

    /// Применяет ветку к её аргументам по одному.
    ///
    /// Тело ветки работает в окружающей самого `handle`, поэтому произвести
    /// операцию оно вправе - и производит её **мимо** этого хендлера.
    fn pass(&self, branch: Rc<Value>, given: &[Rc<Value>], from: usize) -> Outcome {
        let mut branch = branch;
        for index in from..given.len() {
            match self.apply(&branch, Rc::clone(&given[index])) {
                Outcome::Done(value) => branch = value,
                Outcome::Performed(performed) => {
                    let given = given.to_vec();
                    return Outcome::Performed(performed.after(Rc::new(move |machine, branch| {
                        machine.pass(branch, &given, index + 1)
                    })));
                }
            }
        }
        Outcome::Done(branch)
    }

    /// Значение единицы - единственный конструктор `Unit`.
    pub(crate) fn unit(&self) -> Option<Rc<Value>> {
        let [only] = self.signature().constructors(UNIT)? else {
            return None;
        };
        let definition = self.signature().lookup(only)?;
        let levels: Vec<Level> = (0..definition.level_arity)
            .map(|_| Level::number(0))
            .collect();
        Some(Value::constant(
            Rc::clone(only),
            &levels,
            Rc::from([] as [Row<Rc<Value>>; 0]),
        ))
    }
}

/// Резумпция: продолжение вместе с переустановленным хендлером.
fn resuming(inner: &Cont, handler: &Rc<Handler>) -> Cont {
    let (inner, handler) = (Rc::clone(inner), Rc::clone(handler));
    Rc::new(move |machine, value| machine.handled(inner(machine, value), &handler))
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
