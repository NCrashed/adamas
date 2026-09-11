//! Дробление тел кадрами: подготовка представления (решение 3 волны 4).
//!
//! Проход **IR → IR**, и стоит он до вставки RC: дробление меняет порядок
//! вычисления - подвыражение, способное приостановиться, становится отдельным
//! связыванием, - а владение считается по тому порядку, который останется.
//! Устрой это после [`perceus`](crate::perceus), и `dup` с `drop` стояли бы по
//! прежнему порядку.
//!
//! # Что такое точка приостановки
//!
//! Место, где вычисление вправе не вернуться сюда же: операция, возобновление
//! резумпции, вход в хендлер, выход из scope с ресурсом, применение значения и
//! вызов функции, внутри которой есть что-то из перечисленного. Единица
//! дробления - ровно она (решение 3): кадр ставится на неё, максимальный чистый
//! отрезок между двумя точками бежит обычным C. Мельче - плата трамплину на
//! каждом шаге; крупнее - не приостановить.
//!
//! # Что делает проход
//!
//! *Считает, кто приостанавливается.* [`suspending`] - неподвижная точка по
//! графу вызовов. Вторая форма, внутри которой приостановиться нечем, дробления
//! не получает и остаётся обычной C-функцией: лямбда без эффектов не платит за
//! трамплин ничего, и чистый код, применяющий её, - тоже.
//!
//! *Выносит вычисление под хендлером из первой формы.* Кадр `HANDLER` в чистой
//! функции ставится (`runIO` гасит `IO` внутри себя), а вычисление под ним -
//! код второй формы, и дробить его надо кадрами. Дроблёный код есть цепочка
//! C-функций, а вложенных функций в C нет, - поэтому вычисление уезжает в
//! собственную функцию, а свободные связывания идут ей параметрами.
//!
//! *Приводит тела к форме, где точка приостановки стоит связыванием либо в
//! хвосте.* Иначе продолжение точки пришлось бы искать внутри выражения:
//! `Cons n (resume MkUnit)` есть «возобновить, потом собрать `Cons`», и второй
//! половине нужно имя, чтобы стать кодом кадра.
//!
//! # Чего проход не делает
//!
//! Кадров не ставит и функций не дробит: то и другое - работа эмиттера, потому
//! что кадр есть форма C-функции, а не узел IR. Здесь только порядок и границы.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    Arm, Binding, Expr, Fact, Form, FuncId, Function, LocalId, Packing, Program, Repr,
};

/// Функции, чей вызов есть точка приостановки.
///
/// Неподвижная точка: своя причина - операция, хендлер, scope с ресурсом,
/// применение значения либо возобновление; наведённая - вызов такой же.
/// Первая форма сюда не входит ни при каких обстоятельствах: хендлер она
/// заводит на **своём** корне и наружу приостановки не отдаёт (§3.4, погашение
/// расширением справа).
#[must_use]
pub fn suspending(program: &Program) -> BTreeSet<FuncId> {
    let mut found = BTreeSet::new();
    loop {
        let mut grew = false;
        for function in &program.functions {
            if function.form != Form::Detached || found.contains(&function.id) {
                continue;
            }
            if suspends(&function.body, &found) {
                found.insert(function.id);
                grew = true;
            }
        }
        if !grew {
            return found;
        }
    }
}

/// Есть ли внутри выражения точка приостановки.
///
/// Читают это двое, и запись у них одна: проход выносит такое подвыражение в
/// связывание, эмиттер ставит под него кадр. Разойдись они - кадр встал бы не
/// там, где приостановка.
#[must_use]
pub fn halts(expr: &Expr, known: &BTreeSet<FuncId>) -> bool {
    suspends(expr, known)
}

/// Связывания, которые выражение называет. Читает это эмиттер: среда кадра
/// продолжения есть ровно то, что продолжение называет и не вводит само.
pub(crate) fn mentioned(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    named(expr, out);
}

/// Связывания, которые выражение вводит.
pub(crate) fn introduces(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    introduced(expr, out);
}

/// Есть ли внутри выражения точка приостановки.
fn suspends(expr: &Expr, known: &BTreeSet<FuncId>) -> bool {
    let here = match expr {
        Expr::Perform { .. }
        | Expr::Handle { .. }
        | Expr::Closing { .. }
        | Expr::Resume { .. }
        // Граница замыкания динамическая: какая из форм за указателем, место
        // вызова не знает, поэтому применение значения приостанавливается
        // всегда. Снимет это вопрос 74 вместе с инлайнингом.
        | Expr::Apply { .. } => true,
        Expr::Call { function, .. } => known.contains(function),
        _ => false,
    };
    here || expr
        .children()
        .into_iter()
        .any(|child| suspends(child, known))
}

/// Готовит программу к дроблению: выносит вычисления и нормализует порядок.
#[must_use]
pub fn prepare(program: Program) -> Program {
    let program = extracted(program);
    let known = suspending(&program);
    let results: Vec<Repr> = program.functions.iter().map(|it| it.result).collect();
    let Program {
        constructors,
        packings,
        labels,
        handlers,
        mut functions,
        entry,
    } = program;
    for function in &mut functions {
        if !known.contains(&function.id) {
            continue;
        }
        let mut pass = Anf {
            known: &known,
            results: &results,
            packings: &packings,
            locals: shapes(function),
            next: ceiling(function),
        };
        let body = std::mem::replace(&mut function.body, Expr::Erased);
        function.body = pass.tail(body);
    }
    Program {
        constructors,
        packings,
        labels,
        handlers,
        functions,
        entry,
    }
}

/// Выносит вычисление под хендлером из первой формы в свою функцию.
///
/// Только из первой: во второй вычисление есть хвост того же дроблёного тела -
/// кадр `HANDLER` уже лежит под ним, - и выносить нечего.
fn extracted(program: Program) -> Program {
    let Program {
        constructors,
        packings,
        labels,
        handlers,
        mut functions,
        entry,
    } = program;
    let written = functions.len();
    let mut next = written;
    for at in 0..written {
        if functions[at].form != Form::Stack {
            continue;
        }
        let facts = declared(&functions[at]);
        let mut body = std::mem::replace(&mut functions[at].body, Expr::Erased);
        let mut made = Vec::new();
        hoist_handles(&mut body, &facts, &mut next, &mut made);
        functions[at].body = body;
        functions.extend(made);
    }
    Program {
        constructors,
        packings,
        labels,
        handlers,
        functions,
        entry,
    }
}

/// Обходит тело и выносит каждое вычисление под `handle` в свою функцию.
fn hoist_handles(
    expr: &mut Expr,
    facts: &BTreeMap<LocalId, Fact>,
    next: &mut usize,
    made: &mut Vec<Function>,
) {
    if let Expr::Handle { computation, .. } = expr {
        let mut free: BTreeSet<LocalId> = BTreeSet::new();
        named(computation, &mut free);
        let mut inner = BTreeSet::new();
        introduced(computation, &mut inner);
        let parameters: Vec<Binding> = free
            .into_iter()
            .filter(|local| !inner.contains(local))
            .filter_map(|local| {
                Some(Binding {
                    name: format!("v{}", local.0),
                    local,
                    fact: *facts.get(&local)?,
                })
            })
            .collect();
        let id = FuncId(*next);
        *next += 1;
        let arguments: Vec<Expr> = parameters
            .iter()
            .map(|binding| {
                if binding.fact.present {
                    Expr::Local(binding.local)
                } else {
                    Expr::Erased
                }
            })
            .collect();
        let taken = std::mem::replace(&mut **computation, Expr::Erased);
        made.push(Function {
            id,
            name: "вычисление под хендлером".to_owned(),
            form: Form::Detached,
            captured: Vec::new(),
            parameters,
            result: Repr::Boxed,
            body: taken,
        });
        **computation = Expr::Call {
            function: id,
            arguments,
        };
    }
    for child in children_mut(expr) {
        hoist_handles(child, facts, next, made);
    }
}

/// Прямые подвыражения изменяемо - зеркало [`Expr::children`].
///
/// Второй обход заводится по необходимости: изменяемого шага у представления
/// нет, а обход по `children` отдаёт ссылки. Узел, забытый здесь, оставил бы
/// вычисление невынесенным, и порождённый C не собрался бы - молчаливым такой
/// пропуск не бывает.
fn children_mut(expr: &mut Expr) -> Vec<&mut Expr> {
    match expr {
        Expr::Local(_)
        | Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::LayoutField { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => Vec::new(),
        Expr::Unpack { value, .. } => vec![value],
        Expr::RegionLast { region } => vec![region],
        Expr::RegionAlloc { region, value, .. } => vec![region, value],
        Expr::RegionRead { region, at, .. }
        | Expr::RegionRecycle { region, at }
        | Expr::RegionPop { region, at } => vec![region, at],
        Expr::RegionWrite {
            region, at, value, ..
        } => vec![region, at, value],
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Perform { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => arguments.iter_mut().collect(),
        Expr::Handle {
            captured,
            computation,
            ..
        } => captured.iter_mut().chain([&mut **computation]).collect(),
        Expr::Closing { captured, body, .. } => captured.iter_mut().chain([&mut **body]).collect(),
        Expr::ArrayNew { count, initial, .. } => vec![count, initial],
        Expr::ArraySet {
            array, at, value, ..
        } => vec![array, at, value],
        Expr::ArrayIndex { array, at, .. } => vec![array, at],
        Expr::Resume { resumption, value } => vec![resumption, value],
        Expr::Closure { captured, .. } => captured.iter_mut().collect(),
        Expr::Primitive { left, right, .. } => vec![left, right],
        Expr::Apply { callee, argument } => vec![callee, argument],
        Expr::Bind { value, body, .. } => vec![value, body],
        Expr::Match {
            scrutinee, arms, ..
        } => [&mut **scrutinee]
            .into_iter()
            .chain(arms.iter_mut().map(|arm| &mut arm.body))
            .collect(),
        Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
            vec![body]
        }
    }
}

/// Связывания, которые выражение называет.
fn named(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    match expr {
        Expr::Local(local)
        | Expr::LayoutField {
            descriptor: local, ..
        }
        | Expr::Dup { local, .. }
        | Expr::Drop { local, .. }
        | Expr::Reclaim { local, .. } => {
            out.insert(*local);
        }
        _ => {}
    }
    for child in expr.children() {
        named(child, out);
    }
}

/// Связывания, которые выражение вводит.
fn introduced(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    match expr {
        Expr::Bind { binding, .. } => {
            out.insert(binding.local);
        }
        Expr::Match { arms, .. } => {
            for field in arms.iter().flat_map(|arm| &arm.fields) {
                out.insert(field.local);
            }
        }
        Expr::Reclaim { token, .. } => {
            out.insert(*token);
        }
        _ => {}
    }
    for child in expr.children() {
        introduced(child, out);
    }
}

/// Факты обо всех связываниях тела.
fn stated(expr: &Expr, out: &mut BTreeMap<LocalId, Fact>) {
    match expr {
        Expr::Bind { binding, .. } => {
            out.insert(binding.local, binding.fact);
        }
        Expr::Match { arms, .. } => {
            for field in arms.iter().flat_map(|arm| &arm.fields) {
                out.insert(field.local, field.fact);
            }
        }
        _ => {}
    }
    for child in expr.children() {
        stated(child, out);
    }
}

/// Факты обо всех связываниях функции.
fn declared(function: &Function) -> BTreeMap<LocalId, Fact> {
    let mut found: BTreeMap<LocalId, Fact> = function
        .captured
        .iter()
        .chain(&function.parameters)
        .map(|binding| (binding.local, binding.fact))
        .collect();
    stated(&function.body, &mut found);
    found
}

/// Представления всех связываний функции.
fn shapes(function: &Function) -> BTreeMap<LocalId, Repr> {
    declared(function)
        .into_iter()
        .map(|(local, fact)| (local, fact.repr))
        .collect()
}

/// Первый свободный номер связывания.
fn ceiling(function: &Function) -> u32 {
    let mut top = 0;
    for local in declared(function).keys() {
        top = top.max(local.0 + 1);
    }
    let mut tokens = BTreeSet::new();
    introduced(&function.body, &mut tokens);
    for local in tokens {
        top = top.max(local.0 + 1);
    }
    top
}

/// Приведение тела к форме, где точка приостановки стоит связыванием.
struct Anf<'a> {
    known: &'a BTreeSet<FuncId>,
    results: &'a [Repr],
    packings: &'a [Packing],
    locals: BTreeMap<LocalId, Repr>,
    next: u32,
}

impl Anf<'_> {
    /// Свежее связывание под вынесенное подвыражение.
    fn temporary(&mut self, repr: Repr) -> Binding {
        let local = LocalId(self.next);
        self.next += 1;
        self.locals.insert(local, repr);
        Binding {
            name: "приостановка".to_owned(),
            local,
            fact: Fact::opaque().shaped(repr),
        }
    }

    /// Есть ли внутри точка приостановки.
    fn stops(&self, expr: &Expr) -> bool {
        suspends(expr, self.known)
    }

    /// Представление значения выражения.
    fn shape(&self, expr: &Expr) -> Repr {
        match expr {
            Expr::Local(local) => self.locals.get(local).copied().unwrap_or(Repr::Boxed),
            Expr::Literal { ty, .. } | Expr::Primitive { ty, .. } => Repr::Flat(*ty),
            Expr::Call { function, .. } => {
                self.results.get(function.0).copied().unwrap_or(Repr::Boxed)
            }
            Expr::Bind { body, .. }
            | Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. }
            | Expr::Closing { body, .. } => self.shape(body),
            Expr::Match { arms, .. } => arms
                .first()
                .map_or(Repr::Boxed, |arm| self.shape(&arm.body)),
            Expr::Layout { .. } => Repr::Layout,
            Expr::LayoutField { .. } => Repr::Flat(adamas_core::prim::PrimTy::UInt32),
            Expr::Pack { packing, .. } => Repr::Packed(*packing),
            Expr::Unpack {
                packing,
                variant,
                field,
                ..
            } => self.packings[packing.0 as usize].variants[*variant as usize].slots
                [*field as usize]
                .ty
                .repr(),
            Expr::ArrayNew { stride, .. } | Expr::ArraySet { stride, .. } => {
                Repr::Array(match stride {
                    Some(_) => crate::ir::Elems::Flat,
                    None => crate::ir::Elems::Boxed,
                })
            }
            Expr::ArrayIndex { stride, .. } => {
                stride.map_or(Repr::Boxed, crate::ir::Stride::element)
            }
            Expr::RegionNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => Repr::Region,
            Expr::RegionLast { .. } => Repr::Flat(adamas_core::prim::PrimTy::UInt64),
            Expr::RegionRead { stride, .. } => stride.element(),
            Expr::Erased
            | Expr::Construct { .. }
            | Expr::ConstructClosure { .. }
            | Expr::Closure { .. }
            | Expr::Handle { .. }
            | Expr::Perform { .. }
            | Expr::Resume { .. }
            | Expr::Apply { .. } => Repr::Boxed,
        }
    }

    /// Выражение в хвостовой позиции: продолжения у него нет.
    fn tail(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Bind {
                binding,
                value,
                body,
            } => {
                let value = self.stepped(*value);
                Expr::Bind {
                    binding,
                    value: Box::new(value),
                    body: Box::new(self.tail(*body)),
                }
            }
            Expr::Dup { local, body } => Expr::Dup {
                local,
                body: Box::new(self.tail(*body)),
            },
            Expr::Drop { local, body } => Expr::Drop {
                local,
                body: Box::new(self.tail(*body)),
            },
            Expr::Reclaim { local, token, body } => Expr::Reclaim {
                local,
                token,
                body: Box::new(self.tail(*body)),
            },
            Expr::Match {
                scrutinee,
                consumed,
                arms,
            } => {
                let mut binds = Vec::new();
                let scrutinee = self.operand(*scrutinee, &mut binds);
                let arms = arms
                    .into_iter()
                    .map(|arm| Arm {
                        constructor: arm.constructor,
                        fields: arm.fields,
                        body: self.tail(arm.body),
                    })
                    .collect();
                bound(
                    binds,
                    Expr::Match {
                        scrutinee: Box::new(scrutinee),
                        consumed,
                        arms,
                    },
                )
            }
            // Вычисление под хендлером и тело scope - хвосты своих кадров:
            // кадр стоит **под** ними, и значение доходит до него трамплином.
            Expr::Handle {
                handler,
                captured,
                computation,
            } => {
                let mut binds = Vec::new();
                let captured = captured
                    .into_iter()
                    .map(|capture| self.operand(capture, &mut binds))
                    .collect();
                let computation = self.tail(*computation);
                bound(
                    binds,
                    Expr::Handle {
                        handler,
                        captured,
                        computation: Box::new(computation),
                    },
                )
            }
            Expr::Closing {
                closer,
                captured,
                body,
            } => {
                let mut binds = Vec::new();
                let captured = captured
                    .into_iter()
                    .map(|capture| self.operand(capture, &mut binds))
                    .collect();
                let body = self.tail(*body);
                bound(
                    binds,
                    Expr::Closing {
                        closer,
                        captured,
                        body: Box::new(body),
                    },
                )
            }
            other => self.stepped(other),
        }
    }

    /// Выражение, чьё значение принимает одно связывание либо хвост.
    ///
    /// Само оно вправе приостановиться - кадр под него поставит эмиттер, - а
    /// подвыражения его обязаны быть чистыми: их считает тот же отрезок C.
    fn stepped(&mut self, expr: Expr) -> Expr {
        if !self.stops(&expr) {
            return expr;
        }
        match expr {
            // Составные узлы остаются собой: внутри них хвост, а не операнд.
            Expr::Bind { .. }
            | Expr::Dup { .. }
            | Expr::Drop { .. }
            | Expr::Reclaim { .. }
            | Expr::Match { .. }
            | Expr::Handle { .. }
            | Expr::Closing { .. } => self.tail(expr),
            other => {
                let mut binds = Vec::new();
                let node = self.operands(other, &mut binds);
                bound(binds, node)
            }
        }
    }

    /// Переводит операнды узла, вынося те, что приостанавливаются.
    ///
    /// Выносятся **все** операнды разом, а не только приостанавливающиеся:
    /// порядок вычисления значим - переиспользование ячейки и запись по месту
    /// спрашивают уникальность в рантайме, - и оставить сосед на месте значило
    /// бы посчитать его позже, чем он написан.
    fn operands(&mut self, expr: Expr, binds: &mut Vec<(Binding, Expr)>) -> Expr {
        let mut node = expr;
        for child in children_mut(&mut node) {
            let taken = std::mem::replace(child, Expr::Erased);
            *child = self.operand(taken, binds);
        }
        node
    }

    /// Операнд: чистый остаётся собой, приостанавливающийся уезжает в связывание.
    fn operand(&mut self, expr: Expr, binds: &mut Vec<(Binding, Expr)>) -> Expr {
        if !self.stops(&expr) {
            return expr;
        }
        if matches!(expr, Expr::Local(_) | Expr::Erased) {
            return expr;
        }
        let value = self.stepped(expr);
        let repr = self.shape(&value);
        let binding = self.temporary(repr);
        let local = binding.local;
        binds.push((binding, value));
        Expr::Local(local)
    }
}

/// Оборачивает выражение вынесенными связываниями в порядке вычисления.
fn bound(binds: Vec<(Binding, Expr)>, body: Expr) -> Expr {
    binds
        .into_iter()
        .rev()
        .fold(body, |body, (binding, value)| Expr::Bind {
            binding,
            value: Box::new(value),
            body: Box::new(body),
        })
}
