//! Владеемый тип в позиции типового параметра (§3.3, §10 вопрос 76).
//!
//! Правила владения читают голову написанного типа, а под переменной головы
//! нет. Ядро поэтому считает **кратность носителя** ([`adamas_core::carrier`]):
//! как определение обошлось со значениями каждого своего типового параметра.
//! Здесь эта кратность встречается с владением - той единственной стороной,
//! которая о нём знает.
//!
//! Правило одно: **владеемый тип инстанцирует только тот параметр, носитель
//! которого равен `1`.** `1` означает «всякое значение этого типа употреблено
//! ровно однажды», то есть ровно то, чего владение и требует: не забыто (иначе
//! `drop` не вызван) и не размножено (иначе два `drop` на один хендл).
//!
//! Проверка идёт по **уже объявленному** телу: к этому моменту дырки решены и
//! подставлены, поэтому видно, чем на самом деле стал каждый выводимый
//! аргумент. До объявления там стоит дырка, и смотреть не на что.
//!
//! Границы названы. Носитель постулата и конструктора неизвестен, поэтому `ω`,
//! и полиморфный контейнер владеемым типом не наполняется - а он и не пишется
//! (§10 вопрос 78). Держатель ресурсного поля при инстанциации - вторая
//! половина вопроса 76, и она уезжает туда же: без параметров семейства
//! `Pair File File` не собрать.

use std::rc::Rc;

use adamas_core::eval::eval;
use adamas_core::mult::Mult;
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Env, Head, Lvl, Value};
use adamas_parser::ast::Symbol;

use crate::error::ElabError;
use crate::own::Owned;

/// Проверяет тело определения на инстанциацию параметров владеемыми типами.
///
/// # Errors
///
/// [`ElabError::OwnedCarrier`], если владеемый тип подставлен в параметр,
/// носитель которого не `1`.
pub(crate) fn check(
    signature: &Signature,
    owned: &Owned,
    name: &Symbol,
    span: Span,
) -> Result<(), ElabError> {
    let Some(definition) = signature.lookup(name) else {
        return Ok(());
    };
    let mut found = None;
    if let Some(body) = &definition.body {
        walk(signature, owned, body, 0, &mut found);
    }
    // Тип смотрится тоже: `f : Wrap File -> Bool` инстанцирует параметр `Wrap`
    // ничуть не меньше, чем это делает тело.
    walk(signature, owned, &definition.ty, 0, &mut found);
    match found {
        Some(Bad::Carrier {
            callee,
            parameter,
            owned,
            carrier,
        }) => Err(ElabError::OwnedCarrier {
            callee,
            parameter,
            owned,
            carrier,
            span,
        }),
        Some(Bad::Holder { family, owned }) => Err(ElabError::OwnedHolder {
            family,
            owned,
            span,
        }),
        None => Ok(()),
    }
}

/// Найденное нарушение.
enum Bad {
    /// Определение обходится со значениями параметра не так, как требует
    /// владение.
    Carrier {
        callee: Symbol,
        parameter: Symbol,
        owned: Symbol,
        carrier: Mult,
    },
    /// Семейство без деструктора наполнено владеемым типом.
    Holder { family: Symbol, owned: Symbol },
}

/// `depth` - сколько связываний открыто над термом: аргумент вычисляется, и
/// без окружения такого размера вычислять его нечем.
fn walk(signature: &Signature, owned: &Owned, term: &Term, depth: u32, found: &mut Option<Bad>) {
    if found.is_some() {
        return;
    }
    if let Term::App(..) = term {
        spine(signature, owned, term, depth, found);
    }
    match term {
        Term::App(callee, argument) => {
            walk(signature, owned, callee, depth, found);
            walk(signature, owned, argument, depth, found);
        }
        Term::Lam(_, _, body) => walk(signature, owned, body, depth + 1, found),
        Term::Pi(_, _, domain, row, codomain) => {
            walk(signature, owned, domain, depth, found);
            for label in row.labels() {
                for argument in &label.arguments {
                    walk(signature, owned, argument, depth, found);
                }
            }
            walk(signature, owned, codomain, depth + 1, found);
        }
        Term::Let(_, _, ty, value, body) => {
            walk(signature, owned, ty, depth, found);
            walk(signature, owned, value, depth, found);
            walk(signature, owned, body, depth + 1, found);
        }
        Term::Case(case) => {
            walk(signature, owned, &case.scrutinee, depth, found);
            walk(signature, owned, &case.motive, depth, found);
            for branch in &case.branches {
                walk(signature, owned, &branch.body, depth, found);
            }
        }
        Term::Var(_) | Term::Universe(_) | Term::Const(..) | Term::Meta(_) => {}
    }
}

/// Разбирает спайн применения: голова, аргументы, носители головы.
fn spine(signature: &Signature, owned: &Owned, term: &Term, depth: u32, found: &mut Option<Bad>) {
    let mut arguments = Vec::new();
    let mut head = term;
    while let Term::App(callee, argument) = head {
        arguments.push(&**argument);
        head = callee;
    }
    arguments.reverse();
    let Term::Const(callee, _) = head else {
        return;
    };
    let Some(definition) = signature.lookup(callee) else {
        return;
    };
    // Семейство - отдельное правило: параметр, инстанцированный владеемым
    // типом, делает поле конструктора ресурсным, а держатель обязан быть
    // `resource` (§3.3, вопрос 77). Носителем это не выражается: положить
    // ресурс однажды - как раз то, что конструктор и делает.
    // Конструктор идёт за своим семейством: `Nil` кладёт значение в `List`,
    // и держатель тут - `List`, а не `Nil`.
    let family = match &definition.kind {
        DefinitionKind::Data { .. } => Some(Rc::clone(callee)),
        DefinitionKind::Constructor { data, .. } => Some(Rc::clone(data)),
        DefinitionKind::Regular => None,
    };
    for (position, argument) in arguments.iter().enumerate() {
        // `1` - ограничения нет; так помечены и позиции, которые вовсе не
        // параметры типа.
        let carrier = definition.carriers.get(position).copied();
        let Some(carrier) = carrier.filter(|it| family.is_some() || *it != Mult::One) else {
            continue;
        };
        let Some(head) = constant(argument, depth) else {
            continue;
        };
        if !owned.owns(&head) {
            continue;
        }
        // Семейство, само объявленное `resource`, держать ресурс вправе: у
        // него есть деструктор, и §3.3 требует ровно этого.
        if let Some(family) = &family {
            if owned.owns(family) {
                continue;
            }
            *found = Some(Bad::Holder {
                family: Rc::from(&**family),
                owned: Rc::from(&*head),
            });
            return;
        }
        *found = Some(Bad::Carrier {
            callee: Rc::from(&**callee),
            parameter: parameter(&definition.ty, position),
            owned: Rc::from(&*head),
            carrier,
        });
        return;
    }
}

/// Голова аргумента - **вычисленная**, а не прочитанная синтаксически.
///
/// Решение дырки подставляется зонканьем как есть, поэтому выводимый аргумент
/// доезжает сюда бета-редексом: `(\m0 -> File) h`. Синтаксический поиск головы
/// увидел бы там лямбду; вычисление видит `File`. Окружение - свежие
/// переменные по числу открытых связываний: терм уже проверен, значит
/// вычислим.
fn constant(term: &Term, depth: u32) -> Option<Name> {
    let env = (0..depth).fold(Env::default(), |env, level| {
        env.extend(Value::var(Lvl(level)))
    });
    match &*eval(&env, term) {
        Value::Neutral(Head::Global(name, _), _) => Some(Rc::clone(name)),
        _ => None,
    }
}

/// Имя связывания на этой позиции телескопа - для сообщения.
fn parameter(ty: &Term, position: usize) -> Symbol {
    let mut current = ty;
    for _ in 0..position {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return Rc::from("_");
        };
        current = codomain;
    }
    match current {
        Term::Pi(_, name, ..) => Rc::from(&**name),
        _ => Rc::from("_"),
    }
}
