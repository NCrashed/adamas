//! Кратность носителя: как определение обходится со значениями типа-параметра.
//!
//! # Зачем
//!
//! Правила владения (§3.3) читают **голову написанного типа**: связывание типа
//! `File` получает `1`, забытое закрывается вставленным `drop`, поле требует
//! держателя-`resource`. Под переменной типа головы нет, поэтому не срабатывает
//! ни одно из трёх, и `ignore : a -> Bool` с телом `ignore x = True` принимает
//! `File` и не закрывает его (§10 вопрос 76).
//!
//! Тип этого не расскажет: `consumeWith` и `ignoreWith` ниже отличаются только
//! телом, а сигнатура у них одна.
//!
//! ```text
//! consumeWith : (1 x : a) -> (1 f : (1 y : a) -> Bool) -> Bool
//! consumeWith x f = f x        -- потребляет
//! ignoreWith  x f = True       -- течёт
//! ```
//!
//! Значит нужна величина, выведенная из **тела**. Проверка её уже считает:
//! вектор использований даёт фактическую кратность каждого связывания, а
//! объявленная стоит на связывании. Здесь она только собирается по параметрам.
//!
//! # Что именно собирается
//!
//! Для каждого связывания, **тип которого есть в точности переменная** `a`:
//!
//! - объявленная кратность `0` — связывание стёрто, значения в рантайме не
//!   возникает, и обязательства с ним никакого; такое пропускается;
//! - фактическое употребление `0` — значение забыто, носитель `0`;
//! - фактическое `ω` — значение алиасировано, носитель `ω`;
//! - фактическое `1` — ровно то, чего требует владение.
//!
//! Считается **фактическое**, а не объявленное: `identity x = x` объявлена `ω`
//! по умолчанию (§4.1), но значение из неё выходит обратно, и владение
//! продолжается у вызывающего. Объявленная кратность значима только когда она
//! `0`.
//!
//! Итог по параметру — худшее из встреченного, где `1` хорошо, а `ω` хуже `0`:
//! алиас ломает уникальность, забвение — только закрытие.
//!
//! Смотреть достаточно на **голую** переменную: у связывания типа `List a`
//! голова написана (`List`), и его разбирают существующие правила владения.
//!
//! # Почему носители обязаны распространяться
//!
//! Иначе они не композиционны. `g x f = ignoreWith x f` употребляет каждое своё
//! связывание ровно однажды, но течёт, потому что течёт `ignoreWith`.
//! Инстанциация чужого параметра **собственной** переменной поэтому переносит
//! чужой носитель на свою: обещание о `a` не может быть сильнее того, что о нём
//! обещали те, кому его передали.
//!
//! # Кто проверяет
//!
//! Не ядро. Владение — понятие поверхностного языка (§3.3: «`unique`,
//! `resource` — surface-конструкции, а не расширение ядра»), поэтому ядро
//! носитель **считает и хранит**, а сверяет его с владеемым типом элаборация.
//! Ровно так же устроена тотальность (§4.7): вычисляет ядро, требует атрибут.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::eval::eval;
use crate::mult::Mult;
use crate::sig::Signature;
use crate::term::Term;
use crate::value::{Env, Head, Lvl, Value};

/// Кратности носителей, копящиеся по ходу проверки одного определения.
///
/// Ключ — уровень де Брёйна связывания-параметра, значение — худшее, что с
/// его значениями сделали. Внутренняя изменяемость потому, что контекст
/// проверки персистентен и раздаётся по ссылке: копилка обязана быть одна на
/// всё определение, а не по одной на каждое связывание.
#[derive(Debug, Default)]
pub struct Carriers {
    seen: RefCell<HashMap<u32, Mult>>,
}

impl Carriers {
    /// Отмечает, что со значением типа-переменной `level` обошлись так.
    pub fn record(&self, level: u32, mult: Mult) {
        let mut seen = self.seen.borrow_mut();
        let entry = seen.entry(level).or_insert(Mult::One);
        *entry = worse(*entry, mult);
    }

    /// Как обошлись со значениями переменной `level`. `1` — не встречалось
    /// ничего, что нарушило бы владение.
    #[must_use]
    pub fn get(&self, level: u32) -> Mult {
        self.seen.borrow().get(&level).copied().unwrap_or(Mult::One)
    }
}

/// Худшее из двух с точки зрения владения: `1` хорошо, `ω` хуже `0`.
fn worse(left: Mult, right: Mult) -> Mult {
    match (left, right) {
        (Mult::Many, _) | (_, Mult::Many) => Mult::Many,
        (Mult::Zero, _) | (_, Mult::Zero) => Mult::Zero,
        (Mult::One, Mult::One) => Mult::One,
    }
}

/// Отмечает связывание, если его тип — голая переменная.
///
/// `allowed` — объявленная кратность (уже умноженная на кратность суждения),
/// `actual` — фактическое употребление из вектора использований.
pub(crate) fn record(carriers: &Carriers, ty: &Value, allowed: Mult, actual: Mult) {
    let Some(level) = variable(ty) else {
        return;
    };
    // Стёртое связывание значения не порождает: закрывать нечего. У всех
    // прочих считается **фактическое** употребление, а не объявленная граница:
    // `identity x = x` объявлена `ω` по умолчанию (§4.1), но значение из неё
    // выходит обратно, и владение продолжается у вызывающего.
    if allowed != Mult::Zero {
        carriers.record(level, actual);
    }
}

/// Уровень, если значение — переменная контекста без спайна.
fn variable(ty: &Value) -> Option<u32> {
    match ty {
        Value::Neutral(Head::Local(level), spine) if spine.is_empty() => Some(level.0),
        _ => None,
    }
}

/// Носители по позициям телескопа: столько же записей, сколько связываний.
///
/// Позиция, чей домен не универсум, параметром типа не является, и запись у неё
/// `1` — «ограничения нет». Так индекс записи совпадает с номером аргумента, и
/// сверять их на применении можно не пересчитывая.
///
/// Тип и тело идут в ногу: уровень связывания совпадает с его позицией ровно
/// пока лямбды тела отвечают `Pi` типа. Разойдись они — и связывание открылось
/// не там, где его ждали, поэтому остаток телескопа считается неизвестным.
#[must_use]
pub fn profile(ty: &Term, body: &Term, carriers: &Carriers) -> Rc<[Mult]> {
    let mut found = Vec::new();
    let mut current = ty;
    let mut term = Some(body);
    let mut level = 0;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        let opened = matches!(term, Some(Term::Lam(..)));
        found.push(match (matches!(&**domain, Term::Universe(_)), opened) {
            (false, _) => Mult::One,
            (true, true) => carriers.get(level),
            (true, false) => Mult::Many,
        });
        term = match term {
            Some(Term::Lam(_, _, inner)) => Some(inner),
            _ => None,
        };
        level += 1;
        current = codomain;
    }
    found.into()
}

/// Носители определения, о теле которого ничего не известно.
///
/// Постулат, конструктор и тип-формер: тела нет, значит нет и способа узнать,
/// что станет со значением. `ω` — консервативный ответ, отвергающий
/// инстанциацию владеемым типом. Конструкторы вернутся к этому вместе с
/// параметрами семейства (§10 вопрос 78): поле хранится ровно однажды, но
/// держатель обязан быть `resource`, и это уже другое правило.
#[must_use]
pub fn unknown(ty: &Term) -> Rc<[Mult]> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        found.push(if matches!(&**domain, Term::Universe(_)) {
            Mult::Many
        } else {
            Mult::One
        });
        current = codomain;
    }
    found.into()
}

/// Носители конструктора: ограничения нет ни на одной позиции.
///
/// Конструктор кладёт аргумент ровно однажды - это и есть `1`. Что ресурс в
/// держателе без деструктора не закроется, говорит не носитель, а правило
/// держателя (§3.3, вопрос 77): оно смотрит на семейство, а не на то, сколько
/// раз значение употреблено.
#[must_use]
pub fn stored(ty: &Term) -> Rc<[Mult]> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        found.push(Mult::One);
        current = codomain;
    }
    found.into()
}

/// Носители, которые определение наследует от тех, кого зовёт.
///
/// Инстанциация чужого параметра **собственной** переменной переносит чужой
/// носитель на свою. Идёт это по **зонканному** телу и потому отдельной фазой:
/// в момент проверки выводимый аргумент - ещё нерешённая дырка, и что им
/// станет, там не видно.
///
/// Возвращается вклад вызываемых; складывать его с уже посчитанным - дело
/// вызывающего ([`worst`]).
#[must_use]
pub fn propagated(signature: &Signature, ty: &Term, body: &Term) -> Rc<[Mult]> {
    let mut found = vec![Mult::One; length(ty)];
    inherit(signature, body, 0, &mut found);
    found.into()
}

/// Складывает два профиля по позициям, беря худшее.
#[must_use]
pub fn worst(left: &[Mult], right: &[Mult]) -> Rc<[Mult]> {
    left.iter()
        .zip(right)
        .map(|(left, right)| worse(*left, *right))
        .collect()
}

/// Длина телескопа.
fn length(ty: &Term) -> usize {
    let mut found = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        found += 1;
        current = codomain;
    }
    found
}

fn inherit(signature: &Signature, term: &Term, depth: u32, found: &mut [Mult]) {
    if let Term::App(..) = term {
        borrowed(signature, term, depth, found);
    }
    match term {
        Term::App(callee, argument) => {
            inherit(signature, callee, depth, found);
            inherit(signature, argument, depth, found);
        }
        Term::Lam(_, _, body) => inherit(signature, body, depth + 1, found),
        Term::Record(fields) | Term::Row(fields) => {
            for (index, field) in fields.iter().enumerate() {
                let depth = depth + u32::try_from(index).unwrap_or(0);
                inherit(signature, &field.ty, depth, found);
            }
            if let Some(tail) = &fields.tail {
                inherit(signature, tail, depth, found);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                inherit(signature, value, depth, found);
            }
        }
        Term::With(base, fields) => {
            inherit(signature, base, depth, found);
            for (_, value) in fields.iter() {
                inherit(signature, value, depth, found);
            }
        }
        Term::Project(record, _) => inherit(signature, record, depth, found),
        Term::Pi(_, _, domain, _, codomain) => {
            inherit(signature, domain, depth, found);
            inherit(signature, codomain, depth + 1, found);
        }
        Term::Let(_, _, ty, value, body) => {
            inherit(signature, ty, depth, found);
            inherit(signature, value, depth, found);
            inherit(signature, body, depth + 1, found);
        }
        Term::Case(case) => {
            inherit(signature, &case.scrutinee, depth, found);
            inherit(signature, &case.motive, depth, found);
            for branch in &case.branches {
                inherit(signature, &branch.body, depth, found);
            }
        }
        Term::Var(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Const(..)
        | Term::Meta(_) => {}
    }
}

/// Один спайн: чей параметр инстанцируют и какой переменной.
fn borrowed(signature: &Signature, term: &Term, depth: u32, found: &mut [Mult]) {
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
    let env = (0..depth).fold(Env::default(), |env, level| {
        env.extend(Value::var(Lvl(level)))
    });
    for (position, argument) in arguments.iter().enumerate() {
        let Some(carrier) = definition.carriers.get(position).copied() else {
            break;
        };
        if carrier == Mult::One {
            continue;
        }
        // Уровень собственной переменной совпадает с её позицией в телескопе,
        // пока лямбды тела отвечают `Pi` типа; где не отвечают, там `profile`
        // уже поставил `ω`, и худшее из двух его и оставит.
        let Value::Neutral(Head::Local(Lvl(level)), spine) = &*eval(&env, argument) else {
            continue;
        };
        if !spine.is_empty() {
            continue;
        }
        if let Some(slot) = found.get_mut(*level as usize) {
            *slot = worse(*slot, carrier);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Carriers, worse};
    use crate::mult::Mult;

    #[test]
    fn the_worst_of_what_was_seen_wins() {
        // `1` - единственное, что владение допускает, поэтому оно уступает
        // всему; между двумя нарушениями хуже алиас: забвение теряет ресурс,
        // алиас ломает саму уникальность.
        assert_eq!(worse(Mult::One, Mult::One), Mult::One);
        assert_eq!(worse(Mult::One, Mult::Zero), Mult::Zero);
        assert_eq!(worse(Mult::Zero, Mult::Many), Mult::Many);
        assert_eq!(worse(Mult::Many, Mult::One), Mult::Many);
    }

    #[test]
    fn a_parameter_nobody_touched_carries_nothing() {
        // Значений такого типа в теле не возникало - ограничивать нечего.
        let carriers = Carriers::default();
        assert_eq!(carriers.get(0), Mult::One);
        carriers.record(1, Mult::Zero);
        assert_eq!(carriers.get(0), Mult::One, "запись соседа не в счёт");
    }
}
