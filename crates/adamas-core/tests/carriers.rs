//! Кратность носителя - что определение делает со значениями своего параметра.
//!
//! Величина выводится из тела и живёт в сигнатуре рядом с тотальностью; сверяет
//! её с владением элаборация (§10 вопрос 76). Здесь проверяется само число:
//! что оно отвечает телу, а не типу, и что оно наследуется от вызываемых.

use std::rc::Rc;

use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use adamas_core::visibility::Visibility;

/// `{0 a : Type 0} -> (q x : a) -> codomain`.
fn over(mult: Mult, codomain: Term) -> Term {
    Term::Pi(
        Binder {
            mult: Mult::Zero,
            visibility: Visibility::Implicit,
        },
        "a".into(),
        Rc::new(Term::universe(0)),
        Row::empty(),
        Rc::new(Term::Pi(
            Binder::explicit(mult),
            "x".into(),
            Rc::new(Term::var(0)),
            Row::empty(),
            Rc::new(codomain),
        )),
    )
}

/// `\a -> \x -> body`, с кратностями под стать `over`.
fn lambdas(mult: Mult, body: Term) -> Term {
    Term::Lam(
        Mult::Zero,
        "a".into(),
        Rc::new(Term::Lam(mult, "x".into(), Rc::new(body))),
    )
}

/// Носители единственного определения по имени.
fn carriers(members: &[(&str, Term, Term)]) -> Rc<[Mult]> {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut last = None;
    for (name, ty, body) in members {
        signature
            .define(
                &mut metas,
                name,
                Mult::Many,
                0,
                ty.clone(),
                Some(body.clone()),
            )
            .unwrap_or_else(|error| panic!("определение `{name}`: {error:?}"));
        last = Some(*name);
    }
    let Some(name) = last else {
        panic!("хотя бы одно определение");
    };
    let Some(definition) = signature.lookup(name) else {
        panic!("`{name}` объявлено");
    };
    Rc::clone(&definition.carriers)
}

#[test]
fn a_forgotten_value_shows_up_as_zero() {
    // `\a -> \x -> Type 0` связывание `x` не употребляет вовсе. При `a := File`
    // это утечка: `drop` вызвать некому.
    let profile = carriers(&[(
        "f",
        over(Mult::One, Term::universe(1)),
        lambdas(Mult::One, Term::universe(0)),
    )]);
    assert_eq!(&*profile, &[Mult::Zero, Mult::One]);
}

#[test]
fn a_value_that_comes_back_out_shows_up_as_one() {
    // Кратность связывания здесь `ω` - умолчание §4.1, - но значение выходит
    // обратно, и владение продолжается у вызывающего. Считается фактическое,
    // а не объявленное, иначе тождество оказалось бы небезопасным.
    let profile = carriers(&[(
        "f",
        over(Mult::Many, Term::var(1)),
        lambdas(Mult::Many, Term::var(0)),
    )]);
    assert_eq!(&*profile, &[Mult::One, Mult::One]);
}

#[test]
fn the_second_position_is_not_a_type_parameter() {
    // Записей столько же, сколько связываний: так индекс совпадает с номером
    // аргумента. У позиции, которая параметром типа не является, ограничения
    // нет, и стоит там `1`.
    let profile = carriers(&[(
        "f",
        over(Mult::One, Term::universe(1)),
        lambdas(Mult::One, Term::universe(0)),
    )]);
    assert_eq!(profile.len(), 2);
    assert_eq!(profile[1], Mult::One);
}

#[test]
fn a_carrier_is_inherited_from_whoever_was_called() {
    // `g` употребляет своё связывание ровно однажды и всё равно течёт: она
    // отдала его тому, кто течёт. Без наследования дыра открывалась бы одним
    // лишним слоем.
    let forgets = (
        "f",
        over(Mult::One, Term::universe(1)),
        lambdas(Mult::One, Term::universe(0)),
    );
    let passes = (
        "g",
        over(Mult::One, Term::universe(1)),
        lambdas(
            Mult::One,
            Term::constant("f").apply([Term::var(1), Term::var(0)]),
        ),
    );
    assert_eq!(&*carriers(&[forgets, passes]), &[Mult::Zero, Mult::One]);
}
