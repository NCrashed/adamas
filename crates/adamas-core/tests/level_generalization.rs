//! Обобщение уровней: арность определения выводится, а не объявляется.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, TypeError, check_definition, infer_closed_with};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use proptest::prelude::*;

// ------------------------------------------------------------- конструкторы

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(
        mult,
        name.into(),
        Rc::new(domain),
        Row::empty(),
        Rc::new(codomain),
    )
}

// -------------------------------------------------------------------- вывод

#[test]
fn a_single_hole_becomes_one_parameter() {
    // `Id` пишется через дырку, арность не объявляется.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();

    signature
        .define_inferred(
            &mut metas,
            "Id",
            Mult::Many,
            pi(
                Mult::Zero,
                "a",
                Term::Universe(level),
                pi(Mult::Many, "x", Term::var(0), Term::var(1)),
            ),
            Some(lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)))),
        )
        .unwrap();

    let definition = signature.lookup("Id").unwrap();
    assert_eq!(definition.level_arity, 1, "одна дырка - один параметр");
    assert_eq!(
        definition.ty.to_string(),
        "(0 a : Type u0) -> (ω x : #0) -> #1",
        "дырка заменена параметром"
    );
}

#[test]
fn the_generalized_definition_is_usable_polymorphically() {
    // Выведенная арность работает в местах использования так же, как
    // объявленная: инстанциация подставляет дырки, они решаются.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();
    signature
        .define_inferred(
            &mut metas,
            "Id",
            Mult::Many,
            pi(
                Mult::Zero,
                "a",
                Term::Universe(level),
                pi(Mult::Many, "x", Term::var(0), Term::var(1)),
            ),
            Some(lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)))),
        )
        .unwrap();

    for level in 0..3 {
        let mut uses = Metas::default();
        let applied = signature
            .instantiate("Id", &mut uses)
            .unwrap()
            .apply([Term::universe(level)]);
        assert_eq!(
            infer_closed_with(&signature, &mut uses, &applied)
                .unwrap()
                .to_string(),
            format!("(ω x : Type {level}) -> Type {level}")
        );
    }
}

#[test]
fn parameters_are_numbered_by_first_appearance() {
    // Порядок параметров задан порядком появления в типе, а не порядком
    // создания дырок: иначе одно и то же определение получало бы разную
    // нумерацию в зависимости от того, как его собирали.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let first = metas.fresh_level();
    let second = metas.fresh_level();

    // В типе `second` встречается раньше `first`.
    signature
        .postulate_inferred(
            &mut metas,
            "Both",
            Mult::Many,
            pi(
                Mult::Many,
                "x",
                Term::Universe(second),
                Term::Universe(first.succ()),
            ),
        )
        .unwrap();

    let definition = signature.lookup("Both").unwrap();
    assert_eq!(definition.level_arity, 2);
    assert_eq!(definition.ty.to_string(), "(ω x : Type u0) -> Type u1+1");
}

#[test]
fn a_hole_used_twice_becomes_one_parameter() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();

    signature
        .postulate_inferred(
            &mut metas,
            "Endo",
            Mult::Many,
            pi(
                Mult::Many,
                "x",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
        )
        .unwrap();

    assert_eq!(signature.lookup("Endo").unwrap().level_arity, 1);
}

#[test]
fn a_solved_hole_does_not_become_a_parameter() {
    // Дырка, определившаяся по ходу проверки, - уже не свобода. Обобщать её
    // значило бы объявить полиморфизм там, где его нет.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();

    // `Type ?l` проверяется против `Type 3`, значит `?l := 2`.
    signature
        .define_inferred(
            &mut metas,
            "Concrete",
            Mult::Many,
            Term::universe(3),
            Some(Term::Universe(level)),
        )
        .unwrap();

    let definition = signature.lookup("Concrete").unwrap();
    assert_eq!(definition.level_arity, 0, "решённая дырка - не параметр");
    assert_eq!(
        definition.body.as_ref().unwrap().to_string(),
        "Type 2",
        "решение подставлено"
    );
}

#[test]
fn a_definition_without_holes_gets_arity_zero() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define_inferred(
            &mut metas,
            "Simple",
            Mult::Many,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .unwrap();

    assert_eq!(signature.lookup("Simple").unwrap().level_arity, 0);
}

// ------------------------------------------------------------------ границы

#[test]
fn a_hole_living_only_in_the_body_is_rejected() {
    // Тип определяет, что подставится в месте использования. Дырка, которой в
    // типе нет, параметром стать не может: заполнить её было бы нечем.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "Any", Mult::Many, 1, Term::universe(9))
        .unwrap();

    let mut metas = Metas::default();
    let hole = metas.fresh_level();

    let outcome = signature.define_inferred(
        &mut metas,
        "BodyOnly",
        Mult::Many,
        Term::universe(9),
        Some(Term::Const("Any".into(), Rc::from([hole]))),
    );
    assert!(
        matches!(
            outcome,
            Err(TypeError {
                kind: ErrorKind::UnsolvedDefinitionLevel { .. },
                ..
            })
        ),
        "получено: {outcome:?}"
    );
}

#[test]
fn a_level_parameter_in_the_input_is_rejected() {
    // Параметры - результат обобщения, а не вход. Написанный руками `u0`
    // означает, что вызывающий смешал две записи.
    let mut signature = Signature::default();
    let mut metas = Metas::default();

    let outcome = signature.postulate_inferred(
        &mut metas,
        "Wrong",
        Mult::Many,
        Term::Universe(Level::Var(LevelVar(0)).succ()),
    );
    assert!(
        matches!(
            outcome,
            Err(TypeError {
                kind: ErrorKind::LevelVarOutOfScope { arity: 0, .. },
                ..
            })
        ),
        "получено: {outcome:?}"
    );
}

#[test]
fn the_explicit_path_still_rejects_leftover_holes() {
    // `define` арность объявляет, значит выводить нечего, и остаточная дырка
    // остаётся отказом.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "Any", Mult::Many, 1, Term::universe(9))
        .unwrap();

    let mut metas = Metas::default();
    let hole = metas.fresh_level();

    let outcome = signature.define(
        &mut metas,
        "Leftover",
        Mult::Many,
        0,
        Term::universe(9),
        Some(Term::Const("Any".into(), Rc::from([hole]))),
    );
    assert!(
        matches!(
            outcome,
            Err(TypeError {
                kind: ErrorKind::UnsolvedDefinitionLevel { .. },
                ..
            })
        ),
        "получено: {outcome:?}"
    );
}

// ----------------------------------------------------------------- инвариант

#[test]
fn generalization_preserves_checkability() {
    // Обобщение - согласованное переименование нерешённых дырок в параметры,
    // и результат обязан проходить проверку заново. Проверяется явно, потому
    // что в рабочем пути повторной проверки нет: платить за неё на каждом
    // определении было бы двойной работой.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();

    signature
        .define_inferred(
            &mut metas,
            "Id",
            Mult::Many,
            pi(
                Mult::Zero,
                "a",
                Term::Universe(level),
                pi(Mult::Many, "x", Term::var(0), Term::var(1)),
            ),
            Some(lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)))),
        )
        .unwrap();

    let stored = signature.lookup("Id").unwrap().clone();
    let empty = Signature::default();
    let mut fresh = Metas::default();
    assert!(
        check_definition(&empty, &mut fresh, &"Id".into(), &stored).is_ok(),
        "обобщённая форма обязана проверяться"
    );
}

// ------------------------------------------------------------------ свойства

/// Тип-"скелет" из дырок: `Pi` произвольной вложенности, где каждый универсум
/// стоит на дырке из общего набора.
///
/// Генерируются не произвольные термы (такие почти никогда не типизируются), а
/// формы, о которых заранее известно, что они типы: вложенные `Pi` над
/// универсумами. Индексы в наборе повторяются, поэтому попадаются и случаи, где
/// одна дырка встречается несколько раз.
fn any_skeleton() -> impl Strategy<Value = Vec<usize>> {
    proptest::collection::vec(0usize..3, 1..5)
}

/// Собирает тип по скелету: `(0 a0 : Type ?h0) -> … -> Type ?hn`.
fn build(metas: &mut Metas, skeleton: &[usize]) -> Term {
    let holes: Vec<Level> = (0..3).map(|_| metas.fresh_level()).collect();
    let last = Term::Universe(holes[skeleton[skeleton.len() - 1]].clone());
    skeleton[..skeleton.len() - 1]
        .iter()
        .rev()
        .fold(last, |acc, index| {
            pi(Mult::Zero, "a", Term::Universe(holes[*index].clone()), acc)
        })
}

/// Все переменные уровня, встречающиеся в терме.
fn level_vars(term: &Term, found: &mut Vec<u32>) {
    fn in_level(level: &Level, found: &mut Vec<u32>) {
        match level {
            Level::Zero | Level::Meta(_) => {}
            Level::Succ(inner) => in_level(inner, found),
            Level::Max(a, b) => {
                in_level(a, found);
                in_level(b, found);
            }
            Level::Var(LevelVar(index)) => {
                if !found.contains(index) {
                    found.push(*index);
                }
            }
        }
    }
    match term {
        Term::Var(_) => {}
        Term::Universe(level) => in_level(level, found),
        Term::Case(_) => unreachable!("генератор определений не порождает разбор"),
        Term::Lam(_, _, body) => level_vars(body, found),
        Term::App(a, b) => {
            level_vars(a, found);
            level_vars(b, found);
        }
        Term::Pi(_, _, domain, _, codomain) => {
            level_vars(domain, found);
            level_vars(codomain, found);
        }
        Term::Let(_, _, ty, value, body) => {
            level_vars(ty, found);
            level_vars(value, found);
            level_vars(body, found);
        }
        Term::Const(_, levels) => {
            for level in levels.iter() {
                in_level(level, found);
            }
        }
    }
}

proptest! {
    /// Обобщённая форма обязана проходить проверку заново.
    ///
    /// В рабочем пути повторной проверки нет - платить за неё на каждом
    /// определении было бы двойной работой, - поэтому согласованность
    /// переименования дырок в параметры держится только этим свойством.
    #[test]
    fn generalization_preserves_checkability_for_any_shape(skeleton in any_skeleton()) {
        let mut signature = Signature::default();
        let mut metas = Metas::default();
        let ty = build(&mut metas, &skeleton);

        prop_assume!(
            signature
                .define_inferred(&mut metas, "D", Mult::Many, ty, None)
                .is_ok()
        );

        let stored = signature.lookup("D").unwrap().clone();
        let empty = Signature::default();
        let mut fresh = Metas::default();
        prop_assert!(
            check_definition(&empty, &mut fresh, &"D".into(), &stored).is_ok(),
            "обобщённая форма не проверяется: {}", stored.ty
        );
    }

    /// Параметры плотно занумерованы `0..arity`.
    ///
    /// Дырка, не ставшая параметром, и параметр с индексом за арностью - это
    /// определение, зависящее от того, чего у него нет.
    #[test]
    fn parameters_are_dense_and_within_the_arity(skeleton in any_skeleton()) {
        let mut signature = Signature::default();
        let mut metas = Metas::default();
        let ty = build(&mut metas, &skeleton);

        prop_assume!(
            signature
                .define_inferred(&mut metas, "D", Mult::Many, ty, None)
                .is_ok()
        );

        let stored = signature.lookup("D").unwrap();
        let mut found = Vec::new();
        level_vars(&stored.ty, &mut found);
        found.sort_unstable();

        let expected: Vec<u32> = (0..stored.level_arity).collect();
        prop_assert_eq!(found, expected, "тип: {}", stored.ty);
    }
}
