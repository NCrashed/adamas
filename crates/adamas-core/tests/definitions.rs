//! Определения верхнего уровня, universe polymorphism и δ-редукция.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, TypeError, check_closed, infer_closed};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use proptest::prelude::*;

// ------------------------------------------------------------- конструкторы

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
}

/// Параметр уровня по индексу.
fn u(index: u32) -> Level {
    Level::Var(LevelVar(index))
}

/// `Type u{index}`.
fn universe_var(index: u32) -> Term {
    Term::Universe(u(index))
}

/// Ссылка на определение с явными аргументами уровня.
fn at(name: &str, levels: &[Level]) -> Term {
    Term::Const(name.into(), levels.iter().cloned().collect())
}

/// `Id : (0 a : Type u0) -> (ω x : a) -> a`, полиморфная по уровню
/// тождественная функция со стёртым параметром типа.
fn identity_signature() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.define(
        &mut metas,
        "Id",
        Mult::Many,
        1,
        pi(
            Mult::Zero,
            "a",
            universe_var(0),
            pi(Mult::Many, "x", Term::var(0), Term::var(1)),
        ),
        Some(lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)))),
    );
    assert!(outcome.is_ok(), "Id корректна: {outcome:?}");
    signature
}

// --------------------------------------------------------------- базовое

#[test]
fn a_definition_gets_the_type_it_declares() {
    let signature = identity_signature();
    assert_eq!(
        infer_closed(&signature, &at("Id", &[Level::Zero]))
            .unwrap()
            .to_string(),
        "(0 a : Type 0) -> (ω x : #0) -> #1"
    );
}

#[test]
fn the_same_definition_serves_every_level() {
    // Ровно то, ради чего нужен universe polymorphism: одно определение,
    // разные универсумы. Без него `Id` пришлось бы копировать на каждый
    // уровень - предикативность сама по себе такой возможности не даёт.
    let signature = identity_signature();

    for level in 0..3 {
        let instantiated = infer_closed(&signature, &at("Id", &[Level::number(level)])).unwrap();
        assert_eq!(
            instantiated.to_string(),
            format!("(0 a : Type {level}) -> (ω x : #0) -> #1")
        );
    }
}

#[test]
fn a_level_argument_may_itself_be_an_expression() {
    let signature = identity_signature();
    let level = u(0).max(Level::number(2));
    let instantiated = infer_closed(&signature, &at("Id", &[level])).unwrap();
    assert!(
        instantiated
            .to_string()
            .starts_with("(0 a : Type max 2 u0)"),
        "получено: {instantiated}"
    );
}

#[test]
fn applying_a_polymorphic_definition_substitutes_into_the_result_type() {
    // Id{1} (Type 0) : (ω x : Type 0) -> Type 0
    let signature = identity_signature();
    let applied = at("Id", &[Level::number(1)]).apply([Term::universe(0)]);
    assert_eq!(
        infer_closed(&signature, &applied).unwrap().to_string(),
        "(ω x : Type 0) -> Type 0"
    );
}

// --------------------------------------------------------------- δ-редукция

#[test]
fn definitions_unfold_when_conversion_needs_them() {
    // `Alias` определён как `Type 0`, значит `Type 0` ему конвертируем -
    // но только после разворота.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "Alias",
            Mult::Many,
            0,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .unwrap();

    assert!(check_closed(&signature, &Term::universe(0), &Term::universe(1)).is_ok());
    assert!(check_closed(&signature, &Term::constant("Alias"), &Term::universe(1)).is_ok());
    // Тип `Type 0` и тип `Alias` - один и тот же тип.
    let arrow_via_alias = pi(Mult::Many, "x", Term::constant("Alias"), Term::universe(0));
    let identity = lam(Mult::Many, "x", Term::var(0));
    assert!(check_closed(&signature, &identity, &arrow_via_alias).is_ok());
}

#[test]
fn two_definitions_with_the_same_body_are_convertible() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    for name in ["First", "Second"] {
        signature
            .define(
                &mut metas,
                name,
                Mult::Many,
                0,
                Term::universe(1),
                Some(Term::universe(0)),
            )
            .unwrap();
    }

    let via_first = pi(Mult::Many, "x", Term::constant("First"), Term::universe(0));
    let via_second = pi(Mult::Many, "x", Term::constant("Second"), Term::universe(0));
    let identity = lam(Mult::Many, "x", Term::var(0));

    assert!(check_closed(&signature, &identity, &via_first).is_ok());
    // Тот же терм против типа, записанного через другое имя с тем же телом.
    assert!(check_closed(&signature, &identity, &via_second).is_ok());
}

#[test]
fn a_postulate_stays_stuck() {
    // У постулата тела нет, разворачивать нечего: два разных постулата
    // остаются разными типами.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "A", Mult::Many, 0, Term::universe(1))
        .unwrap();
    signature
        .postulate(&mut metas, "B", Mult::Many, 0, Term::universe(1))
        .unwrap();

    let identity = lam(Mult::Many, "x", Term::var(0));
    let a_to_a = pi(Mult::Many, "x", Term::constant("A"), Term::constant("A"));
    let a_to_b = pi(Mult::Many, "x", Term::constant("A"), Term::constant("B"));

    assert!(check_closed(&signature, &identity, &a_to_a).is_ok());
    assert!(matches!(
        check_closed(&signature, &identity, &a_to_b),
        Err(TypeError {
            kind: ErrorKind::Mismatch { .. },
            ..
        })
    ));
}

#[test]
fn level_arguments_are_part_of_the_head() {
    // Постулат, применённый на разных уровнях, - разные типы.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(
            &mut metas,
            "Box",
            Mult::Many,
            1,
            Term::Universe(u(0).succ()),
        )
        .unwrap();

    let identity = lam(Mult::Many, "x", Term::var(0));
    let same = pi(
        Mult::Many,
        "x",
        at("Box", &[Level::Zero]),
        at("Box", &[Level::Zero]),
    );
    let different = pi(
        Mult::Many,
        "x",
        at("Box", &[Level::Zero]),
        at("Box", &[Level::number(1)]),
    );

    assert!(check_closed(&signature, &identity, &same).is_ok());
    assert!(matches!(
        check_closed(&signature, &identity, &different),
        Err(TypeError {
            kind: ErrorKind::Mismatch { .. },
            ..
        })
    ));
}

// -------------------------------------------------------- прозрачность формы

/// Тип-синоним функции - такой же тип функции, как записанная стрелка.
///
/// Проверка спрашивает у типа его **форму** в трёх местах: применение - "это
/// `Pi`?", правило лямбды - то же самое, позиция типа - "это универсум?".
/// Определение имеет собственную голову, и без приведения к головной нормальной
/// форме синоним не годился бы ни в одном из трёх.
#[test]
fn a_definition_is_transparent_where_the_shape_of_a_type_is_asked() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "Nat", Mult::Many, 0, Term::universe(0))
        .unwrap();
    signature
        .postulate(&mut metas, "z", Mult::Many, 0, Term::constant("Nat"))
        .unwrap();
    signature
        .define(
            &mut metas,
            "Fn",
            Mult::Many,
            0,
            Term::universe(0),
            Some(pi(
                Mult::Many,
                "_",
                Term::constant("Nat"),
                Term::constant("Nat"),
            )),
        )
        .unwrap();
    signature
        .postulate(&mut metas, "f", Mult::Many, 0, Term::constant("Fn"))
        .unwrap();

    let applied = check_closed(
        &signature,
        &Term::constant("f").apply([Term::constant("z")]),
        &Term::constant("Nat"),
    );
    assert!(applied.is_ok(), "применение через синоним: {applied:?}");

    let identity = check_closed(
        &signature,
        &lam(Mult::Many, "x", Term::var(0)),
        &Term::constant("Fn"),
    );
    assert!(identity.is_ok(), "лямбда против синонима: {identity:?}");
}

#[test]
fn a_definition_is_transparent_in_the_position_of_a_type() {
    // `Sort2 = Type 2`, поэтому `T : Sort2` обязана годиться как тип.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "Sort2",
            Mult::Many,
            0,
            Term::universe(3),
            Some(Term::universe(2)),
        )
        .unwrap();
    signature
        .postulate(&mut metas, "T", Mult::Many, 0, Term::constant("Sort2"))
        .unwrap();
    signature
        .postulate(&mut metas, "t", Mult::Many, 0, Term::constant("T"))
        .unwrap();

    let outcome = check_closed(&signature, &Term::constant("t"), &Term::constant("T"));
    assert!(outcome.is_ok(), "{outcome:?}");
}

// --------------------------------------------------------------- кратности

#[test]
fn an_erased_definition_cannot_be_used_at_runtime() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "Proof",
            Mult::Zero,
            0,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .unwrap();

    assert!(matches!(
        infer_closed(&signature, &Term::constant("Proof")),
        Err(TypeError {
            kind: ErrorKind::ErasedConstant { .. },
            ..
        })
    ));
}

#[test]
fn an_erased_definition_is_fine_inside_a_type() {
    // Тот же `Proof`, но в позиции типа: там σ = 0, и запрет не срабатывает.
    // Иначе стирание было бы бесполезно - доказательства нельзя было бы даже
    // упоминать в сигнатурах.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "Proof",
            Mult::Zero,
            0,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .unwrap();

    let identity = lam(Mult::Many, "x", Term::var(0));
    let ty = pi(Mult::Many, "x", Term::constant("Proof"), Term::universe(0));
    assert!(check_closed(&signature, &identity, &ty).is_ok());
}

#[test]
fn a_linear_definition_is_rejected() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(matches!(
        signature.define(
            &mut metas,
            "L",
            Mult::One,
            0,
            Term::universe(1),
            Some(Term::universe(0))
        ),
        Err(TypeError {
            kind: ErrorKind::LinearDefinition { .. },
            ..
        })
    ));
}

// ------------------------------------------------------------ некорректность

#[test]
fn an_unknown_constant_is_rejected() {
    let signature = Signature::default();
    assert!(matches!(
        infer_closed(&signature, &Term::constant("Missing")),
        Err(TypeError {
            kind: ErrorKind::UnknownConstant { .. },
            ..
        })
    ));
}

#[test]
fn the_number_of_level_arguments_must_match() {
    let signature = identity_signature();

    assert!(matches!(
        infer_closed(&signature, &Term::constant("Id")),
        Err(TypeError {
            kind: ErrorKind::LevelArity {
                expected: 1,
                found: 0,
                ..
            },
            ..
        })
    ));
    assert!(matches!(
        infer_closed(&signature, &at("Id", &[Level::Zero, Level::Zero])),
        Err(TypeError {
            kind: ErrorKind::LevelArity {
                expected: 1,
                found: 2,
                ..
            },
            ..
        })
    ));
}

#[test]
fn a_level_parameter_beyond_the_declared_arity_is_rejected() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(matches!(
        signature.postulate(
            &mut metas,
            "Bad",
            Mult::Many,
            1,
            Term::Universe(u(3).succ())
        ),
        Err(TypeError {
            kind: ErrorKind::LevelVarOutOfScope {
                var: 3,
                arity: 1,
                ..
            },
            ..
        })
    ));
}

#[test]
fn a_definition_body_must_match_its_type() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(matches!(
        signature.define(
            &mut metas,
            "Wrong",
            Mult::Many,
            0,
            Term::universe(0),
            Some(Term::universe(1)),
        ),
        Err(TypeError {
            kind: ErrorKind::Mismatch { .. },
            ..
        })
    ));
}

#[test]
fn a_name_cannot_be_defined_twice() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "A", Mult::Many, 0, Term::universe(1))
        .unwrap();
    assert!(matches!(
        signature.postulate(&mut metas, "A", Mult::Many, 0, Term::universe(1)),
        Err(TypeError {
            kind: ErrorKind::DuplicateDefinition { .. },
            ..
        })
    ));
    // Отказ по занятому имени происходит до единой вставки, поэтому откату
    // нечего снимать. Проверь имена позже - и откат снял бы `A`, то есть то
    // самое определение, на которое жаловался.
    assert!(
        signature.lookup("A").is_some(),
        "занятое имя осталось за прежним определением"
    );
}

#[test]
fn a_definition_refers_to_itself_only_in_its_body() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    // Тип проверяется без собственного имени: `Loop : Loop` цикличен.
    assert!(matches!(
        signature.define(
            &mut metas,
            "Loop",
            Mult::Many,
            0,
            Term::constant("Loop"),
            None
        ),
        Err(TypeError {
            kind: ErrorKind::UnknownConstant { .. },
            ..
        })
    ));

    // Тело - уже с ним, и `Loop = Loop` принимается. Тотальным оно при этом не
    // становится, и завершаемость δ-разворота держится именно на этом.
    let outcome = signature.define(
        &mut metas,
        "Loop",
        Mult::Many,
        0,
        Term::universe(1),
        Some(Term::constant("Loop")),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(!signature.lookup("Loop").unwrap().total);
}

/// `Alias : Type (u0 + 1)` с телом `Type u0` - определение, вычисляющееся в тип.
fn alias_signature() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.define(
        &mut metas,
        "Alias",
        Mult::Many,
        1,
        Term::Universe(u(0).succ()),
        Some(universe_var(0)),
    );
    assert!(outcome.is_ok(), "Alias корректна: {outcome:?}");
    signature
}

// ------------------------------------------------------------------ свойства

/// Уровневые выражения без `imax` - того же вида, что порождает элаборатор.
fn any_level() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::Zero),
        (0u32..3).prop_map(Level::number),
        (0u32..2).prop_map(|index| Level::Var(LevelVar(index))),
    ];
    leaf.prop_recursive(3, 16, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner).prop_map(|(a, b)| a.max(b)),
        ]
    })
}

/// Другое написание того же уровня: `max l 0`, `max 0 l` и сам `l` равны.
fn respell(level: &Level, variant: u8) -> Level {
    match variant % 3 {
        0 => level.clone(),
        1 => level.clone().max(Level::Zero),
        _ => Level::Zero.max(level.clone()),
    }
}

proptest! {
    /// Аргументы уровня участвуют в равенстве по значению, а не по написанию.
    ///
    /// Голова застрявшего определения сравнивается структурно, поэтому уровни
    /// в ней обязаны быть нормализованы. Постулат - худший случай: развернуть
    /// его нельзя, и несовпадение написаний было бы окончательным.
    #[test]
    fn respelling_a_level_argument_changes_nothing(level in any_level(), variant in 0u8..3) {
        let mut signature = Signature::default();
        let mut metas = Metas::default();
        signature
            .postulate(&mut metas, "Box", Mult::Many, 2, Term::Universe(u(0).succ()))
            .expect("постулат добавляется");

        let spelled = at("Box", &[respell(&level, variant), Level::Zero]);
        let plain = at("Box", &[level, Level::Zero]);
        let identity = lam(Mult::Many, "x", Term::var(0));

        let outcome = check_closed(
            &signature,
            &identity,
            &pi(Mult::Many, "x", spelled, plain),
        );
        prop_assert!(outcome.is_ok(), "{outcome:?}");
    }


    /// δ делает определение взаимозаменяемым с телом в обе стороны.
    ///
    /// `Alias{l}` вычисляется в `Type l`, но приходит в конвертируемость
    /// неразвёрнутым: быстрый путь на такой паре не сходится (слева голова -
    /// определение, справа - универсум), и работает только откат к развороту.
    /// Тождественная функция типизируется против `A -> B` тогда и только
    /// тогда, когда `A` и `B` конвертируемы, - этим и проверяется.
    #[test]
    fn a_definition_is_interchangeable_with_its_body(level in any_level()) {
        let signature = alias_signature();
        let identity = lam(Mult::Many, "x", Term::var(0));

        let folded = at("Alias", std::slice::from_ref(&level));
        let unfolded = Term::Universe(level);

        for (left, right) in [
            (folded.clone(), unfolded.clone()),
            (unfolded, folded.clone()),
            (folded.clone(), folded),
        ] {
            let outcome = check_closed(&signature, &identity, &pi(Mult::Many, "x", left, right));
            prop_assert!(outcome.is_ok(), "{outcome:?}");
        }
    }

    /// Разворот не меняет типа: `Alias{l}` и `Type l` живут этажом выше `l`.
    #[test]
    fn unfolding_preserves_the_type(level in any_level()) {
        let signature = alias_signature();
        let folded = infer_closed(&signature, &at("Alias", std::slice::from_ref(&level)));
        let unfolded = infer_closed(&signature, &Term::Universe(level));
        prop_assert_eq!(
            folded.map(|ty| ty.to_string()),
            unfolded.map(|ty| ty.to_string())
        );
    }
}
