//! Разбор по конструктору: ι-редукция, мотив, покрытие, кратности ветвей
//! (§9 Фаза 1).
//!
//! Заготовки здесь свои, а не общие с `inductive.rs`: тому нужны отказы при
//! объявлении, этому - работающие типы, и общий набор был бы компромиссом в
//! обе стороны.

use std::rc::Rc;

use adamas_core::check::{TypeError, check_closed, infer_closed};
use adamas_core::eval::normalize;
use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::{Branch, Case, Term};
use proptest::prelude::*;

// -------------------------------------------------------------- конструкторы

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
}

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

/// Стрелка без зависимости.
fn arrow(domain: Term, codomain: Term) -> Term {
    pi(Mult::Many, "_", domain, codomain)
}

/// Ссылка на определение без параметров уровня.
fn c(name: &str) -> Term {
    Term::constant(name)
}

/// Разбор по конструктору.
fn case(
    data: &str,
    levels: &[Level],
    params: u32,
    scrutinee: Term,
    motive: Term,
    branches: Vec<(&str, Term)>,
) -> Term {
    Term::Case(Rc::new(Case {
        data: data.into(),
        levels: levels.iter().cloned().collect(),
        params,
        scrutinee: Rc::new(scrutinee),
        motive: Rc::new(motive),
        branches: branches
            .into_iter()
            .map(|(constructor, body)| Branch {
                constructor: constructor.into(),
                body: Rc::new(body),
            })
            .collect(),
    }))
}

/// Непараметризованный разбор: `case scrutinee return motive of …`.
fn simple(data: &str, scrutinee: Term, motive: Term, branches: Vec<(&str, Term)>) -> Term {
    case(data, &[], 0, scrutinee, motive, branches)
}

/// Постоянный мотив - для разбора, не зависящего от разбираемого значения.
fn constantly(result: Term) -> Term {
    lam(Mult::Zero, "_", result)
}

// -------------------------------------------------------------- заготовки

fn declared(what: &str, outcome: &Result<(), TypeError>) {
    assert!(outcome.is_ok(), "{what} корректен: {outcome:?}");
}

/// `Bool`, `Nat`, `Void`, `Pair` и две ω-функции над `Bool`.
///
/// `Void` без конструкторов - разбор по нему даёт ex falso. `Pair` держит два
/// поля кратности `1`: на нём проверяется масштабирование кратности поля.
fn base() -> Signature {
    use adamas_core::meta::Metas;

    let mut signature = Signature::default();
    let mut metas = Metas::default();

    declared(
        "Bool",
        &signature.declare_data("Bool", 0, &mut metas, Term::universe(0)),
    );
    for name in ["true", "false"] {
        declared(
            name,
            &signature.declare_constructor("Bool", name, &mut metas, c("Bool")),
        );
    }

    declared(
        "Nat",
        &signature.declare_data("Nat", 0, &mut metas, Term::universe(0)),
    );
    declared(
        "zero",
        &signature.declare_constructor("Nat", "zero", &mut metas, c("Nat")),
    );
    declared(
        "succ",
        &signature.declare_constructor("Nat", "succ", &mut metas, arrow(c("Nat"), c("Nat"))),
    );

    declared(
        "Void",
        &signature.declare_data("Void", 0, &mut metas, Term::universe(0)),
    );

    declared(
        "Pair",
        &signature.declare_data("Pair", 0, &mut metas, Term::universe(0)),
    );
    declared(
        "mk",
        &signature.declare_constructor(
            "Pair",
            "mk",
            &mut metas,
            pi(
                Mult::One,
                "x",
                c("Bool"),
                pi(Mult::One, "y", c("Bool"), c("Pair")),
            ),
        ),
    );

    declared(
        "and",
        &signature.postulate(
            "and",
            Mult::Many,
            0,
            arrow(c("Bool"), arrow(c("Bool"), c("Bool"))),
        ),
    );
    declared(
        "use",
        &signature.postulate("use", Mult::Many, 0, arrow(c("Bool"), c("Bool"))),
    );

    signature
}

/// `Vect : (0 A : Type 0) -> (0 n : Nat) -> Type 0` поверх [`base`].
///
/// Мономорфный по уровню сознательно: индексы и параметры уровня - независимые
/// оси, и мешать их в одном тесте значит не проверить ни одну.
fn vectors() -> Signature {
    use adamas_core::meta::Metas;

    let mut signature = base();
    let mut metas = Metas::default();

    declared(
        "Vect",
        &signature.declare_data(
            "Vect",
            1,
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::universe(0),
                pi(Mult::Zero, "n", c("Nat"), Term::universe(0)),
            ),
        ),
    );
    declared(
        "vnil",
        &signature.declare_constructor(
            "Vect",
            "vnil",
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::universe(0),
                c("Vect").apply([Term::var(0), c("zero")]),
            ),
        ),
    );
    declared(
        "vcons",
        &signature.declare_constructor(
            "Vect",
            "vcons",
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::universe(0),
                pi(
                    Mult::Zero,
                    "n",
                    c("Nat"),
                    pi(
                        Mult::One,
                        "x",
                        Term::var(1),
                        pi(
                            Mult::One,
                            "xs",
                            c("Vect").apply([Term::var(2), Term::var(1)]),
                            c("Vect").apply([Term::var(3), c("succ").apply([Term::var(2)])]),
                        ),
                    ),
                ),
            ),
        ),
    );
    signature
}

/// `List : (0 A : Type u) -> Type u` поверх [`base`] - параметр и уровень.
fn lists() -> Signature {
    use adamas_core::meta::Metas;

    let mut signature = base();
    let mut metas = Metas::default();

    let level = metas.fresh_level();
    declared(
        "List",
        &signature.declare_data(
            "List",
            1,
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
        ),
    );
    let list_of = |signature: &Signature, metas: &mut Metas, element: Term| {
        signature
            .instantiate("List", metas)
            .unwrap_or_else(|| panic!("List объявлен"))
            .apply([element])
    };
    let nil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        list_of(&signature, &mut metas, Term::var(0)),
    );
    declared(
        "nil",
        &signature.declare_constructor("List", "nil", &mut metas, nil),
    );
    let cons = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::One,
            "x",
            Term::var(0),
            pi(
                Mult::One,
                "xs",
                list_of(&signature, &mut metas, Term::var(1)),
                list_of(&signature, &mut metas, Term::var(2)),
            ),
        ),
    );
    declared(
        "cons",
        &signature.declare_constructor("List", "cons", &mut metas, cons),
    );
    signature
}

/// `\(ω b) -> case b return (\(0 _) -> Bool) of {true => …; false => …}`.
fn negation() -> Term {
    lam(
        Mult::Many,
        "b",
        simple(
            "Bool",
            Term::var(0),
            constantly(c("Bool")),
            vec![("true", c("false")), ("false", c("true"))],
        ),
    )
}

// ------------------------------------------------------------------ ι-редукция

#[test]
fn a_case_on_a_constructor_picks_its_branch() {
    let signature = base();
    let outcome = check_closed(&signature, &negation(), &arrow(c("Bool"), c("Bool")));
    assert!(outcome.is_ok(), "{outcome:?}");
    assert_eq!(normalize(&negation().apply([c("true")])), c("false"));
    assert_eq!(normalize(&negation().apply([c("false")])), c("true"));
}

#[test]
fn a_branch_receives_the_fields_but_not_the_parameters() {
    // `succ` несёт одно поле, `Nat` - ноль параметров, поэтому ветвь ждёт
    // ровно один аргумент.
    let signature = base();
    let predecessor = lam(
        Mult::Many,
        "n",
        simple(
            "Nat",
            Term::var(0),
            constantly(c("Nat")),
            vec![
                ("zero", c("zero")),
                ("succ", lam(Mult::Many, "k", Term::var(0))),
            ],
        ),
    );
    let two = c("succ").apply([c("succ").apply([c("zero")])]);
    assert_eq!(
        normalize(&predecessor.clone().apply([two.clone()])),
        normalize(&c("succ").apply([c("zero")]))
    );
    let outcome = check_closed(&signature, &predecessor, &arrow(c("Nat"), c("Nat")));
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_case_on_a_variable_stays_stuck() {
    // Нормальная форма сохраняет и мотив, и ветви: разбор - часть терма, а не
    // отложенное действие.
    assert_eq!(
        normalize(&negation()).to_string(),
        "\\(ω b) -> case #0 return (\\(0 _) -> Bool) of {true => false; false => true}"
    );
}

#[test]
fn a_stuck_case_may_be_applied_further() {
    // `(case b of …) x` - разбор в середине спайна, а не в его конце.
    let signature = base();
    let selector = lam(
        Mult::Many,
        "b",
        simple(
            "Bool",
            Term::var(0),
            constantly(arrow(c("Bool"), c("Bool"))),
            vec![
                ("true", lam(Mult::Many, "x", Term::var(0))),
                ("false", lam(Mult::Many, "x", c("true"))),
            ],
        )
        .apply([c("false")]),
    );
    let outcome = check_closed(&signature, &selector, &arrow(c("Bool"), c("Bool")));
    assert!(outcome.is_ok(), "{outcome:?}");
    assert_eq!(normalize(&selector.apply([c("true")])), c("false"));
}

#[test]
fn a_definition_reduces_through_a_case_only_when_unfolded() {
    // `eval` определений не разворачивает, поэтому `case two of …` остаётся
    // застрявшим. Свести его обязана проверка конвертируемости - и сводит.
    let mut signature = base();
    let two = c("succ").apply([c("succ").apply([c("zero")])]);
    declared(
        "two",
        &signature.define("two", Mult::Many, 0, c("Nat"), Some(two)),
    );

    let discriminated = simple(
        "Nat",
        c("two"),
        constantly(c("Bool")),
        vec![
            ("zero", c("true")),
            ("succ", lam(Mult::Many, "k", c("false"))),
        ],
    );
    assert!(
        normalize(&discriminated).to_string().contains("case"),
        "нормальная форма застряла на `two`"
    );
    let outcome = check_closed(&signature, &discriminated, &c("Bool"));
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(
        matches!(
            check_closed(&signature, &discriminated, &c("Nat")),
            Err(TypeError::Mismatch { .. })
        ),
        "тип от разворота не меняется"
    );
}

// ---------------------------------------------------------------------- мотив

#[test]
fn a_dependent_motive_gives_each_branch_its_own_type() {
    // Большая элиминация: разбор сам является типом, и ветви живут в разных
    // типах, а не в одном.
    let signature = base();
    let chosen = simple(
        "Bool",
        c("true"),
        constantly(Term::universe(0)),
        vec![("true", c("Nat")), ("false", c("Bool"))],
    );
    assert_eq!(infer_closed(&signature, &chosen), Ok(Term::universe(0)));

    // `case true of {true => Nat; …}` сводится к `Nat`, поэтому `zero` ему
    // принадлежит.
    let outcome = check_closed(&signature, &c("zero"), &chosen);
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(
        matches!(
            check_closed(&signature, &c("true"), &chosen),
            Err(TypeError::Mismatch { .. })
        ),
        "а `true` - нет"
    );
}

#[test]
fn a_branch_is_checked_against_the_motive_at_its_own_constructor() {
    let signature = base();
    // Мотив `\(0 x) -> case x of {true => Nat; false => Bool}`: ветвь `true`
    // обязана дать `Nat`, ветвь `false` - `Bool`.
    let motive = lam(
        Mult::Zero,
        "x",
        simple(
            "Bool",
            Term::var(0),
            constantly(Term::universe(0)),
            vec![("true", c("Nat")), ("false", c("Bool"))],
        ),
    );
    let correct = lam(
        Mult::Many,
        "b",
        simple(
            "Bool",
            Term::var(0),
            motive.clone(),
            vec![("true", c("zero")), ("false", c("true"))],
        ),
    );
    let ty = pi(
        Mult::Many,
        "b",
        c("Bool"),
        simple(
            "Bool",
            Term::var(0),
            constantly(Term::universe(0)),
            vec![("true", c("Nat")), ("false", c("Bool"))],
        ),
    );
    let outcome = check_closed(&signature, &correct, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    let swapped = lam(
        Mult::Many,
        "b",
        simple(
            "Bool",
            Term::var(0),
            motive,
            vec![("true", c("true")), ("false", c("true"))],
        ),
    );
    assert!(
        matches!(
            check_closed(&signature, &swapped, &ty),
            Err(TypeError::Mismatch { .. })
        ),
        "в ветви `true` требуется `Nat`"
    );
}

#[test]
fn a_motive_of_the_wrong_shape_is_rejected() {
    let signature = base();
    // Мотив обязан быть функцией от разбираемого значения. `Type 0` ею не
    // является, и отказ приходит от сверки с построенным типом мотива, а не от
    // попытки его применить.
    let broken = simple(
        "Bool",
        c("true"),
        Term::universe(0),
        vec![("true", c("Nat")), ("false", c("Bool"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &broken),
            Err(TypeError::Mismatch { .. })
        ),
        "мотив не функция"
    );

    // Кратность мотива тоже задана: он живёт в стёртом фрагменте целиком.
    let unerased = simple(
        "Bool",
        c("true"),
        lam(Mult::Many, "_", c("Bool")),
        vec![("true", c("false")), ("false", c("true"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &unerased),
            Err(TypeError::LambdaMultiplicity {
                expected: Mult::Zero,
                found: Mult::Many
            })
        ),
        "мотив связывает значение стёртым"
    );
}

// ------------------------------------------------------------------- индексы

#[test]
fn an_indexed_motive_specialises_per_branch() {
    // `\(0 n) -> \(1 xs) -> case xs return (\(0 m) -> \(0 _) -> Vect Bool m)`:
    // ветвь `vnil` обязана дать `Vect Bool zero`, ветвь `vcons` -
    // `Vect Bool (succ k)`. Ни то ни другое не совпадает с типом самого
    // разбираемого значения, и в этом весь смысл индекса.
    let signature = vectors();
    let motive = lam(
        Mult::Zero,
        "m",
        lam(Mult::Zero, "_", c("Vect").apply([c("Bool"), Term::var(1)])),
    );
    let copy = lam(
        Mult::Zero,
        "n",
        lam(
            Mult::One,
            "xs",
            case(
                "Vect",
                &[],
                1,
                Term::var(0),
                motive,
                vec![
                    ("vnil", c("vnil").apply([c("Bool")])),
                    (
                        "vcons",
                        lam(
                            Mult::Zero,
                            "k",
                            lam(
                                Mult::One,
                                "x",
                                lam(
                                    Mult::One,
                                    "ys",
                                    c("vcons").apply([
                                        c("Bool"),
                                        Term::var(2),
                                        Term::var(1),
                                        Term::var(0),
                                    ]),
                                ),
                            ),
                        ),
                    ),
                ],
            ),
        ),
    );
    let ty = pi(
        Mult::Zero,
        "n",
        c("Nat"),
        pi(
            Mult::One,
            "xs",
            c("Vect").apply([c("Bool"), Term::var(0)]),
            c("Vect").apply([c("Bool"), Term::var(1)]),
        ),
    );
    let outcome = check_closed(&signature, &copy, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_branch_cannot_ignore_its_index() {
    // Та же функция, но ветвь `vcons` возвращает пустой вектор: `Vect Bool
    // zero` против требуемого `Vect Bool (succ k)`.
    let signature = vectors();
    let motive = lam(
        Mult::Zero,
        "m",
        lam(Mult::Zero, "_", c("Vect").apply([c("Bool"), Term::var(1)])),
    );
    let broken = lam(
        Mult::Zero,
        "n",
        lam(
            Mult::One,
            "xs",
            case(
                "Vect",
                &[],
                1,
                Term::var(0),
                motive,
                vec![
                    ("vnil", c("vnil").apply([c("Bool")])),
                    (
                        "vcons",
                        lam(
                            Mult::Zero,
                            "k",
                            lam(
                                Mult::One,
                                "x",
                                lam(Mult::One, "ys", c("vnil").apply([c("Bool")])),
                            ),
                        ),
                    ),
                ],
            ),
        ),
    );
    let ty = pi(
        Mult::Zero,
        "n",
        c("Nat"),
        pi(
            Mult::One,
            "xs",
            c("Vect").apply([c("Bool"), Term::var(0)]),
            c("Vect").apply([c("Bool"), Term::var(1)]),
        ),
    );
    assert!(
        matches!(
            check_closed(&signature, &broken, &ty),
            Err(TypeError::Mismatch { .. })
        ),
        "длина в типе не сходится"
    );
}

// ----------------------------------------------------------------- параметры

#[test]
fn a_parametric_case_carries_its_level_arguments() {
    let signature = lists();
    let empty = lam(
        Mult::One,
        "xs",
        case(
            "List",
            &[Level::Zero],
            1,
            Term::var(0),
            constantly(c("Bool")),
            vec![
                ("nil", c("true")),
                (
                    "cons",
                    lam(Mult::One, "x", lam(Mult::One, "ys", c("false"))),
                ),
            ],
        ),
    );
    let ty = pi(
        Mult::One,
        "xs",
        Term::Const("List".into(), [Level::Zero].into()).apply([c("Bool")]),
        c("Bool"),
    );
    let outcome = check_closed(&signature, &empty, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    let applied = empty.apply([Term::Const("nil".into(), [Level::Zero].into()).apply([c("Bool")])]);
    assert_eq!(normalize(&applied), c("true"));
}

#[test]
fn a_wrong_parameter_count_is_rejected() {
    let signature = lists();
    let broken = lam(
        Mult::One,
        "xs",
        case(
            "List",
            &[Level::Zero],
            0,
            Term::var(0),
            constantly(c("Bool")),
            vec![
                ("nil", c("true")),
                (
                    "cons",
                    lam(Mult::One, "x", lam(Mult::One, "ys", c("false"))),
                ),
            ],
        ),
    );
    let ty = pi(
        Mult::One,
        "xs",
        Term::Const("List".into(), [Level::Zero].into()).apply([c("Bool")]),
        c("Bool"),
    );
    assert!(
        matches!(
            check_closed(&signature, &broken, &ty),
            Err(TypeError::CaseParameters {
                expected: 1,
                found: 0,
                ..
            })
        ),
        "число параметров сверяется с объявлением"
    );
}

// ----------------------------------------------------------------- покрытие

#[test]
fn a_missing_branch_is_rejected() {
    let signature = base();
    let partial = simple(
        "Bool",
        c("true"),
        constantly(c("Bool")),
        vec![("true", c("false"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &partial),
            Err(TypeError::NonExhaustive { .. })
        ),
        "конструктор `false` не покрыт"
    );
}

#[test]
fn branches_must_follow_the_declaration_order() {
    let signature = base();
    let swapped = simple(
        "Bool",
        c("true"),
        constantly(c("Bool")),
        vec![("false", c("true")), ("true", c("false"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &swapped),
            Err(TypeError::BranchOrder { .. })
        ),
        "порядок ветвей задан порядком объявления"
    );
}

#[test]
fn a_branch_for_a_foreign_constructor_is_rejected() {
    let signature = base();
    let alien = simple(
        "Bool",
        c("true"),
        constantly(c("Bool")),
        vec![
            ("true", c("false")),
            ("false", c("true")),
            ("zero", c("true")),
        ],
    );
    assert!(
        matches!(
            infer_closed(&signature, &alien),
            Err(TypeError::RedundantBranch { .. })
        ),
        "`zero` не конструктор `Bool`"
    );
}

#[test]
fn an_empty_type_needs_no_branches() {
    // Ex falso: из `Void` следует что угодно, и никакой ветви для этого не
    // требуется.
    let signature = base();
    let absurd = lam(
        Mult::One,
        "v",
        simple("Void", Term::var(0), constantly(c("Nat")), Vec::new()),
    );
    let outcome = check_closed(
        &signature,
        &absurd,
        &pi(Mult::One, "v", c("Void"), c("Nat")),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_case_needs_a_value_of_that_type() {
    let signature = base();
    let confused = simple(
        "Bool",
        c("zero"),
        constantly(c("Bool")),
        vec![("true", c("false")), ("false", c("true"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &confused),
            Err(TypeError::NotADataValue { .. })
        ),
        "`zero` не булево"
    );

    let postulated = simple(
        "and",
        c("true"),
        constantly(c("Bool")),
        vec![("true", c("false"))],
    );
    assert!(
        matches!(
            infer_closed(&signature, &postulated),
            Err(TypeError::NotADataType { .. })
        ),
        "по постулату разбирать нечего"
    );
}

// ---------------------------------------------------------------- кратности

#[test]
fn branches_are_joined_not_added() {
    // Линейное связывание, использованное в каждой из двух ветвей, остаётся
    // линейным: выполняется ровно одна ветвь. Сложение дало бы `ω` и отвергло
    // бы корректную программу.
    let signature = base();
    let chooser = lam(
        Mult::Many,
        "b",
        lam(
            Mult::One,
            "x",
            simple(
                "Bool",
                Term::var(1),
                constantly(c("Bool")),
                vec![("true", Term::var(0)), ("false", Term::var(0))],
            ),
        ),
    );
    let ty = pi(
        Mult::Many,
        "b",
        c("Bool"),
        pi(Mult::One, "x", c("Bool"), c("Bool")),
    );
    let outcome = check_closed(&signature, &chooser, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    // А два использования внутри одной ветви - уже `ω`.
    let doubled = lam(
        Mult::Many,
        "b",
        lam(
            Mult::One,
            "x",
            simple(
                "Bool",
                Term::var(1),
                constantly(c("Bool")),
                vec![
                    ("true", c("and").apply([Term::var(0), Term::var(0)])),
                    ("false", Term::var(0)),
                ],
            ),
        ),
    );
    assert!(
        matches!(
            check_closed(&signature, &doubled, &ty),
            Err(TypeError::UsageViolation { .. })
        ),
        "внутри ветви использования складываются"
    );
}

#[test]
fn a_field_is_spent_at_its_declared_multiplicity() {
    let signature = base();
    let ty = pi(Mult::Many, "p", c("Pair"), c("Bool"));
    let first = lam(
        Mult::Many,
        "p",
        simple(
            "Pair",
            Term::var(0),
            constantly(c("Bool")),
            vec![("mk", lam(Mult::One, "x", lam(Mult::One, "y", Term::var(1))))],
        ),
    );
    let outcome = check_closed(&signature, &first, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    let doubled = lam(
        Mult::Many,
        "p",
        simple(
            "Pair",
            Term::var(0),
            constantly(c("Bool")),
            vec![(
                "mk",
                lam(
                    Mult::One,
                    "x",
                    lam(Mult::One, "y", c("and").apply([Term::var(1), Term::var(1)])),
                ),
            )],
        ),
    );
    assert!(
        matches!(
            check_closed(&signature, &doubled, &ty),
            Err(TypeError::UsageViolation { .. })
        ),
        "поле кратности 1 нельзя использовать дважды"
    );
}

#[test]
fn a_field_multiplicity_scales_with_the_judgement() {
    // Тот же разбор с двойным использованием линейного поля: под `σ = 1`
    // отвергается, а в аргументе ω-функции проходит, потому что разрешено
    // `1 · ω = ω`. Это то самое масштабирование, на котором держится дефолт
    // кратности полей конструкторов (§4.1).
    let signature = base();
    let ty = pi(Mult::Many, "p", c("Pair"), c("Bool"));
    let doubling = || {
        simple(
            "Pair",
            Term::var(0),
            constantly(c("Bool")),
            vec![(
                "mk",
                lam(
                    Mult::One,
                    "x",
                    lam(Mult::One, "y", c("and").apply([Term::var(1), Term::var(1)])),
                ),
            )],
        )
    };

    assert!(
        matches!(
            check_closed(&signature, &lam(Mult::Many, "p", doubling()), &ty),
            Err(TypeError::UsageViolation { .. })
        ),
        "при σ = 1 разрешено 1 · 1 = 1"
    );
    let inside_omega = lam(Mult::Many, "p", c("use").apply([doubling()]));
    let outcome = check_closed(&signature, &inside_omega, &ty);
    assert!(
        outcome.is_ok(),
        "при σ = ω разрешено 1 · ω = ω: {outcome:?}"
    );
}

#[test]
fn an_erased_value_may_be_scrutinised_only_in_the_erased_fragment() {
    let signature = base();
    // В типе - можно: там σ = 0, и стёртое связывание доступно.
    let ty = pi(
        Mult::Zero,
        "b",
        c("Bool"),
        simple(
            "Bool",
            Term::var(0),
            constantly(Term::universe(0)),
            vec![("true", c("Nat")), ("false", c("Bool"))],
        ),
    );
    let inhabitant = lam(Mult::Zero, "b", c("zero"));
    assert!(
        matches!(
            check_closed(&signature, &inhabitant, &ty),
            Err(TypeError::Mismatch { .. })
        ),
        "тип корректен, но `zero` не подходит под оба варианта"
    );

    // В рантайме - нельзя: разбор расходует значение при σ = 1.
    let runtime = lam(
        Mult::Zero,
        "b",
        simple(
            "Bool",
            Term::var(0),
            constantly(c("Bool")),
            vec![("true", c("false")), ("false", c("true"))],
        ),
    );
    assert!(
        matches!(
            check_closed(
                &signature,
                &runtime,
                &pi(Mult::Zero, "b", c("Bool"), c("Bool"))
            ),
            Err(TypeError::UsageViolation { .. })
        ),
        "стёртое значение разобрать в рантайме нельзя"
    );
}

// ------------------------------------------------------- конвертируемость

#[test]
fn stuck_cases_are_compared_branch_by_branch() {
    let signature = base();
    let ty = arrow(c("Bool"), c("Bool"));
    // Разбор, эквивалентный тождественной функции по значению, но застрявший:
    // сам себе конвертируем, чужому - нет.
    let identity_like = |first: Term, second: Term| {
        lam(
            Mult::Many,
            "b",
            simple(
                "Bool",
                Term::var(0),
                constantly(c("Bool")),
                vec![("true", first), ("false", second)],
            ),
        )
    };
    let same = identity_like(c("true"), c("false"));
    let outcome = check_closed(&signature, &same, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    // Два застрявших разбора с разными ветвями не конвертируемы, хотя оба
    // имеют один тип: сравнение идёт по ветвям, а не по типу.
    let ty_of_pair = pi(
        Mult::Many,
        "f",
        arrow(c("Bool"), c("Bool")),
        arrow(c("Bool"), c("Bool")),
    );
    let checked = lam(Mult::Many, "f", same.clone());
    assert!(check_closed(&signature, &checked, &ty_of_pair).is_ok());
    assert_ne!(
        normalize(&same),
        normalize(&identity_like(c("false"), c("true"))),
        "разные ветви - разные нормальные формы"
    );
}

// ------------------------------------------------------------ запечатывание

/// Пустое семейство остаётся пустым после того, как по нему разобрали.
///
/// `absurd : Void -> A` проверена с нулём ветвей, потому что у `Void` не было
/// конструкторов. Если конструктор появится позже, полнота ветвей окажется
/// проверенной по прежнему списку, а перепроверять принятые определения
/// некому: `absurd boom` дала бы замкнутого обитателя произвольного типа,
/// признанного тотальным.
#[test]
fn a_family_that_has_been_eliminated_takes_no_more_constructors() {
    let mut signature = Signature::default();
    let mut metas = adamas_core::meta::Metas::default();
    signature
        .postulate("A", Mult::Many, 0, Term::universe(0))
        .expect("A корректен");
    signature
        .declare_data("Void", 0, &mut metas, Term::universe(0))
        .expect("Void корректен");

    signature
        .define(
            "absurd",
            Mult::Many,
            0,
            arrow(c("Void"), c("A")),
            Some(lam(
                Mult::Many,
                "v",
                case(
                    "Void",
                    &[],
                    0,
                    Term::var(0),
                    lam(Mult::Zero, "x", c("A")),
                    Vec::new(),
                ),
            )),
        )
        .expect("разбор пустого семейства законен, пока оно пусто");

    assert!(
        matches!(
            signature.declare_constructor("Void", "boom", &mut metas, c("Void")),
            Err(TypeError::SealedFamily { .. })
        ),
        "список конструкторов закрыт разбором"
    );
    assert!(
        signature.lookup("boom").is_none(),
        "отказ не оставляет следов в сигнатуре"
    );
}

/// Закрывается только разобранное семейство и только им.
#[test]
fn sealing_is_confined_to_the_family_that_was_eliminated() {
    let mut signature = base();
    let mut metas = adamas_core::meta::Metas::default();
    signature
        .declare_data("Colour", 0, &mut metas, Term::universe(0))
        .expect("Colour корректен");
    signature
        .declare_constructor("Colour", "red", &mut metas, c("Colour"))
        .expect("первый конструктор законен");

    // Разбор по `Bool` не касается `Colour`.
    signature
        .define(
            "negate",
            Mult::Many,
            0,
            arrow(c("Bool"), c("Bool")),
            Some(lam(
                Mult::Many,
                "b",
                simple(
                    "Bool",
                    Term::var(0),
                    constantly(c("Bool")),
                    vec![("true", c("false")), ("false", c("true"))],
                ),
            )),
        )
        .expect("negate корректна");

    assert!(
        signature
            .declare_constructor("Colour", "blue", &mut metas, c("Colour"))
            .is_ok(),
        "по `Colour` не разбирали - список ещё открыт"
    );
    assert!(
        matches!(
            signature.declare_constructor("Bool", "maybe", &mut metas, c("Bool")),
            Err(TypeError::SealedFamily { .. })
        ),
        "а по `Bool` разбирали"
    );
}

// ------------------------------------------------------------------ свойства

/// Имена, из которых собираются списки ветвей: два конструктора `Bool` и
/// чужой, чтобы в выборку попадали и посторонние ветви.
const BRANCH_NAMES: [&str; 3] = ["true", "false", "zero"];

/// Список ветвей произвольной формы - перестановки, пропуски, повторы, чужие.
fn any_branch_names() -> impl Strategy<Value = Vec<usize>> {
    proptest::collection::vec(0usize..BRANCH_NAMES.len(), 0..4)
}

/// `succ (succ (… zero))`, `k` раз.
fn nat(k: u32) -> Term {
    (0..k).fold(c("zero"), |acc, _| c("succ").apply([acc]))
}

/// Предшественник: `case n return (\_ -> Nat) of { zero => zero; succ m => m }`.
fn predecessor(scrutinee: Term) -> Term {
    simple(
        "Nat",
        scrutinee,
        constantly(c("Nat")),
        vec![
            ("zero", c("zero")),
            ("succ", lam(Mult::Many, "m", Term::var(0))),
        ],
    )
}

proptest! {
    /// Покрытие точное: `case` принимается тогда и только тогда, когда список
    /// ветвей дословно равен списку конструкторов.
    ///
    /// Отдельные примеры выше фиксируют по одной точке - пропуск, порядок,
    /// чужой конструктор. Свойство закрывает и повторы, и любые их сочетания
    /// разом, а главное - проверяет, что *принимается* только точный список.
    #[test]
    fn coverage_accepts_exactly_the_declared_list(names in any_branch_names()) {
        let signature = base();
        let branches: Vec<(&str, Term)> = names
            .iter()
            .map(|index| (BRANCH_NAMES[*index], c("Bool")))
            .collect();
        let term = simple("Bool", c("true"), constantly(Term::universe(0)), branches);

        let exact = names.len() == 2 && names[0] == 0 && names[1] == 1;
        prop_assert_eq!(
            infer_closed(&signature, &term).is_ok(),
            exact,
            "ветви: {:?}", names.iter().map(|i| BRANCH_NAMES[*i]).collect::<Vec<_>>()
        );
    }

    /// ι выбирает ветвь того конструктора и передаёт ей **поля**, а не всё
    /// значение целиком.
    ///
    /// Предшественник - самый короткий разбор, в котором это различимо: тело
    /// ветви `succ` возвращает своё поле, поэтому неверная передача спайна
    /// видна сразу и по значению, а не только по типу.
    #[test]
    fn iota_selects_the_branch_and_passes_its_fields(k in 0u32..6) {
        let signature = base();
        let term = predecessor(nat(k));
        let expected = nat(k.saturating_sub(1));

        prop_assert!(check_closed(&signature, &term, &c("Nat")).is_ok());
        prop_assert_eq!(
            normalize(&term).to_string(),
            expected.to_string(),
            "предшественник {}",
            k
        );
    }

    /// Subject reduction через ι: вычисление разбора не меняет его тип.
    ///
    /// То же свойство, что уже проверяется на термах без разбора, но здесь
    /// редукция выбирает ветвь, а не подставляет аргумент, и сохранение типа
    /// становится утверждением о мотиве.
    #[test]
    fn iota_preserves_the_inferred_type(k in 0u32..6) {
        let signature = base();
        let term = predecessor(nat(k));

        let before = infer_closed(&signature, &term);
        prop_assume!(before.is_ok());
        let after = infer_closed(&signature, &normalize(&term));
        prop_assert_eq!(
            before.map(|ty| ty.to_string()),
            after.map(|ty| ty.to_string())
        );
    }
}

proptest! {
    /// Поля приходят в ветвь в порядке объявления.
    ///
    /// На однополевом конструкторе это неразличимо, поэтому нужен `Pair`:
    /// ветвь возвращает первое поле или второе, и перепутанный порядок виден
    /// по значению. Поля объявлены линейными, а `1` аффинна, поэтому
    /// невозвращённое поле остаться неиспользованным вправе.
    #[test]
    fn fields_arrive_in_declaration_order(first in any::<bool>(), second in any::<bool>(), take_second in any::<bool>()) {
        let signature = base();
        let name = |flag: bool| if flag { "true" } else { "false" };

        let pair = c("mk").apply([c(name(first)), c(name(second))]);
        // `\(1 x) -> \(1 y) -> x` либо `… -> y`.
        let projection = lam(
            Mult::One,
            "x",
            lam(Mult::One, "y", Term::var(u32::from(!take_second))),
        );
        let term = simple(
            "Pair",
            pair,
            constantly(c("Bool")),
            vec![("mk", projection)],
        );

        prop_assert!(check_closed(&signature, &term, &c("Bool")).is_ok());
        let expected = if take_second { name(second) } else { name(first) };
        prop_assert_eq!(normalize(&term).to_string(), expected);
    }
}
