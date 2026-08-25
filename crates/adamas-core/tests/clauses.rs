//! Элаборация клауз в дерево разбора (§9 Фаза 1, §10 вопрос 7).
//!
//! Проверяется не форма дерева, а два его свойства: собранный терм **проходит
//! проверку типов** и **вычисляет то, что написано в клаузах**. Форма - деталь
//! стратегии компиляции, и тест на неё ломался бы от смены эвристики выбора
//! колонки, ничего при этом не защищая.

use std::rc::Rc;

use proptest::prelude::*;

use adamas_core::check::{TypeError, check_closed};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern, PatternError, compile};
use adamas_core::sig::Signature;
use adamas_core::term::Term;

// -------------------------------------------------------------- конструкторы

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
}

fn arrow(domain: Term, codomain: Term) -> Term {
    pi(Mult::Many, "_", domain, codomain)
}

fn c(name: &str) -> Term {
    Term::constant(name)
}

fn var(name: &str) -> Pattern {
    Pattern::Var(name.into())
}

fn ctor(name: &str, fields: Vec<Pattern>) -> Pattern {
    Pattern::Constructor(name.into(), fields)
}

fn clause(patterns: Vec<Pattern>, body: Term) -> Clause {
    Clause { patterns, body }
}

fn number(value: u32) -> Term {
    (0..value).fold(c("zero"), |term, _| c("succ").apply([term]))
}

/// `P n` - семейство, различающее числа; свидетель - `anything n`.
fn family(index: Term) -> Term {
    c("P").apply([index])
}

// -------------------------------------------------------------- заготовки

fn declared(what: &str, outcome: &Result<(), TypeError>) {
    assert!(outcome.is_ok(), "{what} корректен: {outcome:?}");
}

/// `Bool`, `Nat`, семейство `P` и свидетель `anything`.
fn base() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    declared(
        "Bool",
        &signature.declare_data(
            &mut metas,
            "Bool",
            0,
            Term::universe(0),
            &[("true", c("Bool")), ("false", c("Bool"))],
        ),
    );
    declared(
        "Nat",
        &signature.declare_data(
            &mut metas,
            "Nat",
            0,
            Term::universe(0),
            &[("zero", c("Nat")), ("succ", arrow(c("Nat"), c("Nat")))],
        ),
    );
    declared(
        "P",
        &signature.postulate(
            &mut metas,
            "P",
            Mult::Many,
            0,
            pi(Mult::Zero, "n", c("Nat"), Term::universe(0)),
        ),
    );
    declared(
        "anything",
        &signature.postulate(
            &mut metas,
            "anything",
            Mult::Many,
            0,
            pi(Mult::Zero, "n", c("Nat"), family(Term::var(0))),
        ),
    );
    signature
}

/// `List : (0 A : Type u) -> Type u` с `nil` и `cons`.
fn with_lists(signature: &mut Signature) {
    let mut metas = Metas::default();
    let level = metas.fresh_level();
    // Ссылка на член объявляемой группы пишется дырками: спросить у сигнатуры
    // нечего - семейства там ещё нет. Число дырок обязано совпасть с арностью,
    // и это проверяется (`LevelArity`).
    let list_of = |metas: &mut Metas, element: Term| {
        Term::Const("List".into(), Rc::from([metas.fresh_level()])).apply([element])
    };
    let nil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        list_of(&mut metas, Term::var(0)),
    );
    let cons = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::Many,
            "x",
            Term::var(0),
            pi(
                Mult::Many,
                "xs",
                list_of(&mut metas, Term::var(1)),
                list_of(&mut metas, Term::var(2)),
            ),
        ),
    );
    declared(
        "List",
        &signature.declare_data(
            &mut metas,
            "List",
            1,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
            &[("nil", nil), ("cons", cons)],
        ),
    );
}

/// Собирает клаузы и определяет функцию, требуя успеха на обоих шагах.
fn define(signature: &mut Signature, name: &str, ty: Term, clauses: &[Clause]) {
    // Одно хранилище на весь вызов: сборка клауз и проверка определения - это
    // один прогон, и дырка из первого шага обязана дожить до второго.
    let mut metas = Metas::default();
    let body = compile(signature, &mut metas, &ty, clauses);
    let body = match body {
        Ok(body) => body,
        Err(error) => panic!("`{name}` не собирается: {error}"),
    };
    let outcome = signature.define(&mut metas, name, Mult::Many, 0, ty, Some(body));
    assert!(outcome.is_ok(), "`{name}` не типизируется: {outcome:?}");
}

// ------------------------------------------------------------------ сборка

#[test]
fn clauses_become_a_well_typed_term() {
    // `not true = false; not false = true`
    let mut signature = base();
    define(
        &mut signature,
        "not",
        arrow(c("Bool"), c("Bool")),
        &[
            clause(vec![ctor("true", Vec::new())], c("false")),
            clause(vec![ctor("false", Vec::new())], c("true")),
        ],
    );
    let outcome = check_closed(&signature, &c("not").apply([c("true")]), &c("Bool"));
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_recursive_definition_is_written_as_clauses() {
    // `plus zero m = m; plus (succ k) m = succ (plus k m)`
    //
    // Переменные клаузы нумеруются слева направо: во второй клаузе `k` - #0,
    // `m` - #1, поэтому в теле `m` это `#0`, а `k` - `#1`.
    let mut signature = base();
    define(
        &mut signature,
        "plus",
        arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
        &[
            clause(vec![ctor("zero", Vec::new()), var("m")], Term::var(0)),
            clause(
                vec![ctor("succ", vec![var("k")]), var("m")],
                c("succ").apply([c("plus").apply([Term::var(1), Term::var(0)])]),
            ),
        ],
    );
    assert!(
        signature
            .lookup("plus")
            .is_some_and(|definition| definition.total),
        "структурная рекурсия распознана и на собранном терме"
    );

    for (left, right, sum) in [(0, 0, 0), (2, 3, 5), (4, 1, 5)] {
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(sum)]),
            &family(c("plus").apply([number(left), number(right)])),
        );
        assert!(outcome.is_ok(), "{left}+{right} = {sum}: {outcome:?}");
    }
}

#[test]
fn nested_patterns_are_compiled_into_a_chain() {
    // `even zero = true; even (succ zero) = false; even (succ (succ k)) = even k`
    let mut signature = base();
    let mut metas = Metas::default();
    define(
        &mut signature,
        "even",
        arrow(c("Nat"), c("Bool")),
        &[
            clause(vec![ctor("zero", Vec::new())], c("true")),
            clause(
                vec![ctor("succ", vec![ctor("zero", Vec::new())])],
                c("false"),
            ),
            clause(
                vec![ctor("succ", vec![ctor("succ", vec![var("k")])])],
                c("even").apply([Term::var(0)]),
            ),
        ],
    );
    assert!(
        signature
            .lookup("even")
            .is_some_and(|definition| definition.total),
        "уменьшение через два разбора видно проверке тотальности"
    );

    // Значение проверяется через семейство над `Bool`: `even n` конвертируем с
    // ожидаемым конструктором только если цепочка разборов сложилась верно.
    let mut probe = signature.clone();
    declared(
        "Q",
        &probe.postulate(
            &mut metas,
            "Q",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), Term::universe(0)),
        ),
    );
    declared(
        "witness",
        &probe.postulate(
            &mut metas,
            "witness",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), c("Q").apply([Term::var(0)])),
        ),
    );
    for (value, expected) in [(0, "true"), (1, "false"), (4, "true"), (7, "false")] {
        let outcome = check_closed(
            &probe,
            &c("witness").apply([c(expected)]),
            &c("Q").apply([c("even").apply([number(value)])]),
        );
        assert!(outcome.is_ok(), "even {value} = {expected}: {outcome:?}");
    }
}

#[test]
fn the_first_matching_clause_wins() {
    // `orb true  b = true; orb a false = a; orb a b = b`
    // Первая клауза перекрывает вторую при `true false`, и результат обязан
    // быть `true`, а не разбор второй.
    let mut signature = base();
    let mut metas = Metas::default();
    define(
        &mut signature,
        "orb",
        arrow(c("Bool"), arrow(c("Bool"), c("Bool"))),
        &[
            clause(vec![ctor("true", Vec::new()), var("b")], c("true")),
            clause(vec![var("a"), ctor("false", Vec::new())], Term::var(0)),
            clause(vec![var("a"), var("b")], Term::var(0)),
        ],
    );

    declared(
        "Q",
        &signature.postulate(
            &mut metas,
            "Q",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), Term::universe(0)),
        ),
    );
    declared(
        "witness",
        &signature.postulate(
            &mut metas,
            "witness",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), c("Q").apply([Term::var(0)])),
        ),
    );
    for (left, right, expected) in [
        ("true", "false", "true"),
        ("true", "true", "true"),
        ("false", "false", "false"),
        ("false", "true", "true"),
    ] {
        let outcome = check_closed(
            &signature,
            &c("witness").apply([c(expected)]),
            &c("Q").apply([c("orb").apply([c(left), c(right)])]),
        );
        assert!(
            outcome.is_ok(),
            "orb {left} {right} = {expected}: {outcome:?}"
        );
    }
}

#[test]
fn a_parameter_survives_the_split() {
    // `length nil = zero; length (cons x xs) = succ (length xs)` над
    // параметризованным `List`. Параметр в ветвь не приходит, но и не теряется:
    // поля `cons` берутся при уже подставленном `A`, а `Case` несёт их число.
    //
    // Кратности здесь всюду ω: `succ` объявлен с ω-аргументом, поэтому
    // `succ (length xs)` тратил бы хвост неограниченно, и линейные поля
    // `cons` сделали бы определение непроверяемым.
    let mut signature = base();
    with_lists(&mut signature);

    let list_of_bool =
        Term::Const("List".into(), [adamas_core::level::Level::Zero].into()).apply([c("Bool")]);
    define(
        &mut signature,
        "length",
        pi(Mult::Many, "xs", list_of_bool.clone(), c("Nat")),
        &[
            clause(vec![ctor("nil", Vec::new())], c("zero")),
            clause(
                vec![ctor("cons", vec![var("x"), var("xs")])],
                c("succ").apply([c("length").apply([Term::var(0)])]),
            ),
        ],
    );
    assert!(
        signature
            .lookup("length")
            .is_some_and(|definition| definition.total)
    );

    let cons = |head: Term, tail: Term| {
        Term::Const("cons".into(), [adamas_core::level::Level::Zero].into()).apply([
            c("Bool"),
            head,
            tail,
        ])
    };
    let empty =
        Term::Const("nil".into(), [adamas_core::level::Level::Zero].into()).apply([c("Bool")]);
    let two = cons(c("true"), cons(c("false"), empty));
    let outcome = check_closed(
        &signature,
        &c("anything").apply([number(2)]),
        &family(c("length").apply([two])),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_dependent_result_is_refined_by_every_split() {
    // `f : (n : Nat) -> (b : Bool) -> P n`. Тип результата зависит от первого
    // аргумента, а разбор идёт по обоим: во второй ветви тело обязано иметь тип
    // `P zero`, а не `P n`. Уточнение должно доживать до вложенного разбора.
    let mut signature = base();
    let witness = |index: Term| c("anything").apply([index]);
    define(
        &mut signature,
        "f",
        pi(
            Mult::Many,
            "n",
            c("Nat"),
            pi(Mult::Many, "b", c("Bool"), family(Term::var(1))),
        ),
        &[
            clause(
                vec![ctor("zero", Vec::new()), ctor("true", Vec::new())],
                witness(c("zero")),
            ),
            clause(
                vec![ctor("zero", Vec::new()), ctor("false", Vec::new())],
                witness(c("zero")),
            ),
            clause(
                vec![ctor("succ", vec![var("k")]), var("b")],
                witness(c("succ").apply([Term::var(1)])),
            ),
        ],
    );
}

#[test]
fn a_variable_pattern_is_refined_by_the_split() {
    // `g zero = anything zero; g n = anything n`. Вторая клауза связала
    // аргумент переменной, но в ветви `succ` эта переменная - `succ k`, и тип
    // тела обязан быть `P (succ k)`, а не `P n`.
    let mut signature = base();
    define(
        &mut signature,
        "g",
        pi(Mult::Many, "n", c("Nat"), family(Term::var(0))),
        &[
            clause(
                vec![ctor("zero", Vec::new())],
                c("anything").apply([c("zero")]),
            ),
            clause(vec![var("n")], c("anything").apply([Term::var(0)])),
        ],
    );
}

/// `If : Bool -> Type 0` - `If true = Nat`, `If false = Bool`.
///
/// Само определение пишется клаузами: большая элиминация ничем не отличается
/// от обычной, кроме того, что тип результата - универсум.
fn with_if(signature: &mut Signature) {
    define(
        signature,
        "If",
        arrow(c("Bool"), Term::universe(0)),
        &[
            clause(vec![ctor("true", Vec::new())], c("Nat")),
            clause(vec![ctor("false", Vec::new())], c("Bool")),
        ],
    );
}

/// `(ω b : Bool) -> (ω x : If b) -> Nat`
fn dependent_pair() -> Term {
    pi(
        Mult::Many,
        "b",
        c("Bool"),
        arrow(c("If").apply([Term::var(0)]), c("Nat")),
    )
}

#[test]
fn a_neighbour_is_refined_by_the_split() {
    // Индексов здесь нет ни одного, но тип второго аргумента зависит от
    // первого: в ветви `true` он обязан стать `Nat`, в ветви `false` - `Bool`.
    // Ядро связывает мотив с одним значением, поэтому сосед выносится в тот же
    // мотив, а разбор применяется обратно к нему.
    let mut signature = base();
    with_if(&mut signature);
    define(
        &mut signature,
        "g",
        dependent_pair(),
        &[
            // `x : Nat` - только поэтому его и можно вернуть.
            clause(vec![ctor("true", Vec::new()), var("x")], Term::var(0)),
            // `x : Bool` - вернуть его нельзя, и клауза этого не делает.
            clause(vec![ctor("false", Vec::new()), var("x")], c("zero")),
        ],
    );

    for (flag, argument, result) in [("true", number(2), 2), ("false", c("true"), 0)] {
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(result)]),
            &family(c("g").apply([c(flag), argument])),
        );
        assert!(outcome.is_ok(), "g {flag} = {result}: {outcome:?}");
    }
}

#[test]
fn a_refinement_that_did_not_happen_is_rejected() {
    // Обратная сторона: в ветви `false` сосед - `Bool`, и вернуть его вместо
    // `Nat` нельзя. Уточнение обязано быть уточнением, а не размыванием.
    let mut signature = base();
    let mut metas = Metas::default();
    with_if(&mut signature);
    let body = compile(
        &signature,
        &mut Metas::default(),
        &dependent_pair(),
        &[
            clause(vec![ctor("true", Vec::new()), var("x")], Term::var(0)),
            clause(vec![ctor("false", Vec::new()), var("x")], Term::var(0)),
        ],
    )
    .expect("дерево собирается: неверен здесь тип тела, а не форма клауз");
    assert!(
        matches!(
            signature.define(&mut metas, "g", Mult::Many, 0, dependent_pair(), Some(body)),
            Err(TypeError::Mismatch { .. })
        ),
        "`Bool` вместо `Nat`"
    );
}

#[test]
fn a_refined_neighbour_can_be_matched_in_turn() {
    // Разбирать `x : If b` нельзя - до уточнения это застрявшее вычисление, а
    // не семейство. В ветви `true` оно становится `Nat`, и вложенный разбор
    // идёт уже по нему.
    let mut signature = base();
    with_if(&mut signature);
    define(
        &mut signature,
        "h",
        dependent_pair(),
        &[
            clause(
                vec![ctor("true", Vec::new()), ctor("zero", Vec::new())],
                c("zero"),
            ),
            clause(
                vec![ctor("true", Vec::new()), ctor("succ", vec![var("k")])],
                Term::var(0),
            ),
            clause(vec![ctor("false", Vec::new()), var("x")], c("zero")),
        ],
    );

    for (flag, argument, result) in [
        ("true", number(3), 2),
        ("true", number(0), 0),
        ("false", c("false"), 0),
    ] {
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(result)]),
            &family(c("h").apply([c(flag), argument])),
        );
        assert!(outcome.is_ok(), "h {flag} = {result}: {outcome:?}");
    }
}

#[test]
fn recursion_on_a_refined_neighbour_is_still_structural() {
    // Уточнённый аргумент приходит в ветвь лишней лямбдой, и убывание по нему
    // обязано доживать до проверки тотальности - иначе convoy делал бы
    // нетотальным всякое определение, рекурсия которого идёт по соседу.
    let mut signature = base();
    with_if(&mut signature);
    define(
        &mut signature,
        "count",
        dependent_pair(),
        &[
            clause(
                vec![ctor("true", Vec::new()), ctor("zero", Vec::new())],
                c("zero"),
            ),
            clause(
                vec![ctor("true", Vec::new()), ctor("succ", vec![var("k")])],
                c("succ").apply([c("count").apply([c("true"), Term::var(0)])]),
            ),
            clause(vec![ctor("false", Vec::new()), var("x")], c("zero")),
        ],
    );
    assert!(
        signature
            .lookup("count")
            .is_some_and(|definition| definition.total),
        "рекурсия по вынесенному соседу структурная"
    );
    let outcome = check_closed(
        &signature,
        &c("anything").apply([number(3)]),
        &family(c("count").apply([c("true"), number(3)])),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_variable_pattern_is_refined_by_a_nested_split() {
    // Та же связка на два разбора в глубину: третья клауза достаётся ветви
    // `succ (succ k)`, и её `n` там - построенное значение, а не исходный
    // аргумент. Иначе тело имеет тип `P n` там, где требуется `P (succ (succ k))`.
    let mut signature = base();
    define(
        &mut signature,
        "f",
        pi(Mult::Many, "n", c("Nat"), family(Term::var(0))),
        &[
            clause(
                vec![ctor("zero", Vec::new())],
                c("anything").apply([c("zero")]),
            ),
            clause(
                vec![ctor("succ", vec![ctor("zero", Vec::new())])],
                c("anything").apply([number(1)]),
            ),
            clause(vec![var("n")], c("anything").apply([Term::var(0)])),
        ],
    );
}

#[test]
fn a_linear_argument_survives_being_matched() {
    // `f zero = zero; f n = n` при линейном аргументе. Разбор тратит значение,
    // поэтому тело обязано пользоваться полями ветви, а не исходным
    // аргументом: иначе расход выходит вторым.
    let mut signature = base();
    define(
        &mut signature,
        "f",
        pi(Mult::One, "n", c("Nat"), c("Nat")),
        &[
            clause(vec![ctor("zero", Vec::new())], c("zero")),
            clause(vec![var("n")], Term::var(0)),
        ],
    );
    let outcome = check_closed(
        &signature,
        &c("anything").apply([number(3)]),
        &family(c("f").apply([number(3)])),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_split_on_a_later_column_binds_correctly() {
    // `f m zero = m; f m (succ k) = succ (f m k)` - разбор идёт по второй
    // колонке, а первая остаётся переменной во всех клаузах.
    let mut signature = base();
    define(
        &mut signature,
        "f",
        arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
        &[
            clause(vec![var("m"), ctor("zero", Vec::new())], Term::var(0)),
            clause(
                vec![var("m"), ctor("succ", vec![var("k")])],
                c("succ").apply([c("f").apply([Term::var(1), Term::var(0)])]),
            ),
        ],
    );
    assert!(
        signature
            .lookup("f")
            .is_some_and(|definition| definition.total)
    );
    for (left, right, sum) in [(0, 0, 0), (2, 3, 5), (4, 1, 5)] {
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(sum)]),
            &family(c("f").apply([number(left), number(right)])),
        );
        assert!(outcome.is_ok(), "{left}+{right} = {sum}: {outcome:?}");
    }
}

// ------------------------------------------------------------------- отказы

#[test]
fn a_missing_case_is_reported_with_an_example() {
    let signature = base();
    let outcome = compile(
        &signature,
        &mut Metas::default(),
        &arrow(c("Nat"), c("Bool")),
        &[clause(vec![ctor("zero", Vec::new())], c("true"))],
    );
    assert_eq!(
        outcome.map(|_| ()).unwrap_err().to_string(),
        "не покрыто: `succ _`"
    );

    // Вложенный случай называется целиком, а не «где-то в succ».
    let outcome = compile(
        &signature,
        &mut Metas::default(),
        &arrow(c("Nat"), c("Bool")),
        &[
            clause(vec![ctor("zero", Vec::new())], c("true")),
            clause(
                vec![ctor("succ", vec![ctor("zero", Vec::new())])],
                c("false"),
            ),
        ],
    );
    assert_eq!(
        outcome.map(|_| ()).unwrap_err().to_string(),
        "не покрыто: `succ (succ _)`"
    );
}

#[test]
fn an_unreachable_clause_is_reported() {
    let signature = base();
    assert!(
        matches!(
            compile(
                &signature,
                &mut Metas::default(),
                &arrow(c("Nat"), c("Bool")),
                &[
                    clause(vec![var("n")], c("true")),
                    clause(vec![ctor("zero", Vec::new())], c("false")),
                ],
            ),
            Err(PatternError::UnreachableClause { clause: 1 })
        ),
        "первая клауза покрывает всё"
    );
}

#[test]
fn a_foreign_constructor_is_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(c("Nat"), c("Bool")),
            &[
                clause(vec![ctor("true", Vec::new())], c("true")),
                clause(vec![var("n")], c("false")),
            ],
        ),
        Err(PatternError::ForeignConstructor { .. })
    ));
}

#[test]
fn clauses_disagreeing_on_arity_are_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(c("Nat"), arrow(c("Nat"), c("Bool"))),
            &[
                clause(vec![var("n"), var("m")], c("true")),
                clause(vec![var("n")], c("false")),
            ],
        ),
        Err(PatternError::ClauseArity {
            clause: 1,
            expected: 2,
            found: 1
        })
    ));
}

#[test]
fn more_patterns_than_arguments_are_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(c("Nat"), c("Bool")),
            &[clause(vec![var("n"), var("m")], c("true"))],
        ),
        Err(PatternError::ClauseArity {
            clause: 0,
            expected: 1,
            found: 2
        })
    ));
}

#[test]
fn a_definition_may_return_a_function() {
    // `twice g = \x. g (g x)` - паттернов меньше, чем `Pi` в типе. Арность
    // задают клаузы: разбирается ровно то, что они называют.
    let mut signature = base();
    define(
        &mut signature,
        "twice",
        arrow(arrow(c("Nat"), c("Nat")), arrow(c("Nat"), c("Nat"))),
        &[clause(
            vec![var("g")],
            Term::Lam(
                Mult::Many,
                "x".into(),
                Rc::new(Term::var(1).apply([Term::var(1).apply([Term::var(0)])])),
            ),
        )],
    );

    define(
        &mut signature,
        "double",
        arrow(c("Nat"), c("Nat")),
        &[clause(vec![var("n")], c("succ").apply([Term::var(0)]))],
    );
    let outcome = check_closed(
        &signature,
        &c("anything").apply([number(3)]),
        &family(c("twice").apply([c("double"), number(1)])),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn an_empty_family_is_eliminated_without_clauses() {
    // Пустой тип населить нечем, поэтому `absurd` пишется без единой клаузы:
    // разбор с нулём ветвей и есть доказательство.

    let mut signature = base();
    let mut metas = Metas::default();
    declared(
        "Void",
        &signature.declare_data(&mut metas, "Void", 0, Term::universe(0), &[]),
    );
    define(&mut signature, "absurd", arrow(c("Void"), c("Nat")), &[]);

    // И то же самое посреди разбора: ветвь `false` недостижима не потому, что
    // её забыли, а потому, что второй аргумент населить нечем.
    define(
        &mut signature,
        "only_true",
        arrow(c("Bool"), arrow(c("Void"), c("Nat"))),
        &[clause(vec![ctor("true", Vec::new()), var("v")], c("zero"))],
    );
}

#[test]
fn a_wrong_field_count_is_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(c("Nat"), c("Bool")),
            &[
                clause(vec![ctor("zero", Vec::new())], c("true")),
                clause(vec![ctor("succ", vec![var("k"), var("j")])], c("false")),
            ],
        ),
        Err(PatternError::ConstructorArity {
            expected: 1,
            found: 2,
            ..
        })
    ));
}

#[test]
fn matching_a_non_inductive_value_is_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(arrow(c("Nat"), c("Nat")), c("Bool")),
            &[clause(vec![ctor("zero", Vec::new())], c("true"))],
        ),
        Err(PatternError::NotMatchable { .. })
    ));
}

// -------------------------------------------------- индексированные семейства

/// `Vect : (0 A : Type 0) -> (0 n : Nat) -> Type 0` с `vnil` и `vcons`.
fn with_vectors(signature: &mut Signature) {
    let mut metas = Metas::default();
    declared(
        "Vect",
        &signature.declare_data(
            &mut metas,
            "Vect",
            1,
            pi(
                Mult::Zero,
                "A",
                Term::universe(0),
                pi(Mult::Zero, "n", c("Nat"), Term::universe(0)),
            ),
            &[
                (
                    "vnil",
                    pi(
                        Mult::Zero,
                        "A",
                        Term::universe(0),
                        c("Vect").apply([Term::var(0), c("zero")]),
                    ),
                ),
                (
                    "vcons",
                    pi(
                        Mult::Zero,
                        "A",
                        Term::universe(0),
                        pi(
                            Mult::Zero,
                            "k",
                            c("Nat"),
                            pi(
                                Mult::Many,
                                "x",
                                Term::var(1),
                                pi(
                                    Mult::Many,
                                    "xs",
                                    c("Vect").apply([Term::var(2), Term::var(1)]),
                                    c("Vect")
                                        .apply([Term::var(3), c("succ").apply([Term::var(2)])]),
                                ),
                            ),
                        ),
                    ),
                ),
            ],
        ),
    );
}

/// `Q : Bool -> Type 0` и свидетель: так проверяется вычисленное булево.
fn with_bool_family(signature: &mut Signature) {
    let mut metas = Metas::default();
    declared(
        "Q",
        &signature.postulate(
            &mut metas,
            "Q",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), Term::universe(0)),
        ),
    );
    declared(
        "witness",
        &signature.postulate(
            &mut metas,
            "witness",
            Mult::Many,
            0,
            pi(Mult::Zero, "b", c("Bool"), c("Q").apply([Term::var(0)])),
        ),
    );
}

/// `vcons Bool k x xs`
fn vcons(head: Term, length: Term, tail: Term) -> Term {
    c("vcons").apply([c("Bool"), length, head, tail])
}

/// Вектор булевых значений заданной длины.
fn vector(values: &[&str]) -> Term {
    values
        .iter()
        .rev()
        .zip(0u32..)
        .fold(c("vnil").apply([c("Bool")]), |tail, (value, length)| {
            vcons(c(value), number(length), tail)
        })
}

/// `(0 A : Type 0) -> (0 n : Nat) -> (ω v : Vect A (succ n)) -> <результат>`
fn on_a_nonempty_vector(result: Term) -> Term {
    pi(
        Mult::Zero,
        "A",
        Term::universe(0),
        pi(
            Mult::Zero,
            "n",
            c("Nat"),
            pi(
                Mult::Many,
                "v",
                c("Vect").apply([Term::var(1), c("succ").apply([Term::var(0)])]),
                result,
            ),
        ),
    )
}

/// `head A n (vcons k x xs) = x` - клауза с полями `k`, `x`, `xs`.
fn on_a_cons(body: Term) -> Clause {
    clause(
        vec![
            var("A"),
            var("n"),
            ctor("vcons", vec![var("k"), var("x"), var("xs")]),
        ],
        body,
    )
}

#[test]
fn an_index_that_is_a_variable_is_refined_in_each_branch() {
    // `vlength : (0 A) -> (0 n) -> Vect A n -> Nat`. Индекс - переменная, обе
    // ветви достижимы, и уточнение нужно лишь для того, чтобы в ветви `vcons`
    // сошёлся тип хвоста.
    let mut signature = base();
    with_vectors(&mut signature);
    define(
        &mut signature,
        "vlength",
        pi(
            Mult::Zero,
            "A",
            Term::universe(0),
            pi(
                Mult::Zero,
                "n",
                c("Nat"),
                pi(
                    Mult::Many,
                    "v",
                    c("Vect").apply([Term::var(1), Term::var(0)]),
                    c("Nat"),
                ),
            ),
        ),
        &[
            clause(
                vec![var("A"), var("n"), ctor("vnil", Vec::new())],
                c("zero"),
            ),
            // Переменные клаузы: A, n, k, x, xs - то есть `A` это `#4`,
            // `k` - `#2`, хвост - `#0`.
            on_a_cons(c("succ").apply([c("vlength").apply([
                Term::var(4),
                Term::var(2),
                Term::var(0),
            ])])),
        ],
    );
    assert!(
        signature
            .lookup("vlength")
            .is_some_and(|definition| definition.total),
        "рекурсия по хвосту структурная"
    );

    for length in 0..3u32 {
        let values = vec!["true"; length as usize];
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(length)]),
            &family(c("vlength").apply([c("Bool"), number(length), vector(&values)])),
        );
        assert!(outcome.is_ok(), "длина {length}: {outcome:?}");
    }
}

#[test]
fn an_impossible_branch_is_not_written() {
    // `head` и `tail` над непустым вектором: ветви `vnil` быть не должно, а
    // писать её и нечем - `Vect A zero` не сходится с `Vect A (succ n)`.
    // Ветвь всё равно существует в терме ядра, но мотив отдал ей заведомо
    // обитаемый тип, и населяет его тождество.
    let mut signature = base();
    with_vectors(&mut signature);
    with_bool_family(&mut signature);

    define(
        &mut signature,
        "head",
        on_a_nonempty_vector(Term::var(2)),
        &[on_a_cons(Term::var(1))],
    );
    // Хвост требует и уточнения: тело имеет тип `Vect A k`, а требуется
    // `Vect A n` - сходятся они только потому, что `n` уточнён до `k`.
    define(
        &mut signature,
        "tail",
        on_a_nonempty_vector(c("Vect").apply([Term::var(2), Term::var(1)])),
        &[on_a_cons(Term::var(0))],
    );

    let outcome = check_closed(
        &signature,
        &c("witness").apply([c("false")]),
        &c("Q").apply([c("head").apply([c("Bool"), number(1), vector(&["false", "true"])])]),
    );
    assert!(outcome.is_ok(), "head [false, true] = false: {outcome:?}");

    let outcome = check_closed(
        &signature,
        &c("witness").apply([c("true")]),
        &c("Q").apply([c("head").apply([
            c("Bool"),
            c("zero"),
            c("tail").apply([c("Bool"), number(1), vector(&["false", "true"])]),
        ])]),
    );
    assert!(
        outcome.is_ok(),
        "head (tail [false, true]) = true: {outcome:?}"
    );
}

#[test]
fn a_clause_for_an_impossible_case_is_rejected() {
    // `head A n vnil = ...` - не недостижимая клауза, а невозможная: её нечему
    // перекрывать, она не сработала бы и в одиночестве.
    let mut signature = base();
    with_vectors(&mut signature);
    let outcome = compile(
        &signature,
        &mut Metas::default(),
        &on_a_nonempty_vector(Term::var(2)),
        &[
            on_a_cons(Term::var(1)),
            clause(
                vec![var("A"), var("n"), ctor("vnil", Vec::new())],
                Term::var(1),
            ),
        ],
    );
    assert_eq!(
        outcome.map(|_| ()).unwrap_err().to_string(),
        "клауза #1: `vnil` здесь невозможен - индекс требует `succ`, а конструктор даёт `zero`"
    );
}

#[test]
fn two_vectors_of_one_length_are_matched_together() {
    // Обе ветви второго вектора решаются длиной: разобрав первый, элаборация
    // знает `n`, и у второго остаётся ровно один возможный конструктор. Ради
    // этого случая индексы и заводят.
    let mut signature = base();
    with_vectors(&mut signature);
    let vect = |length: Term| c("Vect").apply([c("Bool"), length]);
    define(
        &mut signature,
        "both",
        pi(
            Mult::Zero,
            "n",
            c("Nat"),
            pi(
                Mult::Many,
                "xs",
                vect(Term::var(0)),
                pi(Mult::Many, "ys", vect(Term::var(1)), c("Nat")),
            ),
        ),
        &[
            clause(
                vec![var("n"), ctor("vnil", Vec::new()), ctor("vnil", Vec::new())],
                c("zero"),
            ),
            // Переменные: n, k, x, xs, j, y, ys - то есть `xs` это `#3`,
            // `ys` - `#0`, а длина хвоста `k` - `#5`.
            clause(
                vec![
                    var("n"),
                    ctor("vcons", vec![var("k"), var("x"), var("xs")]),
                    ctor("vcons", vec![var("j"), var("y"), var("ys")]),
                ],
                c("succ").apply([c("both").apply([Term::var(5), Term::var(3), Term::var(0)])]),
            ),
        ],
    );
    assert!(
        signature
            .lookup("both")
            .is_some_and(|definition| definition.total),
        "рекурсия по хвостам структурная и после уточнения"
    );

    for length in 0..3u32 {
        let values = vec!["true"; length as usize];
        let outcome = check_closed(
            &signature,
            &c("anything").apply([number(length)]),
            &family(c("both").apply([number(length), vector(&values), vector(&values)])),
        );
        assert!(outcome.is_ok(), "длина {length}: {outcome:?}");
    }
}

#[test]
fn an_opaque_index_neither_refines_nor_rejects() {
    // Индекс - застрявшее вычисление: различать по нему нечего, но и отвергать
    // не за что. Мотив по такой позиции постоянен, обе ветви остаются, и терм
    // проходит проверку. Отказ здесь означал бы, что элаборация требует
    // индексов только конструкторной формы, а это отвергало бы программы зря.
    let mut signature = base();
    let mut metas = Metas::default();
    with_vectors(&mut signature);
    declared(
        "len",
        &signature.postulate(&mut metas, "len", Mult::Many, 0, arrow(c("Nat"), c("Nat"))),
    );
    define(
        &mut signature,
        "count",
        pi(
            Mult::Zero,
            "n",
            c("Nat"),
            pi(
                Mult::Many,
                "v",
                c("Vect").apply([c("Bool"), c("len").apply([Term::var(0)])]),
                c("Nat"),
            ),
        ),
        &[
            clause(vec![var("n"), ctor("vnil", Vec::new())], c("zero")),
            clause(
                vec![var("n"), ctor("vcons", vec![var("k"), var("x"), var("xs")])],
                number(1),
            ),
        ],
    );
}

#[test]
fn an_index_that_does_not_reduce_is_reported() {
    // `mk : (k : Nat) -> Foo k` при разборе `Foo (succ n)`: решением было бы
    // `k := succ n`, то есть подстановка в поля ветви, а ветвь - функция от
    // всех своих полей. Это граница фрагмента, и отказ здесь обязан называть
    // причину, а не приходить из ядра ошибкой про чужой терм.
    let mut signature = base();
    let mut metas = Metas::default();
    declared(
        "Foo",
        &signature.declare_data(
            &mut metas,
            "Foo",
            0,
            pi(Mult::Zero, "n", c("Nat"), Term::universe(0)),
            &[(
                "mk",
                pi(Mult::Many, "k", c("Nat"), c("Foo").apply([Term::var(0)])),
            )],
        ),
    );

    // Цель зависит от `n`, поэтому уточнять придётся - и не выйдет.
    let outcome = compile(
        &signature,
        &mut Metas::default(),
        &pi(
            Mult::Zero,
            "n",
            c("Nat"),
            pi(
                Mult::Many,
                "f",
                c("Foo").apply([c("succ").apply([Term::var(0)])]),
                family(Term::var(1)),
            ),
        ),
        &[clause(
            vec![var("n"), ctor("mk", vec![var("k")])],
            c("anything").apply([Term::var(1)]),
        )],
    );
    assert!(
        matches!(outcome, Err(PatternError::StuckIndex { .. })),
        "{outcome:?}"
    );
}

#[test]
fn a_body_reaching_outside_its_variables_is_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &arrow(c("Nat"), c("Nat")),
            // Паттерн связывает одну переменную, тело ссылается на вторую.
            &[clause(vec![var("n")], Term::var(1))],
        ),
        Err(PatternError::UnboundInBody { clause: 0 })
    ));
}

#[test]
fn a_type_reaching_outside_its_arguments_is_rejected() {
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &pi(Mult::Many, "n", c("Nat"), family(Term::var(5))),
            &[clause(vec![var("n")], c("zero"))],
        ),
        Err(PatternError::IllTypedType { ref error })
            if matches!(**error, TypeError::UnboundIndex { .. })
    ));
}

#[test]
fn an_ill_typed_type_is_rejected_before_anything_is_evaluated() {
    // `Nat zero` - не тип, и элаборация обязана сказать это сама: она работает
    // до `check`, а вычисление непроверенного терма - паника, а не отказ.
    let signature = base();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &pi(Mult::Many, "x", c("Nat").apply([c("zero")]), c("Nat")),
            &[clause(vec![ctor("zero", Vec::new())], c("zero"))],
        ),
        Err(PatternError::IllTypedType { ref error })
            if matches!(**error, TypeError::NotAFunction { .. })
    ));
}

#[test]
fn an_unchecked_domain_is_never_evaluated() {
    // Домен замкнут, но не типизирован: замкнутости мало, `eval` роняет процесс
    // на применении не-функции. Регрессия на панику из `compile`.
    let signature = Signature::default();
    assert!(matches!(
        compile(
            &signature,
            &mut Metas::default(),
            &pi(
                Mult::Many,
                "_",
                Term::universe(0).apply([Term::universe(0)]),
                Term::universe(0),
            ),
            &[clause(vec![var("x")], Term::universe(0))],
        ),
        Err(PatternError::IllTypedType { .. })
    ));
}

#[test]
fn a_synonym_is_as_good_a_function_type_as_an_arrow() {
    // `def Fn = Nat -> Bool` - тот же тип функции, что записанная стрелка.
    // Телескоп снимается по значению, иначе арность вышла бы нулевой и клаузы
    // отверглись бы с выдуманным числом аргументов.
    let mut signature = base();
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "Fn",
            Mult::Many,
            0,
            Term::universe(0),
            Some(arrow(c("Nat"), c("Bool"))),
        )
        .expect("Fn корректен");
    define(
        &mut signature,
        "isZero",
        c("Fn"),
        &[
            clause(vec![ctor("zero", Vec::new())], c("true")),
            clause(vec![ctor("succ", vec![var("k")])], c("false")),
        ],
    );
    let outcome = check_closed(&signature, &c("isZero").apply([number(2)]), &c("Bool"));
    assert!(outcome.is_ok(), "{outcome:?}");
}

// ------------------------------------------------------------------ свойства

/// Форма паттерна над `Nat` глубины не больше двух.
///
/// Пять форм покрывают всё, что различает разбор на этой глубине, и три случая
/// входа - `0`, `1`, `>= 2` - полностью определяют, какая из них сработает.
/// Поэтому и полноту, и недостижимость можно посчитать без компилятора.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Form {
    /// `x`
    Any,
    /// `zero`
    Zero,
    /// `succ k`
    Succ,
    /// `succ zero`
    SuccZero,
    /// `succ (succ k)`
    SuccSucc,
}

/// Случаи входа по одному аргументу: `0`, `1`, `>= 2`.
const CASES: usize = 3;

/// Случаи входа по двум аргументам.
const CELLS: usize = CASES * CASES;

impl Form {
    fn covers(self) -> [bool; CASES] {
        match self {
            Self::Any => [true, true, true],
            Self::Zero => [true, false, false],
            Self::Succ => [false, true, true],
            Self::SuccZero => [false, true, false],
            Self::SuccSucc => [false, false, true],
        }
    }

    /// Связывает ли форма переменную.
    fn binds(self) -> bool {
        matches!(self, Self::Any | Self::Succ | Self::SuccSucc)
    }

    /// Сработает ли форма на входе, и что достанется переменной.
    ///
    /// Не связывающая форма отдаёт `0`: тела, которое к нему обратилось бы,
    /// генератор не порождает.
    fn matches(self, input: u32) -> Option<u32> {
        match self {
            Self::Any => Some(input),
            Self::Zero => (input == 0).then_some(0),
            Self::Succ => input.checked_sub(1),
            Self::SuccZero => (input == 1).then_some(0),
            Self::SuccSucc => input.checked_sub(2),
        }
    }

    fn pattern(self) -> Pattern {
        match self {
            Self::Any => var("x"),
            Self::Zero => ctor("zero", Vec::new()),
            Self::Succ => ctor("succ", vec![var("k")]),
            Self::SuccZero => ctor("succ", vec![ctor("zero", Vec::new())]),
            Self::SuccSucc => ctor("succ", vec![ctor("succ", vec![var("k")])]),
        }
    }
}

/// Что клауза возвращает.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Body {
    Zero,
    One,
    /// Переменная, связанная первым паттерном.
    Left,
    /// Переменная, связанная вторым.
    Right,
}

impl Body {
    fn value(self, left: u32, right: u32) -> u32 {
        match self {
            Self::Zero => 0,
            Self::One => 1,
            Self::Left => left,
            Self::Right => right,
        }
    }

    /// Тело в индексах де Брёйна.
    ///
    /// Переменные клаузы нумеруются слева направо, а индекс считает изнутри,
    /// поэтому левая - самая дальняя из связанных, правая - всегда `#0`.
    fn term(self, left: Form, right: Form) -> Term {
        let bound = u32::from(left.binds()) + u32::from(right.binds());
        match self {
            Self::Zero => c("zero"),
            Self::One => number(1),
            Self::Left => Term::var(bound - 1),
            Self::Right => Term::var(0),
        }
    }
}

/// Клауза: форма на каждый из двух аргументов и тело.
type Row = (Form, Form, Body);

fn any_form() -> impl Strategy<Value = Form> {
    prop_oneof![
        Just(Form::Any),
        Just(Form::Zero),
        Just(Form::Succ),
        Just(Form::SuccZero),
        Just(Form::SuccSucc),
    ]
}

fn any_body() -> impl Strategy<Value = Body> {
    prop_oneof![
        Just(Body::Zero),
        Just(Body::One),
        Just(Body::Left),
        Just(Body::Right),
    ]
}

/// Какие пары случаев накрывает клауза.
fn cells((left, right, _): Row) -> [bool; CELLS] {
    let (left, right) = (left.covers(), right.covers());
    let mut cells = [false; CELLS];
    for (index, cell) in cells.iter_mut().enumerate() {
        *cell = left[index / CASES] && right[index % CASES];
    }
    cells
}

fn any_programme() -> impl Strategy<Value = Vec<Row>> {
    proptest::collection::vec((any_form(), any_form(), any_body()), 0..4).prop_map(|rough| {
        // Недостижимые клаузы выбрасываются, а недостающие случаи добираются
        // катч-олом: элаборация обязана принять такой набор, и свойство
        // проверяет именно принятые наборы, а не отказы.
        let mut covered = [false; CELLS];
        let mut programme: Vec<Row> = Vec::new();
        for (left, right, body) in rough {
            let row = (left, right, body);
            if cells(row)
                .iter()
                .zip(&covered)
                .all(|(cell, seen)| !cell || *seen)
            {
                continue;
            }
            for (seen, cell) in covered.iter_mut().zip(cells(row)) {
                *seen |= cell;
            }
            // Тело не вправе называть переменную, которой паттерн не связал.
            let body = match body {
                Body::Left if !left.binds() => Body::Zero,
                Body::Right if !right.binds() => Body::Zero,
                other => other,
            };
            programme.push((left, right, body));
        }
        if !covered.iter().all(|cell| *cell) {
            programme.push((Form::Any, Form::Any, Body::Left));
        }
        programme
    })
}

/// Первое совпадение, посчитанное прямо по клаузам.
fn first_match(programme: &[Row], left: u32, right: u32) -> Option<u32> {
    programme.iter().find_map(|(first, second, body)| {
        let first = first.matches(left)?;
        let second = second.matches(right)?;
        Some(body.value(first, second))
    })
}

fn written(programme: &[Row]) -> Vec<Clause> {
    programme
        .iter()
        .map(|&(left, right, body)| {
            clause(
                vec![left.pattern(), right.pattern()],
                body.term(left, right),
            )
        })
        .collect()
}

fn binary() -> Term {
    arrow(c("Nat"), arrow(c("Nat"), c("Nat")))
}

proptest! {
    /// Собранный терм типизируется.
    ///
    /// Оба шага проверяются отдельно: сборка не должна ни падать, ни
    /// отказывать на полном наборе клауз, а результат - проходить `check`.
    /// Ошибку элаборации ядро поймает и само, но пользователю она достанется
    /// невнятным отказом на терме, которого он не писал.
    #[test]
    fn a_compiled_clause_set_type_checks(programme in any_programme()) {
        let mut signature = base();
        let mut metas = Metas::default();
        let body = compile(&signature, &mut Metas::default(), &binary(), &written(&programme));
        prop_assert!(body.is_ok(), "{programme:?}: {body:?}");
        let outcome = signature.define(&mut metas, "f", Mult::Many, 0, binary(), Some(body.unwrap()));
        prop_assert!(outcome.is_ok(), "{programme:?}: {outcome:?}");
    }

    /// Дерево вычисляет то же, что даёт первое совпадение по клаузам.
    ///
    /// Единственное свойство, которое за элаборацию не проверит `check`: терм
    /// может быть типизирован и при этом выбирать не ту клаузу или связывать
    /// не ту переменную.
    #[test]
    fn the_tree_agrees_with_first_match(programme in any_programme()) {
        let mut signature = base();
        let mut metas = Metas::default();
        let body = compile(&signature, &mut Metas::default(), &binary(), &written(&programme))
            .unwrap_or_else(|error| panic!("{programme:?}: {error}"));
        let outcome = signature.define(&mut metas, "f", Mult::Many, 0, binary(), Some(body));
        prop_assert!(outcome.is_ok(), "{programme:?}: {outcome:?}");

        for left in 0..4 {
            for right in 0..4 {
                let expected = first_match(&programme, left, right)
                    .unwrap_or_else(|| panic!("{programme:?} не покрывает {left} {right}"));
                let outcome = check_closed(
                    &signature,
                    &c("anything").apply([number(expected)]),
                    &family(c("f").apply([number(left), number(right)])),
                );
                prop_assert!(
                    outcome.is_ok(),
                    "{programme:?} на {left} {right} даёт не {expected}: {outcome:?}"
                );
            }
        }
    }
}
