//! Рекурсивные определения и проверка структурной рекурсии (§4.7, §9 Фаза 1).
//!
//! Здесь впервые появляются функции, которые что-то вычисляют: до рекурсии
//! `case` умел разбирать, но не сворачивать. Отсюда же и цена - ядро само по
//! себе перестало гарантировать завершаемость, и держат её два правила,
//! проверяемые ниже: нетотальное определение не разворачивается и не
//! допускается в стёртый фрагмент.
//!
//! Вычисление проверяется через **семейство** `P : (0 n : Nat) -> Type 0`:
//! `anything 5` принадлежит `P (plus 2 3)` тогда и только тогда, когда
//! `plus 2 3` конвертируем с `5`. Прямее не получится - `eval` определений не
//! разворачивает, сводит их только проверка конвертируемости.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, TypeError, check_closed};
use adamas_core::eval::normalize;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Branch, Case, Term};
use proptest::prelude::*;

// -------------------------------------------------------------- конструкторы

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(
        mult,
        name.into(),
        Rc::new(domain),
        Row::empty(),
        Rc::new(codomain),
    )
}

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn arrow(domain: Term, codomain: Term) -> Term {
    pi(Mult::Many, "_", domain, codomain)
}

fn c(name: &str) -> Term {
    Term::constant(name)
}

/// Разбор непараметризованного типа.
fn case(data: &str, scrutinee: Term, motive: Term, branches: Vec<(&str, Term)>) -> Term {
    Term::Case(Rc::new(Case {
        data: data.into(),
        levels: Rc::from([]),
        params: 0,
        // Разбор здесь линеен: `q · 1 = q`, то есть кратности полей приходят в
        // ветвь такими, какими объявлены, и тесты про рекурсию не смешиваются
        // с масштабированием (§3.3).
        consumed: Mult::One,
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

/// Постоянный мотив.
fn constantly(result: Term) -> Term {
    lam(Mult::Zero, "_", result)
}

/// Натуральное число как терм.
fn number(value: u32) -> Term {
    (0..value).fold(c("zero"), |term, _| c("succ").apply([term]))
}

/// `P n` - тип, различающий числа. Свидетель принадлежности - `anything n`.
fn family(index: Term) -> Term {
    c("P").apply([index])
}

// -------------------------------------------------------------- заготовки

fn declared(what: &str, outcome: &Result<(), TypeError>) {
    assert!(outcome.is_ok(), "{what} корректен: {outcome:?}");
}

/// `Nat`, семейство `P` над ним и свидетель `anything`.
fn base() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
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

/// `plus n m = case n of {zero => m; succ k => succ (plus k m)}`.
fn arithmetic() -> Signature {
    let mut signature = base();
    let mut metas = Metas::default();
    let body = lam(
        Mult::Many,
        "n",
        lam(
            Mult::Many,
            "m",
            case(
                "Nat",
                Term::var(1),
                constantly(c("Nat")),
                vec![
                    ("zero", Term::var(0)),
                    (
                        "succ",
                        lam(
                            Mult::Many,
                            "k",
                            c("succ").apply([c("plus").apply([Term::var(0), Term::var(1)])]),
                        ),
                    ),
                ],
            ),
        ),
    );
    declared(
        "plus",
        &signature.define(
            &mut metas,
            "plus",
            Mult::Many,
            0,
            arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
            Some(body),
        ),
    );
    signature
}

/// Определяет одноаргументную функцию над `Nat` и возвращает её вердикт.
fn define_unary(signature: &mut Signature, name: &str, body: Term) -> bool {
    let mut metas = Metas::default();
    let outcome = signature.define(
        &mut metas,
        name,
        Mult::Many,
        0,
        arrow(c("Nat"), c("Nat")),
        Some(body),
    );
    assert!(outcome.is_ok(), "`{name}` типизируется: {outcome:?}");
    verdict(signature, name)
}

/// Вердикт тотальности уже определённого имени.
fn verdict(signature: &Signature, name: &str) -> bool {
    signature
        .lookup(name)
        .unwrap_or_else(|| panic!("`{name}` определено"))
        .total
}

// ------------------------------------------------------------------ рекурсия

#[test]
fn a_structurally_recursive_definition_computes() {
    let signature = arithmetic();
    assert!(
        verdict(&signature, "plus"),
        "рекурсия по первому аргументу структурная"
    );

    for (left, right, sum) in [(0, 0, 0), (2, 3, 5), (4, 1, 5), (3, 0, 3)] {
        let witness = c("anything").apply([number(sum)]);
        let outcome = check_closed(
            &signature,
            &witness,
            &family(c("plus").apply([number(left), number(right)])),
        );
        assert!(outcome.is_ok(), "{left}+{right} = {sum}: {outcome:?}");
    }

    let witness = c("anything").apply([number(5)]);
    assert!(
        matches!(
            check_closed(
                &signature,
                &witness,
                &family(c("plus").apply([number(2), number(2)])),
            ),
            Err(TypeError {
                kind: ErrorKind::Mismatch { .. },
                ..
            })
        ),
        "и различает числа, а не сводит всё ко всему"
    );
}

#[test]
fn a_recursive_definition_stays_stuck_under_evaluation() {
    // `eval` определений не разворачивает вовсе, поэтому нормальная форма
    // вызова - он сам. Сводит его конвертируемость, и только она.
    let signature = arithmetic();
    let applied = c("plus").apply([number(1), number(1)]);
    assert_eq!(normalize(&applied), applied);
    let outcome = check_closed(&signature, &applied, &c("Nat"));
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_definition_sees_itself_only_in_its_body() {
    let mut signature = base();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.define(&mut metas, "Loop", Mult::Many, 0, c("Loop"), None),
            Err(TypeError {
                kind: ErrorKind::UnknownConstant { .. },
                ..
            })
        ),
        "тип проверяется без собственного имени"
    );
    assert!(!define_unary(
        &mut signature,
        "Loop",
        lam(Mult::Many, "n", c("Loop").apply([Term::var(0)]))
    ));
}

#[test]
fn the_decreasing_position_is_found_by_search() {
    // Рекурсия по **второму** аргументу: объявлять позицию, как `{struct n}` в
    // Coq, не требуется.
    let mut signature = base();
    let mut metas = Metas::default();
    let body = lam(
        Mult::Many,
        "acc",
        lam(
            Mult::Many,
            "n",
            case(
                "Nat",
                Term::var(0),
                constantly(c("Nat")),
                vec![
                    ("zero", Term::var(1)),
                    (
                        "succ",
                        lam(
                            Mult::Many,
                            "k",
                            c("count").apply([c("succ").apply([Term::var(2)]), Term::var(0)]),
                        ),
                    ),
                ],
            ),
        ),
    );
    let outcome = signature.define(
        &mut metas,
        "count",
        Mult::Many,
        0,
        arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
        Some(body),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(verdict(&signature, "count"));
}

#[test]
fn a_field_of_a_field_is_smaller_too() {
    // Разбор разбора: `k` меньше `n`, `j` меньше `k`, значит и меньше `n`.
    let mut signature = base();
    let inner = case(
        "Nat",
        Term::var(0),
        constantly(c("Nat")),
        vec![
            ("zero", c("zero")),
            (
                "succ",
                lam(Mult::Many, "j", c("half").apply([Term::var(0)])),
            ),
        ],
    );
    let body = lam(
        Mult::Many,
        "n",
        case(
            "Nat",
            Term::var(0),
            constantly(c("Nat")),
            vec![("zero", c("zero")), ("succ", lam(Mult::Many, "k", inner))],
        ),
    );
    assert!(define_unary(&mut signature, "half", body));
}

/// Разбор, применённый к соседнему аргументу: ветвь связывает лямбдой не
/// только поля.
///
/// `g n m = (case n return (\(0 _) -> Nat -> Nat) of
///             { zero   => \m'. zero
///             ; succ k => \k. \m'. case m' of {zero => zero; succ j => g n j} }) m`
///
/// Так элаборация клауз уточняет тип соседа (convoy, §10 вопрос 44), и
/// уменьшается здесь **только** второй аргумент - тот, что прошёл через лямбду
/// сверх полей.
fn convoyed(recursive: Term) -> Term {
    let convoy = case(
        "Nat",
        Term::var(1),
        constantly(arrow(c("Nat"), c("Nat"))),
        vec![
            ("zero", lam(Mult::Many, "m", c("zero"))),
            (
                "succ",
                lam(Mult::Many, "k", lam(Mult::Many, "m", recursive)),
            ),
        ],
    );
    lam(
        Mult::Many,
        "n",
        lam(Mult::Many, "m", convoy.apply([Term::var(0)])),
    )
}

/// Определяет двухаргументную функцию над `Nat` и возвращает её вердикт.
fn define_binary(signature: &mut Signature, name: &str, body: Term) -> bool {
    let mut metas = Metas::default();
    let outcome = signature.define(
        &mut metas,
        name,
        Mult::Many,
        0,
        arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
        Some(body),
    );
    assert!(outcome.is_ok(), "`{name}` типизируется: {outcome:?}");
    verdict(signature, name)
}

#[test]
fn an_argument_carried_through_a_convoy_keeps_its_size() {
    // Внутри ветви разбирается уже переданный аргумент, и его поле обязано
    // считаться меньшим - иначе convoy делал бы нетотальным всякое
    // определение, рекурсия которого идёт по уточнённому аргументу.
    let mut signature = base();
    let inner = case(
        "Nat",
        Term::var(0),
        constantly(c("Nat")),
        vec![
            ("zero", c("zero")),
            (
                "succ",
                lam(Mult::Many, "j", c("g").apply([Term::var(4), Term::var(0)])),
            ),
        ],
    );
    assert!(define_binary(&mut signature, "g", convoyed(inner)));
}

#[test]
fn a_convoy_does_not_invent_a_decrease() {
    // Обратная сторона: сам по себе перенос через лямбду ничего не уменьшает.
    // `g n m = g n m` в той же форме обязано остаться нетотальным.
    let mut signature = base();
    let recursive = c("g").apply([Term::var(3), Term::var(0)]);
    assert!(!define_binary(&mut signature, "g", convoyed(recursive)));
}

#[test]
fn several_calls_must_share_one_decreasing_position() {
    // Оба вызова уменьшаются по одному и тому же полю.
    let mut signature = base();
    let mut metas = Metas::default();
    let body = lam(
        Mult::Many,
        "n",
        case(
            "Nat",
            Term::var(0),
            constantly(c("Nat")),
            vec![
                ("zero", c("zero")),
                (
                    "succ",
                    lam(
                        Mult::Many,
                        "k",
                        c("succ").apply([c("plus").apply([
                            c("twice").apply([Term::var(0)]),
                            c("twice").apply([Term::var(0)]),
                        ])]),
                    ),
                ),
            ],
        ),
    );
    let mut signature = {
        let body = lam(Mult::Many, "n", lam(Mult::Many, "m", Term::var(1)));
        declared(
            "plus",
            &signature.define(
                &mut metas,
                "plus",
                Mult::Many,
                0,
                arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
                Some(body),
            ),
        );
        signature
    };
    assert!(define_unary(&mut signature, "twice", body));
}

// -------------------------------------------------------------- нетотальность

#[test]
fn a_call_on_the_parameter_itself_does_not_decrease() {
    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "loop",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));
}

#[test]
fn a_call_on_a_rebuilt_argument_does_not_decrease() {
    // `grow n = grow (succ n)` - аргумент растёт.
    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "grow",
        lam(
            Mult::Many,
            "n",
            c("grow").apply([c("succ").apply([Term::var(0)])])
        )
    ));
}

#[test]
fn a_bare_self_reference_does_not_decrease() {
    // Имя без аргументов - вызов без единой позиции, по которой можно было бы
    // уменьшаться.
    let mut signature = base();
    let mut metas = Metas::default();
    let outcome = signature.define(
        &mut metas,
        "Same",
        Mult::Many,
        0,
        arrow(c("Nat"), c("Nat")),
        Some(c("Same")),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(!verdict(&signature, "Same"));
}

#[test]
fn calls_decreasing_at_different_positions_are_rejected() {
    // Известное ограничение: лексикографический порядок не покрыт. Один вызов
    // убывает по первому аргументу, другой по второму, общей позиции нет.
    let mut signature = base();
    let mut metas = Metas::default();
    let by_second = lam(
        Mult::Many,
        "j",
        c("ack").apply([Term::var(2), Term::var(0)]),
    );
    let by_first = lam(
        Mult::Many,
        "k",
        case(
            "Nat",
            Term::var(1),
            constantly(c("Nat")),
            vec![
                ("zero", c("ack").apply([Term::var(0), c("zero")])),
                ("succ", by_second),
            ],
        ),
    );
    let body = lam(
        Mult::Many,
        "n",
        lam(
            Mult::Many,
            "m",
            case(
                "Nat",
                Term::var(1),
                constantly(c("Nat")),
                vec![("zero", Term::var(0)), ("succ", by_first)],
            ),
        ),
    );
    let outcome = signature.define(
        &mut metas,
        "ack",
        Mult::Many,
        0,
        arrow(c("Nat"), arrow(c("Nat"), c("Nat"))),
        Some(body),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(!verdict(&signature, "ack"));
}

#[test]
fn totality_propagates_through_the_call_graph() {
    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "loop",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));
    // Рекурсии нет вовсе, но вызывается нетотальное - значит нетотально и само.
    assert!(!define_unary(
        &mut signature,
        "caller",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));
    assert!(define_unary(
        &mut signature,
        "honest",
        lam(Mult::Many, "n", c("succ").apply([Term::var(0)]))
    ));
}

// ------------------------------------------- следствия для стёртого фрагмента

#[test]
fn a_partial_definition_is_barred_from_types() {
    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "loop",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));

    // В рантайме - можно.
    let outcome = check_closed(&signature, &c("loop").apply([c("zero")]), &c("Nat"));
    assert!(outcome.is_ok(), "{outcome:?}");

    // В типе - нельзя: тип проверяется при σ = 0.
    assert!(
        matches!(
            check_closed(
                &signature,
                &c("anything").apply([c("zero")]),
                &family(c("loop").apply([c("zero")])),
            ),
            Err(TypeError {
                kind: ErrorKind::PartialConstant { .. },
                ..
            })
        ),
        "нетотальная функция в типе"
    );
}

#[test]
fn a_partial_definition_is_barred_from_erased_arguments() {
    // Аргумент `0`-связывания - тот же стёртый фрагмент, что и тип.
    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "loop",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));
    assert!(
        matches!(
            check_closed(
                &signature,
                &c("anything").apply([c("loop").apply([c("zero")])]),
                &family(c("loop").apply([c("zero")])),
            ),
            Err(TypeError {
                kind: ErrorKind::PartialConstant { .. },
                ..
            })
        ),
        "стёртый аргумент нетотальной функцией не заполнить"
    );
}

/// Граница запрета, зафиксированная тестом: через `let` нетотальное значение в
/// тип всё-таки попадает.
///
/// Значение `let` проверяется при `q · σ`, а не при нулевой кратности, поэтому
/// `loop zero` там законно; дальше оно уходит в окружение, и выведенный тип
/// тела его подхватывает. Расходимости это не даёт - разворачивать `loop`
/// по-прежнему некому, - но обещание §4.7 "нетотальная функция не участвует в
/// доказательствах" здесь не выполняется. См. §10.
#[test]
fn a_partial_value_still_reaches_a_type_through_let() {
    use adamas_core::check::infer_closed;

    let mut signature = base();
    assert!(!define_unary(
        &mut signature,
        "loop",
        lam(Mult::Many, "n", c("loop").apply([Term::var(0)]))
    ));

    let leaked = Term::Let(
        Mult::Many,
        "x".into(),
        Rc::new(c("Nat")),
        Rc::new(c("loop").apply([c("zero")])),
        Rc::new(c("anything").apply([Term::var(0)])),
    );
    let inferred = infer_closed(&signature, &leaked);
    assert_eq!(
        inferred.map(|ty| ty.to_string()),
        Ok("P (loop zero)".to_string()),
        "известная дыра, а не проверка желаемого поведения"
    );
}

#[test]
fn a_total_definition_still_unfolds() {
    // Обратная сторона запрета: тотальное определение δ по-прежнему
    // разворачивает, иначе проверка типов потеряла бы всё вычисление.
    let mut signature = base();
    assert!(define_unary(
        &mut signature,
        "identity",
        lam(Mult::Many, "n", Term::var(0))
    ));
    let outcome = check_closed(
        &signature,
        &c("anything").apply([c("zero")]),
        &family(c("identity").apply([c("zero")])),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

// -------------------------------------------------------- предел развёртки

/// `name n = case n of {zero => Bool; succ k => name k}` - тотальная функция,
/// вычисляющая тип.
///
/// Две такие функции с разными именами конвертируемы на всяком **замкнутом**
/// аргументе, но на свободной переменной ι не срабатывает, и сравнение
/// разворачивает их без дна.
fn define_recursive_family(signature: &mut Signature, name: &str) {
    let mut metas = Metas::default();
    let body = lam(
        Mult::Many,
        "n",
        case(
            "Nat",
            Term::var(0),
            constantly(Term::universe(0)),
            vec![
                ("zero", c("Nat")),
                ("succ", lam(Mult::Many, "k", c(name).apply([Term::var(0)]))),
            ],
        ),
    );
    let outcome = signature.define(
        &mut metas,
        name,
        Mult::Many,
        0,
        arrow(c("Nat"), Term::universe(0)),
        Some(body),
    );
    declared(name, &outcome);
    assert!(verdict(signature, name), "`{name}` тотальна");
}

#[test]
fn comparing_two_recursive_families_refuses_instead_of_diverging() {
    // Обе тотальны, обе разворачиваются, и на свободной переменной разворот
    // не заканчивается сам: `F x` против `G x` даёт застрявшие `case`, спуск
    // в ветви даёт `F k` против `G k`, и так далее. Тотальность здесь не
    // помогает - она про замкнутые аргументы. Останавливает предел развёртки,
    // и остановка обязана быть отказом, а не переполнением стека.
    let mut signature = base();
    define_recursive_family(&mut signature, "F");
    define_recursive_family(&mut signature, "G");

    let coercion = pi(
        Mult::Zero,
        "x",
        c("Nat"),
        pi(
            Mult::Many,
            "w",
            c("F").apply([Term::var(0)]),
            c("G").apply([Term::var(1)]),
        ),
    );
    let identity = lam(Mult::Zero, "x", lam(Mult::Many, "w", Term::var(0)));

    assert!(
        matches!(
            check_closed(&signature, &identity, &coercion),
            Err(TypeError {
                kind: ErrorKind::Mismatch { .. },
                ..
            })
        ),
        "сравнение обязано закончиться отказом"
    );
}

#[test]
fn unfolding_still_reaches_far_enough_to_be_useful() {
    // Обратная сторона предела: он не должен резать обычную арифметику в
    // типах. `F n` на замкнутом `n` стоит ровно `n` разворотов.
    let mut signature = base();
    define_recursive_family(&mut signature, "F");

    let identity = lam(Mult::Many, "w", Term::var(0));
    for length in [1u32, 16, 100] {
        let coercion = arrow(c("F").apply([number(length)]), c("Nat"));
        let outcome = check_closed(&signature, &identity, &coercion);
        assert!(outcome.is_ok(), "глубина {length}: {outcome:?}");
    }
}

// ------------------------------------------------------------------ свойства

/// На чём рекурсивный вызов делается в ветви `succ k`.
#[derive(Clone, Debug)]
enum Recursion {
    /// `f k` - поле разбора, строго меньше аргумента.
    OnTheField,
    /// `f (succ k)` - обратно исходный размер.
    OnTheRebuiltValue,
    /// `f n` - сам аргумент, без убывания.
    OnTheArgument,
    /// Рекурсии нет вовсе.
    None,
}

fn any_recursion() -> impl Strategy<Value = Recursion> {
    prop_oneof![
        Just(Recursion::OnTheField),
        Just(Recursion::OnTheRebuiltValue),
        Just(Recursion::OnTheArgument),
        Just(Recursion::None),
    ]
}

/// `name n = case n of {zero => zero; succ k => <вызов>}`.
///
/// Индексы внутри ветви: `#0` - поле `k`, `#1` - аргумент `n`.
fn unary_body(name: &str, recursion: &Recursion) -> Term {
    let branch = match recursion {
        Recursion::OnTheField => c(name).apply([Term::var(0)]),
        Recursion::OnTheRebuiltValue => c(name).apply([c("succ").apply([Term::var(0)])]),
        Recursion::OnTheArgument => c(name).apply([Term::var(1)]),
        Recursion::None => Term::var(0),
    };
    lam(
        Mult::Many,
        "n",
        case(
            "Nat",
            Term::var(0),
            constantly(c("Nat")),
            vec![("zero", c("zero")), ("succ", lam(Mult::Many, "k", branch))],
        ),
    )
}

proptest! {
    /// Тотальным признаётся ровно вызов по полю разбора.
    ///
    /// Отдельные тесты выше фиксируют по одной форме; свойство проверяет, что
    /// принимается **только** убывание - `f (succ k)` и `f n` возвращают
    /// исходный размер или больше, и оба обязаны быть отвергнуты.
    #[test]
    fn only_a_call_on_a_field_counts_as_decreasing(recursion in any_recursion()) {
        let mut signature = base();
        let total = define_unary(&mut signature, "f", unary_body("f", &recursion));

        let expected = matches!(recursion, Recursion::OnTheField | Recursion::None);
        prop_assert_eq!(total, expected, "форма: {:?}", recursion);
    }

    /// Тотальность распространяется по графу вызовов через любое число звеньев.
    ///
    /// `g` зовёт `f`, `h` зовёт `g`: нетотальность `f` обязана дойти до `h`.
    /// Проверка смотрит только на непосредственно вызванные имена, и держится
    /// это на том, что каждое уже несёт свой вердикт - свойство и проверяет,
    /// что перенос действительно транзитивен.
    #[test]
    fn partiality_propagates_along_the_call_graph(recursion in any_recursion()) {
        let mut signature = base();
        let base_total = define_unary(&mut signature, "f", unary_body("f", &recursion));

        // g n = f n, h n = g n - никакой собственной рекурсии.
        let forward = |callee: &str| lam(Mult::Many, "n", c(callee).apply([Term::var(0)]));
        let g_total = define_unary(&mut signature, "g", forward("f"));
        let h_total = define_unary(&mut signature, "h", forward("g"));

        prop_assert_eq!(g_total, base_total, "через одно звено");
        prop_assert_eq!(h_total, base_total, "через два звена");
    }
}
