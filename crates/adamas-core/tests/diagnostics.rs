//! Форма отказа: телескоп точки отказа и маршрут до неё (§10 вопрос 49а).
//!
//! Проверяется не текст сообщения, а два факта: маршрут - **настоящий путь** в
//! проверяемом терме, и телескоп называет связывания, под которые проверка
//! спустилась. Текст - работа рендеринга, живущего вне ядра.
//!
//! Пропуск кадра тих по природе: маршрут просто окажется короче, компилятор об
//! этом не скажет. Поэтому здесь и лежит свойство, обходящее произвольные
//! термы, а не набор примеров.

use std::rc::Rc;

use adamas_core::check::{Binding, ErrorKind, Frame, TypeError, check_closed};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use proptest::prelude::*;

// ------------------------------------------------------------- конструкторы

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(
        Binder::explicit(mult),
        name.into(),
        Rc::new(domain),
        Row::empty(),
        Rc::new(codomain),
    )
}

fn let_(mult: Mult, name: &str, ty: Term, value: Term, body: Term) -> Term {
    Term::Let(
        mult,
        name.into(),
        Rc::new(ty),
        Rc::new(value),
        Rc::new(body),
    )
}

/// Применение, которого не бывает: `Type 0` не функция.
///
/// Отказ гарантирован, форма его известна - `NotAFunction`, - и подставить его
/// можно в любую позицию, чтобы посмотреть, каким маршрутом он выйдет.
fn broken() -> Term {
    Term::universe(0).apply([Term::universe(0)])
}

/// `f : Type 0 -> Type 0` - функция, чтобы у применения был законный аргумент.
fn with_f() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.postulate(
        &mut metas,
        "f",
        Mult::Many,
        0,
        pi(Mult::Many, "_", Term::universe(0), Term::universe(0)),
    );
    assert!(outcome.is_ok(), "`f` объявлена: {outcome:?}");
    signature
}

/// Отказ проверки; успех - провал теста.
fn refused(signature: &Signature, term: &Term, ty: &Term) -> TypeError {
    match check_closed(signature, term, ty) {
        Err(error) => error,
        Ok(()) => panic!("ожидался отказ"),
    }
}

fn path(error: &TypeError) -> Vec<Frame> {
    error.path().collect()
}

// ------------------------------------------------------------------ маршрут

/// Один шаг маршрута по терму. `None` - кадр не ложится на узел.
///
/// Это ровно то соответствие, которое обещает [`Frame`]: кадр называет позицию
/// в узле. Пройти по нему обязан любой читатель ошибки - и элаборация, которой
/// маршрут нужен, чтобы дойти до спана.
#[allow(
    clippy::match_same_arms,
    reason = "каждая пара - отдельное правило соответствия; слить их - потерять таблицу"
)]
fn step(term: &Term, frame: Frame) -> Option<&Term> {
    match (term, frame) {
        (Term::App(callee, _), Frame::Callee) => Some(callee),
        (Term::App(_, argument), Frame::Argument) => Some(argument),
        (Term::Pi(_, _, domain, _, _), Frame::Domain) => Some(domain),
        (Term::Pi(_, _, _, _, codomain), Frame::Codomain) => Some(codomain),
        (Term::Lam(_, _, body), Frame::Body) => Some(body),
        (Term::Let(_, _, ty, _, _), Frame::BindingType) => Some(ty),
        (Term::Let(_, _, _, value, _), Frame::BindingValue) => Some(value),
        (Term::Let(_, _, _, _, body), Frame::BindingBody) => Some(body),
        (Term::Case(case), Frame::Scrutinee) => Some(&case.scrutinee),
        (Term::Case(case), Frame::Motive) => Some(&case.motive),
        (Term::Case(case), Frame::Branch(index)) => case
            .branches
            .get(index as usize)
            .map(|branch| &*branch.body),
        _ => None,
    }
}

/// Куда приводит маршрут целиком. `Err` - кадр, на котором путь оборвался.
fn follow<'a>(term: &'a Term, route: &[Frame]) -> Result<&'a Term, Frame> {
    let mut current = term;
    for frame in route {
        current = step(current, *frame).ok_or(*frame)?;
    }
    Ok(current)
}

/// То же для входа, которому терм и тип даны отдельно: `Stated` в начале
/// маршрута переключает дерево.
fn follow_entry<'a>(term: &'a Term, ty: &'a Term, route: &[Frame]) -> Result<&'a Term, Frame> {
    match route.split_first() {
        Some((Frame::Stated, rest)) => follow(ty, rest),
        _ => follow(term, route),
    }
}

#[test]
fn a_refusal_at_the_root_has_an_empty_route() {
    // Кадр кладёт точка вызова, а не место отказа: `Type 0 Type 0` отвергается
    // тем самым узлом, с которого проверка началась, и класть нечего.
    let error = refused(&Signature::default(), &broken(), &Term::universe(5));
    assert!(matches!(error.kind, ErrorKind::NotAFunction { .. }));
    assert_eq!(path(&error), Vec::new());
}

#[test]
fn nesting_lengthens_the_route_by_one_frame_each_time() {
    let signature = with_f();
    for depth in 0..4_usize {
        let term = (0..depth).fold(broken(), |inner, _| Term::constant("f").apply([inner]));
        let error = refused(&signature, &term, &Term::universe(0));
        assert_eq!(
            path(&error),
            vec![Frame::Argument; depth],
            "глубина {depth}"
        );
        assert!(
            follow(
                &term,
                &error.route().iter().rev().copied().collect::<Vec<_>>()
            )
            .is_ok()
        );
    }
}

#[test]
fn every_position_names_itself() {
    let signature = with_f();
    // Каждая пара - терм с одним заведомо сломанным подтермом и маршрут,
    // которым отказ обязан выйти наружу.
    let cases: Vec<(Term, Vec<Frame>)> = vec![
        (Term::constant("f").apply([broken()]), vec![Frame::Argument]),
        (broken().apply([Term::universe(0)]), vec![Frame::Callee]),
        (
            pi(Mult::Many, "_", broken(), Term::universe(0)),
            vec![Frame::Domain],
        ),
        (
            pi(Mult::Many, "_", Term::universe(0), broken()),
            vec![Frame::Codomain],
        ),
        (lam(Mult::Many, "x", broken()), vec![Frame::Body]),
        (
            let_(
                Mult::Many,
                "a",
                broken(),
                Term::universe(0),
                Term::universe(0),
            ),
            vec![Frame::BindingType],
        ),
        (
            let_(
                Mult::Many,
                "a",
                Term::universe(1),
                broken(),
                Term::universe(0),
            ),
            vec![Frame::BindingValue],
        ),
        (
            let_(
                Mult::Many,
                "a",
                Term::universe(1),
                Term::universe(0),
                broken(),
            ),
            vec![Frame::BindingBody],
        ),
    ];

    for (term, expected) in cases {
        // Лямбда проверяется против `Pi`, остальное - против универсума
        // повыше: тип здесь не проверяемое, а способ дойти до подтерма.
        let ty = match &term {
            Term::Lam(..) => pi(Mult::Many, "x", Term::universe(0), Term::universe(5)),
            _ => Term::universe(5),
        };
        let error = refused(&signature, &term, &ty);
        assert_eq!(path(&error), expected, "{term}");
        assert!(follow(&term, &expected).is_ok(), "{term}");
    }
}

#[test]
fn a_case_names_the_scrutinee_the_motive_and_the_branch() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.declare_data(
        &mut metas,
        "Bool",
        0,
        Term::universe(0),
        &[
            ("true", Term::constant("Bool")),
            ("false", Term::constant("Bool")),
        ],
    );
    assert!(outcome.is_ok(), "`Bool` объявлен: {outcome:?}");

    // Мотив постоянный: разбор возвращает `Type 0` при любом значении.
    let motive = lam(Mult::Zero, "_", Term::universe(1));
    let scrutinee = Term::constant("true");
    let build = |scrutinee: Term, motive: Term, first: Term, second: Term| {
        Term::Case(Rc::new(adamas_core::term::Case {
            data: "Bool".into(),
            levels: Rc::from([] as [Level; 0]),
            params: 0,
            consumed: Mult::One,
            scrutinee: Rc::new(scrutinee),
            motive: Rc::new(motive),
            branches: vec![
                adamas_core::term::Branch {
                    constructor: "true".into(),
                    body: Rc::new(first),
                },
                adamas_core::term::Branch {
                    constructor: "false".into(),
                    body: Rc::new(second),
                },
            ],
        }))
    };

    let cases = [
        (
            build(
                broken(),
                motive.clone(),
                Term::universe(0),
                Term::universe(0),
            ),
            vec![Frame::Scrutinee],
        ),
        (
            build(
                scrutinee.clone(),
                broken(),
                Term::universe(0),
                Term::universe(0),
            ),
            vec![Frame::Motive],
        ),
        (
            build(
                scrutinee.clone(),
                motive.clone(),
                broken(),
                Term::universe(0),
            ),
            vec![Frame::Branch(0)],
        ),
        (
            build(scrutinee, motive, Term::universe(0), broken()),
            vec![Frame::Branch(1)],
        ),
    ];

    for (term, expected) in cases {
        let error = refused(&signature, &term, &Term::universe(2));
        assert!(
            matches!(error.kind, ErrorKind::NotAFunction { .. }),
            "отказ обязан идти от `broken`, а не от заготовки: {error:?}"
        );
        assert_eq!(path(&error), expected, "{term}");
        assert!(follow(&term, &expected).is_ok(), "{term}");
    }
}

#[test]
fn a_group_route_names_the_member_and_the_constructor() {
    // Отказ внутри объявления: второй конструктор возвращает не своё семейство.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.declare_data(
        &mut metas,
        "Bool",
        0,
        Term::universe(0),
        &[
            ("True", Term::constant("Bool")),
            ("False", Term::universe(0)),
        ],
    );
    let error = outcome.expect_err("`False : Type 0` не конструктор `Bool`");
    assert_eq!(
        path(&error),
        vec![Frame::MemberType(0), Frame::Constructor(1)]
    );
}

// ----------------------------------------------------------------- телескоп

#[test]
fn the_telescope_carries_the_binders_the_check_descended_under() {
    // Связывания, которых у вызывающего нет: он их не вводил, `check` ввёл.
    let term = lam(Mult::Zero, "a", lam(Mult::Many, "x", broken()));
    let ty = pi(
        Mult::Zero,
        "a",
        Term::universe(0),
        pi(Mult::Many, "x", Term::var(0), Term::universe(3)),
    );
    let error = refused(&Signature::default(), &term, &ty);

    let names: Vec<&str> = error
        .context()
        .iter()
        .map(|binding| &*binding.name)
        .collect();
    assert_eq!(names, ["a", "x"], "телескоп идёт снаружи внутрь");
    let mults: Vec<Mult> = error
        .context()
        .iter()
        .map(|binding: &Binding| binding.mult)
        .collect();
    assert_eq!(mults, [Mult::Zero, Mult::Many]);
    assert_eq!(
        error.context()[0].ty,
        Term::universe(0),
        "тип связывания прочитан обратно в терм"
    );
}

#[test]
fn a_refusal_without_local_bindings_carries_an_empty_telescope() {
    let error = refused(&Signature::default(), &broken(), &Term::universe(5));
    assert!(error.context().is_empty());
}

// ------------------------------------------------------------------ свойство

/// Произвольный терм: замкнутость не требуется, тип - тоже.
///
/// Почти любой такой терм отвергается, и это ровно то, что нужно: свойство
/// смотрит на форму отказа, а не на то, чем он вызван.
fn any_term(depth: u32) -> BoxedStrategy<Term> {
    let leaf = prop_oneof![
        (0u32..3).prop_map(Term::universe),
        (0u32..3).prop_map(Term::var),
        Just(Term::Const("f".into(), Rc::from([] as [Level; 0]))),
    ];
    leaf.prop_recursive(4, 64, 3, move |inner| {
        let _ = depth;
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(callee, argument)| callee.apply([argument])),
            (any_mult(), inner.clone()).prop_map(|(mult, body)| lam(mult, "x", body)),
            (any_mult(), inner.clone(), inner.clone())
                .prop_map(|(mult, domain, codomain)| pi(mult, "y", domain, codomain)),
            (any_mult(), inner.clone(), inner.clone(), inner)
                .prop_map(|(mult, ty, value, body)| let_(mult, "z", ty, value, body)),
        ]
    })
    .boxed()
}

fn any_mult() -> impl Strategy<Value = Mult> {
    prop_oneof![Just(Mult::Zero), Just(Mult::One), Just(Mult::Many)]
}

proptest! {
    /// Маршрут - настоящий путь в проверяемом терме.
    ///
    /// Свойство ловит то, чего не ловит компилятор: кадр, поставленный не в
    /// той точке вызова, уводит путь в узел, где такой позиции нет. Пропуск
    /// кадра свойство не ловит - на него смотрят примеры выше.
    #[test]
    fn a_route_is_a_path_in_the_term(term in any_term(3), ty in any_term(3)) {
        let signature = with_f();
        if let Err(error) = check_closed(&signature, &term, &ty) {
            let route: Vec<Frame> = error.path().collect();
            prop_assert!(
                follow_entry(&term, &ty, &route).is_ok(),
                "маршрут {route:?} оборвался в `{term}` : `{ty}`"
            );
        }
    }

    /// Телескоп не длиннее, чем маршрут мог увести под связывания.
    ///
    /// Каждое связывание в контексте введено каким-то кадром маршрута, а
    /// кадров, вводящих связывание, не больше, чем кадров всего.
    #[test]
    fn the_telescope_fits_the_route(term in any_term(3), ty in any_term(3)) {
        let signature = with_f();
        if let Err(error) = check_closed(&signature, &term, &ty) {
            prop_assert!(
                error.context().len() <= error.route().len(),
                "телескоп {} длиннее маршрута {}",
                error.context().len(),
                error.route().len()
            );
        }
    }
}
