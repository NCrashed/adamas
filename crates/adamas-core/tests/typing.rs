//! Проверка типов и учёт кратностей.
//!
//! Термы ядра пишутся руками, поэтому здесь есть маленький конструктор -
//! иначе тесты читались бы как перечень `Rc::new`. Поверхностного синтаксиса
//! нет до Фазы 2.

use std::rc::Rc;

use adamas_core::check::{TypeError, infer};
use adamas_core::ctx::{Ctx, Usage};
use adamas_core::eval::normalize;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

// ------------------------------------------------------------- конструкторы

/// Обёртки над проверяющим: сигнатура одна на весь файл, см. ниже.
fn infer_closed(term: &Term) -> Result<Term, TypeError> {
    adamas_core::check::infer_closed(&fixture_signature(), term)
}

fn check_closed(term: &Term, ty: &Term) -> Result<(), TypeError> {
    adamas_core::check::check_closed(&fixture_signature(), term, ty)
}

/// Сигнатура для свойств: по одному определению каждого вида, которые
/// проверяющий обязан различать.
///
/// Свойства ниже гоняют произвольные термы, и без непустой сигнатуры
/// `Term::Const` в них не попадал бы вовсе - то есть целая конструкция ядра
/// оставалась бы вне обстрела.
fn fixture_signature() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let add = |outcome: Result<(), TypeError>| assert!(outcome.is_ok(), "{outcome:?}");
    // Определение с телом: разворачивается.
    add(signature.define(
        &mut metas,
        "alias",
        Mult::Many,
        0,
        Term::universe(1),
        Some(ty0()),
    ));
    // Постулат: застревает навсегда.
    add(signature.postulate(&mut metas, "opaque", Mult::Many, 0, Term::universe(1)));
    // Стёртое определение: в рантайм-позиции обязано отвергаться.
    add(signature.define(
        &mut metas,
        "erased",
        Mult::Zero,
        0,
        Term::universe(1),
        Some(ty0()),
    ));
    signature
}

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
}

fn let_in(mult: Mult, name: &str, ty: Term, value: Term, body: Term) -> Term {
    Term::Let(
        mult,
        name.into(),
        Rc::new(ty),
        Rc::new(value),
        Rc::new(body),
    )
}

fn ty0() -> Term {
    Term::universe(0)
}

/// В сигнатурах **этого файла** `Type 0` необитаем: индуктивных типов здесь
/// нет, а замкнутый терм этого типа больше построить не из чего - `Pi` живёт в
/// `max` уровней своих частей, и опуститься до нуля неоткуда. Поэтому там, где
/// нужен обитаемый тип, берётся `Type 1`, а его жителем служит `Type 0`.
///
/// Про язык в целом это неверно: data-декларация населяет `Type 0`, см.
/// `inductive.rs`.
fn ty1() -> Term {
    Term::universe(1)
}

// ------------------------------------------------------------------ базовое

#[test]
fn universes_are_predicative_and_not_cumulative() {
    assert_eq!(infer_closed(&ty0()).unwrap().to_string(), "Type 1");
    assert!(check_closed(&ty0(), &Term::universe(1)).is_ok());
    // Без кумулятивности (§10 вопрос 1) `Type 0` не житель `Type 2`.
    assert!(matches!(
        check_closed(&ty0(), &Term::universe(2)),
        Err(TypeError::Mismatch { .. })
    ));
}

#[test]
fn function_type_lands_in_the_maximum_of_its_parts() {
    // (ω x : Type 0) -> Type 0 : Type 1
    let arrow = pi(Mult::Many, "x", ty0(), ty0());
    assert_eq!(infer_closed(&arrow).unwrap().to_string(), "Type 1");

    // Предикативность: квантификация по Type 0 поднимает результат, а не
    // оставляет его в Type 0.
    let quantified = pi(Mult::Zero, "a", ty0(), Term::var(0));
    assert_eq!(infer_closed(&quantified).unwrap().to_string(), "Type 1");
}

#[test]
fn identity_checks_against_its_type() {
    let identity = lam(Mult::Many, "x", Term::var(0));
    assert!(check_closed(&identity, &pi(Mult::Many, "x", ty0(), ty0())).is_ok());
}

#[test]
fn lambda_cannot_be_inferred_without_an_annotation() {
    let identity = lam(Mult::Many, "x", Term::var(0));
    assert!(matches!(
        infer_closed(&identity),
        Err(TypeError::CannotInfer { .. })
    ));
}

#[test]
fn applying_a_non_function_is_rejected() {
    let term = ty0().apply([ty0()]);
    assert!(matches!(
        infer_closed(&term),
        Err(TypeError::NotAFunction { .. })
    ));
}

#[test]
fn argument_type_is_checked() {
    // (\(ω x : Type 0) -> x) (Type 1) - аргумент живёт этажом выше.
    let applied = let_in(
        Mult::Many,
        "f",
        pi(Mult::Many, "x", ty0(), ty0()),
        lam(Mult::Many, "x", Term::var(0)),
        Term::var(0).apply([Term::universe(1)]),
    );
    assert!(matches!(
        infer_closed(&applied),
        Err(TypeError::Mismatch { .. })
    ));
}

// -------------------------------------------------------------- зависимость

#[test]
fn erased_type_parameter_is_the_flagship_case() {
    // \(0 a) -> \(ω x) -> x  :  (0 a : Type 0) -> (ω x : a) -> a
    //
    // Полиморфная тождественная функция, у которой параметр типа стёрт: в
    // рантайме от неё остаётся `\x -> x` (§3.3).
    let term = lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)));
    let ty = pi(
        Mult::Zero,
        "a",
        ty0(),
        pi(Mult::Many, "x", Term::var(0), Term::var(1)),
    );
    assert!(
        check_closed(&term, &ty).is_ok(),
        "{:?}",
        check_closed(&term, &ty)
    );
}

#[test]
fn dependent_application_substitutes_the_argument_into_the_result_type() {
    // f : (0 a : Type 1) -> (ω x : a) -> a, применённая к Type 0,
    // должна дать (ω x : Type 0) -> Type 0.
    let term = let_in(
        Mult::Many,
        "f",
        pi(
            Mult::Zero,
            "a",
            ty1(),
            pi(Mult::Many, "x", Term::var(0), Term::var(1)),
        ),
        lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0))),
        Term::var(0).apply([ty0()]),
    );
    assert_eq!(
        infer_closed(&term).unwrap().to_string(),
        "(ω x : Type 0) -> Type 0"
    );
}

// --------------------------------------------------------------- кратности

#[test]
fn linear_variable_used_once_is_accepted() {
    let term = lam(Mult::One, "x", Term::var(0));
    assert!(check_closed(&term, &pi(Mult::One, "x", ty0(), ty0())).is_ok());
}

#[test]
fn linear_variable_left_unused_is_accepted_because_one_is_affine() {
    // §3.3: кратность 1 - "не более одного раза". Без этого handler, не
    // вызывающий `resume`, не типизировался бы.
    let term = lam(Mult::One, "x", lam(Mult::Many, "y", Term::var(0)));
    let ty = pi(Mult::One, "x", ty0(), pi(Mult::Many, "y", ty0(), ty0()));
    assert!(check_closed(&term, &ty).is_ok());
}

#[test]
fn linear_variable_used_twice_is_rejected() {
    // \(1 x) -> f x x, где f принимает два неограниченных аргумента.
    let f_ty = pi(Mult::Many, "a", ty0(), pi(Mult::Many, "b", ty0(), ty0()));
    let term = let_in(
        Mult::Many,
        "f",
        f_ty,
        lam(Mult::Many, "a", lam(Mult::Many, "b", Term::var(1))),
        lam(
            Mult::One,
            "x",
            Term::var(1).apply([Term::var(0), Term::var(0)]),
        ),
    );
    let ty = pi(Mult::One, "x", ty0(), ty0());

    match check_closed(&term, &ty) {
        Err(TypeError::UsageViolation {
            name,
            declared,
            actual,
        }) => {
            assert_eq!(&*name, "x");
            assert_eq!(declared, Mult::One);
            assert_eq!(actual, Mult::Many);
        }
        other => panic!("ожидалось нарушение кратности, получено {other:?}"),
    }
}

/// Счёт использований проверяется по числу вхождений, а не одним примером.
///
/// `\(q x) -> g x … x` с `n` вхождениями: принимается тогда и только тогда,
/// когда `q` допускает `n`. Отдельные примеры выше фиксируют по одной точке,
/// а здесь связь между объявленной кратностью и фактическим счётом проверяется
/// как таковая - включая границу между "одно вхождение" и "два".
#[test]
fn usage_is_counted_by_occurrences() {
    for uses in 0..4usize {
        // g принимает `uses` линейных аргументов типа Type 0 и возвращает
        // Type 0, то есть сама живёт в Type 1. Аргументы именно линейные:
        // под неограниченным связыванием каждое вхождение стоило бы ω, и
        // счёт вхождений перестал бы быть виден.
        let g_ty = (0..uses).fold(ty1(), |acc, _| pi(Mult::One, "a", ty0(), acc));
        let g_value = (0..uses).fold(ty0(), |acc, _| lam(Mult::One, "a", acc));
        let calls = Term::var(1).apply(std::iter::repeat_n(Term::var(0), uses));

        for declared in [Mult::Zero, Mult::One, Mult::Many] {
            let term = let_in(
                Mult::Many,
                "g",
                g_ty.clone(),
                g_value.clone(),
                lam(declared, "x", calls.clone()),
            );
            let ty = pi(declared, "x", ty0(), ty1());

            let actual = match uses {
                0 => Mult::Zero,
                1 => Mult::One,
                _ => Mult::Many,
            };
            let accepted = check_closed(&term, &ty).is_ok();
            assert_eq!(
                accepted,
                declared.admits(actual),
                "кратность {declared}, вхождений {uses}"
            );
        }
    }
}

#[test]
fn erased_variable_used_at_runtime_is_rejected() {
    // \(0 a) -> \(ω x) -> a - `a` стёрта, а возвращается как значение.
    let term = lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(1)));
    let ty = pi(Mult::Zero, "a", ty0(), pi(Mult::Many, "x", ty0(), ty0()));

    match check_closed(&term, &ty) {
        Err(TypeError::UsageViolation {
            name,
            declared,
            actual,
        }) => {
            assert_eq!(&*name, "a");
            assert_eq!(declared, Mult::Zero);
            assert_eq!(actual, Mult::One);
        }
        other => panic!("ожидалось нарушение кратности, получено {other:?}"),
    }
}

#[test]
fn erased_variable_used_inside_a_type_is_fine() {
    // Та же `a`, но теперь она встречается только в типе `x`. Типы живут в
    // стёртом фрагменте, поэтому расхода нет - иначе стирание было бы
    // бесполезно.
    let term = lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)));
    let ty = pi(
        Mult::Zero,
        "a",
        ty0(),
        pi(Mult::Many, "x", Term::var(0), Term::var(1)),
    );
    assert!(check_closed(&term, &ty).is_ok());
}

#[test]
fn erased_argument_does_not_consume_a_linear_variable() {
    // f : (0 a : Type 0) -> Type 1, вызванная как f x при линейной x.
    // Аргумент проверяется при кратности 0 · 1 = 0, значит x не потрачена и
    // остаётся доступной.
    let term = let_in(
        Mult::Many,
        "f",
        pi(Mult::Zero, "a", ty0(), ty1()),
        lam(Mult::Zero, "a", ty0()),
        lam(Mult::One, "x", Term::var(1).apply([Term::var(0)])),
    );
    let ty = pi(Mult::One, "x", ty0(), ty1());
    assert!(check_closed(&term, &ty).is_ok());
}

#[test]
fn unrestricted_argument_does_consume_it() {
    // Тот же терм, но связывание неограниченное: 1 · ω = ω, и линейная
    // переменная оказывается потрачена ω раз.
    let term = let_in(
        Mult::Many,
        "f",
        pi(Mult::Many, "a", ty0(), ty1()),
        lam(Mult::Many, "a", ty0()),
        lam(Mult::One, "x", Term::var(1).apply([Term::var(0)])),
    );
    let ty = pi(Mult::One, "x", ty0(), ty1());
    assert!(matches!(
        check_closed(&term, &ty),
        Err(TypeError::UsageViolation { .. })
    ));
}

#[test]
fn lambda_multiplicity_must_match_its_type() {
    let term = lam(Mult::Many, "x", Term::var(0));
    let ty = pi(Mult::One, "x", ty0(), ty0());
    assert!(matches!(
        check_closed(&term, &ty),
        Err(TypeError::LambdaMultiplicity {
            expected: Mult::One,
            found: Mult::Many
        })
    ));
}

#[test]
fn a_linear_binding_is_checked_wherever_the_lambda_stands() {
    // Тип `(1 x : A) -> A` не населяется нелинейной функцией - ни на верхнем
    // уровне, ни в позиции аргумента.
    //
    // Раньше населялся: кратность суждения умножалась на кратность связывания,
    // а параметр обычной функции имеет кратность `ω` (§4.1), и `1 · ω = ω`
    // разрешало `spend` любое использование. Проверка линейности выключалась
    // для всего, что стояло под ω-аргументом, то есть почти везде.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "A", Mult::Many, 0, Term::universe(0))
        .expect("A корректен");
    signature
        .postulate(
            &mut metas,
            "pair",
            Mult::Many,
            0,
            pi(
                Mult::Many,
                "_",
                Term::constant("A"),
                pi(Mult::Many, "_", Term::constant("A"), Term::constant("A")),
            ),
        )
        .expect("pair корректна");
    let linear = pi(Mult::One, "x", Term::constant("A"), Term::constant("A"));
    signature
        .postulate(
            &mut metas,
            "higher",
            Mult::Many,
            0,
            pi(Mult::Many, "h", linear.clone(), Term::constant("A")),
        )
        .expect("higher корректна");

    // `\(1 x) -> pair x x` - `x` потрачен дважды при кратности 1.
    let nonlinear = lam(
        Mult::One,
        "x",
        Term::constant("pair").apply([Term::var(0), Term::var(0)]),
    );

    assert!(
        matches!(
            adamas_core::check::check_closed(&signature, &nonlinear, &linear),
            Err(TypeError::UsageViolation { .. })
        ),
        "напрямую"
    );
    assert!(
        matches!(
            adamas_core::check::check_closed(
                &signature,
                &Term::constant("higher").apply([nonlinear]),
                &Term::constant("A"),
            ),
            Err(TypeError::UsageViolation { .. })
        ),
        "в позиции ω-аргумента - тот же терм и тот же отказ"
    );
}

// --------------------------------------------------------------------- let

#[test]
fn let_binding_is_transparent_to_the_type_checker() {
    // Тип тела знает значение связывания, а не только его тип: иначе
    // `Term::var(0)` не свернулась бы в `Type 0`.
    let term = let_in(Mult::Many, "a", Term::universe(1), ty0(), Term::var(0));
    assert_eq!(infer_closed(&term).unwrap().to_string(), "Type 1");
}

#[test]
fn erased_let_cannot_be_used_at_runtime() {
    let term = let_in(Mult::Zero, "a", Term::universe(1), ty0(), Term::var(0));
    assert!(matches!(
        infer_closed(&term),
        Err(TypeError::UsageViolation { .. })
    ));
}

#[test]
fn let_annotation_is_checked_against_the_value() {
    let term = let_in(Mult::Many, "a", ty0(), Term::universe(1), Term::var(0));
    assert!(matches!(
        infer_closed(&term),
        Err(TypeError::Mismatch { .. })
    ));
}

// ----------------------------------------------------------- некорректность

#[test]
fn open_terms_are_rejected_rather_than_panicking() {
    assert!(matches!(
        infer_closed(&Term::var(0)),
        Err(TypeError::UnboundIndex { .. })
    ));
}

#[test]
fn a_non_type_in_type_position_is_rejected() {
    // Домен `Pi` обязан быть типом, а `\x -> x` им не является.
    let term = pi(Mult::Many, "x", lam(Mult::Many, "y", Term::var(0)), ty0());
    assert!(matches!(
        infer_closed(&term),
        Err(TypeError::CannotInfer { .. })
    ));
}

// ------------------------------------------------------------------ свойства

fn any_mult() -> impl Strategy<Value = Mult> {
    prop_oneof![Just(Mult::Zero), Just(Mult::One), Just(Mult::Many)]
}

/// Произвольный терм - в том числе незамкнутый, нетипизируемый и с редексами.
///
/// Расходимости здесь взяться неоткуда: чтобы что-то вычислить, проверяющий
/// сначала обязан это типизировать, а ядро без рекурсии сильно нормализуемо.
/// Нетипизируемое до вычисления просто не доходит.
fn any_small_term() -> BoxedStrategy<Term> {
    let leaf = prop_oneof![
        (0u32..4).prop_map(Term::var),
        (0u32..3).prop_map(Term::universe),
        // Имена из fixture_signature плюс заведомо отсутствующее: проверяющий
        // обязан ровно отвергать и его тоже.
        proptest::sample::select(vec!["alias", "opaque", "erased", "missing"])
            .prop_map(Term::constant),
    ];
    leaf.prop_recursive(3, 24, 4, |inner| {
        prop_oneof![
            (any_mult(), inner.clone()).prop_map(|(mult, body)| Term::Lam(
                mult,
                "x".into(),
                Rc::new(body)
            )),
            (inner.clone(), inner.clone())
                .prop_map(|(callee, arg)| Term::App(Rc::new(callee), Rc::new(arg))),
            (any_mult(), inner.clone(), inner.clone()).prop_map(|(mult, domain, codomain)| {
                Term::Pi(mult, "x".into(), Rc::new(domain), Rc::new(codomain))
            }),
            (any_mult(), inner.clone(), inner.clone(), inner).prop_map(
                |(mult, ty, value, body)| {
                    Term::Let(mult, "x".into(), Rc::new(ty), Rc::new(value), Rc::new(body))
                }
            ),
        ]
    })
    .boxed()
}

proptest! {
    /// Проверяющий либо типизирует терм, либо отвергает его. Паника - только
    /// на нарушении внутреннего инварианта, а произвольный терм на входе
    /// инвариантов не нарушает.
    #[test]
    fn checking_arbitrary_terms_never_panics(term in any_small_term()) {
        let _ = infer_closed(&term);
    }

    /// Subject reduction: вычисление не меняет тип.
    ///
    /// Свойство условное - большинство порождённых термов не типизируется
    /// вовсе, и тогда проверять нечего.
    #[test]
    fn normalization_preserves_the_inferred_type(term in any_small_term()) {
        if let Ok(before) = infer_closed(&term) {
            let after = infer_closed(&normalize(&term))
                .expect("нормализованный терм обязан остаться типизируемым");
            prop_assert_eq!(before, after);
        }
    }

    /// Синтезированный тип сам является типом.
    #[test]
    fn inferred_types_are_types(term in any_small_term()) {
        if let Ok(ty) = infer_closed(&term) {
            prop_assert!(
                infer_closed(&ty).is_ok(),
                "тип `{}` не типизируется",
                ty
            );
        }
    }

    /// В стёртом фрагменте не расходуется ничего.
    ///
    /// На этом инварианте держится `is_type`: он проверяет терм при `σ = 0` и
    /// отбрасывает вектор использований, не глядя. Если бы вектор мог оказаться
    /// ненулевым, расход внутри типа терялся бы молча.
    #[test]
    fn the_erased_fragment_consumes_nothing(term in any_small_term()) {
        let signature = fixture_signature();
        let ctx = Ctx::new(&signature);
        if let Ok((_, usage)) = infer(&ctx, &mut Metas::default(), Mult::Zero, &term) {
            prop_assert_eq!(usage, Usage::zero(ctx.size()), "терм: {}", term);
        }
    }

    /// Что типизируется в рантайме, типизируется и стёртым.
    ///
    /// Обратное неверно: стёртый фрагмент допускает то, что рантайм отвергает,
    /// - на этом и стоит стирание.
    #[test]
    fn typable_at_runtime_implies_typable_erased(term in any_small_term()) {
        let signature = fixture_signature();
        let ctx = Ctx::new(&signature);
        if infer(&ctx, &mut Metas::default(), Mult::One, &term).is_ok() {
            prop_assert!(infer(&ctx, &mut Metas::default(), Mult::Zero, &term).is_ok(), "терм: {}", term);
        }
    }
}
