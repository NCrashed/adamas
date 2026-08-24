//! Implicit universe polymorphism: аргументы уровня выводятся, а не пишутся.

use std::rc::Rc;

use adamas_core::check::{TypeError, check_closed_with, infer_closed_with};
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

fn u(index: u32) -> Level {
    Level::Var(LevelVar(index))
}

/// `Id : (0 a : Type u0) -> (ω x : a) -> a` - полиморфная по уровню
/// тождественная функция со стёртым параметром типа.
fn identity_signature() -> Signature {
    let mut signature = Signature::default();
    let outcome = signature.define(
        "Id",
        Mult::Many,
        1,
        pi(
            Mult::Zero,
            "a",
            Term::Universe(u(0)),
            pi(Mult::Many, "x", Term::var(0), Term::var(1)),
        ),
        Some(lam(Mult::Zero, "a", lam(Mult::Many, "x", Term::var(0)))),
    );
    assert!(outcome.is_ok(), "Id корректна: {outcome:?}");
    signature
}

// -------------------------------------------------------------------- вывод

#[test]
fn the_level_argument_is_solved_from_the_expected_type() {
    // Пишем `Id` без уровня и проверяем против типа, в котором уровень
    // определён однозначно. Ровно это §3.2 называет "в пользовательском коде
    // уровни появляются только при явной аннотации".
    let signature = identity_signature();
    let mut metas = Metas::default();

    let identity = signature.instantiate("Id", &mut metas).unwrap();
    let expected = pi(
        Mult::Zero,
        "a",
        Term::universe(2),
        pi(Mult::Many, "x", Term::var(0), Term::var(1)),
    );

    assert!(
        check_closed_with(&signature, &mut metas, &identity, &expected).is_ok(),
        "уровень должен вывестись"
    );
}

#[test]
fn the_solution_is_visible_in_the_inferred_type() {
    // `Id` применена к `Type 1`, значит `?l` обязана стать `2`: аргумент
    // должен жить в `Type ?l`, а `Type 1 : Type 2`.
    let signature = identity_signature();
    let mut metas = Metas::default();

    let applied = signature
        .instantiate("Id", &mut metas)
        .unwrap()
        .apply([Term::universe(1)]);

    assert_eq!(
        infer_closed_with(&signature, &mut metas, &applied)
            .unwrap()
            .to_string(),
        "(ω x : Type 1) -> Type 1"
    );
}

#[test]
fn one_definition_serves_several_levels_without_annotations() {
    // То же самое имя, два места использования, два разных решения.
    let signature = identity_signature();

    for level in 0..3 {
        let mut metas = Metas::default();
        let applied = signature
            .instantiate("Id", &mut metas)
            .unwrap()
            .apply([Term::universe(level)]);
        assert_eq!(
            infer_closed_with(&signature, &mut metas, &applied)
                .unwrap()
                .to_string(),
            format!("(ω x : Type {level}) -> Type {level}")
        );
    }
}

#[test]
fn an_undetermined_level_is_rejected_rather_than_guessed() {
    // `Id` сама по себе не даёт ничего, что определило бы уровень. Угадывать
    // нельзя: любой выбор был бы произвольным, а неверный принял бы
    // некорректную программу.
    let signature = identity_signature();
    let mut metas = Metas::default();
    let identity = signature.instantiate("Id", &mut metas).unwrap();

    let expected = Term::Universe(Level::number(9)); // заведомо не тип `Id`
    assert!(check_closed_with(&signature, &mut metas, &identity, &expected).is_err());
}

#[test]
fn conflicting_uses_of_one_metavariable_are_rejected() {
    // Одна дырка не может быть сразу двумя уровнями.
    let mut signature = Signature::default();
    signature
        .postulate(
            "Pair",
            Mult::Many,
            1,
            pi(
                Mult::Many,
                "x",
                Term::Universe(u(0)),
                Term::Universe(u(0).succ()),
            ),
        )
        .unwrap();

    let mut metas = Metas::default();
    let head = signature.instantiate("Pair", &mut metas).unwrap();

    // Первое применение решает `?l := 1`, дальше тип уже не полиморфен.
    let applied = head.apply([Term::universe(0)]);
    assert!(infer_closed_with(&signature, &mut metas, &applied).is_ok());
    assert!(!metas.is_empty(), "дырка была заведена");
}

// -------------------------------------------------------- неоднозначность

#[test]
fn a_leftover_metavariable_is_an_error_not_a_default() {
    // Постулат, уровень которого не проявляется в типе результата: решить
    // дырку неоткуда, и молча подставить ноль было бы враньём.
    let mut signature = Signature::default();
    signature
        .postulate("Opaque", Mult::Many, 1, Term::universe(1))
        .unwrap();

    let mut metas = Metas::default();
    let term = signature.instantiate("Opaque", &mut metas).unwrap();

    assert!(matches!(
        check_closed_with(&signature, &mut metas, &term, &Term::universe(1)),
        Err(TypeError::AmbiguousLevel { .. })
    ));
}

#[test]
fn definitions_may_not_contain_holes() {
    // Метапеременные живут ровно на время одной проверки: определение хранится
    // в сигнатуре навсегда, и дырка в нём была бы вечной.
    let signature = identity_signature();
    assert_eq!(signature.lookup("Id").unwrap().level_arity, 1);
}

#[test]
fn a_level_shared_by_domain_and_codomain_is_solved() {
    // Уровень такого `Pi` - `max (suc ?l) (suc ?l)`, снаружи `max`, и снимать
    // общие `suc` там нечего. Но это не тот `max`, о котором §10 вопрос 39:
    // решение единственно, и нормализация сводит выражение к `suc ?l`.
    //
    // Форма не редкая - это эндофункция на полиморфном типе, ровно то, ради
    // чего universe polymorphism и нужен.
    let signature = Signature::default();
    let mut metas = Metas::default();
    let level = metas.fresh_level();

    let arrow = pi(
        Mult::Many,
        "x",
        Term::Universe(level.clone()),
        Term::Universe(level.clone()),
    );
    assert!(
        check_closed_with(&signature, &mut metas, &arrow, &Term::universe(4)).is_ok(),
        "уровень должен вывестись"
    );
    assert_eq!(metas.zonk(&level), Level::number(3));
}

#[test]
fn two_distinct_levels_under_max_are_still_ambiguous() {
    // Контроль к предыдущему тесту: нормализация не должна превращать
    // неоднозначное в решаемое. `max ?a ?b ~ 3` имеет много решений.
    let signature = Signature::default();
    let mut metas = Metas::default();
    let arrow = pi(
        Mult::Many,
        "x",
        Term::Universe(metas.fresh_level()),
        Term::Universe(metas.fresh_level()),
    );
    assert!(check_closed_with(&signature, &mut metas, &arrow, &Term::universe(4)).is_err());
}

// ---------------------------------------------------- границы решаемого класса

#[test]
fn a_metavariable_under_max_is_not_solved() {
    // `max ?l u0 ~ …` не имеет единственного решения, и вывод отказывается
    // угадывать. Отказ отвергает корректную программу - это цена, названная
    // в §10 вопросе 39.
    let mut signature = Signature::default();
    signature
        .postulate("Both", Mult::Many, 2, Term::Universe(u(0).max(u(1)).succ()))
        .unwrap();

    let mut metas = Metas::default();
    let term = signature.instantiate("Both", &mut metas).unwrap();

    // Тип `Both{?a, ?b}` - это `Type (max ?a ?b + 1)`. Свести его к `Type 3`
    // означало бы решить `max ?a ?b ~ 2`, что вывод не делает.
    assert!(check_closed_with(&signature, &mut metas, &term, &Term::universe(3)).is_err());
}

#[test]
fn instantiating_an_unknown_name_yields_nothing() {
    let signature = Signature::default();
    let mut metas = Metas::default();
    assert!(signature.instantiate("Missing", &mut metas).is_none());
}

#[test]
fn a_definition_with_a_hole_never_reaches_the_signature() {
    // Определение живёт в сигнатуре дольше, чем хранилище метапеременных, и
    // дырка в нём означала бы тип, зависящий от того, что уже уничтожено:
    // следующая сессия подставила бы своё значение, и постулат оказался бы
    // жителем сразу всех универсумов.
    let mut outer = Metas::default();
    let hole = outer.fresh_level();

    let mut signature = Signature::default();
    assert!(matches!(
        signature.postulate("Weird", Mult::Many, 0, Term::Universe(hole)),
        Err(TypeError::UnsolvedDefinitionLevel { .. })
    ));
    assert!(
        signature.lookup("Weird").is_none(),
        "отвергнутое определение не сохраняется"
    );
}

#[test]
fn a_body_built_by_instantiation_cannot_be_stored_as_is() {
    // `instantiate` - штатный вход implicit UP, и он возвращает терм с
    // дырками. Положить такой терм в сигнатуру нельзя: дырки принадлежат
    // хранилищу вызывающего, а проверка определения заводит своё.
    let mut signature = identity_signature();
    let mut metas = Metas::default();
    let body = signature.instantiate("Id", &mut metas).unwrap();

    let ty = pi(
        Mult::Zero,
        "a",
        Term::Universe(u(0)),
        pi(Mult::Many, "x", Term::var(0), Term::var(1)),
    );
    assert!(
        signature
            .define("MyId", Mult::Many, 1, ty, Some(body))
            .is_err(),
        "терм с чужими дырками не должен приниматься"
    );
}

#[test]
fn a_solved_level_is_shown_solved_in_the_error() {
    // Сообщение об ошибке печатается через обратное чтение, а оно уровни
    // нормализует, но решений не подставляет. Решённая дырка выглядела как
    // `?0`, то есть читалась как «уровень не выведен» — при том что выведен, а
    // разошлись два конкретных уровня.
    let mut signature = Signature::default();
    signature
        .postulate("Box", Mult::Many, 1, Term::Universe(u(0).succ()))
        .expect("Box корректен");
    signature
        .postulate(
            "mk",
            Mult::Many,
            1,
            Term::Const("Box".into(), Rc::from([u(0)])),
        )
        .expect("mk корректен");

    let mut metas = Metas::default();
    let boxed = signature
        .instantiate("Box", &mut metas)
        .expect("Box объявлен");

    // Первая проверка решает дырку в `2`.
    let two = Term::Const("mk".into(), Rc::from([Level::number(2)]));
    check_closed_with(&signature, &mut metas, &two, &boxed).expect("решает ?0 := 2");

    // Вторая расходится с ней, и сообщение обязано назвать решение, а не дырку.
    let three = Term::Const("mk".into(), Rc::from([Level::number(3)]));
    let error = check_closed_with(&signature, &mut metas, &three, &boxed)
        .expect_err("2 и 3 - разные уровни");
    let TypeError::Mismatch { expected, found } = &error else {
        panic!("ожидалось несовпадение типов, получено {error:?}");
    };
    assert!(
        !expected.contains('?') && !found.contains('?'),
        "решённая дырка напечатана как невыведенная: ожидался `{expected}`, получен `{found}`"
    );
    assert!(
        expected.contains('2') && found.contains('3'),
        "сообщение обязано назвать разошедшиеся уровни: `{expected}` против `{found}`"
    );
}

// ------------------------------------------------------------------ свойства

/// Уровень над переменными `u0..u{bound-1}`.
///
/// Левая сторона берётся над четырьмя переменными, из которых `u2` и `u3`
/// становятся дырками; правая - над двумя, то есть заведомо без дырок. Такая
/// асимметрия нужна, чтобы оракул вообще работал: он определён на уровнях без
/// дырок, а при дырках с обеих сторон успешное решение чаще всего оставляет
/// хотя бы одну, и проверять оказывается нечего.
fn any_level_over(bound: u32) -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::Zero),
        (0u32..3).prop_map(Level::number),
        (0..bound).prop_map(|index| Level::Var(LevelVar(index))),
    ];
    leaf.prop_recursive(3, 16, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner).prop_map(|(a, b)| a.max(b)),
        ]
    })
}

/// Все подстановки `u0`, `u1` значениями `0..=bound`.
fn assignments(bound: u32) -> impl Iterator<Item = impl Fn(LevelVar) -> u32> {
    let span = bound + 1;
    (0..span * span).map(move |code| {
        move |LevelVar(index)| match index {
            0 => code % span,
            1 => (code / span) % span,
            _ => 0,
        }
    })
}

fn max_constant(level: &Level) -> u32 {
    match level {
        Level::Zero | Level::Var(_) | Level::Meta(_) => 0,
        Level::Succ(inner) => max_constant(inner) + 1,
        Level::Max(a, b) => max_constant(a).max(max_constant(b)),
    }
}

fn has_holes(level: &Level) -> bool {
    match level {
        Level::Zero | Level::Var(_) => false,
        Level::Meta(_) => true,
        Level::Succ(inner) => has_holes(inner),
        Level::Max(a, b) => has_holes(a) || has_holes(b),
    }
}

/// Превращает `u2` и `u3` в свежие дырки, оставляя `u0` и `u1` параметрами.
///
/// Так в уровне появляются метапеременные в тех же позициях, где их ставит
/// [`Signature::instantiate`], а генератор остаётся чистым.
fn with_holes(metas: &mut Metas, level: &Level) -> Level {
    let substitution = [u(0), u(1), metas.fresh_level(), metas.fresh_level()];
    level.substitute(&substitution)
}

proptest! {
    /// Успешное решение действительно делает уровни равными.
    ///
    /// Проверяется не то, что слот помечен занятым, а то, что после подстановки
    /// решений обе стороны совпадают по значению при любой подстановке
    /// параметров. Оракул определён на уровнях без дырок, поэтому случаи, где
    /// после решения дырки остались, пропускаются - там равенство обеспечено
    /// синтаксически.
    #[test]
    fn a_successful_unification_makes_the_levels_equal(
        a in any_level_over(4),
        b in any_level_over(2),
    ) {
        let mut metas = Metas::default();
        let left = with_holes(&mut metas, &a);
        let right = b.clone();

        if metas.unify_levels(&left, &right) {
            let (left, right) = (metas.zonk(&left), metas.zonk(&right));
            if !has_holes(&left) && !has_holes(&right) {
                let bound = max_constant(&left).max(max_constant(&right)) + 3;
                for assignment in assignments(bound) {
                    prop_assert_eq!(
                        left.evaluate(&assignment),
                        right.evaluate(&assignment),
                        "{} и {} признаны равными, но расходятся", left, right
                    );
                }
            }
        }
    }

    /// Решение не зависит от порядка сторон.
    ///
    /// Правило `?m ~ l` симметрично по построению, и асимметрия означала бы,
    /// что `check` и `infer` расходятся на одном и том же ограничении: первый
    /// сталкивает ожидаемое с полученным, второй наоборот.
    #[test]
    fn unification_does_not_depend_on_the_order_of_sides(
        a in any_level_over(4),
        b in any_level_over(2),
    ) {
        let mut forward = Metas::default();
        let left = with_holes(&mut forward, &a);
        let forward_ok = forward.unify_levels(&left, &b);

        let mut backward = Metas::default();
        let left = with_holes(&mut backward, &a);
        let backward_ok = backward.unify_levels(&b, &left);

        prop_assert_eq!(forward_ok, backward_ok, "{} против {}", left, b);
    }
}
