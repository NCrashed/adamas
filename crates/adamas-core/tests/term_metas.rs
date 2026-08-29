//! Метапеременные терма и их решение (§4.1, §9 Фаза 3).
//!
//! Проверяется не форма решения, а то, **что оно означает**: после решения
//! дырка конвертируема с тем, чем её решили, и неконвертируема с тем, чем не
//! решали. Форма - деталь, и тест на неё ломался бы от смены стратегии
//! абстракции, ничего при этом не защищая.
//!
//! Элаборация дырок ещё не заводит - срез ядерный, - поэтому строятся они
//! здесь руками, ровно как это будет делать вставка имплиситов.

use std::rc::Rc;

use adamas_core::check::ErrorKind;
use adamas_core::conv::convertible;
use adamas_core::eval::{eval, normalize, quote};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use adamas_core::value::{Env, Lvl, Value};

/// Окружение из `free` свободных переменных - контекст, в котором живёт дырка.
fn env(free: u32) -> Env {
    (0..free).fold(Env::default(), |env, level| {
        env.extend(Value::var(Lvl(level)))
    })
}

/// Сходятся ли термы при `free` свободных переменных, решая дырки по дороге.
fn unify(metas: &mut Metas, free: u32, left: &Term, right: &Term) -> bool {
    let signature = Signature::default();
    let env = env(free);
    convertible(
        &signature,
        metas,
        free,
        &eval(&env, left),
        &eval(&env, right),
    )
}

/// Тип дырки. Проверка типов здесь не идёт, поэтому годится любой замкнутый.
fn any_type() -> Rc<Value> {
    Rc::new(Value::Universe(adamas_core::level::Level::Zero))
}

#[test]
fn a_hole_takes_the_shape_it_is_compared_with() {
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    assert!(unify(&mut metas, 0, &hole, &Term::universe(3)));
    // Решение наблюдается тем же способом, каким его увидит проверка типов:
    // дырка стала конвертируема с тем, чем её решили, и только с ним.
    assert!(unify(&mut metas, 0, &hole, &Term::universe(3)));
    assert!(!unify(&mut metas, 0, &hole, &Term::universe(4)));
}

#[test]
fn a_hole_is_solved_once_and_keeps_its_solution() {
    // Backtracking'а в проверке нет, поэтому первое решение окончательно:
    // второе ограничение либо совпадает с ним, либо это отказ.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    let pair = |left, right| {
        Term::Pi(
            Binder::explicit(Mult::Many),
            "_".into(),
            Rc::new(left),
            Row::empty(),
            Rc::new(right),
        )
    };
    assert!(unify(
        &mut metas,
        0,
        &pair(hole.clone(), hole.clone()),
        &pair(Term::universe(1), Term::universe(1))
    ));
    assert!(!unify(
        &mut metas,
        0,
        &pair(hole.clone(), hole),
        &pair(Term::universe(1), Term::universe(2))
    ));
}

#[test]
fn a_hole_in_a_context_is_solved_by_a_function_of_it() {
    // Дырка, заведённая под двумя связываниями, приходит применённой к ним:
    // `?m x₀ x₁`. Решением становится функция, и выбирает она то связывание,
    // против которого дырку сравнили.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 2);
    // `#0` - ближайшее связывание, то есть уровень 1.
    assert!(unify(&mut metas, 2, &hole, &Term::var(0)));

    let mut other = Metas::default();
    let hole = other.fresh_term(any_type(), 2);
    assert!(unify(&mut other, 2, &hole, &Term::var(1)));

    // Решения разные, и различие видно снаружи: одна и та же запись `?m x₀ x₁`
    // после решения означает разные переменные.
    let mut compare = Metas::default();
    let left = compare.fresh_term(any_type(), 2);
    let right = compare.fresh_term(any_type(), 2);
    assert!(unify(&mut compare, 2, &left, &Term::var(0)));
    assert!(unify(&mut compare, 2, &right, &Term::var(1)));
    assert!(!unify(&mut compare, 2, &left, &right));
}

#[test]
fn a_solution_may_not_mention_what_the_hole_cannot_see() {
    // Дырка заведена в пустом контексте, а сравнивают её под связыванием:
    // решением была бы переменная, свободная в замкнутом терме.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    assert!(
        !unify(&mut metas, 1, &hole, &Term::var(0)),
        "переменная вне спайна - побег из области видимости"
    );
}

#[test]
fn a_hole_does_not_solve_itself() {
    // `?m ≡ (\x -> x) ?m` после вычисления есть `?m ≡ ?m` - решать нечего, и
    // это не отказ, а совпадение.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    assert!(unify(&mut metas, 0, &hole, &hole.clone()));

    // А вот `?m ≡ Pi ?m ?m` решения не имеет: подстановка дала бы бесконечный
    // терм, и проверка вхождения обязана это поймать.
    let mut other = Metas::default();
    let hole = other.fresh_term(any_type(), 0);
    let cyclic = Term::Pi(
        Binder::explicit(Mult::Many),
        "_".into(),
        Rc::new(hole.clone()),
        Row::empty(),
        Rc::new(Term::universe(0)),
    );
    assert!(
        !unify(&mut other, 0, &hole, &cyclic),
        "дырка в собственном решении - бесконечный терм"
    );
}

#[test]
fn a_solved_hole_computes() {
    // Решение - обычное значение, поэтому дырка под применением сводится:
    // `(?m) Type 0` после решения `?m := \x -> x` даёт `Type 0`.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    let identity = Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)));
    assert!(unify(&mut metas, 0, &hole, &identity));

    let applied = Term::App(Rc::new(hole), Rc::new(Term::universe(0)));
    let value = eval(&Env::default(), &applied);
    let forced = adamas_core::solve::force(&metas, &value).expect("дырка решена");
    assert_eq!(
        quote(0, &forced).to_string(),
        normalize(&Term::universe(0)).to_string()
    );
}

#[test]
fn a_spine_that_is_not_a_pattern_is_refused() {
    // Вне паттернового фрагмента решение не единственно, и угадывать нельзя.
    // `?m (f x) ≡ …` - спайн не переменная; `?m x x ≡ …` - переменная
    // повторена, и какое из двух связываний имелось в виду, не определено.
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    let applied = Term::App(
        Rc::new(hole),
        Rc::new(Term::constant("f").apply([Term::var(0)])),
    );
    assert!(!unify(&mut metas, 1, &applied, &Term::var(0)));

    let mut other = Metas::default();
    let hole = other.fresh_term(any_type(), 0);
    let repeated = Term::App(
        Rc::new(Term::App(Rc::new(hole), Rc::new(Term::var(0)))),
        Rc::new(Term::var(0)),
    );
    assert!(!unify(&mut other, 1, &repeated, &Term::var(0)));
}

#[test]
fn an_unsolved_hole_does_not_reach_the_signature() {
    // Дырка, дожившая до объявления, означала бы определение, зависящее от
    // хранилища, которого уже нет. Обобщать её, в отличие от уровневой,
    // нечем: аргумент терма выводится в месте использования.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    let outcome = signature.postulate(&mut metas, "f", Mult::Many, 0, hole);
    assert!(
        matches!(
            outcome,
            Err(ref error) if matches!(error.kind, ErrorKind::AmbiguousTerm { .. })
        ),
        "получено {outcome:?}"
    );
}

#[test]
fn a_solved_hole_reaches_the_signature_as_its_solution() {
    // Решённая подставляется на границе объявления - тем же способом, что и
    // уровневая: хранилище живёт прогон, а определение всю программу.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let hole = metas.fresh_term(any_type(), 0);
    assert!(unify(&mut metas, 0, &hole, &Term::universe(0)));
    let outcome = signature.postulate(&mut metas, "f", Mult::Many, 0, hole);
    assert!(outcome.is_ok(), "{outcome:?}");
    assert_eq!(
        signature.lookup("f").expect("объявлено").ty.to_string(),
        "Type 0",
        "в сигнатуре стоит решение, а не дырка"
    );
}
