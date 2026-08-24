//! Проверка конвертируемости - definitional equality ядра.
//!
//! Сравниваются значения, а не термы: вычисление уже сделало β-редукцию и
//! развернуло `let`, так что здесь остаётся сопоставление форм плюс η.
//!
//! Кумулятивности нет: `Type 0` и `Type 1` неконвертируемы (§10 вопрос 1).
//!
//! # δ-редукция откладывается до последнего
//!
//! Определения приходят сюда неразвёрнутыми ([`crate::eval`] их не трогает).
//! Сначала сравнение как есть: совпали голова и аргументы уровня - достаточно
//! сверить спайны. Только если не сошлось, определение разворачивается и
//! сравнение повторяется.
//!
//! Неудача быстрого пути **не** означает неравенство: `f a` и `f b` равны,
//! если `f` игнорирует аргумент. Поэтому откат к развороту обязателен, а не
//! факультативен.
//!
//! # Разворот ограничен по глубине
//!
//! Нетотальное определение не разворачивается вовсе - иначе разворот заведомо
//! мог бы не закончиться. Но одной тотальности мало: она гарантирует
//! завершаемость вычисления на **замкнутых** аргументах, а сравниваются
//! значения с открытыми, где ι не срабатывает никогда. Две разные тотальные
//! рекурсивные функции над свободной переменной разворачиваются бесконечно -
//! `F x` против `G x` даёт два застрявших `case`, спуск в ветви даёт `F k`
//! против `G k`, и так без дна.
//!
//! Поэтому число разворотов ограничено [`UNFOLD_LIMIT`]. Исчерпание даёт
//! `false`, то есть отказ, а не зависание: направление безопасное - неполнота
//! отвергает корректную программу, тогда как обратная ошибка приняла бы
//! некорректную. Так же устроены пределы в Coq, Agda и Lean; на тотальность
//! здесь положиться нельзя ни в одной из них.

use std::rc::Rc;

use crate::eval::{apply, eliminate_case};
use crate::meta::Metas;
use crate::sig::Signature;
use crate::value::{Elim, Head, Lvl, StuckCase, Value};

/// Конвертируемы ли два значения в контексте размера `size`.
///
/// Осмысленный вопрос - только про значения одного типа, и проверяющий других
/// не задаёт. Но функция тотальна и на разнотипных: возвращает `false`, а не
/// паникует. Паника здесь была бы не защитой инварианта, а падением на входе,
/// который ничего не нарушает.
///
/// Функция **не чистая**: сравнивая `Type ?l` с `Type 3`, она обязана решить
/// `?l := 3`. Это архитектура, а не недосмотр - вывод уровней происходит
/// именно там, где встречаются два типа. Решения не откатываются, поэтому
/// неудачное сравнение может оставить решённые по дороге метапеременные; для
/// проверки типов это безвредно, потому что неудача всё равно означает отказ.
pub fn convertible(
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    let mut fuel = UNFOLD_LIMIT;
    convertible_within(&mut fuel, sig, metas, size, left, right)
}

/// Сколько δ-разворотов разрешено на одно сравнение.
///
/// Снизу граница задана тем, что должно проходить: разворот `F n` на числе `n`
/// стоит `n` шагов, поэтому предел определяет, до каких чисел арифметика
/// сводится в типах.
///
/// Сверху - стеком: разворот рекурсивен, и предел обязан срабатывать раньше
/// переполнения, иначе он ничего не спасает. Замер на потоке с 2 МБ (столько у
/// тестовых) даёт срыв между 320 и 384 разворотами в debug и между 2400 и 2600
/// в release - кадры debug-сборки на порядок толще, и связывает именно она,
/// потому что тесты и CI гоняются в ней. Предел взят с запасом от меньшего.
const UNFOLD_LIMIT: u32 = 128;

fn convertible_within(
    fuel: &mut u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    if rigid(fuel, sig, metas, size, left, right) {
        return true;
    }
    // Быстрый путь не сошёлся - разворачиваем то, что разворачивается.
    let (unfolded_left, unfolded_right) = (unfold(sig, left), unfold(sig, right));
    if unfolded_left.is_none() && unfolded_right.is_none() {
        return false;
    }
    let Some(remaining) = fuel.checked_sub(1) else {
        return false;
    };
    *fuel = remaining;
    convertible_within(
        fuel,
        sig,
        metas,
        size,
        unfolded_left.as_ref().unwrap_or(left),
        unfolded_right.as_ref().unwrap_or(right),
    )
}

/// Разворачивает определение в голове значения вместе со спайном.
///
/// `None`, если голова - локальная переменная или постулат: разворачивать
/// нечего.
///
/// Спайн переигрывается целиком, включая разбор: развернув `two` в
/// `succ (succ zero)`, застрявший над ним `case` немедленно сводится по ι.
/// Единственное место, где это происходит, - здесь, потому что [`crate::eval`]
/// определений не трогает.
pub(crate) fn unfold(sig: &Signature, value: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(Head::Global(name, levels), spine) = &**value else {
        return None;
    };
    let definition = sig.lookup(name)?;
    // Нетотальное определение не разворачивается никогда: у него разворот мог
    // бы не закончиться уже на замкнутых аргументах. По §4.7 в типах его и не
    // встретишь - там стёртый фрагмент, - так что запрет ничего не стоит.
    //
    // Завершаемость сравнения он при этом **не** даёт: на открытых аргументах
    // расходятся и тотальные определения. За это отвечает `UNFOLD_LIMIT`.
    if !definition.total {
        return None;
    }
    let body = definition.instantiate_body(levels)?;
    Some(spine.iter().fold(body, |callee, elim| match elim {
        Elim::App(argument) => apply(&callee, Rc::clone(argument)),
        Elim::Case(case) => eliminate_case(case, &callee),
    }))
}

/// Совпадают ли головы застрявших вычислений.
///
/// У определения аргументы уровня не сравниваются структурно, а
/// **унифицируются**: в них стоят метапеременные, и `Id{?l}` против `Id{2}` -
/// это не расхождение, а ограничение `?l ~ 2`. Структурное сравнение здесь
/// отвергло бы корректную программу, а у постулата - окончательно, потому что
/// разворачивать нечего.
fn same_head(metas: &mut Metas, left: &Head, right: &Head) -> bool {
    match (left, right) {
        (Head::Local(a), Head::Local(b)) => a == b,
        (Head::Global(name_a, levels_a), Head::Global(name_b, levels_b)) => {
            name_a == name_b
                && levels_a.len() == levels_b.len()
                && levels_a
                    .iter()
                    .zip(levels_b.iter())
                    .all(|(a, b)| metas.unify_levels(a, b))
        }
        _ => false,
    }
}

/// Совпадают ли элиминаторы в одной позиции спайна.
fn same_elim(
    fuel: &mut u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Elim,
    right: &Elim,
) -> bool {
    match (left, right) {
        (Elim::App(a), Elim::App(b)) => convertible_within(fuel, sig, metas, size, a, b),
        (Elim::Case(a), Elim::Case(b)) => same_case(fuel, sig, metas, size, a, b),
        _ => false,
    }
}

/// Совпадают ли два застрявших разбора.
///
/// Мотивы сравниваются, хотя на результат они не влияют: разбор застрял, а
/// значит ни одна ветвь не выбрана, и при любом значении скрутинируемого два
/// разбора с одинаковыми ветвями дадут одно и то же. Сравнение здесь
/// **консервативно** - оно может отвергнуть конвертируемые термы. Отбросить
/// мотив нельзя: он часть терма и виден в типе результата, и признав такие
/// термы равными, конвертируемость перестала бы сохранять типизацию.
fn same_case(
    fuel: &mut u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<StuckCase>,
    right: &Rc<StuckCase>,
) -> bool {
    left.data == right.data
        && left.params == right.params
        && left.levels.len() == right.levels.len()
        && left
            .levels
            .iter()
            .zip(right.levels.iter())
            .all(|(a, b)| metas.unify_levels(a, b))
        && convertible_within(fuel, sig, metas, size, &left.motive, &right.motive)
        && left.branches.len() == right.branches.len()
        && left.branches.iter().zip(&right.branches).all(|(a, b)| {
            a.constructor == b.constructor
                && convertible_within(fuel, sig, metas, size, &a.body, &b.body)
        })
}

/// Сравнение без разворота определений.
fn rigid(
    fuel: &mut u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    match (&**left, &**right) {
        (Value::Universe(a), Value::Universe(b)) => metas.unify_levels(a, b),

        (Value::Neutral(head_a, spine_a), Value::Neutral(head_b, spine_b)) => {
            same_head(metas, head_a, head_b)
                && spine_a.len() == spine_b.len()
                && spine_a
                    .iter()
                    .zip(spine_b)
                    .all(|(a, b)| same_elim(fuel, sig, metas, size, a, b))
        }

        // Кратность - часть типа функции, поэтому здесь она значима:
        // `(1 x : A) -> B` и `(ω x : A) -> B` - разные типы.
        (
            Value::Pi(mult_a, _, domain_a, codomain_a),
            Value::Pi(mult_b, _, domain_b, codomain_b),
        ) => {
            mult_a == mult_b
                && convertible_within(fuel, sig, metas, size, domain_a, domain_b)
                && convertible_under(
                    fuel,
                    sig,
                    metas,
                    size,
                    |v| codomain_a.apply(v),
                    |v| codomain_b.apply(v),
                )
        }

        // Кратность лямбды не сравнивается - иначе ломается транзитивность,
        // см. `comparing_lambda_multiplicities_would_break_transitivity`.
        (Value::Lam(_, _, body_a), Value::Lam(_, _, body_b)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| body_a.apply(v),
            |v| body_b.apply(v),
        ),

        // η: функция равна своему развёрнутому виду `\x -> f x`. Без этого
        // правила `f` и `\x -> f x` были бы разными термами.
        //
        // Разворачивается только против застрявшего значения. Против `Pi` или
        // `Universe` лямбда неконвертируема в любом случае, а применить их
        // нельзя - попытка была бы обращением к `apply` с не-функцией.
        (Value::Lam(_, _, body), Value::Neutral(..)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| body.apply(v),
            |v| apply(right, v),
        ),
        (Value::Neutral(..), Value::Lam(_, _, body)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| apply(left, v),
            |v| body.apply(v),
        ),

        _ => false,
    }
}

/// Сравнивает под свежим связыванием.
fn convertible_under(
    fuel: &mut u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: impl FnOnce(Rc<Value>) -> Rc<Value>,
    right: impl FnOnce(Rc<Value>) -> Rc<Value>,
) -> bool {
    let fresh = Value::var(Lvl(size));
    convertible_within(
        fuel,
        sig,
        metas,
        size + 1,
        &left(Rc::clone(&fresh)),
        &right(fresh),
    )
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::convertible;
    use crate::eval::eval;
    use crate::mult::Mult;
    use crate::term::Term;
    use crate::value::{Env, Lvl, Value};

    fn lam(body: Term) -> Term {
        Term::Lam(Mult::Many, "x".into(), Rc::new(body))
    }

    fn pi(mult: Mult, domain: Term, codomain: Term) -> Term {
        Term::Pi(mult, "x".into(), Rc::new(domain), Rc::new(codomain))
    }

    /// Вычисляет оба терма в контексте с `free` свободными переменными.
    fn conv_in(free: u32, left: &Term, right: &Term) -> bool {
        let env = (0..free).fold(Env::default(), |env, level| {
            env.extend(Value::var(Lvl(level)))
        });
        let signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        convertible(
            &signature,
            &mut metas,
            free,
            &eval(&env, left),
            &eval(&env, right),
        )
    }

    fn conv(left: &Term, right: &Term) -> bool {
        conv_in(0, left, right)
    }

    #[test]
    fn beta_equal_terms_are_convertible() {
        let reduced = Term::universe(0);
        let redex = lam(Term::var(0)).apply([Term::universe(0)]);
        assert!(conv(&redex, &reduced));
    }

    #[test]
    fn names_do_not_matter() {
        let x = Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)));
        let y = Term::Lam(Mult::Many, "y".into(), Rc::new(Term::var(0)));
        assert!(conv(&x, &y));
    }

    #[test]
    fn eta_expansion_is_invisible() {
        // f  ==  \x -> f x, где f свободна.
        let f = Term::var(0);
        let expanded = lam(Term::var(1).apply([Term::var(0)]));
        assert!(conv_in(1, &f, &expanded));
        assert!(conv_in(1, &expanded, &f), "и в обратную сторону");
    }

    #[test]
    fn distinct_universes_are_not_convertible() {
        // Без кумулятивности Type 0 не является Type 1.
        assert!(!conv(&Term::universe(0), &Term::universe(1)));
    }

    #[test]
    fn equivalent_level_expressions_are_convertible() {
        use crate::level::{Level, LevelVar};

        let u = Level::Var(LevelVar(0));
        let left = Term::Universe(u.clone().max(Level::Zero));
        let right = Term::Universe(u);
        assert!(conv(&left, &right));
    }

    #[test]
    fn multiplicity_distinguishes_function_types() {
        let linear = pi(Mult::One, Term::universe(0), Term::universe(0));
        let unrestricted = pi(Mult::Many, Term::universe(0), Term::universe(0));
        assert!(
            !conv(&linear, &unrestricted),
            "(1 x : A) -> B ≠ (ω x : A) -> B"
        );
        assert!(conv(&linear, &linear.clone()));
    }

    #[test]
    fn erased_and_linear_pi_differ_too() {
        let erased = pi(Mult::Zero, Term::universe(0), Term::universe(0));
        let linear = pi(Mult::One, Term::universe(0), Term::universe(0));
        assert!(!conv(&erased, &linear));
    }

    #[test]
    fn neutral_spines_are_compared_pointwise() {
        let applied_once = Term::var(0).apply([Term::universe(0)]);
        let applied_twice = Term::var(0).apply([Term::universe(0), Term::universe(0)]);
        assert!(conv_in(1, &applied_once, &applied_once.clone()));
        assert!(
            !conv_in(1, &applied_once, &applied_twice),
            "разная длина спайна"
        );

        let other_argument = Term::var(0).apply([Term::universe(1)]);
        assert!(!conv_in(1, &applied_once, &other_argument));
    }

    #[test]
    fn different_heads_are_not_convertible() {
        assert!(!conv_in(2, &Term::var(0), &Term::var(1)));
    }

    /// Почему кратность лямбды не сравнивается - регрессионный тест на решение.
    ///
    /// Если бы сравнивалась, конвертируемость перестала бы быть транзитивной:
    /// обе лямбды η-равны одной и той же `f`, а между собой различались бы.
    /// Свободу выбора это не даёт - у корректно типизированных термов под одним
    /// `Pi` кратность совпадает по построению.
    #[test]
    fn comparing_lambda_multiplicities_would_break_transitivity() {
        let f = Term::var(0);
        let expand = |mult| {
            Term::Lam(
                mult,
                "x".into(),
                Rc::new(Term::var(1).apply([Term::var(0)])),
            )
        };

        assert!(conv_in(1, &expand(Mult::One), &f));
        assert!(conv_in(1, &f, &expand(Mult::Zero)));
        assert!(
            conv_in(1, &expand(Mult::One), &expand(Mult::Zero)),
            "иначе транзитивность через f нарушена"
        );
    }

    /// Нормальные формы **не** канонические представители классов
    /// конвертируемости: обратное чтение не выполняет η-развёртку, потому что
    /// не знает типов.
    ///
    /// Это упирается в §7.3: content addressing требует, чтобы семантически
    /// одинаковые определения давали одинаковый хеш. Здесь два конвертируемых
    /// терма одного типа дают разные нормальные формы, значит и разные хеши.
    /// Лечится типизированным обратным чтением (η-длинные нормальные формы) -
    /// работа не этого среза.
    #[test]
    fn eta_equal_terms_have_different_normal_forms() {
        use crate::eval::quote;

        let f = Term::var(0);
        let expanded = Term::Lam(
            Mult::Many,
            "x".into(),
            Rc::new(Term::var(1).apply([Term::var(0)])),
        );

        let env = Env::default().extend(Value::var(Lvl(0)));
        assert!(conv_in(1, &f, &expanded), "конвертируемы");
        assert_ne!(
            quote(1, &eval(&env, &f)),
            quote(1, &eval(&env, &expanded)),
            "но нормальные формы различаются"
        );
    }

    #[test]
    fn convertibility_is_an_equivalence_relation() {
        let terms = [
            Term::universe(0),
            lam(Term::var(0)),
            lam(lam(Term::var(1))),
            pi(Mult::One, Term::universe(0), Term::universe(0)),
        ];

        for left in &terms {
            assert!(conv(left, left), "рефлексивность");
            for right in &terms {
                assert_eq!(conv(left, right), conv(right, left), "симметричность");
                for middle in &terms {
                    if conv(left, middle) && conv(middle, right) {
                        assert!(conv(left, right), "транзитивность");
                    }
                }
            }
        }
    }
}
