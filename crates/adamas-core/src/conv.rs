//! Проверка конвертируемости - definitional equality ядра.
//!
//! Сравниваются значения, а не термы: вычисление уже сделало β-редукцию и
//! развернуло `let`, так что здесь остаётся сопоставление форм плюс η.
//!
//! Кумулятивности нет: `Type 0` и `Type 1` неконвертируемы (§10 вопрос 1).

use std::rc::Rc;

use crate::eval::apply;
use crate::value::{Lvl, Value};

/// Конвертируемы ли два значения в контексте размера `size`.
///
/// Осмысленный вопрос - только про значения одного типа, и проверяющий других
/// не задаёт. Но функция тотальна и на разнотипных: возвращает `false`, а не
/// паникует. Паника здесь была бы не защитой инварианта, а падением на входе,
/// который ничего не нарушает.
#[must_use]
pub fn convertible(size: u32, left: &Rc<Value>, right: &Rc<Value>) -> bool {
    match (&**left, &**right) {
        (Value::Universe(a), Value::Universe(b)) => a.equiv(b),

        (Value::Neutral(head_a, spine_a), Value::Neutral(head_b, spine_b)) => {
            head_a == head_b
                && spine_a.len() == spine_b.len()
                && spine_a
                    .iter()
                    .zip(spine_b)
                    .all(|(a, b)| convertible(size, a, b))
        }

        // Кратность - часть типа функции, поэтому здесь она значима:
        // `(1 x : A) -> B` и `(ω x : A) -> B` - разные типы.
        (
            Value::Pi(mult_a, _, domain_a, codomain_a),
            Value::Pi(mult_b, _, domain_b, codomain_b),
        ) => {
            mult_a == mult_b
                && convertible(size, domain_a, domain_b)
                && convertible_under(size, |v| codomain_a.apply(v), |v| codomain_b.apply(v))
        }

        // Кратность лямбды не сравнивается - иначе ломается транзитивность,
        // см. `comparing_lambda_multiplicities_would_break_transitivity`.
        (Value::Lam(_, _, body_a), Value::Lam(_, _, body_b)) => {
            convertible_under(size, |v| body_a.apply(v), |v| body_b.apply(v))
        }

        // η: функция равна своему развёрнутому виду `\x -> f x`. Без этого
        // правила `f` и `\x -> f x` были бы разными термами.
        //
        // Разворачивается только против застрявшего значения. Против `Pi` или
        // `Universe` лямбда неконвертируема в любом случае, а применить их
        // нельзя - попытка была бы обращением к `apply` с не-функцией.
        (Value::Lam(_, _, body), Value::Neutral(..)) => {
            convertible_under(size, |v| body.apply(v), |v| apply(right, v))
        }
        (Value::Neutral(..), Value::Lam(_, _, body)) => {
            convertible_under(size, |v| apply(left, v), |v| body.apply(v))
        }

        _ => false,
    }
}

/// Сравнивает под свежим связыванием.
fn convertible_under(
    size: u32,
    left: impl FnOnce(Rc<Value>) -> Rc<Value>,
    right: impl FnOnce(Rc<Value>) -> Rc<Value>,
) -> bool {
    let fresh = Value::var(Lvl(size));
    convertible(size + 1, &left(Rc::clone(&fresh)), &right(fresh))
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
        convertible(free, &eval(&env, left), &eval(&env, right))
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
