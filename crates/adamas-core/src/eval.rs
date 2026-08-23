//! Normalization by evaluation (§9, Фаза 1).
//!
//! Вместо того чтобы переписывать термы правилами редукции, терм вычисляется в
//! значение средствами хозяйского языка, а потом читается обратно. Подстановка
//! при этом не выполняется ни разу: её заменяет захват окружения в замыкании.
//! Ровно то, что warm-up делал наивно и медленно - см.
//! `docs/warmup-retrospective.md`.
//!
//! Обратное чтение ([`quote`]) заходит под связывания, применяя замыкание к
//! свежей переменной. Поэтому результат - полная нормальная форма, а не только
//! головная.
//!
//! # Что здесь предполагается о входе
//!
//! Терм обязан быть **замкнутым и корректно типизированным**. Ядро -
//! нетипизированная λ-система, завершаемость ей даёт только типизация: на
//! `(\x -> x x) (\x -> x x)` вычисление разворачивается бесконечно и кладёт
//! процесс переполнением стека. Проверка типов - обязанность вызывающего, и
//! отдельного предохранителя (счётчика шагов) здесь нет: в отличие от
//! warm-up'а, где расходимость была штатным пользовательским случаем, сюда
//! расходящийся терм может попасть только при поломке проверяющего.

use std::rc::Rc;

use crate::term::Term;
use crate::value::{Closure, Env, Lvl, Value};

impl Closure {
    /// Применяет замыкание к аргументу.
    #[must_use]
    pub fn apply(&self, argument: Rc<Value>) -> Rc<Value> {
        eval(&self.env.extend(argument), &self.body)
    }
}

/// Вычисляет терм в окружении.
///
/// Терм обязан быть корректно типизированным - иначе вычисление может не
/// завершиться, см. заголовок модуля.
///
/// # Panics
///
/// Паникует на незамкнутом терме - индексе, которому нечего сопоставить в
/// окружении. Это internal invariant: замкнутость обеспечивает проверяющий, и
/// нарушить её может только поломка компилятора.
#[must_use]
pub fn eval(env: &Env, term: &Term) -> Rc<Value> {
    match term {
        Term::Var(index) => env.lookup(*index).unwrap_or_else(|| {
            unreachable!("незамкнутый терм: {index:?} при {} связываниях", env.len())
        }),

        Term::Universe(level) => Rc::new(Value::Universe(level.clone())),

        Term::Lam(mult, name, body) => Rc::new(Value::Lam(
            *mult,
            Rc::clone(name),
            Closure {
                env: env.clone(),
                body: Rc::clone(body),
            },
        )),

        Term::Pi(mult, name, domain, codomain) => Rc::new(Value::Pi(
            *mult,
            Rc::clone(name),
            eval(env, domain),
            Closure {
                env: env.clone(),
                body: Rc::clone(codomain),
            },
        )),

        Term::App(callee, argument) => apply(&eval(env, callee), eval(env, argument)),

        // Тип связывания при вычислении не нужен: он влияет на проверку, а не
        // на значение.
        Term::Let(_, _, _, value, body) => {
            let value = eval(env, value);
            eval(&env.extend(value), body)
        }
    }
}

/// Применяет значение к аргументу.
///
/// # Panics
///
/// Паникует на применении не-функции. Internal invariant: такие термы
/// отвергает проверяющий.
#[must_use]
pub fn apply(callee: &Rc<Value>, argument: Rc<Value>) -> Rc<Value> {
    match &**callee {
        Value::Lam(_, _, closure) => closure.apply(argument),
        // Применение застряло - аргумент дописывается в спайн.
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(argument);
            Rc::new(Value::Neutral(*head, spine))
        }
        other => unreachable!("применение не-функции: {other}"),
    }
}

/// Читает значение обратно в терм.
///
/// `size` - число связываний в контексте: оно же уровень следующей свежей
/// переменной. Обязано совпадать с контекстом, в котором значение построено.
///
/// # Panics
///
/// Если `size` меньше - в значении окажется уровень, которому не соответствует
/// ни одно связывание. См. [`Lvl::to_index`].
#[must_use]
pub fn quote(size: u32, value: &Rc<Value>) -> Term {
    match &**value {
        // Уровень нормализуется, чтобы нормальная форма была канонической и
        // `max u 0` не отличался от `u`.
        Value::Universe(level) => Term::Universe(level.normalize()),

        Value::Neutral(head, spine) => spine
            .iter()
            .fold(Term::Var(head.to_index(size)), |callee, argument| {
                Term::App(Rc::new(callee), Rc::new(quote(size, argument)))
            }),

        Value::Lam(mult, name, closure) => Term::Lam(
            *mult,
            Rc::clone(name),
            Rc::new(quote(size + 1, &closure.apply(Value::var(Lvl(size))))),
        ),

        Value::Pi(mult, name, domain, codomain) => Term::Pi(
            *mult,
            Rc::clone(name),
            Rc::new(quote(size, domain)),
            Rc::new(quote(size + 1, &codomain.apply(Value::var(Lvl(size))))),
        ),
    }
}

/// Приводит замкнутый корректно типизированный терм к нормальной форме.
#[must_use]
pub fn normalize(term: &Term) -> Term {
    quote(0, &eval(&Env::default(), term))
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{eval, normalize, quote};
    use crate::level::Level;
    use crate::mult::Mult;
    use crate::term::Term;
    use crate::value::{Env, Lvl, Value};

    /// `\(ω x) -> body`
    fn lam(body: Term) -> Term {
        Term::Lam(Mult::Many, "x".into(), Rc::new(body))
    }

    /// `(ω _ : domain) -> codomain`
    fn arrow(domain: Term, codomain: Term) -> Term {
        Term::Pi(Mult::Many, "_".into(), Rc::new(domain), Rc::new(codomain))
    }

    #[test]
    fn beta_reduction_happens() {
        // (\x -> x) (Type 0)  ==>  Type 0
        let term = lam(Term::var(0)).apply([Term::universe(0)]);
        assert_eq!(normalize(&term).to_string(), "Type 0");
    }

    #[test]
    fn normalization_goes_under_binders() {
        // \y -> (\x -> x) y  ==>  \y -> y
        let term = lam(lam(Term::var(0)).apply([Term::var(0)]));
        assert_eq!(normalize(&term).to_string(), "\\(ω x) -> #0");
    }

    #[test]
    fn closures_capture_the_right_binding() {
        // (\a -> \b -> a) (Type 1)  ==>  \b -> Type 1
        // Если бы захват был неверен, тело вернуло бы b.
        let konst = lam(lam(Term::var(1)));
        let term = konst.apply([Term::universe(1)]);
        assert_eq!(normalize(&term).to_string(), "\\(ω x) -> Type 1");
    }

    #[test]
    fn shadowing_resolves_by_index_not_by_name() {
        // \x -> \x -> #1 - внешнее связывание, несмотря на совпадение имён.
        let term = lam(lam(Term::var(1)));
        assert_eq!(normalize(&term), term);
    }

    #[test]
    fn let_is_eliminated_by_evaluation() {
        // let x : Type 1 = Type 0 in x  ==>  Type 0
        let term = Term::Let(
            Mult::Many,
            "x".into(),
            Rc::new(Term::universe(1)),
            Rc::new(Term::universe(0)),
            Rc::new(Term::var(0)),
        );
        assert_eq!(normalize(&term).to_string(), "Type 0");
    }

    #[test]
    fn neutral_terms_accumulate_a_spine() {
        // В контексте из одной свободной переменной: f (\x -> x) остаётся как
        // есть, но аргумент нормализуется.
        let env = Env::default().extend(Value::var(Lvl(0)));
        let term = Term::var(0).apply([lam(lam(Term::var(0)).apply([Term::var(0)]))]);
        let quoted = quote(1, &eval(&env, &term));
        assert_eq!(quoted.to_string(), "#0 (\\(ω x) -> #0)");
    }

    #[test]
    fn universe_levels_are_normalized_on_readback() {
        // max 0 u  ==>  u
        let level = Level::Zero.max(Level::Var(crate::level::LevelVar(0)));
        let term = Term::Universe(level);
        assert_eq!(normalize(&term).to_string(), "Type u0");
    }

    #[test]
    fn pi_normalizes_domain_and_codomain() {
        // ((\x -> x) (Type 0)) -> ((\x -> x) (Type 0))  ==>  Type 0 -> Type 0
        let redex = || lam(Term::var(0)).apply([Term::universe(0)]);
        let term = arrow(redex(), redex());
        assert_eq!(normalize(&term).to_string(), "(ω _ : Type 0) -> Type 0");
    }

    #[test]
    fn normalization_is_idempotent() {
        let term = lam(lam(Term::var(1)).apply([Term::var(0)]));
        let once = normalize(&term);
        assert_eq!(normalize(&once), once);
    }
}
