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

use crate::term::{Branch, Case, Term};
use crate::value::{Closure, Elim, Env, Head, Lvl, StuckBranch, StuckCase, Value};

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

        Term::Pi(mult, name, domain, row, codomain) => Rc::new(Value::Pi(
            *mult,
            Rc::clone(name),
            eval(env, domain),
            // Аргументы меток - обычные термы и вычисляются как всё прочее:
            // `State s` под связыванием `s` без этого осталось бы термом с
            // индексом, которому в значении не на что указывать.
            row.map(|argument| eval(env, argument)),
            Closure {
                env: env.clone(),
                body: Rc::clone(codomain),
            },
        )),

        Term::App(callee, argument) => apply(&eval(env, callee), eval(env, argument)),

        // Определение не разворачивается здесь: оно остаётся застрявшим, а
        // δ-редукцию делает проверка конвертируемости и только когда это
        // действительно нужно (`crate::conv`). Иначе нормальные формы и
        // сообщения об ошибках раздувались бы телами всех определений.
        Term::Const(name, levels) => Value::constant(Rc::clone(name), levels),

        // Тип связывания при вычислении не нужен: он влияет на проверку, а не
        // на значение.
        Term::Let(_, _, _, value, body) => {
            let value = eval(env, value);
            eval(&env.extend(value), body)
        }

        // Вычисляется **одна** ветвь - та, что выбрана. Собрать застрявший
        // разбор целиком значит вычислить мотив и все ветви, а у дерева
        // разбора ветвь сама бывает разбором: цена растёт как `2^d` вместо
        // `d`. Застрявший разбор собирается только когда он и правда застрял.
        Term::Case(case) => {
            let scrutinee = eval(env, &case.scrutinee);
            let selected = match &*scrutinee {
                Value::Neutral(Head::Global(name, _), spine) => case
                    .branches
                    .iter()
                    .find(|branch| branch.constructor == *name)
                    .map(|branch| (Rc::clone(&branch.body), spine.clone())),
                _ => None,
            };
            match selected {
                Some((body, spine)) => apply_fields(eval(env, &body), &spine, case.params)
                    .unwrap_or_else(|| unreachable!("конструктор под разбором: {scrutinee}")),
                None => eliminate_case(&Rc::new(stuck_case(env, case)), &scrutinee),
            }
        }
    }
}

/// Применяет тело ветви к полям конструктора.
///
/// Спайн конструктора - это параметры, потом поля; ветвь получает только
/// вторые. `None` - в спайне оказался разбор, то есть значение не конструктор.
fn apply_fields(body: Rc<Value>, spine: &[Elim], params: u32) -> Option<Rc<Value>> {
    spine
        .iter()
        .skip(params as usize)
        .try_fold(body, |body, elim| match elim {
            Elim::App(argument) => try_apply(&body, Rc::clone(argument)),
            Elim::Case(_) => None,
        })
}

/// Переводит разбор из терма в значение, вычисляя мотив и ветви.
fn stuck_case(env: &Env, case: &Case) -> StuckCase {
    StuckCase {
        data: Rc::clone(&case.data),
        levels: case
            .levels
            .iter()
            .map(crate::level::Level::normalize)
            .collect(),
        params: case.params,
        consumed: case.consumed,
        motive: eval(env, &case.motive),
        branches: case
            .branches
            .iter()
            .map(|branch| StuckBranch {
                constructor: Rc::clone(&branch.constructor),
                body: eval(env, &branch.body),
            })
            .collect(),
    }
}

/// Выполняет разбор над значением - ι-редукция.
///
/// Сводится, когда голова разбираемого значения оказалась конструктором из
/// ветвей: тогда спайн - это параметры, потом поля, и ветвь применяется к
/// полям. Всё остальное застревает, включая **определение с телом**: [`eval`]
/// его не разворачивает, и `case two of …` останется застрявшим до тех пор,
/// пока разворота не потребует проверка конвертируемости ([`crate::conv`]).
///
/// # Panics
///
/// Паникует, если разбирается не застрявшее значение. Internal invariant:
/// у значения индуктивного типа других форм не бывает, а типизацию обеспечивает
/// вызывающий. Там, где инвариант держать некому - δ-разворот переигрывает
/// спайн, накопленный над значением **другого** типа, - берут
/// [`try_eliminate_case`].
#[must_use]
pub fn eliminate_case(case: &Rc<StuckCase>, scrutinee: &Rc<Value>) -> Rc<Value> {
    try_eliminate_case(case, scrutinee)
        .unwrap_or_else(|| unreachable!("разбор неподходящего значения: {scrutinee}"))
}

/// [`eliminate_case`], возвращающая `None` вместо паники.
///
/// `None` - разбираемое значение не той формы: не нейтраль вовсе либо
/// конструктор, над которым уже накоплен разбор. Из корректно типизированного
/// терма ни то ни другое не получается, но δ-разворот ([`crate::conv`])
/// переигрывает спайн над развёрнутым телом, а тело может оказаться чем угодно,
/// если сравниваются значения разных типов - что проверка конвертируемости
/// обязана переживать отказом, а не падением.
#[must_use]
pub fn try_eliminate_case(case: &Rc<StuckCase>, scrutinee: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(head, spine) = &**scrutinee else {
        return None;
    };

    if let Head::Global(name, _) = head {
        if let Some(branch) = case
            .branches
            .iter()
            .find(|branch| branch.constructor == *name)
        {
            return apply_fields(Rc::clone(&branch.body), spine, case.params);
        }
    }

    let mut spine = spine.clone();
    spine.push(Elim::Case(Rc::clone(case)));
    Some(Rc::new(Value::Neutral(head.clone(), spine)))
}

/// Применяет значение к аргументу.
///
/// # Panics
///
/// Паникует на применении не-функции. Internal invariant: такие термы
/// отвергает проверяющий. Где инвариант не гарантирован - [`try_apply`].
#[must_use]
pub fn apply(callee: &Rc<Value>, argument: Rc<Value>) -> Rc<Value> {
    try_apply(callee, argument).unwrap_or_else(|| unreachable!("применение не-функции: {callee}"))
}

/// [`apply`], возвращающая `None` вместо паники. См. [`try_eliminate_case`].
#[must_use]
pub fn try_apply(callee: &Rc<Value>, argument: Rc<Value>) -> Option<Rc<Value>> {
    match &**callee {
        Value::Lam(_, _, closure) => Some(closure.apply(argument)),
        // Применение застряло - аргумент дописывается в спайн.
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::App(argument));
            Some(Rc::new(Value::Neutral(head.clone(), spine)))
        }
        _ => None,
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

        Value::Neutral(head, spine) => {
            let base = match head {
                Head::Local(level) => Term::Var(level.to_index(size)),
                Head::Global(name, levels) => Term::Const(Rc::clone(name), Rc::clone(levels)),
            };
            spine.iter().fold(base, |callee, elim| match elim {
                Elim::App(argument) => Term::App(Rc::new(callee), Rc::new(quote(size, argument))),
                // Накопленный терм и есть то, на чём разбор застрял.
                Elim::Case(case) => Term::Case(Rc::new(Case {
                    data: Rc::clone(&case.data),
                    levels: Rc::clone(&case.levels),
                    params: case.params,
                    consumed: case.consumed,
                    scrutinee: Rc::new(callee),
                    motive: Rc::new(quote(size, &case.motive)),
                    branches: case
                        .branches
                        .iter()
                        .map(|branch| Branch {
                            constructor: Rc::clone(&branch.constructor),
                            body: Rc::new(quote(size, &branch.body)),
                        })
                        .collect(),
                })),
            })
        }

        Value::Lam(mult, name, closure) => Term::Lam(
            *mult,
            Rc::clone(name),
            Rc::new(quote(size + 1, &closure.apply(Value::var(Lvl(size))))),
        ),

        Value::Pi(mult, name, domain, row, codomain) => Term::Pi(
            *mult,
            Rc::clone(name),
            Rc::new(quote(size, domain)),
            row.map(|argument| quote(size, argument)),
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

    use crate::row::Row;

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
        Term::Pi(
            Mult::Many,
            "_".into(),
            Rc::new(domain),
            Row::empty(),
            Rc::new(codomain),
        )
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
