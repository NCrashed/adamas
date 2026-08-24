//! Свойства нормализации и уровней.
//!
//! Термы генерируются **уже в нормальной форме**. Это не осторожность ради
//! осторожности: ядро - нетипизированная λ-система, и произвольный терм с
//! редексами может расходиться (`(\x -> x x) (\y -> y y)` порождается таким
//! генератором на раз). Пока проверяющего типов нет, единственный класс,
//! завершаемость которого гарантирована синтаксически, - нормальные формы.
//!
//! Свойство "`NbE` - тождество на нормальных формах" при этом не тавтология: оно
//! ловит ровно тот класс ошибок, ради которого `NbE` и написан, - путаницу между
//! индексами и уровнями при обратном чтении.

use std::rc::Rc;

use adamas_core::conv::convertible;
use adamas_core::eval::{eval, normalize};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::{Index, Term};
use adamas_core::value::Env;
use proptest::prelude::*;
use proptest::strategy::{BoxedStrategy, Union};

// ---------------------------------------------------------------- генераторы

fn any_mult() -> impl Strategy<Value = Mult> {
    prop_oneof![Just(Mult::Zero), Just(Mult::One), Just(Mult::Many)]
}

fn any_level() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::Zero),
        (0u32..3).prop_map(Level::number),
        (0u32..3).prop_map(|index| Level::Var(LevelVar(index))),
    ];
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner).prop_map(|(a, b)| a.max(b)),
        ]
    })
}

/// Нейтральный терм: переменная, применённая к нормальным аргументам.
fn neutral(binders: u32, depth: u32) -> BoxedStrategy<Term> {
    let head = (0..binders).prop_map(Term::var);
    if depth == 0 {
        return head.boxed();
    }
    (
        head,
        proptest::collection::vec(normal(binders, depth - 1), 0..3),
    )
        .prop_map(|(head, arguments)| head.apply(arguments))
        .boxed()
}

/// Замкнутый терм в нормальной форме при `binders` связываниях в области
/// видимости.
fn normal(binders: u32, depth: u32) -> BoxedStrategy<Term> {
    let mut choices: Vec<BoxedStrategy<Term>> = vec![any_level().prop_map(Term::Universe).boxed()];

    if binders > 0 {
        choices.push(neutral(binders, depth));
    }
    if depth > 0 {
        choices.push(
            (any_mult(), normal(binders + 1, depth - 1))
                .prop_map(|(mult, body)| Term::Lam(mult, "x".into(), Rc::new(body)))
                .boxed(),
        );
        choices.push(
            (
                any_mult(),
                normal(binders, depth - 1),
                normal(binders + 1, depth - 1),
            )
                .prop_map(|(mult, domain, codomain)| {
                    Term::Pi(mult, "x".into(), Rc::new(domain), Rc::new(codomain))
                })
                .boxed(),
        );
    }
    Union::new(choices).boxed()
}

fn any_term() -> BoxedStrategy<Term> {
    normal(0, 3)
}

// ------------------------------------------------------------- вспомогательное

/// Все ли индексы терма попадают в область видимости.
fn well_scoped(term: &Term, binders: u32) -> bool {
    match term {
        Term::Var(Index(index)) => *index < binders,
        Term::Const(..) | Term::Universe(_) => true,
        Term::Lam(_, _, body) => well_scoped(body, binders + 1),
        Term::App(callee, argument) => {
            well_scoped(callee, binders) && well_scoped(argument, binders)
        }
        Term::Pi(_, _, domain, codomain) => {
            well_scoped(domain, binders) && well_scoped(codomain, binders + 1)
        }
        Term::Let(_, _, ty, value, body) => {
            well_scoped(ty, binders)
                && well_scoped(value, binders)
                && well_scoped(body, binders + 1)
        }
    }
}

/// Независимая проверка того, что терм - нормальная форма: ни одного
/// β-редекса, ни одного `let`, все уровни канонические.
///
/// Оракул нарочно не пользуется [`normalize`]: иначе свойство проверяло бы
/// согласованность функции с самой собой.
fn is_normal_form(term: &Term) -> bool {
    match term {
        // Определение застревает так же, как переменная: обратное чтение его
        // не разворачивает, значит это уже нормальная форма.
        Term::Var(_) | Term::Const(..) => true,
        Term::Universe(level) => level.normalize() == *level,
        Term::Lam(_, _, body) => is_normal_form(body),
        Term::Pi(_, _, domain, codomain) => is_normal_form(domain) && is_normal_form(codomain),
        // Голова применения обязана быть застрявшей: под лямбдой это редекс.
        Term::App(callee, argument) => {
            !matches!(**callee, Term::Lam(..)) && is_normal_form(callee) && is_normal_form(argument)
        }
        // `let` вычисление устраняет всегда.
        Term::Let(..) => false,
    }
}

/// Переименовывает все связывания - на семантику это влиять не должно.
fn rename(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Universe(_) | Term::Const(..) => term.clone(),
        Term::Lam(mult, _, body) => Term::Lam(*mult, "renamed".into(), Rc::new(rename(body))),
        Term::App(callee, argument) => {
            Term::App(Rc::new(rename(callee)), Rc::new(rename(argument)))
        }
        Term::Pi(mult, _, domain, codomain) => Term::Pi(
            *mult,
            "renamed".into(),
            Rc::new(rename(domain)),
            Rc::new(rename(codomain)),
        ),
        Term::Let(mult, _, ty, value, body) => Term::Let(
            *mult,
            "renamed".into(),
            Rc::new(rename(ty)),
            Rc::new(rename(value)),
            Rc::new(rename(body)),
        ),
    }
}

fn value_of(term: &Term) -> Rc<adamas_core::value::Value> {
    eval(&Env::default(), term)
}

/// Обкладывает листья терма тождественными редексами: `#0` становится
/// `(\r -> #0) #0`, `Type u` - `(\r -> #0) (Type u)`.
///
/// Так проверяется β, которую генератор нормальных форм не порождает вовсе.
/// Расходимость невозможна: подставляемая функция тождественна и каждый редекс
/// снимается за один шаг. Оборачиваются только листья - тело `\r -> #0`
/// замкнуто, аргумент остаётся на той же глубине связывания, и индексы внутри
/// него не сдвигаются.
fn wrap_in_redexes(term: &Term, budget: &mut u32) -> Term {
    let identity = || Term::Lam(Mult::Many, "r".into(), Rc::new(Term::var(0)));
    let spend = |budget: &mut u32| {
        let available = *budget > 0;
        *budget = budget.saturating_sub(1);
        available
    };

    let rebuilt = match term {
        Term::Var(_) | Term::Universe(_) | Term::Const(..) => term.clone(),
        Term::Lam(mult, name, body) => Term::Lam(
            *mult,
            Rc::clone(name),
            Rc::new(wrap_in_redexes(body, budget)),
        ),
        Term::App(callee, argument) => Term::App(
            Rc::new(wrap_in_redexes(callee, budget)),
            Rc::new(wrap_in_redexes(argument, budget)),
        ),
        Term::Pi(mult, name, domain, codomain) => Term::Pi(
            *mult,
            Rc::clone(name),
            Rc::new(wrap_in_redexes(domain, budget)),
            Rc::new(wrap_in_redexes(codomain, budget)),
        ),
        Term::Let(mult, name, ty, value, body) => Term::Let(
            *mult,
            Rc::clone(name),
            Rc::new(wrap_in_redexes(ty, budget)),
            Rc::new(wrap_in_redexes(value, budget)),
            Rc::new(wrap_in_redexes(body, budget)),
        ),
    };

    // Голову применения оборачивать нельзя: `(\x -> #0) f a` - это уже другой
    // терм, а не `f a` с лишним редексом.
    if matches!(term, Term::Var(_) | Term::Universe(_)) && spend(budget) {
        return identity().apply([rebuilt]);
    }
    rebuilt
}

// -------------------------------------------------------------------- уровни

/// Наибольшая константа, встречающаяся в уровне: числовые литералы вместе с
/// накопленными `suc`.
fn max_constant(level: &Level) -> u32 {
    match level {
        // Метапеременных генератор не порождает: свойства уровней проверяются
        // на замкнутых выражениях, а дырки живут в `meta.rs`.
        Level::Zero | Level::Var(_) | Level::Meta(_) => 0,
        Level::Succ(inner) => max_constant(inner) + 1,
        Level::Max(a, b) => max_constant(a).max(max_constant(b)),
    }
}

/// Сколько переменных различает генератор [`any_level`].
const LEVEL_VARS: u32 = 3;

/// Диапазон значений переменных, на котором различимы любые два неравных
/// уровня из [`any_level`].
///
/// Верхняя граница обязана превышать константы, встречающиеся в выражениях:
/// иначе `max 3 u` и `max 4 u` совпадут на всём диапазоне и полнота сорвётся
/// ложно. Запас взят с избытком - перебор дешёвый, а промах виден только как
/// загадочный отказ.
fn bound_for(levels: [&Level; 2]) -> u32 {
    levels.into_iter().map(max_constant).max().unwrap_or(0) + LEVEL_VARS + 1
}

/// Все подстановки переменных `u0..u2` значениями `0..=bound`.
fn assignments(bound: u32) -> impl Iterator<Item = impl Fn(LevelVar) -> u32> {
    let span = bound + 1;
    (0..span * span * span).map(move |code| {
        move |LevelVar(index)| match index {
            0 => code % span,
            1 => (code / span) % span,
            2 => (code / (span * span)) % span,
            _ => 0,
        }
    })
}

proptest! {
    /// Нормализация не меняет значения ни при какой подстановке.
    ///
    /// Свойство сильнее, чем `equiv(level, level.normalize())`: то сравнивает
    /// нормальную форму с самой собой через ту же функцию, а это - с
    /// независимым определением уровня.
    #[test]
    fn level_normalization_preserves_value(level in any_level()) {
        let normalized = level.normalize();
        let bound = bound_for([&level, &normalized]);
        for assignment in assignments(bound) {
            prop_assert_eq!(
                level.evaluate(&assignment),
                normalized.evaluate(&assignment),
                "{} и {} расходятся", level, normalized
            );
        }
    }

    /// **Корректность:** признав уровни равными, `equiv` обязана быть права на
    /// любой подстановке. Обратное - полнота - тут не требуется: неполнота
    /// отвергает корректную программу, неверность принимает некорректную.
    #[test]
    fn equivalence_never_conflates_distinct_levels(a in any_level(), b in any_level()) {
        if a.equiv(&b) {
            for assignment in assignments(bound_for([&a, &b])) {
                prop_assert_eq!(
                    a.evaluate(&assignment), b.evaluate(&assignment),
                    "{} и {} признаны равными, но расходятся", a, b
                );
            }
        }
    }

    /// **Полнота:** нормальная форма - полный инвариант, и совпадение на всех
    /// подстановках обязано давать `equiv`.
    ///
    /// Безусловная - вместе с `imax` ушёл единственный случай, который её
    /// ломал (§10 вопрос 2 закрыт).
    #[test]
    fn equivalence_is_complete(a in any_level(), b in any_level()) {
        let same_everywhere = assignments(bound_for([&a, &b]))
            .all(|assignment| a.evaluate(&assignment) == b.evaluate(&assignment));
        prop_assert_eq!(a.equiv(&b), same_everywhere, "{} против {}", a, b);
    }

    /// **Порядок:** `leq` совпадает со сравнением значений при любой
    /// подстановке - и в одну сторону, и в другую.
    ///
    /// На этом держится универсумная проверка полей конструктора
    /// (`crate::sig`): она не пускает импредикативность через data-декларацию,
    /// и заявление о полноте `leq` там несущее, а не украшение.
    #[test]
    fn ordering_agrees_with_evaluation(a in any_level(), b in any_level()) {
        let below_everywhere = assignments(bound_for([&a, &b]))
            .all(|assignment| a.evaluate(&assignment) <= b.evaluate(&assignment));
        prop_assert_eq!(a.leq(&b), below_everywhere, "{} <= {}", a, b);
    }

    /// Нормальная форма уровня лежит в том же классе эквивалентности.
    #[test]
    fn level_normalization_preserves_meaning(level in any_level()) {
        prop_assert!(level.equiv(&level.normalize()));
    }

    /// Нормальная форма канонична: равенство нормальных форм и семантическое
    /// равенство - это одно и то же.
    #[test]
    fn level_equivalence_is_normal_form_equality(a in any_level(), b in any_level()) {
        prop_assert_eq!(a.equiv(&b), a.normalize() == b.normalize());
    }

    #[test]
    fn level_normalization_is_idempotent(level in any_level()) {
        let once = level.normalize();
        prop_assert_eq!(once.normalize(), once);
    }

    #[test]
    fn max_is_a_commutative_idempotent_monoid(a in any_level(), b in any_level(), c in any_level()) {
        prop_assert!(a.clone().max(b.clone()).equiv(&b.clone().max(a.clone())));
        prop_assert!(a.clone().max(a.clone()).equiv(&a));
        prop_assert!(a.clone().max(Level::Zero).equiv(&a));
        prop_assert!(
            a.clone().max(b.clone()).max(c.clone()).equiv(&a.max(b.max(c)))
        );
    }

    #[test]
    fn succ_distributes_over_max(a in any_level(), b in any_level()) {
        prop_assert!(a.clone().max(b.clone()).succ().equiv(&a.succ().max(b.succ())));
    }

}

// --------------------------------------------------------------------- термы

proptest! {
    /// Результат нормализации - действительно нормальная форма. Проверяется
    /// независимым оракулом, а не повторным вызовом самой нормализации.
    #[test]
    fn normalization_yields_normal_forms(term in any_term()) {
        let result = normalize(&term);
        prop_assert!(is_normal_form(&result), "не нормальная форма: {result}");
    }

    /// `NbE` - тождество на том, что уже нормализовано.
    #[test]
    fn normalization_is_idempotent(term in any_term()) {
        let once = normalize(&term);
        prop_assert_eq!(normalize(&once), once);
    }

    /// Вставленные редексы обязаны исчезнуть без следа. В отличие от свойств
    /// выше, это проверка самой β-редукции и захвата окружения замыканием:
    /// генератор нормальных форм ни одного редекса не порождает.
    #[test]
    fn inserted_redexes_normalize_away(term in any_term(), budget in 0u32..12) {
        let mut budget = budget;
        let wrapped = wrap_in_redexes(&term, &mut budget);
        prop_assert_eq!(normalize(&wrapped), normalize(&term), "обёртка: {}", wrapped);
    }

    /// Тот же вход, но через конвертируемость: обёрнутый и исходный термы
    /// обязаны быть неразличимы и для неё.
    #[test]
    fn inserted_redexes_preserve_convertibility(term in any_term(), budget in 0u32..12) {
        let mut budget = budget;
        let wrapped = wrap_in_redexes(&term, &mut budget);
        prop_assert!(convertible(&Signature::default(), &mut Metas::default(), 0, &value_of(&term), &value_of(&wrapped)));
    }

    /// Результат нормализации замкнут. Классическая ошибка `NbE` - перепутать
    /// направление счёта при обратном чтении, и наружу лезет индекс, которому
    /// не соответствует ни одно связывание.
    #[test]
    fn normalization_yields_well_scoped_terms(term in any_term()) {
        prop_assert!(well_scoped(&normalize(&term), 0));
    }

    #[test]
    fn convertibility_is_reflexive(term in any_term()) {
        prop_assert!(convertible(&Signature::default(), &mut Metas::default(), 0, &value_of(&term), &value_of(&term)));
    }

    /// Имена связываний на семантику не влияют.
    #[test]
    fn renaming_binders_preserves_convertibility(term in any_term()) {
        let renamed = rename(&term);
        prop_assert!(convertible(&Signature::default(), &mut Metas::default(), 0, &value_of(&term), &value_of(&renamed)));
    }

    #[test]
    fn convertibility_is_symmetric(a in any_term(), b in any_term()) {
        let (left, right) = (value_of(&a), value_of(&b));
        prop_assert_eq!(
            convertible(&Signature::default(), &mut Metas::default(), 0, &left, &right),
            convertible(&Signature::default(), &mut Metas::default(), 0, &right, &left)
        );
    }

    /// Равенство нормальных форм влечёт конвертируемость.
    ///
    /// Обратное неверно, и это не недосмотр: конвертируемость учитывает η и
    /// игнорирует кратность лямбды, а обратное чтение - нет. Оба расхождения
    /// разобраны тестами в `conv`.
    #[test]
    fn equal_normal_forms_are_convertible(a in any_term(), b in any_term()) {
        if normalize(&a) == normalize(&b) {
            prop_assert!(convertible(&Signature::default(), &mut Metas::default(), 0, &value_of(&a), &value_of(&b)));
        }
    }

    /// Транзитивность - то свойство, которым пришлось бы заплатить за
    /// сравнение кратностей лямбд.
    #[test]
    fn convertibility_is_transitive(a in any_term(), b in any_term(), c in any_term()) {
        let (a, b, c) = (value_of(&a), value_of(&b), value_of(&c));
        if convertible(&Signature::default(), &mut Metas::default(), 0, &a, &b) && convertible(&Signature::default(), &mut Metas::default(), 0, &b, &c) {
            prop_assert!(convertible(&Signature::default(), &mut Metas::default(), 0, &a, &c));
        }
    }
}
