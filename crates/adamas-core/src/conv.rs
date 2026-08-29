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
//! Поэтому число разворотов ограничено пределом. Исчерпание даёт
//! `false`, то есть отказ, а не зависание: направление безопасное - неполнота
//! отвергает корректную программу, тогда как обратная ошибка приняла бы
//! некорректную. Так же устроены пределы в Coq, Agda и Lean; на тотальность
//! здесь положиться нельзя ни в одной из них.
//!
//! Предел считается **вдоль пути**, а не на всё сравнение: топливо передаётся
//! вниз копией, поэтому соседние элементы спайна друг у друга его не отнимают.
//! Общий счётчик делал бы конвертируемость зависящей от ширины типа, а не от
//! глубины разворота: два типа, различающихся одним редексом в каждой из `k`
//! стрелок, признавались бы равными при `k = 128` и разными при `k = 129`, то
//! есть отношение переставало быть композициональным - из `A ≡ A'` и `B ≡ B'`
//! не следовало `(A -> B) ≡ (A' -> B')`. Завершаемость от этого не страдает:
//! вдоль любого пути от корня к листу разворотов по-прежнему не больше предела.

use std::rc::Rc;

use crate::eval::{apply, try_apply, try_eliminate_case};
use crate::meta::Metas;
use crate::sig::Signature;
use crate::solve::{force, solve};
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
/// именно там, где встречаются два типа.
///
/// Решения не откатываются, и это источник неполноты. Для внешнего вызова
/// безвредно - неудача означает отказ, - но внутри неудача быстрого пути
/// (`rigid`) штатна: она ведёт к δ-развороту и повторному сравнению. Решения,
/// принятые до того, как быстрый путь провалился, повтор переживают. `F{?l} a`
/// против `F{2} b`, где `F` игнорирует и уровень, и аргумент, фиксирует
/// `?l := 2` без основания: сравнение всё равно пройдёт через разворот, а
/// следующее ограничение `?l ~ 5` отвергнет корректную программу. Лечится тем,
/// чтобы `rigid` сравнивал уровни, а решал их только путь, определяющий
/// исход, - работа не этого среза.
pub fn convertible(
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    convertible_within(UNFOLD_LIMIT, sig, metas, size, left, right)
}

/// Приводит значение к слабой головной нормальной форме: разворачивает
/// определение в голове, пока голова разворачивается.
///
/// Нужна везде, где проверка смотрит на **форму** типа, а не сравнивает его с
/// другим: применение спрашивает "это `Pi`?", позиция типа - "это `Universe`?",
/// разбор - "это то семейство?". [`crate::eval`] определений не разворачивает,
/// поэтому без приведения `def Fn = Nat -> Nat` не был бы типом функции, а
/// `def Sort2 = Type 2` - типом вовсе.
///
/// Предел тот же и по той же причине, что у [`convertible`]; исчерпание
/// возвращает то, что успело развернуться, и вызывающий увидит неразвёрнутую
/// голову - то есть отказ, а не зависание.
#[must_use]
pub fn whnf(sig: &Signature, value: &Rc<Value>) -> Rc<Value> {
    let mut current = Rc::clone(value);
    let mut fuel = UNFOLD_LIMIT;
    while let Some(next) = unfold(sig, &current) {
        current = next;
        let Some(remaining) = fuel.checked_sub(1) else {
            break;
        };
        fuel = remaining;
    }
    current
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
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    // Решённая дырка разворачивается до сравнения: иначе `?m` и её решение
    // оказались бы разными значениями, а это одно и то же значение. Форма
    // та же, что у разворота определений ниже: `None` - разворачивать нечего,
    // и клонировать `Rc` на каждом шаге сравнения незачем.
    let (forced_left, forced_right) = (force(metas, left), force(metas, right));
    let left = forced_left.as_ref().unwrap_or(left);
    let right = forced_right.as_ref().unwrap_or(right);

    if rigid(fuel, sig, metas, size, left, right) {
        return true;
    }

    // Нерешённая дырка в голове - не «не сошлось», а задача унификации.
    // Пробуется она **после** синтаксического сравнения и **до** разворота
    // определений. После - потому что `?m ū ≡ ?m ū` решать нечего, а проверка
    // вхождения приняла бы это за цикл. До - потому что развернув, мы получили
    // бы то же ограничение, только на большем терме.
    match (&**left, &**right) {
        (Value::Neutral(Head::Meta(meta), spine), _) => {
            return solve(sig, metas, size, *meta, spine, right);
        }
        (_, Value::Neutral(Head::Meta(meta), spine)) => {
            return solve(sig, metas, size, *meta, spine, left);
        }
        _ => {}
    }
    // Быстрый путь не сошёлся - разворачиваем то, что разворачивается.
    let (unfolded_left, unfolded_right) = (unfold(sig, left), unfold(sig, right));
    if unfolded_left.is_none() && unfolded_right.is_none() {
        return false;
    }
    let Some(remaining) = fuel.checked_sub(1) else {
        return false;
    };
    convertible_within(
        remaining,
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
///
/// Переигрывание **может не получиться**, и тогда результат тоже `None`.
/// Спайн накапливается над значением одного типа, а разворачивается голова
/// другого: η-правило ниже дописывает `Elim::App` к любой нейтрали, поэтому
/// сравнение `\x -> x` с `def c : Type 1 = Type 0` доходит сюда с попыткой
/// применить `Type 0` к аргументу. Для сравнения разнотипных значений это
/// штатный исход - `convertible` обязана отвечать `false`, - а не поломка
/// инварианта, поэтому здесь стоят `try_`-варианты, а не паникующие.
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
    spine.iter().try_fold(body, |callee, elim| match elim {
        Elim::App(argument) => try_apply(&callee, Rc::clone(argument)),
        Elim::Case(case) => try_eliminate_case(case, &callee),
        // Проекция из развёрнутого определения: если это уже запись, поле
        // берётся, иначе разворот не помог и сравнение идёт дальше.
        Elim::Project(name) => {
            matches!(&*callee, Value::Object(_)).then(|| crate::eval::project(&callee, name))
        }
    })
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
        // Одна и та же нерешённая дырка - это одно и то же значение, и решать
        // тут нечего. Без этой строки `?m ū ≡ ?m ū` уходило бы в решение, где
        // проверка вхождения приняла бы его за цикл.
        (Head::Meta(a), Head::Meta(b)) => a == b,
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
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Elim,
    right: &Elim,
) -> bool {
    match (left, right) {
        (Elim::App(a), Elim::App(b)) => convertible_within(fuel, sig, metas, size, a, b),
        (Elim::Case(a), Elim::Case(b)) => same_case(fuel, sig, metas, size, a, b),
        (Elim::Project(a), Elim::Project(b)) => a == b,
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
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<StuckCase>,
    right: &Rc<StuckCase>,
) -> bool {
    // `consumed` не сравнивается сознательно. Кратность потребления - учётная
    // аннотация, а не часть вычисления: ι-редукция её не смотрит, и два
    // разбора, различающиеся только ею, дают одно значение. Сравнивай мы её,
    // мотив, собранный элаборацией с `r = 1`, перестал бы совпадать с
    // написанным при `r = ω`, то есть отвергались бы корректные программы.
    // Учёт кратностей при этом не страдает: вектор использований считает
    // `infer_case` по самому терму, а не через конвертируемость.
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
    fuel: u32,
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

        // Связывание - часть типа функции целиком: `(1 x : A) -> B` и
        // `(ω x : A) -> B` разные типы, и `{a : A} -> B` с `(a : A) -> B`
        // тоже. Видимость сравнивается по тому же доводу, что кратность:
        // считай их одним типом - и значение одного встало бы на место
        // другого, а вставка имплиситов перестала бы быть определённой.
        //
        // Row - на тех же правах (§3.4): `A -> {IO} B` и `A -> B` различаются,
        // потому что различается контракт применения. Формы сравниваются
        // синтаксически - метки в каноническом порядке, - а аргументы меток
        // конвертируемостью, как всякие термы.
        (
            Value::Pi(binder_a, _, domain_a, row_a, codomain_a),
            Value::Pi(binder_b, _, domain_b, row_b, codomain_b),
        ) => {
            binder_a == binder_b
                && row_a.same_shape(row_b)
                && row_a
                    .zip(row_b)
                    .all(|(a, b)| convertible_within(fuel, sig, metas, size, a, b))
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
    fuel: u32,
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

    use crate::row::{Label, Row};
    use crate::term::Binder;
    use crate::visibility::Visibility;

    use super::{UNFOLD_LIMIT, convertible};
    use crate::eval::eval;
    use crate::mult::Mult;
    use crate::term::Term;
    use crate::value::{Env, Lvl, Value};

    fn lam(body: Term) -> Term {
        Term::Lam(Mult::Many, "x".into(), Rc::new(body))
    }

    fn pi(mult: Mult, domain: Term, codomain: Term) -> Term {
        rowed(mult, Row::empty(), domain, codomain)
    }

    fn rowed(mult: Mult, row: Row<Term>, domain: Term, codomain: Term) -> Term {
        Term::Pi(
            Binder::explicit(mult),
            "x".into(),
            Rc::new(domain),
            row,
            Rc::new(codomain),
        )
    }

    fn effect(name: &str, arguments: Vec<Term>) -> Row<Term> {
        Row::new([Label {
            name: name.into(),
            arguments,
        }])
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

    /// Разворот определения не обязан принимать накопленный спайн.
    ///
    /// η-правило дописывает `Elim::App` к любой нейтрали, поэтому сравнение
    /// лямбды с `c : Type 1 = Type 0` доходит до попытки применить `Type 0` к
    /// аргументу. Значения здесь разных типов, и контракт функции - ответить
    /// `false`, а не упасть: раньше здесь была паника в `eval`.
    #[test]
    fn unfolding_a_non_function_is_a_refusal_not_a_panic() {
        let mut signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        signature
            .define(
                &mut metas,
                "c",
                Mult::Many,
                0,
                Term::universe(1),
                Some(Term::universe(0)),
            )
            .expect("определение корректно");
        let mut metas = crate::meta::Metas::default();

        let lambda = eval(&Env::default(), &lam(Term::var(0)));
        let constant = eval(&Env::default(), &Term::constant("c"));
        assert!(!convertible(&signature, &mut metas, 0, &lambda, &constant));
        assert!(
            !convertible(&signature, &mut metas, 0, &constant, &lambda),
            "и в обратную сторону"
        );
    }

    /// Топливо разворота тратится вдоль пути, а не на всё сравнение.
    ///
    /// Иначе конвертируемость зависела бы от ширины типа: `k` стрелок, каждая
    /// с одним редексом, признавались бы равными при `k <= 128` и разными
    /// дальше, то есть из `A ≡ A'` и `B ≡ B'` не следовало бы
    /// `(A -> B) ≡ (A' -> B')`.
    #[test]
    fn fuel_is_spent_along_a_path_not_across_the_width() {
        let mut signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        signature
            .postulate(&mut metas, "Nat", Mult::Many, 0, Term::universe(0))
            .expect("Nat корректен");
        signature
            .postulate(&mut metas, "zero", Mult::Many, 0, Term::constant("Nat"))
            .expect("zero корректен");
        signature
            .define(
                &mut metas,
                "id",
                Mult::Many,
                0,
                pi(Mult::Many, Term::constant("Nat"), Term::constant("Nat")),
                Some(lam(Term::var(0))),
            )
            .expect("id корректна");
        signature
            .postulate(
                &mut metas,
                "F",
                Mult::Many,
                0,
                pi(Mult::Zero, Term::constant("Nat"), Term::universe(0)),
            )
            .expect("F корректна");

        // `(0 _ : F n) -> … k раз … -> Type 0`, где слева `n` под редексом либо
        // уже сведённое. Каждая стрелка стоит ровно один разворот.
        let chain = |redex: bool| {
            let index = if redex {
                Term::constant("id").apply([Term::constant("zero")])
            } else {
                Term::constant("zero")
            };
            (0..UNFOLD_LIMIT + 8).fold(Term::universe(0), |tail, _| {
                Term::Pi(
                    Binder::explicit(Mult::Zero),
                    "_".into(),
                    Rc::new(Term::constant("F").apply([index.clone()])),
                    Row::empty(),
                    Rc::new(tail),
                )
            })
        };

        let mut metas = crate::meta::Metas::default();
        let left = eval(&Env::default(), &chain(true));
        let right = eval(&Env::default(), &chain(false));
        assert!(
            convertible(&signature, &mut metas, 0, &left, &right),
            "ширина типа не должна расходовать общий запас разворотов"
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

    #[test]
    fn a_row_is_part_of_the_function_type() {
        // §3.4: row описывает, что происходит при применении, и стоит на тех
        // же правах, что кратность. `A -> {IO} B` и `A -> B` - разные типы,
        // ровно как `(1 x : A) -> B` и `(ω x : A) -> B`.
        let pure = pi(Mult::Many, Term::universe(0), Term::universe(0));
        let effectful = rowed(
            Mult::Many,
            effect("IO", Vec::new()),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(!conv_in(0, &pure, &effectful), "чистая против эффектной");
        assert!(conv_in(0, &effectful, &effectful.clone()));
    }

    #[test]
    fn row_arguments_are_compared_up_to_conversion() {
        // Аргументы метки - обычные термы, поэтому сравниваются так же, как
        // всё прочее: с точностью до вычисления, а не по написанию.
        let redex = Term::App(Rc::new(lam(Term::var(0))), Rc::new(Term::universe(0)));
        let written = rowed(
            Mult::Many,
            effect("State", vec![Term::universe(0)]),
            Term::universe(0),
            Term::universe(0),
        );
        let computed = rowed(
            Mult::Many,
            effect("State", vec![redex]),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(
            conv_in(0, &written, &computed),
            "`(\\x -> x) Type 0` есть `Type 0`"
        );

        let other = rowed(
            Mult::Many,
            effect("State", vec![Term::universe(1)]),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(
            !conv_in(0, &written, &other),
            "разные аргументы - разные типы"
        );
    }

    #[test]
    fn labels_are_ordered_canonically_but_not_within_a_group() {
        // Группы упорядочены по имени, поэтому написание не влияет; порядок
        // внутри группы значим - внутренний хендлер перехватывает раньше
        // внешнего (§4.1), и переставить их значит изменить тип.
        let row = |labels: Vec<(&str, u32)>| {
            Row::new(labels.into_iter().map(|(name, level)| Label {
                name: name.into(),
                arguments: vec![Term::universe(level)],
            }))
        };
        let ty = |labels| {
            rowed(
                Mult::Many,
                row(labels),
                Term::universe(0),
                Term::universe(0),
            )
        };
        assert!(
            conv_in(
                0,
                &ty(vec![("A", 0), ("B", 1)]),
                &ty(vec![("B", 1), ("A", 0)])
            ),
            "порядок групп канонический"
        );
        assert!(
            !conv_in(
                0,
                &ty(vec![("A", 0), ("A", 1)]),
                &ty(vec![("A", 1), ("A", 0)])
            ),
            "порядок внутри группы значим"
        );
    }

    #[test]
    fn visibility_is_part_of_the_function_type() {
        // §4.1: `{a : A} -> B` и `(a : A) -> B` - разные типы. Считай их одним,
        // и значение одного встало бы на место другого, а вставка имплиситов
        // перестала бы быть определённой.
        let visible = |visibility| {
            Term::Pi(
                Binder {
                    mult: Mult::Many,
                    visibility,
                },
                "x".into(),
                Rc::new(Term::universe(0)),
                Row::empty(),
                Rc::new(Term::universe(0)),
            )
        };
        let explicit = visible(Visibility::Explicit);
        let implicit = visible(Visibility::Implicit);
        assert!(!conv_in(0, &explicit, &implicit));
        assert!(conv_in(0, &implicit, &implicit.clone()));
        assert_eq!(
            implicit.to_string(),
            "{ω x : Type 0} -> Type 0",
            "вид скобок несёт связывание"
        );
    }
}
