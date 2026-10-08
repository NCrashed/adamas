//! Проверка тотальности: структурная рекурсия и цикл по числу (§4.7, §9 Фаза 1).
//!
//! С появлением рекурсии ядро перестало гарантировать завершаемость само по
//! себе - это цена выбора `case` вместо рекурсоров (decision log 2026-08-24).
//! Держат её здесь, и результат нужен ядру в двух местах:
//!
//! - **δ-разворот** ([`crate::conv`]) нетотальное определение не трогает вовсе,
//!   поэтому проверка конвертируемости завершается независимо от того, что
//!   пользователь написал;
//! - **стёртый фрагмент** ([`crate::check`]) нетотальное определение не
//!   принимает: §4.7 запрещает нетотальным функциям участвовать в
//!   доказательствах, а типы - тот же фрагмент.
//!
//! # Что считается уменьшением
//!
//! Параметры определения нумеруются, и каждому связыванию сопоставляется
//! "размер" - пара "номер параметра, сколько шагов вниз". Разбор по значению
//! размера `(i, d)` даёт полям размер `(i, d+1)`: поле конструктора строго
//! меньше разобранного значения. Рекурсивный вызов засчитывается уменьшающимся
//! по позиции `k`, если его `k`-й аргумент имеет размер `(k, d)` при `d > 0`.
//!
//! Шагом вниз считается не только разбор: на примитиве им служит проверенное
//! вычитание - см. ниже. Смешаться две меры не могут, их разводит тип: у
//! примитива нет конструкторов, у семейства нет ширины.
//!
//! Определение тотально, если такая позиция `k` **одна на все** рекурсивные
//! вызовы. Позиция ищется перебором - объявлять её, как `{struct n}` в Coq,
//! незачем.
//!
//! # Убывание по примитиву, и почему ему нужен пол
//!
//! Цикл по числу (`countdown n = countdown (subUInt64 n 1)`) конструкторов не
//! разбирает, и структурной меры у него нет вовсе. Мерой служит **само
//! значение**, но одного «вычли - стало меньше» здесь мало, и это не
//! осторожность: арифметика **заворачивается** по ширине типа (§4.3, §10 вопрос
//! 151), поэтому `subUInt8 1 2` даёт 255, а не отказ. Числу поэтому нужен пол,
//! и складывается он из двух источников сразу.
//!
//! **Тип** даёт нижнюю границу: беззнаковое значение есть натуральное число, и
//! мера ограничена нулём снизу. У знакового такой границы нет.
//!
//! **Литеральные паттерны** не дают вычитанию пол перешагнуть: ветвь `False`
//! разбора `eqT x k` знает `x != k` (в эту форму элаборация и переводит
//! литеральный паттерн, [`crate::pattern`]), и когда исключены все `0 .. step`,
//! верно `x >= step` - вычитание идёт без заворачивания, результат строго
//! меньше, а число шагов не больше `x / step`.
//!
//! Ни один источник в одиночку не работает, и оба измерены прогоном
//! 2026-09-14. Знаковый `countdown (subInt8 n 1)` при базе `0`
//! **завершается** - 256 шагов через `-128` и `127` к нулю, - и всё равно
//! отвергается: предъявимой меры у него нет, а оценка в 2⁶⁴ шагов для
//! δ-разворота от расходимости неотличима. Беззнаковый `subUInt8 n 2` при базе
//! `0` от нечётного `n` **расходится** по-настоящему - заворачивается и
//! остаётся нечётным навсегда, - и его отвергает покрытие: исключён `0`, а
//! нужны `0` и `1`.
//!
//! Пол читается и с `if`: он элаборируется разбором по связыванию, и
//! сравнение уезжает в значение `let` - факт берётся оттуда (§10 вопрос
//! 227). Оператор `n - 1` прелюдии приходит вызовом метода через словарь и
//! сводится к примитиву ограниченной редукцией; вычитанием читается и
//! `add x (neg k)`, во что оператор определён.
//!
//! # Шаг вверх
//!
//! Цикл `if i < n then … (i + 1) n` меряется `n - i`: ветвь `True` разбора
//! `ltT i n` знает `i < n`, сложение с единицей тогда не заворачивается, мера
//! строго убывает и ограничена нулём - при любом знаке типа, потому что граница
//! берётся из сравнения. Вызов засчитывается, только если `n` передан
//! неизменным; шаг - ровно единица.
//!
//! # Разбор под применением
//!
//! Ветвь связывает лямбдами не только поля: элаборация клауз выносит соседние
//! аргументы в мотив и применяет разбор обратно к ним (convoy - иначе тип
//! соседа не уточнить). Лямбды сверх полей связывают ровно эти аргументы, и
//! размеры им раздаются от применения. Без раздачи убывание терялось бы на
//! каждом аргументе, прошедшем через уточнение, - то есть ровно на тех, ради
//! которых пишут индексированные семейства.
//!
//! # Взаимная рекурсия
//!
//! `mutual` (§4.8) делает её выразимой, поэтому вызов соседа по циклу считается
//! рекурсивным наравне с самовызовом. Позиция убывания при этом у каждого члена
//! своя - у `even : Nat -> Bool` нулевой аргумент, у `odd : {0 a : Type} -> a
//! -> Nat -> Bool` второй, - но согласованная: вызов из `A` в `B` засчитывается,
//! когда аргумент на позиции `B` произошёл разбором от параметра на позиции `A`.
//! Рекурсией считается вызов **по циклу**, а не всякое упоминание соседа:
//! словарь инстанса называет свои методы, и убывать ему не по чему.
//!
//! # Что не покрыто
//!
//! Лексикографический порядок (`ack`), well-founded рекурсия с явной мерой,
//! шаг вверх больше единицы и знаковый счёт вниз.
//! Проверка консервативна: отвергает часть завершающихся определений, но не
//! пропускает расходящиеся.
//!
//! # Рекурсия через словарь
//!
//! Вердикт считается по **зонканному** телу: словарь метода инстанса стоит в
//! теле дыркой, а `Meta` здесь инертна - ни вызовом, ни носителем размера, -
//! поэтому до зонканья рекурсия метода через словарь не видна вовсе (§10
//! вопрос 134). После зонканья она приходит спайном `spin {словарь} n`, где
//! имя головы - метод-проекция, а не член группы. Связь «проекция → член»
//! восстанавливает [`member_call`] - ограниченная головная редукция: δ только
//! уже-тотальных определений вне группы, β, проекция из литерала записи. Ядру
//! она видна как редукция, знания о классах не требует, а завершается по тому
//! же инварианту, что δ-разворот в [`crate::conv`]: нетотальное не
//! разворачивается, у членов группы вердикта ещё нет - и они не
//! разворачиваются тоже.
//!
//! Запись-словарь, ушедшая аргументом в чужую функцию, редукцией не
//! разбирается и остаётся голым именем члена - вызовом без позиций, то есть
//! нетотальным. Это консервативно верно: свой словарь, отданный неизвестной
//! функции, и есть незащищённый самовызов.

use std::rc::Rc;

use crate::meta::{Metas, zonk_term};
use crate::mult::Mult;
use crate::prim::{Prim, PrimCmp, PrimOp, PrimTy};
use crate::sig::{Definition, Signature};
use crate::term::{Case, Index, Name, Term, spine};
use crate::value::{Env, Head, Lvl, Value};

/// Размер связывания относительно параметров определения.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Size {
    /// Номер параметра, от которого связывание произошло.
    argument: usize,
    /// Сколько разборов отделяет его от самого параметра.
    depth: u32,
    /// Позиция параметра-границы у шага вверх: `upto (i + 1) n` под `i < n`
    /// убывает мерой `n - i`, только если граница `n` передана неизменной
    /// (§10 вопрос 227). `None` - обычное убывание вниз.
    bound: Option<usize>,
}

/// Завершается ли определение на всех входах.
///
/// Постулат тотален: тела нет, разворачивать нечего. Определение без
/// рекурсивных вызовов тотально, если тотально всё, что оно зовёт.
///
/// `group` - имена всех членов объявляемой группы, включая само `name`. Вызов
/// соседа по группе считается рекурсивным наравне с самовызовом: `ping`, зовущий
/// `pong`, зовущий `ping`, расходится ровно так же, как `ping`, зовущий себя, а
/// проверка, знающая только своё имя, не видела в такой паре ни одного вызова и
/// объявляла её тотальной. Позиция убывания при этом ищется у каждого члена
/// своя: убывает ли `ping` по первому аргументу, а `pong` по второму, для
/// завершаемости безразлично - важно, что каждый вызов группы убывает.
#[must_use]
pub fn is_total(
    signature: &Signature,
    metas: &Metas,
    name: &Name,
    group: &[Name],
    undecided: &[Name],
    definition: &Definition,
) -> bool {
    let Some(body) = &definition.body else {
        return true;
    };
    // По зонканному: словарь метода инстанса стоит в теле дыркой, и до
    // подстановки решения рекурсия через него не видна вовсе (§10 вопрос 134).
    let body = zonk_term(metas, body);

    // Тотальность распространяется по графу вызовов (§4.7). Отдельного обхода
    // это не требует: определения добавляются по одному и каждое уже несёт свой
    // вердикт, поэтому достаточно посмотреть на непосредственно вызванные.
    // Внутри группы вердикта ещё нет ни у кого - его считает неподвижная точка
    // вызывающего, - и понижение соседа доедет сюда её следующим проходом.
    if calls_a_partial_definition(signature, name, &body) {
        return false;
    }

    if group.len() > 1 {
        return cycle_decreases(signature, metas, group, undecided);
    }

    let (arity, calls) = collected(signature, group, undecided, &body);
    calls.is_empty()
        || (0..arity).any(|position| {
            calls.iter().all(|(_, sizes)| {
                matches!(
                    sizes.get(position),
                    Some(&Some(Size { argument, depth, bound }))
                        if argument == position
                            && depth > 0
                            && bound.is_none_or(|at| unchanged(sizes, at))
                )
            })
        })
}

/// Арность тела и рекурсивные вызовы в нём.
fn collected(
    signature: &Signature,
    group: &[Name],
    undecided: &[Name],
    body: &Term,
) -> (usize, Vec<Call>) {
    let mut walk = Walk {
        signature,
        group,
        undecided,
        calls: Vec::new(),
        apart: Vec::new(),
        bound: Vec::new(),
        below: Vec::new(),
        bound_below: Vec::new(),
    };
    let mut sizes = Vec::new();
    let arity = walk.parameters(&mut sizes, body);
    (arity, walk.calls)
}

/// Убывает ли **каждый** вызов внутри цикла взаимной рекурсии.
///
/// Одной позиции на всех не хватает: у `ping : Nat -> Bool` убывает нулевой
/// аргумент, а у `pong : {0 a : Type} -> a -> Nat -> Bool` - второй, и мерить
/// их одним числом нечем. Позиция поэтому ищется **каждому члену своя**, но
/// согласованно: вызов из `A` в `B` засчитывается, если аргумент, стоящий у
/// него на позиции `B`, произошёл разбором от параметра на позиции `A`.
/// Тогда по любому обходу цикла величина строго убывает, а значит цикл
/// конечен.
///
/// Позиции подбираются перебором - как и у одиночного определения, объявлять
/// их незачем. Названная граница: перебор ограничен [`SEARCH_LIMIT`]
/// сочетаниями, и группа, у которой их больше, отвергается как непроверенная.
/// Вердикт один на весь цикл: завершаемость его членов - общее свойство.
fn cycle_decreases(
    signature: &Signature,
    metas: &Metas,
    cycle: &[Name],
    undecided: &[Name],
) -> bool {
    let mut members = Vec::with_capacity(cycle.len());
    for name in cycle {
        let Some(body) = signature.lookup(name).and_then(|it| it.body.as_ref()) else {
            return false;
        };
        members.push(collected(
            signature,
            cycle,
            undecided,
            &zonk_term(metas, body),
        ));
    }
    let combinations = members
        .iter()
        .try_fold(1usize, |count, (arity, _)| count.checked_mul(*arity))
        .unwrap_or(usize::MAX);
    if combinations == 0 || combinations > SEARCH_LIMIT {
        return false;
    }
    let mut positions = vec![0usize; members.len()];
    for _ in 0..combinations {
        if agrees(&members, &positions) {
            return true;
        }
        for (at, position) in positions.iter_mut().enumerate() {
            *position += 1;
            if *position < members[at].0 {
                break;
            }
            *position = 0;
        }
    }
    false
}

/// Убывает ли каждый вызов при таком назначении позиций.
fn agrees(members: &[(usize, Vec<Call>)], positions: &[usize]) -> bool {
    members.iter().enumerate().all(|(caller, (_, calls))| {
        calls.iter().all(|(callee, sizes)| {
            matches!(
                sizes.get(positions[*callee]),
                Some(&Some(Size { argument, depth, bound: None }))
                    if argument == positions[caller] && depth > 0
            )
        })
    })
}

/// Сколько назначений позиций разрешено перебрать у одной группы.
const SEARCH_LIMIT: usize = 4096;

/// Имена из `group`, которые тело зовёт напрямую.
///
/// Нужно вызывающему, чтобы построить граф вызовов внутри группы: рекурсией
/// считается вызов по **циклу**, а не всякое упоминание соседа. Словарь
/// инстанса называет свои методы, методы словарь не зовут - цикла нет, и
/// требовать от словаря убывания было бы отказом ни за что.
///
/// Терм ожидается **зонканным** - как и у [`is_total`]: вызов через словарь
/// инстанса до подстановки решения не виден. Вызов через метод-проекцию
/// восстанавливает та же редукция, что у обхода размеров, - [`member_call`];
/// две половины проверки обязаны видеть один и тот же граф.
pub(crate) fn calls_within(signature: &Signature, group: &[Name], term: &Term) -> Vec<Name> {
    let mut found = Vec::new();
    collect_calls(signature, group, 0, term, &mut found);
    found
}

fn collect_calls(
    signature: &Signature,
    group: &[Name],
    depth: usize,
    term: &Term,
    found: &mut Vec<Name>,
) {
    let mut recur = |at: usize, inner: &Term| collect_calls(signature, group, at, inner, found);
    match term {
        Term::Var(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Prim(_)
        | Term::Meta(_) => {}
        Term::Const(other, _, _) => {
            if group.contains(other) && !found.contains(other) {
                found.push(Rc::clone(other));
            }
        }
        // Поля закрытой записи - телескоп: тип поля живёт под связываниями
        // предыдущих (§4.2), и глубина растёт по одному на поле.
        Term::Record(fields) | Term::Row(fields) => {
            for (at, field) in fields.iter().enumerate() {
                recur(depth + at, &field.ty);
            }
            if let Some(tail) = fields.tail.as_ref() {
                recur(depth, tail);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                recur(depth, value);
            }
        }
        Term::With(base, fields) => {
            recur(depth, base);
            for (_, value) in fields.iter() {
                recur(depth, value);
            }
        }
        Term::Project(record, _) => recur(depth, record),
        Term::Lam(_, _, body) => recur(depth + 1, body),
        Term::App(..) => {
            // Спайн разбирается целиком: вызов члена группы через
            // метод-проекцию виден только редукции, а ей нужен весь спайн.
            // У calls_within объявляемая группа и есть множество без
            // вердикта: граф зовётся до неподвижной точки, когда не решён
            // никто.
            if let Some(reduced) = member_call(signature, group, group, depth, term) {
                // Редукция потребила словарь: имена внутри съеденной записи
                // стояли полями, а не вызовами, и в граф не идут.
                recur(depth, &reduced);
                return;
            }
            let (head, arguments) = spine(term);
            recur(depth, head);
            for argument in arguments {
                recur(depth, argument);
            }
        }
        Term::Pi(_, _, domain, row, codomain) => {
            recur(depth, domain);
            recur(depth + 1, codomain);
            // Row стоит под связыванием стрелки наравне с кодоменом.
            for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                recur(depth + 1, argument);
            }
        }
        Term::Let(_, _, ty, value, body) => {
            recur(depth, ty);
            recur(depth, value);
            recur(depth + 1, body);
        }
        Term::Split(split) => {
            recur(depth, &split.scrutinee);
            recur(depth, &split.motive);
            recur(depth, &split.body);
        }
        Term::Case(case) => {
            recur(depth, &case.scrutinee);
            recur(depth, &case.motive);
            for branch in &case.branches {
                recur(depth, &branch.body);
            }
        }
    }
}

/// Спайн после редукции, годный на замену написанному, - или ничего.
///
/// Восстанавливает вызов члена инстанса из вызова метода-проекции: зонканное
/// тело зовёт `spin {уровень} {словарь} n`, где словарь - β-редекс над
/// литералом записи, и δ проекции, β и проекция из литерала дают
/// `Loop#Nat.spin n` - имя **и позиции аргументов** одним движением (§10
/// вопрос 134).
///
/// Редукция останавливается с ответом в двух случаях: голова редукта - имя из
/// `group` (искомый вызов), либо имена группы из редукта **исчезли** - словарь
/// потреблён проекцией, и полей-соседей, которые сырой обход счёл бы вызовами,
/// в нём больше нет. Так дефолтный метод, зовущий соседа (`atMost x y = below
/// x y`), не расплачивается за собственный словарь.
///
/// Шаги ограничены: δ разворачивает только тотальное (ворота - те же, что у
/// [`crate::conv::unfold`]) и только вне `undecided` - у членов объявляемой
/// группы вердикта ещё нет, и тело соседа разворачивать нельзя. β и проекцию
/// делает само вычисление, а число δ-шагов режет топливо - как у `whnf`,
/// потому что на открытых аргументах расходятся и тотальные определения. Не
/// дошла редукция ни до одного из двух исходов - ответ пуст, и вызывающий
/// обходит спайн как написан.
fn member_call(
    signature: &Signature,
    group: &[Name],
    undecided: &[Name],
    depth: usize,
    term: &Term,
) -> Option<Term> {
    // Голова уже из группы - вызов виден и без редукции.
    let (head, _) = spine(term);
    if matches!(head, Term::Const(name, _, _) if group.contains(name)) {
        return None;
    }
    // Дёшево и почти всегда: редукция может обнажить только имя, уже стоящее
    // в спайне синтаксически, - всё, что объявлено раньше группы, её имён не
    // знает. Нет имени - нет и вызова.
    if !mentions_group(group, term) {
        return None;
    }
    // Вычисление паникует на индексе за пределами окружения, а глубина здесь
    // считана обходом; расхождение - повод отступить, не упасть.
    if !closed_under(depth, term) {
        return None;
    }
    let width = u32::try_from(depth).ok()?;
    let mut env = Env::default();
    for level in 0..width {
        env = env.extend(Value::var(Lvl(level)));
    }
    let mut current = crate::eval::eval(&env, term);
    for _ in 0..REDUCTION_LIMIT {
        let Value::Neutral(Head::Global(name, ..), _) = &*current else {
            return None;
        };
        if group.iter().any(|it| it == name) {
            let quoted = crate::eval::quote(width, &current);
            // Прогресса нет - редукт совпал с написанным: имя группы стоит
            // головой **под проекцией** (`член.same x`), и вычислению снять
            // её нечем. Ответить таким редуктом значило бы зациклить обход:
            // вызывающий пускает ответ тем же путём (§10 вопрос 163, найдено
            // на специализации функтора). Спайн обходится как написан.
            if quoted == *term {
                return None;
            }
            return Some(quoted);
        }
        let quoted = crate::eval::quote(width, &current);
        if !mentions_group(group, &quoted) {
            return Some(quoted);
        }
        if undecided.iter().any(|it| it == name) {
            return None;
        }
        current = crate::conv::unfold(signature, &current)?;
    }
    None
}

/// Написанное, сведённое к примитиву: `Prelude.- UInt64 Sub#UInt64 n 1` - к
/// `subUInt64 n 1` (§10 вопрос 227).
///
/// Та же ограниченная редукция, что у [`member_call`]: δ только тотального и
/// только вне `undecided`, β и проекцию делает вычисление, число δ-шагов режет
/// топливо. Ответ - только если голова стала примитивом; иначе пусто, и мера
/// читается с написанного.
fn primitive_of(
    signature: &Signature,
    undecided: &[Name],
    depth: usize,
    term: &Term,
) -> Option<Term> {
    if !matches!(spine(term).0, Term::Const(..)) || !closed_under(depth, term) {
        return None;
    }
    let width = u32::try_from(depth).ok()?;
    let mut env = Env::default();
    for level in 0..width {
        env = env.extend(Value::var(Lvl(level)));
    }
    let mut current = crate::eval::eval(&env, term);
    for _ in 0..REDUCTION_LIMIT {
        match &*current {
            // Аргументы примитива сводятся тоже: у `add x (neg 1)` второй
            // ещё вызов, а мера ждёт литерал шага.
            Value::Neutral(head @ (Head::Prim(..) | Head::Cmp(..)), spine) => {
                let mut built = match head {
                    Head::Prim(op, ty) => Term::Prim(Prim::Op(*op, *ty)),
                    Head::Cmp(op, ty) => Term::Prim(Prim::Cmp(*op, *ty)),
                    _ => return None,
                };
                for elim in spine {
                    let crate::value::Elim::App(argument) = elim else {
                        return None;
                    };
                    let argument = crate::conv::whnf(signature, argument);
                    built = Term::App(
                        Rc::new(built),
                        Rc::new(crate::eval::quote(width, &argument)),
                    );
                }
                return Some(built);
            }
            Value::Neutral(Head::Global(name, ..), _) if !undecided.contains(name) => {
                current = crate::conv::unfold(signature, &current)?;
            }
            _ => return None,
        }
    }
    None
}

/// Сколько δ-шагов разрешено редукции одного спайна.
const REDUCTION_LIMIT: u32 = 128;

/// Стоит ли имя группы в терме синтаксически.
fn mentions_group(group: &[Name], term: &Term) -> bool {
    let recur = |inner: &Term| mentions_group(group, inner);
    match term {
        Term::Var(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Prim(_)
        | Term::Meta(_) => false,
        Term::Const(other, _, _) => group.contains(other),
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().any(|field| recur(&field.ty))
                || fields.tail.as_ref().is_some_and(|tail| recur(tail))
        }
        Term::Object(fields) => fields.iter().any(|(_, value)| recur(value)),
        Term::With(base, fields) => recur(base) || fields.iter().any(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || recur(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(recur)
        }
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || recur(body),
        Term::Split(split) => recur(&split.scrutinee) || recur(&split.motive) || recur(&split.body),
        Term::Case(case) => {
            recur(&case.scrutinee)
                || recur(&case.motive)
                || case.branches.iter().any(|branch| recur(&branch.body))
        }
    }
}

/// Указывают ли все индексы терма внутрь `depth` связываний.
fn closed_under(depth: usize, term: &Term) -> bool {
    let recur = |at: usize, inner: &Term| closed_under(at, inner);
    match term {
        Term::Var(Index(index)) => (*index as usize) < depth,
        Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Meta(_)
        | Term::Prim(_)
        | Term::Const(..) => true,
        Term::Record(fields) | Term::Row(fields) => {
            fields
                .iter()
                .enumerate()
                .all(|(at, field)| recur(depth + at, &field.ty))
                && fields.tail.as_ref().is_none_or(|tail| recur(depth, tail))
        }
        Term::Object(fields) => fields.iter().all(|(_, value)| recur(depth, value)),
        Term::With(base, fields) => {
            recur(depth, base) && fields.iter().all(|(_, value)| recur(depth, value))
        }
        Term::Project(record, _) => recur(depth, record),
        Term::Lam(_, _, body) => recur(depth + 1, body),
        Term::App(callee, argument) => recur(depth, callee) && recur(depth, argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(depth, domain)
                && recur(depth + 1, codomain)
                // Row стоит под связыванием стрелки наравне с кодоменом.
                && row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .all(|argument| recur(depth + 1, argument))
        }
        Term::Let(_, _, ty, value, body) => {
            recur(depth, ty) && recur(depth, value) && recur(depth + 1, body)
        }
        Term::Split(split) => {
            recur(depth, &split.scrutinee)
                && recur(depth, &split.motive)
                && recur(depth, &split.body)
        }
        Term::Case(case) => {
            recur(depth, &case.scrutinee)
                && recur(depth, &case.motive)
                && case
                    .branches
                    .iter()
                    .all(|branch| recur(depth, &branch.body))
        }
    }
}

/// Зовёт ли тело хоть одно нетотальное определение.
///
/// Собственное имя пропускается: рекурсию разбирает структурная проверка, а на
/// этом шаге определение ещё числится тотальным по умолчанию.
fn calls_a_partial_definition(signature: &Signature, name: &Name, term: &Term) -> bool {
    let recur = |inner| calls_a_partial_definition(signature, name, inner);
    match term {
        Term::Var(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Prim(_)
        | Term::Meta(_) => false,
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().any(|field| recur(&field.ty))
                || fields.tail.as_ref().is_some_and(|tail| recur(tail))
        }
        Term::Object(fields) => fields.iter().any(|(_, value)| recur(value)),
        Term::With(base, fields) => recur(base) || fields.iter().any(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Const(other, _, _) => {
            other != name && signature.lookup(other).is_some_and(|found| !found.total)
        }
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || recur(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(recur)
        }
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || recur(body),
        Term::Split(split) => recur(&split.scrutinee) || recur(&split.motive) || recur(&split.body),
        Term::Case(case) => {
            recur(&case.scrutinee)
                || recur(&case.motive)
                || case.branches.iter().any(|branch| recur(&branch.body))
        }
    }
}

/// Обход тела с накоплением рекурсивных вызовов.
/// Рекурсивный вызов: кого из цикла зовут и с какими размерами аргументов.
type Call = (usize, Vec<Option<Size>>);

/// Связывание, о котором известно, что оно **не равно** этому литералу.
///
/// Ставит такой факт ветвь `False` разбора по `eqT x k` - той самой форме, в
/// которую элаборация переводит литеральный паттерн ([`crate::pattern`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Apart {
    /// Уровень связывания. Уровень, а не индекс: под ветвью бывают свои
    /// связывания, и индекс от них уехал бы, а уровень нет.
    level: usize,
    /// Тип, в котором записан литерал.
    ty: PrimTy,
    /// Биты литерала.
    bits: u64,
}

/// Факт «связывание строго меньше другого» - ветвь `True` разбора `ltT x y`.
/// Уровни, а не индексы: под ветвью бывают свои связывания.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Below {
    /// Уровень меньшего.
    level: usize,
    /// Уровень границы.
    limit: usize,
}

struct Walk<'a> {
    signature: &'a Signature,
    /// Имена, вызов которых считается рекурсивным: своё и соседи по циклу.
    group: &'a [Name],
    /// Имена без вердикта - вся объявляемая группа; редукция их не трогает.
    undecided: &'a [Name],
    /// Вызовы в порядке обхода.
    calls: Vec<Call>,
    /// Литералы, которых связывание заведомо не равно, - пол меры на примитиве.
    ///
    /// Стек: факт живёт ровно под своей ветвью. Соседняя ветвь его не видит, и
    /// это существенно - в ветви `True` аргумент как раз **равен** литералу.
    apart: Vec<Apart>,
    /// Факты, записанные в значении `let`: `if n == 0` элаборируется связыванием
    /// сравнения и разбором по нему, и пол ветви `False` надо брать оттуда (§10
    /// вопрос 227). Пара - уровень связывания `let` и факт о разбираемом.
    bound: Vec<(usize, Apart)>,
    /// Факты «строго меньше» - ветвь `True` разбора `ltT i n`: у шага вверх они
    /// и есть граница меры `n - i` (§10 вопрос 227).
    below: Vec<Below>,
    /// Те же факты, записанные в значении `let` - так приходит `if i < n`.
    bound_below: Vec<(usize, Below)>,
}

impl Walk<'_> {
    /// Снимает лямбды-параметры, приписывая каждой её номер, и обходит тело.
    ///
    /// Возвращает число снятых параметров - только по ним и ищется уменьшение.
    fn parameters(&mut self, sizes: &mut Vec<Option<Size>>, term: &Term) -> usize {
        match term {
            Term::Lam(_, _, body) => {
                sizes.push(Some(Size {
                    argument: sizes.len(),
                    depth: 0,
                    bound: None,
                }));
                self.parameters(sizes, body)
            }
            other => {
                let arity = sizes.len();
                self.term(sizes, other);
                arity
            }
        }
    }

    /// Размер связывания, на которое указывает индекс.
    fn size(sizes: &[Option<Size>], term: &Term) -> Option<Size> {
        let level = Self::level(sizes, term)?;
        *sizes.get(level)?
    }

    /// Уровень связывания, на которое указывает индекс.
    fn level(sizes: &[Option<Size>], term: &Term) -> Option<usize> {
        let Term::Var(Index(index)) = term else {
            return None;
        };
        sizes.len().checked_sub(*index as usize + 1)
    }

    /// Размер аргумента рекурсивного вызова: разбор либо убывание по примитиву.
    fn measured(&self, sizes: &[Option<Size>], term: &Term) -> Option<Size> {
        Self::size(sizes, term)
            .or_else(|| self.descended(sizes, term))
            .or_else(|| self.ascended(sizes, term))
    }

    /// Убывание по примитиву: `subT x k` при беззнаковом `T` и известном
    /// `x >= k`.
    ///
    /// # Почему одного «стало меньше» мало
    ///
    /// Арифметика заворачивается по ширине типа (§4.3, §10 вопрос 151), а
    /// значит «вычли - уменьшилось» на примитиве **неверно**: `subUInt8 1 2`
    /// даёт 255. Структурному разбору такой оговорки не нужно - поле
    /// конструктора меньше по построению и дна не имеет, - а числу нужен пол,
    /// и берётся он из двух источников сразу.
    ///
    /// **Тип** даёт нижнюю границу: у беззнакового значение есть натуральное
    /// число, и мера «само значение» ограничена нулём снизу. У знакового такой
    /// границы нет, и потому знаковый здесь отвергается.
    ///
    /// **Литеральные паттерны** дают то, что вычитание пола не перешагнёт:
    /// ветвь `False` каждого `eqT x k` знает `x != k`, и если исключены все
    /// `0 .. step`, то `x >= step`, вычитание идёт без заворачивания, а
    /// результат строго меньше. Мера убывает и снизу ограничена - это и есть
    /// завершаемость, с оценкой в `x / step` шагов.
    ///
    /// # Что отвергается и почему именно так
    ///
    /// Знаковый `countdown n = countdown (subInt8 n 1)` при базе `0`
    /// **завершается** - счёт проходит `-128`, заворачивается к `127` и
    /// доходит до нуля за 256 шагов (замерено 2026-09-14). Отвергается он всё
    /// равно, и это не осторожность впустую: у такого счёта нет предъявимой
    /// меры, а оценка в 2⁶⁴ шагов для δ-разворота ([`crate::conv`]) от
    /// расходимости неотличима - ради него вердикт и считается.
    ///
    /// Шаг мимо пола расходится по-настоящему: `countdown n = countdown
    /// (subUInt8 n 2)` при базе `0` от нечётного `n` заворачивается и остаётся
    /// нечётным навсегда (замерено тем же прогоном - зависает). Его отвергает
    /// покрытие: исключён `0`, а нужны `0` и `1`.
    fn descended(&self, sizes: &[Option<Size>], term: &Term) -> Option<Size> {
        // Оператор `n - 1` прелюдии приходит вызовом метода через словарь, а
        // мера читается с примитива: написанное сводится к нему ограниченной
        // редукцией, как вызов члена группы (§10 вопрос 227).
        let reduced = primitive_of(self.signature, self.undecided, sizes.len(), term);
        let term = reduced.as_ref().unwrap_or(term);
        let (head, arguments) = spine(term);
        let Term::Prim(Prim::Op(op @ (PrimOp::Sub | PrimOp::Add), ty)) = head else {
            return None;
        };
        if ty.signed() || ty.floating() {
            return None;
        }
        let [subject, written] = arguments[..] else {
            return None;
        };
        let Term::Prim(Prim::Lit(_, written)) = written else {
            return None;
        };
        // `x - k` прелюдии есть `add x (neg k)`: сложение с дополнением шага
        // по ширине типа. Шаг поэтому - литерал вычитания либо дополнение
        // литерала сложения; у настоящего сложения (`x + 1`) дополнение
        // огромно, и его отвергает граница ниже.
        let step = &match op {
            PrimOp::Add => ty.ones() & written.wrapping_neg(),
            _ => *written,
        };
        // Ноль не убывает, а шире исключённого пол не бывает: перебор снизу
        // ограничен числом известных фактов, а не значением литерала.
        if *step == 0 || *step > self.apart.len() as u64 {
            return None;
        }
        let Size {
            argument, depth, ..
        } = Self::size(sizes, subject)?;
        let level = Self::level(sizes, subject)?;
        let excluded = |bits| {
            self.apart.contains(&Apart {
                level,
                ty: *ty,
                bits,
            })
        };
        if !(0..*step).all(excluded) {
            return None;
        }
        Some(Size {
            argument,
            depth: depth + 1,
            bound: None,
        })
    }

    /// Шаг вверх: `addT i 1` под фактом `i < n`, где `n` - параметр
    /// (§10 вопрос 227).
    ///
    /// Мера - `n - i`: под `i < n` сложение с единицей не заворачивается
    /// (`i + 1 <= n`, а `n` - представимое число), мера строго убывает и снизу
    /// ограничена нулём. Знак типа здесь не важен - граница берётся из
    /// сравнения, а не из типа. Шаг - ровно единица: больший шаг под `i < n`
    /// вправе перешагнуть границу и завернуться. Вызов засчитывается, только
    /// если граница передана неизменной - это проверяет [`unchanged`].
    fn ascended(&self, sizes: &[Option<Size>], term: &Term) -> Option<Size> {
        let reduced = primitive_of(self.signature, self.undecided, sizes.len(), term)?;
        let (head, arguments) = spine(&reduced);
        let Term::Prim(Prim::Op(PrimOp::Add, ty)) = head else {
            return None;
        };
        if ty.floating() {
            return None;
        }
        let ([subject, Term::Prim(Prim::Lit(_, 1))] | [Term::Prim(Prim::Lit(_, 1)), subject]) =
            arguments[..]
        else {
            return None;
        };
        let Size {
            argument,
            depth: 0,
            bound: None,
        } = Self::size(sizes, subject)?
        else {
            return None;
        };
        let level = Self::level(sizes, subject)?;
        self.below.iter().rev().find_map(|fact| {
            if fact.level != level {
                return None;
            }
            let limit = (*sizes.get(fact.limit)?)?;
            (limit.depth == 0 && limit.bound.is_none()).then_some(Size {
                argument,
                depth: 1,
                bound: Some(limit.argument),
            })
        })
    }

    /// Факт «строго меньше», если разбираемое - `ltT x y` над связываниями.
    fn less(sizes: &[Option<Size>], term: &Term) -> Option<Below> {
        let (head, arguments) = spine(term);
        let Term::Prim(Prim::Cmp(PrimCmp::Lt, ty)) = head else {
            return None;
        };
        if ty.floating() {
            return None;
        }
        let [left, right] = arguments[..] else {
            return None;
        };
        Some(Below {
            level: Self::level(sizes, left)?,
            limit: Self::level(sizes, right)?,
        })
    }

    /// Факт «связывание не равно литералу», если разбираемое - сравнение с ним.
    ///
    /// Форма ровно та, которую строит элаборация литерального паттерна:
    /// `eqT x k`. Порядок операндов берётся любой - равенство симметрично, а
    /// написанное руками `case eqUInt64 0 n of` иначе теряло бы пол ни за что.
    fn compared(sizes: &[Option<Size>], term: &Term) -> Option<Apart> {
        let (head, arguments) = spine(term);
        let Term::Prim(Prim::Cmp(PrimCmp::Eq, ty)) = head else {
            return None;
        };
        let [left, right] = arguments[..] else {
            return None;
        };
        let named = |subject: &Term, literal: &Term| match literal {
            Term::Prim(Prim::Lit(_, bits)) => Some(Apart {
                level: Self::level(sizes, subject)?,
                ty: *ty,
                bits: *bits,
            }),
            _ => None,
        };
        named(left, right).or_else(|| named(right, left))
    }

    fn term(&mut self, sizes: &mut Vec<Option<Size>>, term: &Term) {
        match term {
            // Дырка размера не несёт и вызовом не является: она замкнута, а
            // зависимость от контекста выражена применениями вокруг неё.
            Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Prim(_)
            | Term::Meta(_) => {}

            // Запись размера не несёт: поля - типы и значения, а уменьшение
            // считается по разбору. Обход нужен, чтобы вызовы внутри нашлись.
            // Поля - телескоп: тип поля живёт под связываниями предыдущих, и
            // глубина растёт по одному на поле, размера не получая.
            Term::Record(fields) | Term::Row(fields) => {
                for (at, field) in fields.iter().enumerate() {
                    let before = sizes.len();
                    sizes.extend(std::iter::repeat_n(None, at));
                    self.term(sizes, &field.ty);
                    sizes.truncate(before);
                }
                // Хвост - обычный терм на исходной глубине: вызов в нём
                // обязан найтись так же, как в поле.
                if let Some(tail) = &fields.tail {
                    self.term(sizes, tail);
                }
            }
            Term::Object(fields) => {
                for (_, value) in fields.iter() {
                    self.term(sizes, value);
                }
            }
            Term::With(base, fields) => {
                self.term(sizes, base);
                for (_, value) in fields.iter() {
                    self.term(sizes, value);
                }
            }
            Term::Project(record, _) => self.term(sizes, record),

            // Голое имя без аргументов - тоже вызов, просто без единой
            // позиции, по которой можно было бы уменьшаться.
            Term::Const(other, _, _) => {
                if let Some(callee) = self.group.iter().position(|it| it == other) {
                    self.calls.push((callee, Vec::new()));
                }
            }

            Term::Lam(_, _, body) => self.under(sizes, None, body),

            Term::App(..) => {
                let (head, arguments) = spine(term);
                let applied: Vec<Option<Size>> = arguments
                    .iter()
                    .map(|argument| self.measured(sizes, argument))
                    .collect();
                // Позиция члена группы считается **до** разбора, а не стражем
                // `if let`: тот требует Rust 2024, а MSRV проекта 1.85, и CI
                // ловит это отдельной джобой.
                let callee = match head {
                    Term::Const(other, _, _) => self.group.iter().position(|it| it == other),
                    _ => None,
                };
                if let Some(callee) = callee {
                    self.calls.push((callee, applied));
                    for argument in arguments {
                        self.term(sizes, argument);
                    }
                    return;
                }
                match head {
                    // Convoy: аргументы применения - те самые соседи, которые
                    // ветвь связывает лямбдами сверх полей.
                    Term::Case(case) => self.case(sizes, case, &applied),
                    other => {
                        // Вызов члена группы через метод-проекцию видит
                        // только редукция; удалась - обходится редукт, и
                        // спайн с потреблённым словарём заново не читается.
                        if let Some(reduced) = member_call(
                            self.signature,
                            self.group,
                            self.undecided,
                            sizes.len(),
                            term,
                        ) {
                            self.term(sizes, &reduced);
                            return;
                        }
                        self.term(sizes, other);
                    }
                }
                for argument in arguments {
                    self.term(sizes, argument);
                }
            }

            Term::Pi(_, _, domain, row, codomain) => {
                self.term(sizes, domain);
                self.under(sizes, None, codomain);
                // Аргументы меток стоят под связыванием стрелки наравне с
                // кодоменом: применение аргумент уже знает, и метка вправе его
                // назвать.
                for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                    self.under(sizes, None, argument);
                }
            }

            Term::Let(_, _, ty, value, body) => self.binding(sizes, ty, value, body),

            // Поля записи размера не несут: разбор записи не уменьшает ни одного
            // аргумента, и тело обходится с неизвестными размерами полей.
            Term::Split(split) => {
                self.term(sizes, &split.scrutinee);
                self.term(sizes, &split.body);
            }
            Term::Case(case) => self.case(sizes, case, &[]),
        }
    }

    /// Связывание `let`: размер и факты его значения (§10 вопрос 227).
    ///
    /// Связывание несёт размер своего значения: `let j = i - 1` и вызов от `j`
    /// убывают так же, как вызов от `i - 1` - значение то же, что подставилось
    /// бы. Сравнение в значении - так элаборируется `if` - даёт разбору по
    /// связыванию пол либо границу, как литеральный паттерн.
    fn binding(&mut self, sizes: &mut Vec<Option<Size>>, ty: &Term, value: &Term, body: &Term) {
        self.term(sizes, ty);
        self.term(sizes, value);
        let size = self.measured(sizes, value);
        // `decide c` несёт тот же факт, что `c`: разбор по нему - тот же `if`,
        // только с доказательством в ветви (§10 вопрос 224).
        let checked = decided(value).unwrap_or(value);
        let reduced = primitive_of(self.signature, self.undecided, sizes.len(), checked);
        let compared = reduced.as_ref().unwrap_or(checked);
        let fact = Self::compared(sizes, compared);
        let less = Self::less(sizes, compared);
        if let Some(fact) = fact {
            self.bound.push((sizes.len(), fact));
        }
        if let Some(less) = less {
            self.bound_below.push((sizes.len(), less));
        }
        self.under(sizes, size, body);
        if fact.is_some() {
            self.bound.pop();
        }
        if less.is_some() {
            self.bound_below.pop();
        }
    }

    /// Обходит разбор, раздавая ветвям размеры аргументов, к которым он
    /// применён.
    fn case(&mut self, sizes: &mut Vec<Option<Size>>, case: &Case, applied: &[Option<Size>]) {
        self.term(sizes, &case.scrutinee);
        self.term(sizes, &case.motive);
        // Поля строго меньше разобранного значения - здесь и только здесь
        // размер растёт в глубину.
        let smaller = Self::size(sizes, &case.scrutinee).map(|size| Size {
            argument: size.argument,
            depth: size.depth + 1,
            bound: None,
        });
        // Разбор по сравнению с литералом даёт ветви `False` пол: под ней
        // разбираемое заведомо не равно этому числу (§4.3).
        let apart = Self::compared(sizes, &case.scrutinee).or_else(|| {
            let level = Self::level(sizes, &case.scrutinee)?;
            self.bound
                .iter()
                .rev()
                .find(|(at, _)| *at == level)
                .map(|(_, fact)| *fact)
        });
        // Разбор по «строго меньше» даёт ветви `True` границу шага вверх.
        let less = Self::less(sizes, &case.scrutinee).or_else(|| {
            let level = Self::level(sizes, &case.scrutinee)?;
            self.bound_below
                .iter()
                .rev()
                .find(|(at, _)| *at == level)
                .map(|(_, fact)| *fact)
        });
        for branch in &case.branches {
            let fields = self.fields(&branch.constructor, case.params);
            let short = crate::term::short(&branch.constructor);
            let floored = apart.filter(|_| {
                matches!(
                    short,
                    crate::prim::FALSE | crate::prim::NO | crate::prim::ELSE
                )
            });
            let bounded = less.filter(|_| {
                matches!(
                    short,
                    crate::prim::TRUE | crate::prim::YES | crate::prim::THEN
                )
            });
            if let Some(fact) = floored {
                self.apart.push(fact);
            }
            if let Some(fact) = bounded {
                self.below.push(fact);
            }
            self.branch(sizes, fields, smaller, applied, &branch.body);
            if floored.is_some() {
                self.apart.pop();
            }
            if bounded.is_some() {
                self.below.pop();
            }
        }
    }

    /// Сколько полей связывает ветвь конструктора.
    fn fields(&self, constructor: &Name, params: u32) -> usize {
        let Some(declaration) = self.signature.lookup(constructor) else {
            return 0;
        };
        let mut binders = 0usize;
        let mut current = &declaration.ty;
        while let Term::Pi(_, _, _, _, codomain) = current {
            binders += 1;
            current = codomain;
        }
        binders.saturating_sub(params as usize)
    }

    /// Обходит тело ветви, раздавая её полям размер `smaller`.
    ///
    /// Ветвь - функция от полей, но быть записанной лямбдами она не обязана
    /// (η). Что не снялось лямбдами, обходится как обычный терм: размеров такие
    /// поля не получают, и рекурсия по ним не засчитывается.
    fn branch(
        &mut self,
        sizes: &mut Vec<Option<Size>>,
        fields: usize,
        smaller: Option<Size>,
        applied: &[Option<Size>],
        term: &Term,
    ) {
        match (fields, term) {
            (0, other) => self.convoyed(sizes, applied, other),
            (_, Term::Lam(_, _, body)) => {
                sizes.push(smaller);
                self.branch(sizes, fields - 1, smaller, applied, body);
                sizes.pop();
            }
            // Поля кончились не лямбдами: до аргументов применения такая ветвь
            // не добирается, и раздавать их размеры некому.
            (_, other) => self.term(sizes, other),
        }
    }

    /// Обходит то, что осталось от ветви после полей, раздавая лямбдам размеры
    /// аргументов применения - каждой свой, слева направо.
    fn convoyed(&mut self, sizes: &mut Vec<Option<Size>>, applied: &[Option<Size>], term: &Term) {
        match (applied.split_first(), term) {
            (Some((first, rest)), Term::Lam(_, _, body)) => {
                sizes.push(*first);
                self.convoyed(sizes, rest, body);
                sizes.pop();
            }
            (_, other) => self.term(sizes, other),
        }
    }

    /// Обходит терм под одним связыванием.
    fn under(&mut self, sizes: &mut Vec<Option<Size>>, size: Option<Size>, term: &Term) {
        sizes.push(size);
        self.term(sizes, term);
        sizes.pop();
    }
}

/// Допустимо ли определение в стёртом фрагменте (§4.7).
///
/// Нетотальная функция не может участвовать в доказательствах, а типы живут в
/// том же фрагменте, поэтому проверка одна на оба случая.
#[must_use]
pub fn admits(definition: &Definition, sigma: Mult) -> bool {
    definition.total || sigma != Mult::Zero
}

/// Передан ли параметр `at` вызову неизменным - граница шага вверх (§10
/// вопрос 227): мера `n - i` убывает, только пока `n` та же.
fn unchanged(sizes: &[Option<Size>], at: usize) -> bool {
    matches!(
        sizes.get(at),
        Some(&Some(Size {
            argument,
            depth: 0,
            bound: None,
        })) if argument == at
    )
}

/// Проверка `c`, если терм - `decide c` или `inspect c` прелюдии
/// ([`crate::prim::DECIDE`], [`crate::prim::INSPECT`]): `if` пишется вторым.
fn decided(term: &Term) -> Option<&Term> {
    let Term::App(callee, argument) = term else {
        return None;
    };
    let Term::Const(name, ..) = &**callee else {
        return None;
    };
    matches!(
        crate::term::short(name),
        crate::prim::DECIDE | crate::prim::INSPECT
    )
    .then_some(&**argument)
}
