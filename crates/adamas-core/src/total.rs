//! Проверка тотальности: структурная рекурсия (§4.7, §9 Фаза 1).
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
//! "размер" - пара "номер параметра, глубина разбора". Разбор по значению
//! размера `(i, d)` даёт полям размер `(i, d+1)`: поле конструктора строго
//! меньше разобранного значения. Рекурсивный вызов засчитывается уменьшающимся
//! по позиции `k`, если его `k`-й аргумент - переменная размера `(k, d)` при
//! `d > 0`.
//!
//! Определение тотально, если такая позиция `k` **одна на все** рекурсивные
//! вызовы. Позиция ищется перебором - объявлять её, как `{struct n}` в Coq,
//! незачем.
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
//! Лексикографический порядок (`ack`), well-founded рекурсия с явной мерой.
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
                    Some(&Some(Size { argument, depth }))
                        if argument == position && depth > 0
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
                Some(&Some(Size { argument, depth }))
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
        Term::Var(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind | Term::Meta(_) => {}
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
            for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                recur(depth, argument);
            }
        }
        Term::Let(_, _, ty, value, body) => {
            recur(depth, ty);
            recur(depth, value);
            recur(depth + 1, body);
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
            return Some(crate::eval::quote(width, &current));
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

/// Сколько δ-шагов разрешено редукции одного спайна.
const REDUCTION_LIMIT: u32 = 128;

/// Стоит ли имя группы в терме синтаксически.
fn mentions_group(group: &[Name], term: &Term) -> bool {
    let recur = |inner: &Term| mentions_group(group, inner);
    match term {
        Term::Var(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind | Term::Meta(_) => {
            false
        }
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
                && row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .all(|argument| recur(depth, argument))
        }
        Term::Let(_, _, ty, value, body) => {
            recur(depth, ty) && recur(depth, value) && recur(depth + 1, body)
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
        Term::Var(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind | Term::Meta(_) => {
            false
        }
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

struct Walk<'a> {
    signature: &'a Signature,
    /// Имена, вызов которых считается рекурсивным: своё и соседи по циклу.
    group: &'a [Name],
    /// Имена без вердикта - вся объявляемая группа; редукция их не трогает.
    undecided: &'a [Name],
    /// Вызовы в порядке обхода.
    calls: Vec<Call>,
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
        let Term::Var(Index(index)) = term else {
            return None;
        };
        let level = sizes.len().checked_sub(*index as usize + 1)?;
        *sizes.get(level)?
    }

    fn term(&mut self, sizes: &mut Vec<Option<Size>>, term: &Term) {
        match term {
            // Дырка размера не несёт и вызовом не является: она замкнута, а
            // зависимость от контекста выражена применениями вокруг неё.
            Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
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
                    .map(|argument| Self::size(sizes, argument))
                    .collect();
                match head {
                    Term::Const(other, _, _)
                        if let Some(callee) = self.group.iter().position(|it| it == other) =>
                    {
                        self.calls.push((callee, applied));
                    }
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
                // Аргументы меток стоят под тем же контекстом, что домен:
                // связывание `Pi` вводится только для кодомена.
                for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                    self.term(sizes, argument);
                }
            }

            Term::Let(_, _, ty, value, body) => {
                self.term(sizes, ty);
                self.term(sizes, value);
                // Связывание `let` размера не несёт: значение известно, но
                // отследить его убывание эта проверка не берётся.
                self.under(sizes, None, body);
            }

            Term::Case(case) => self.case(sizes, case, &[]),
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
        });
        for branch in &case.branches {
            let fields = self.fields(&branch.constructor, case.params);
            self.branch(sizes, fields, smaller, applied, &branch.body);
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
