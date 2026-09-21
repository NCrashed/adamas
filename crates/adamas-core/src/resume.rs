//! Хвостовая резумптивность ветки хендлера (§3.4): вердикт и два его читателя.
//!
//! §3.4 перечисляет четыре класса хендлера, а вердикт у анализа **трёхзначный**,
//! и это записано там же: «сколько раз зовётся `resume`» отделяет мультишот,
//! «в хвостовой ли позиции» отделяет хвостово-резумптивный, а ноль вызовов -
//! отдельный ответ, потому что снимает вопрос о продолжении целиком.
//!
//! # Читателей двое, и сливать их нельзя
//!
//! | Вердикт | §5.1 «аллоцирует?» | §5.3 «вернётся в чужой кадр?» |
//! |---|---|---|
//! | [`Verdict::Tail`] | нет | да |
//! | [`Verdict::Abortive`] | **нет** | **нет** |
//! | [`Verdict::General`] | да | нет |
//!
//! Абортивная ветка продолжение **отбрасывает**: захватывать нечего, раскрутка
//! до метки плюс отложенные деструкторы, ноль ячеек кучи - и §5.1 её пропускает
//! ([`Verdict::allocates`]). Правило чужого кадра спрашивает про другое -
//! вернётся ли управление в сишный фрейм нормально, - и по этому вопросу
//! абортивный стоит на стороне общего: он как раз и означает, что не вернётся
//! ([`Verdict::returns`]). §5.3 предупреждает об этом прямо: симметричная правка
//! от §5.1 сюда была бы ошибкой.
//!
//! Порядок [`Verdict::worst`] - `Tail < Abortive < General` - годится обоим:
//! площадка аллоцирует, если аллоцирует хоть одна ветка, и возвращается, только
//! если возвращаются все.
//!
//! # Где стоит `resume`
//!
//! Ветка операции есть `\a⃗ -> \resume -> тело` (§3.4: имя вводит сама форма,
//! связывание последнее). Хвост считается **по написанному**, и перечень
//! позиций такой:
//!
//! - `resume e` целиком телом - хвост, [`Verdict::Tail`];
//! - `let … in … resume e` - хвост сквозь цепочку `let`: она вычисление, а не
//!   ветвление. Значение связывания при этом резумпцию называть не вправе -
//!   `let x = resume 1 in resume x` зовёт её дважды;
//! - резумпция не названа **ни разу** - [`Verdict::Abortive`];
//! - `case … of … -> resume e` - **не** хвост: у разбора по ответу на ветвь, и
//!   снимать резумпцию пришлось бы в каждой. Граница среза названа, а не
//!   молчание: такая ветка получает [`Verdict::General`];
//! - `f (resume e)`, `Cons n (resume e)`, `{ x = resume e }` - аргументом,
//!   полем конструктора, полем записи: продолжение нужно после возобновления;
//! - `let x = resume e in …` - значением связывания;
//! - `\() -> resume ()` внутри конструктора (идиома `reify` §3.4) - резумпция
//!   уходит значением;
//! - названа дважды в любой комбинации выше;
//! - названа, но не применена (`MkBox resume`) - тоже общий случай: смотрит на
//!   неё [`mentions`], а не форма применения.
//!
//! Мультишотная площадка вердикта **не считает**: `ω`-резумпция не обещает «не
//! более одного раза», и все её ветки общие (§3.4, «Стоимость multi-shot»).
//! Параметризованная (`#handleState`) вердикта не получает особого: элаборация
//! дописывает лямбду по состоянию **последним** связыванием ветки, поэтому
//! `resume` стоит под ней и в хвосте не оказывается никогда - [`Verdict::General`]
//! по построению формы, а не по осторожности (§10 вопрос 129).
//!
//! # Направление
//!
//! Консервативное, и в одну сторону для обоих читателей: то, чего анализ не
//! разобрал, объявляется [`Verdict::General`]. У §5.1 это отказ законному
//! `@noalloc`, у §5.3 - отказ законному колбэку; принять аллоцирующее либо
//! непроходимое через чужой кадр оно не может ни в одном случае.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::rc::Rc;

use crate::eval::{eval, quote};
use crate::row::{Row, Tail};
use crate::sig::{DefinitionKind, Signature};
use crate::term::{Index, Name, Term, spine};
use crate::value::{Env, Lvl, Value};

/// Префиксы имён элиминаторов. Имена невыразимы в языке (§3.4), поэтому
/// столкнуться с пользовательскими они не могут.
const HANDLE: &str = "#handle.";
const MULTI: &str = "#handleMulti.";
const STATE: &str = "#handleState.";
const MASK: &str = "#mask.";

/// Какой элиминатор стоит в голове спайна.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form {
    /// `handle` - одношотный.
    Handle,
    /// `handleMulti` - `ω`-резумпция.
    Multi,
    /// `handleState` - параметризованный (§3.4, сахар `state`).
    State,
    /// `mask` - веток нет вовсе, только вычисление.
    Mask,
}

impl Form {
    /// Мультишотна ли площадка: у такой вердикт не считается.
    #[must_use]
    pub const fn multi(self) -> bool {
        matches!(self, Self::Multi)
    }
}

/// Разбирает имя элиминатора на форму и метку. `None` - имя не элиминатор.
#[must_use]
pub fn eliminated(name: &str) -> Option<(Form, &str)> {
    // Порядок важен: `#handle.` - префикс не самого себя, но `#handleMulti.`
    // начинается с `#handle`, а разделителем служит точка, поэтому сначала
    // длинные.
    for (prefix, form) in [
        (MULTI, Form::Multi),
        (STATE, Form::State),
        (HANDLE, Form::Handle),
        (MASK, Form::Mask),
    ] {
        if let Some(label) = name.strip_prefix(prefix) {
            return Some((form, label));
        }
    }
    None
}

/// Трёхзначный вердикт §3.4.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Verdict {
    /// `resume` в хвосте и ровно один раз: продолжение остаётся на месте.
    Tail,
    /// `resume` не зовётся вовсе: продолжение отброшено, захватывать нечего.
    Abortive,
    /// `resume` зовётся вне хвоста, несколько раз либо уходит значением:
    /// продолжение снимается в сегмент кучи.
    General,
}

impl Verdict {
    /// §5.1: снимает ли ветка продолжение в кучу Perceus.
    ///
    /// Абортивная - **нет**: «раскрутка до метки плюс отложенные деструкторы,
    /// ноль аллокаций» (§5.1).
    #[must_use]
    pub const fn allocates(self) -> bool {
        matches!(self, Self::General)
    }

    /// §5.3: вернётся ли управление в чужой кадр нормально.
    ///
    /// Абортивная - **нет**, и здесь она стоит на стороне общего случая: она
    /// как раз и означает, что не вернётся. Читать этот ответ как отрицание
    /// [`Verdict::allocates`] - ровно та симметричная правка, которую §5.3
    /// называет ошибкой.
    #[must_use]
    pub const fn returns(self) -> bool {
        matches!(self, Self::Tail)
    }

    /// Худший из двух: площадка отвечает за все свои ветки.
    #[must_use]
    pub fn worst(self, other: Self) -> Self {
        if other > self { other } else { self }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tail => f.write_str("хвостово-резумптивный"),
            Self::Abortive => f.write_str("абортивный"),
            Self::General => f.write_str("общий"),
        }
    }
}

/// Вердикт одной ветки операции.
///
/// `term` - ветка целиком, вместе со своими лямбдами; `written` - сколько
/// аргументов операции она связывает (резумпция идёт следом и в счёт не
/// входит); `multi` - мультишотна ли площадка.
#[must_use]
pub fn branch(term: &Term, written: usize, multi: bool) -> Verdict {
    if multi {
        return Verdict::General;
    }
    let mut current = term;
    for _ in 0..written {
        let Term::Lam(_, _, body) = current else {
            // Форма ветки нарушена: связываний меньше, чем объявила операция.
            // Разбирать нечего, и ответ идёт в консервативную сторону.
            return Verdict::General;
        };
        current = body;
    }
    // Последнее связывание - `resume`; имя вводит сама форма (§3.4).
    let Term::Lam(_, _, body) = current else {
        return Verdict::General;
    };
    // Хвостовая спрашивается первой: `untailed` смотрит написанное, а
    // `mentions` - нормализованное, и ветка с имплиситом в аргументе проходит
    // только в этом порядке.
    match untailed(body, 0) {
        Some(rest) if !mentions(&rest, 0) => Verdict::Tail,
        None if !mentions(body, 0) => Verdict::Abortive,
        _ => Verdict::General,
    }
}

/// Ветка, зовущая резумпцию **в хвосте**: `resume e` заменяется на `e`.
///
/// `depth` - индекс связывания `resume` в этой точке. `None` значит «в хвосте
/// не зовёт»; абортивную от общей вызывающий различает по [`mentions`].
///
/// Хвост считается по написанному, поэтому цепочка `let` сквозная - она
/// вычисление, а не ветвление, - а разбор нет: у него по ответу на ветвь.
#[must_use]
pub fn untailed(term: &Term, depth: u32) -> Option<Term> {
    match term {
        Term::App(callee, argument) => match &**callee {
            Term::Var(Index(index)) if *index == depth => Some((**argument).clone()),
            _ => None,
        },
        Term::Let(mult, name, ty, value, body) => {
            if mentions(value, depth) {
                return None;
            }
            Some(Term::Let(
                *mult,
                Rc::clone(name),
                Rc::clone(ty),
                Rc::clone(value),
                Rc::new(untailed(body, depth + 1)?),
            ))
        }
        _ => None,
    }
}

/// Смотрит ли терм на связывание с индексом `index`.
///
/// Считает по **нормализованному** терму, и это не осторожность: решение
/// имплисита приезжает бета-редексом по всему контексту - `((\m₂ -> \m₁ -> \m₀
/// -> #2) #2 #1 #0)`, - то есть называет каждое связывание, включая резумпцию.
/// Считай по написанному, и всякая ветка с имплиситом в аргументе оказалась бы
/// «зовущей резумпцию и в хвосте, и до него».
#[must_use]
pub fn mentions(term: &Term, index: u32) -> bool {
    let mut free = BTreeSet::new();
    escaping(&normalized(term), 0, &mut free);
    free.contains(&index)
}

/// Нормализует терм под контекстом из переменных.
///
/// Глубину контекста терм задаёт сам ([`ceiling`]), и это не лень, а
/// устойчивость: ветка стоит под связываниями определения, число которых обход
/// §5.1 не считает, а посчитай его неверно - `eval` падает «незамкнутый терм»
/// на первой же программе корпуса. Завышение безвредно: окружение из `d`
/// переменных при `d` больше всякого свободного индекса возвращает `quote` ровно
/// те же индексы - отображение `i ↦ Lvl(d-1-i) ↦ i` от `d` не зависит.
fn normalized(term: &Term) -> Term {
    let depth = ceiling(term);
    let mut env = Env::default();
    for level in 0..depth {
        env = env.extend(Value::var(Lvl(level)));
    }
    quote(depth, &eval(&env, term))
}

/// На единицу больше самого большого индекса, встреченного где угодно в терме.
///
/// Связывания не вычитаются намеренно: нужна **верхняя** оценка, а не точная
/// глубина, и обход обязан пройти все позиции, куда заглядывает `eval`, включая
/// типы, мотив разбора и телескопы записей. Пропущенная позиция - это падение,
/// а не неточность, поэтому пропускать нечего.
fn ceiling(term: &Term) -> u32 {
    fn seen(term: &Term, top: &mut u32) {
        match term {
            Term::Var(Index(index)) => *top = (*top).max(index + 1),
            Term::Lam(_, _, body) | Term::Project(body, _) => seen(body, top),
            Term::App(left, right) => {
                seen(left, top);
                seen(right, top);
            }
            Term::Pi(_, _, domain, row, codomain) => {
                seen(domain, top);
                within(row, top);
                seen(codomain, top);
            }
            Term::Let(_, _, ty, value, body) => {
                seen(ty, top);
                seen(value, top);
                seen(body, top);
            }
            Term::Const(_, _, args) => {
                for row in args.row_args() {
                    within(row, top);
                }
            }
            Term::Case(case) => {
                seen(&case.scrutinee, top);
                seen(&case.motive, top);
                for branch in &case.branches {
                    seen(&branch.body, top);
                }
            }
            Term::Record(fields) | Term::Row(fields) => {
                for field in fields.fields.iter() {
                    seen(&field.ty, top);
                }
                if let Some(tail) = &fields.tail {
                    seen(tail, top);
                }
            }
            Term::Object(fields) => {
                for (_, value) in fields.iter() {
                    seen(value, top);
                }
            }
            Term::With(base, fields) => {
                seen(base, top);
                for (_, value) in fields.iter() {
                    seen(value, top);
                }
            }
            Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Meta(_)
            | Term::Prim(_) => {}
        }
    }
    fn within(row: &Row<Term>, top: &mut u32) {
        for label in row.labels() {
            for argument in &label.arguments {
                seen(argument, top);
            }
        }
    }
    let mut top = 0;
    seen(term, &mut top);
    top
}

/// Индексы, уходящие за `depth`, приведённые к внешнему счёту.
///
/// Обход покрывает **все** позиции, где значение доживает до исполнения, и
/// запись входит в их число наравне с применением: ветка `{ x = resume MkUnit }`
/// резумпцию зовёт, и пропусти её обход - вердикт вышел бы абортивным, то есть
/// §5.1 принял бы `@noalloc` над снятым в кучу сегментом. Типы, мотив разбора и
/// телескопы пропускаются: значений в рантайме там нет.
fn escaping(term: &Term, depth: u32, out: &mut BTreeSet<u32>) {
    match term {
        Term::Var(Index(index)) => {
            if *index >= depth {
                out.insert(index - depth);
            }
        }
        Term::Lam(_, _, body) => escaping(body, depth + 1, out),
        Term::App(callee, argument) => {
            escaping(callee, depth, out);
            escaping(argument, depth, out);
        }
        Term::Let(_, _, _, value, body) => {
            escaping(value, depth, out);
            escaping(body, depth + 1, out);
        }
        Term::Case(case) => {
            escaping(&case.scrutinee, depth, out);
            for branch in &case.branches {
                escaping(&branch.body, depth, out);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                escaping(value, depth, out);
            }
        }
        Term::With(base, fields) => {
            escaping(base, depth, out);
            for (_, value) in fields.iter() {
                escaping(value, depth, out);
            }
        }
        Term::Project(record, _) => escaping(record, depth, out),
        _ => {}
    }
}

/// Ветка одной операции на площадке.
#[derive(Clone, Debug)]
pub struct Branched {
    /// Операция, которую она обрабатывает.
    pub operation: Name,
    /// Сколько аргументов операции она связывает - без резумпции.
    pub written: usize,
    /// Вердикт §3.4.
    pub verdict: Verdict,
    /// Тело под снятыми связываниями.
    ///
    /// У [`Verdict::Tail`] применение резумпции **снято**: `resume e` стоит
    /// телом `e`, и это не украшение, а то, что увидит понижение - ответ
    /// хвостовой ветки и есть значение операции, вызова там не остаётся.
    /// Потребителю §5.1 это существенно: иначе `ask -> resume 2` читалось бы
    /// как применение значения-функции, то есть боксирование (§4.11).
    pub body: Rc<Term>,
}

/// Площадка `handle`: что стоит в её спайне и чем она отвечает.
#[derive(Clone, Debug)]
pub struct Site {
    /// Форма элиминатора.
    pub form: Form,
    /// Метка, которую площадка снимает.
    pub label: Name,
    /// Вердикт по веткам: худший из них.
    pub verdict: Verdict,
    /// Операция, чья ветка дала худший вердикт. `None` - веток нет вовсе
    /// (метка без операций) либо площадка мультишотна: там вердикт у всех
    /// веток один и берётся он не из ветки.
    pub blamed: Option<Name>,
    /// Тело вычисления под хендлером - оно же аргумент маски, со снятым
    /// связыванием синтезированного триггера.
    pub computation: Option<Rc<Term>>,
    /// Тело ветки `return` под снятыми связываниями, если площадка её
    /// принимает.
    pub returned: Option<Rc<Term>>,
    /// Ветки операций.
    pub branches: Vec<Branched>,
    /// Аргументы сверх насыщения: у параметризованного это начальное состояние.
    pub extra: Vec<Rc<Term>>,
}

/// Разбирает применение элиминатора. `None` - голова не элиминатор либо спайн
/// не насыщен.
///
/// Ненасыщенный спайн ответа не получает намеренно: имя элиминатора в языке
/// невыразимо (§3.4), написать его частично применённым автор не может, а
/// молчаливое «сойдёт» здесь означало бы вердикт по неполному набору веток.
#[must_use]
pub fn site(signature: &Signature, name: &Name, arguments: &[&Term]) -> Option<Site> {
    let (form, label) = eliminated(name)?;
    let label: Name = Rc::from(label);
    if form == Form::Mask {
        // `#mask.L {p⃗} {a} computation`: веток нет, вердикта нет.
        let params = match &signature.lookup(&label)?.kind {
            DefinitionKind::Effect { params, .. } => *params as usize,
            _ => return None,
        };
        let arity = params + 2;
        let computation = arguments.get(arity - 1)?;
        return Some(Site {
            form,
            label,
            verdict: Verdict::Tail,
            blamed: None,
            computation: Some(stripped(computation, 1)),
            returned: None,
            branches: Vec::new(),
            extra: arguments[arity..]
                .iter()
                .map(|it| Rc::new((*it).clone()))
                .collect(),
        });
    }
    let eliminator = signature.lookup(name)?;
    let (operations, params) = match &signature.lookup(&label)?.kind {
        DefinitionKind::Effect { operations, params } => (operations.clone(), *params as usize),
        _ => return None,
    };
    // Параметры метки, `a`, `b`, вычисление, `return` и ветки.
    let arity = params + 4 + operations.len();
    if arguments.len() < arity {
        return None;
    }
    let multi = form.multi();
    // Связывание, дописанное самой формой сверх типа элиминатора: у
    // параметризованной это `state`, и стоит оно последним у каждой ветки,
    // включая `return` (§3.4, сахар `state`). Тип у третьего элиминатора тот
    // же, что у одношотного, поэтому по нему это связывание не читается ничем.
    let appended = usize::from(form == Form::State);
    let mut verdict = Verdict::Tail;
    let mut blamed = None;
    let mut branches = Vec::with_capacity(operations.len());
    for (slot, operation) in operations.iter().enumerate() {
        let term = arguments[params + 4 + slot];
        // Сколько аргументов связывает ветка, знает тип элиминатора: последнее
        // связывание там - резумпция, и в счёт она не идёт.
        let written = domain(&eliminator.ty, params + 4 + slot)
            .map(binders)
            .and_then(|count| count.checked_sub(1))?;
        let found = branch(term, written, multi);
        if found > verdict {
            verdict = found;
            blamed = Some(Rc::clone(operation));
        }
        let body = stripped(term, written + 1 + appended);
        let body = if found == Verdict::Tail {
            untailed(&body, 0).map_or(body, Rc::new)
        } else {
            body
        };
        branches.push(Branched {
            operation: Rc::clone(operation),
            written,
            verdict: found,
            body,
        });
    }
    if multi {
        // У мультишотной площадки вердикт не считается по ветке, и называть
        // ветку виноватой нечем: платит сама форма (§3.4).
        verdict = Verdict::General;
        blamed = None;
    }
    Some(Site {
        form,
        label,
        verdict,
        blamed,
        computation: Some(stripped(arguments[params + 2], 1)),
        returned: Some(stripped(arguments[params + 3], 1 + appended)),
        branches,
        extra: arguments[arity..]
            .iter()
            .map(|it| Rc::new((*it).clone()))
            .collect(),
    })
}

/// Снимает ведущие лямбды. Что не снялось - отдаётся как есть.
///
/// Записаны они не обязаны (η), и тогда остаток есть обычный терм: то же
/// правило, каким снимает связывания ветви разбора обход §5.1.
fn stripped(term: &Term, binders: usize) -> Rc<Term> {
    let mut current = term;
    for _ in 0..binders {
        let Term::Lam(_, _, body) = current else {
            break;
        };
        current = body;
    }
    Rc::new(current.clone())
}

/// Домен связывания под номером `index`.
fn domain(ty: &Term, index: usize) -> Option<&Term> {
    let mut current = ty;
    for _ in 0..index {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    match current {
        Term::Pi(_, _, domain, _, _) => Some(domain),
        _ => None,
    }
}

/// Сколько связываний у типа подряд.
fn binders(ty: &Term) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, _, _, _, codomain) = current {
        count += 1;
        current = codomain;
    }
    count
}

/// Вердикт каждой метки по **всем** её площадкам в сигнатуре.
///
/// Метка, у которой площадок нет вовсе, в карту не попадает: «все её ветки
/// хвостовые» здесь было бы вакуумной истиной, а вакуумная истина у этого
/// вопроса неверна - непогашенная операция обрывает машину, то есть управление
/// не возвращает никуда. Различает эти два случая [`crossing`].
///
/// Ответ зависит от **всей** сигнатуры, и спрашивать его посреди объявления
/// значит спрашивать не тот: площадка, написанная ниже, в него ещё не вошла.
/// Это тот же порядковый капкан, который §3.4 закрывает предпроходом у ресурсов
/// под `handleMulti`; здесь предпрохода нет, и потому карта строится по готовой
/// программе.
#[must_use]
pub fn labels(signature: &Signature) -> BTreeMap<Name, Verdict> {
    let mut found: BTreeMap<Name, Verdict> = BTreeMap::new();
    for name in signature.names() {
        let Some(definition) = signature.lookup(&name) else {
            continue;
        };
        let Some(body) = &definition.body else {
            continue;
        };
        sites(signature, body, &mut |site| {
            if site.form == Form::Mask {
                return;
            }
            let entry = found.entry(Rc::clone(&site.label)).or_insert(Verdict::Tail);
            *entry = entry.worst(site.verdict);
        });
    }
    found
}

/// Обходит терм, отдавая каждую встреченную площадку.
fn sites(signature: &Signature, term: &Term, found: &mut impl FnMut(&Site)) {
    if let Term::App(..) = term {
        let (head, arguments) = spine(term);
        if let Term::Const(name, _, _) = head {
            if let Some(site) = site(signature, name, &arguments) {
                found(&site);
            }
        }
    }
    match term {
        Term::Lam(_, _, body) => sites(signature, body, found),
        Term::App(callee, argument) => {
            sites(signature, callee, found);
            sites(signature, argument, found);
        }
        Term::Let(_, _, _, value, body) => {
            sites(signature, value, found);
            sites(signature, body, found);
        }
        Term::Case(case) => {
            sites(signature, &case.scrutinee, found);
            for branch in &case.branches {
                sites(signature, &branch.body, found);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                sites(signature, value, found);
            }
        }
        Term::With(base, fields) => {
            sites(signature, base, found);
            for (_, value) in fields.iter() {
                sites(signature, value, found);
            }
        }
        Term::Project(record, _) => sites(signature, record, found),
        _ => {}
    }
}

/// Чем row не проходит через чужой кадр (§5.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Blocked {
    /// Метка, чей хендлер управление не вернёт.
    Handler {
        /// Имя метки.
        label: Name,
        /// Её вердикт: абортивный либо общий.
        verdict: Verdict,
    },
    /// Метка, которую в программе не гасит ни одна площадка.
    Unhandled(Name),
    /// Открытый хвост: что придёт сверх написанного, неизвестно.
    Open(Tail),
}

impl fmt::Display for Blocked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Handler { label, verdict } => write!(
                f,
                "эффект `{label}` в позиции колбэка: его хендлер {verdict}, то есть управление \
                 в чужой кадр нормально не вернёт (§5.3). Между входом в колбэк и возвратом из \
                 него лежит фрейм, построенный C: раскрутить его мы не можем и пропустить не \
                 имеем права. Идиома отмены - записать намерение и вернуться нормально, а \
                 действовать уже на своей стороне границы"
            ),
            Self::Unhandled(label) => write!(
                f,
                "эффект `{label}` в позиции колбэка не гасит ни один хендлер программы: \
                 непогашенная операция обрывает исполнение, и в чужой кадр управление не \
                 возвращается вовсе (§5.3)"
            ),
            Self::Open(tail) => write!(
                f,
                "row колбэка открыта хвостом `{tail}`: что придёт сверх написанного, в точке \
                 регистрации неизвестно, а чужой кадр требует ответа до вызова (§5.3). \
                 Напишите row замкнутой"
            ),
        }
    }
}

/// Пройдёт ли row через чужой кадр (§5.3, правило чужого кадра).
///
/// `None` - пройдёт. Спрашивается **двузначно**, и различать абортивный случай
/// правило не должно: вопрос здесь не «аллоцирует ли», а «вернётся ли
/// управление», и по нему абортивный стоит на стороне общего.
///
/// `known` - карта [`labels`] по готовой программе; вызывающий строит её один
/// раз, потому что обход у неё по всей сигнатуре.
#[must_use]
pub fn crossing(known: &BTreeMap<Name, Verdict>, row: &Row<Term>) -> Option<Blocked> {
    for label in row.labels() {
        let Some(verdict) = known.get(&label.name) else {
            return Some(Blocked::Unhandled(Rc::clone(&label.name)));
        };
        if !verdict.returns() {
            return Some(Blocked::Handler {
                label: Rc::clone(&label.name),
                verdict: *verdict,
            });
        }
    }
    // Хвост спрашивается **после** меток: написанная метка - точнее указание,
    // чем «что-то ещё», и отказ обязан называть конкретный эффект, пока он
    // есть (§5.3).
    row.tail().map(Blocked::Open)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{Verdict, branch};
    use crate::mult::Mult;
    use crate::term::Term;

    /// Ветка операции без написанных аргументов: `\resume -> body`.
    fn branched(body: Term) -> Verdict {
        let term = Term::Lam(Mult::One, "resume".into(), Rc::new(body));
        branch(&term, 0, false)
    }

    /// `let aside : Nat = value in body`.
    ///
    /// Поверхностный язык `let` в теле ветки сегодня не берёт - тело ветки есть
    /// одно выражение, - но `untailed` эту позицию знает, и проверяется она
    /// здесь: иначе правило оказалось бы закрыто на том, что сейчас написуемо.
    fn bound(value: Term, body: Term) -> Term {
        Term::Let(
            Mult::One,
            "aside".into(),
            Rc::new(Term::constant("Nat")),
            Rc::new(value),
            Rc::new(body),
        )
    }

    #[test]
    fn a_tail_call_through_a_chain_of_lets_stays_tail() {
        // `let a = Zero in let b = Zero in resume a`: цепочка сквозная.
        let inner = bound(
            Term::constant("Zero"),
            Term::App(Rc::new(Term::var(2)), Rc::new(Term::var(1))),
        );
        assert_eq!(
            branched(bound(Term::constant("Zero"), inner)),
            Verdict::Tail
        );
    }

    #[test]
    fn a_let_whose_value_resumes_is_general() {
        // `let a = resume Zero in a`: резумпция стоит значением связывания.
        let value = Term::App(Rc::new(Term::var(0)), Rc::new(Term::constant("Zero")));
        assert_eq!(branched(bound(value, Term::var(0))), Verdict::General);
    }

    #[test]
    fn untailing_stops_at_a_let_whose_value_resumes() {
        // `let a = resume Zero in resume a`. Вердикт тут общий в любом случае -
        // резумпцию зовут дважды, - но спрашивается здесь не он, а контракт
        // самой `untailed`: снятое ею применение обязано быть **единственным**.
        // Отдай она `Some`, и всякий читатель, у которого нет проверки на
        // повторное упоминание, принял бы эту ветку за хвостовую.
        let value = Term::App(Rc::new(Term::var(0)), Rc::new(Term::constant("Zero")));
        let body = Term::App(Rc::new(Term::var(1)), Rc::new(Term::var(0)));
        assert_eq!(super::untailed(&bound(value, body), 0), None);
    }

    #[test]
    fn resuming_twice_is_general_even_when_the_outer_call_is_tail() {
        // `resume (resume Zero)`: хвост снят, а имя осталось - значит зовут её
        // дважды, и сегмент режется.
        let inner = Term::App(Rc::new(Term::var(0)), Rc::new(Term::constant("Zero")));
        assert_eq!(
            branched(Term::App(Rc::new(Term::var(0)), Rc::new(inner))),
            Verdict::General
        );
    }

    #[test]
    fn a_resumption_named_but_not_applied_is_general() {
        // `MkBox resume`: резумпция уходит значением, а не зовётся.
        assert_eq!(
            branched(Term::App(
                Rc::new(Term::constant("MkBox")),
                Rc::new(Term::var(0))
            )),
            Verdict::General
        );
    }

    #[test]
    fn a_branch_that_never_names_the_resumption_is_abortive() {
        assert_eq!(branched(Term::constant("Zero")), Verdict::Abortive);
        assert_eq!(
            branched(bound(Term::constant("Zero"), Term::constant("Zero"))),
            Verdict::Abortive
        );
    }

    #[test]
    fn a_multishot_branch_gets_no_verdict_of_its_own() {
        let term = Term::Lam(
            Mult::Many,
            "resume".into(),
            Rc::new(Term::App(
                Rc::new(Term::var(0)),
                Rc::new(Term::constant("Zero")),
            )),
        );
        assert_eq!(branch(&term, 0, false), Verdict::Tail);
        assert_eq!(branch(&term, 0, true), Verdict::General);
    }

    #[test]
    fn a_branch_that_binds_fewer_arguments_than_declared_is_general() {
        // Форма нарушена: разбирать нечего, и ответ идёт в консервативную
        // сторону, а не в «похоже на хвостовую».
        let term = Term::Lam(
            Mult::One,
            "resume".into(),
            Rc::new(Term::App(
                Rc::new(Term::var(0)),
                Rc::new(Term::constant("Zero")),
            )),
        );
        assert_eq!(branch(&term, 3, false), Verdict::General);
    }
}
