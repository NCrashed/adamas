//! Классы и их инстансы: реестр и разрешение (§3.5, §4.1).
//!
//! По §3.5 класс есть module type плюс режим разрешения, а инстанс - его
//! module value. Отсюда и реализация: класс объявляется типом записи,
//! параметризованным своими аргументами, инстанс - записью, а метод -
//! определением верхнего уровня, проецирующим словарь.
//!
//! # Разрешение отложено, и иначе нельзя
//!
//! Вставка имплиситов **энергичная** (§4.1): аргумент выводится там, где имя
//! встретилось. У словаря в этот момент неизвестен тип - `compare Zero Zero`
//! вставляет его раньше, чем аргументы решат `a := Nat`. Поэтому словарь
//! вставляется обычной дыркой, а поиском заполняется потом, когда проверка уже
//! всё решила. Тем же порядком считаются носители (§10 вопрос 76): сначала
//! проверка, потом фаза, читающая её результат.
//!
//! Отдельного списка обязательств при этом не нужно: дырка, дожившая до конца
//! проверки, - и есть обязательство, а класс ли у неё в типе, видно по нему
//! самому.

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::eval::quote;
use adamas_core::meta::{Metas, unsolved_term_meta, zonk_term};
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::Term;
use adamas_core::value::Value;
use adamas_parser::ast::Symbol;

use crate::error::ElabError;

/// Объявленные классы и их инстансы.
///
/// Живёт рядом с сигнатурой, а не в ней: ядро о классах не знает и знать не
/// должно - для него словарь есть обычная запись, а метод обычная проекция.
#[derive(Debug, Default)]
pub struct Instances {
    /// Объявленные классы и то, что о них знает разрешение.
    classes: HashMap<Symbol, Class>,
    /// Кандидаты: класс и голова аргумента - имя объявленного словаря.
    ///
    /// Голова, а не тип целиком: `instance Eqv (List a)` этим срезом не
    /// поддержан, поэтому ключ однозначен. Область видимости одна на прогон -
    /// импортов в языке ещё нет, и вопрос 48 (приоритет при импорте) пока не
    /// имеет предмета.
    candidates: HashMap<(Symbol, Symbol), Symbol>,
    /// Именованные кандидаты по той же паре.
    ///
    /// Список, а не один: имя нужно ровно тем инстансам, которых на один
    /// тип несколько (§4.3). Пока такой один, разрешение берёт его само;
    /// несколько - отказ с требованием `using`.
    named: HashMap<(Symbol, Symbol), Vec<Symbol>>,
}

/// Чем разрешение отвечает на пару «класс, голова».
pub(crate) enum Candidate {
    /// Кандидат один - он и берётся.
    One(Symbol),
    /// Кандидата нет.
    None,
    /// Именованных несколько: выбрать автоматика не вправе.
    Many(Vec<Symbol>),
}

/// Что о классе знают разрешение и объявление инстанса.
#[derive(Debug, Default)]
pub struct Class {
    /// Сколько полей словаря занимают суперклассы. Стоят они **первыми**:
    /// разряжает их объявление инстанса, а не автор.
    pub superclasses: usize,
    /// Методы в порядке объявления.
    pub methods: Vec<Symbol>,
    /// Умолчания: клаузы, написанные в самом классе.
    ///
    /// Хранятся написанными, а не элаборированными: тело умолчания зовёт
    /// другие методы того же класса, и словарь для них - тот, который
    /// объявляет инстанс. Раскрывается умолчание поэтому **в инстансе**, где
    /// этот словарь уже собирается.
    pub defaults: HashMap<Symbol, Vec<adamas_parser::ast::Clause>>,
}

impl Instances {
    /// Объявлен ли класс с таким именем.
    #[must_use]
    pub fn is_class(&self, name: &str) -> bool {
        self.classes.contains_key(name)
    }

    /// Что известно о классе.
    #[must_use]
    pub fn class(&self, name: &str) -> Option<&Class> {
        self.classes.get(name)
    }

    /// Запоминает класс.
    pub fn declare(&mut self, name: &Symbol, class: Class) {
        self.classes.insert(Rc::clone(name), class);
    }

    /// Запоминает анонимный инстанс. `false` - такой уже есть.
    pub fn add(&mut self, class: &Symbol, head: &Symbol, name: Symbol) -> bool {
        self.candidates
            .insert((Rc::clone(class), Rc::clone(head)), name)
            .is_none()
    }

    /// Запоминает именованный инстанс. Их на пару бывает сколько угодно.
    pub fn add_named(&mut self, class: &Symbol, head: &Symbol, name: Symbol) {
        self.named
            .entry((Rc::clone(class), Rc::clone(head)))
            .or_default()
            .push(name);
    }

    /// Кандидат для `class head`.
    ///
    /// Анонимный выигрывает всегда: он и объявлен как «тот самый». Его нет -
    /// берётся единственный именованный; несколько - выбирать автоматике
    /// нечем, и об этом надо сказать, а не молча взять первый.
    fn candidate(&self, class: &Symbol, head: &Symbol) -> Candidate {
        let key = (Rc::clone(class), Rc::clone(head));
        if let Some(found) = self.candidates.get(&key) {
            return Candidate::One(Rc::clone(found));
        }
        match self.named.get(&key).map(Vec::as_slice) {
            Some([one]) => Candidate::One(Rc::clone(one)),
            Some(many) if many.len() > 1 => Candidate::Many(many.to_vec()),
            _ => Candidate::None,
        }
    }
}

/// Заполняет словари, оставшиеся дырками после проверки.
///
/// Дырка, чей тип есть применение класса, решается **поиском**: у неё нет
/// уравнения, которое бы её определило, и унификация здесь не при чём (§3.5).
/// Дырка с любым другим типом остаётся как была - о ней скажет объявление,
/// которому нерешённая дырка запрещена.
///
/// Проверка здесь нужна **до** поиска: тип словаря становится известен её
/// решениями, а не сам по себе. Зовётся она только если дырка вообще есть,
/// поэтому обычное определение за классы не платит.
///
/// # Errors
///
/// Инстанса для написанного типа нет.
pub fn resolve(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    declaring: Option<&Declaring>,
    term: &Term,
    ty: &Term,
    span: Span,
) -> Result<(), ElabError> {
    if unsolved_term_meta(metas, term).is_none() && unsolved_term_meta(metas, ty).is_none() {
        return Ok(());
    }
    // Дырка есть - значит нужна проверка: её решения и делают тип словаря
    // известным. Не сошлось - здесь молчим: об этом скажет объявление, где у
    // ошибки есть маршрут по терму.
    let _ =
        adamas_core::check::check_within(&adamas_core::ctx::Ctx::new(signature), metas, term, ty);
    // И тело, и тип: словарь стоит в обоих - `witnessed : Wit (eq Zero Zero)`
    // несёт его в написанном типе, а не в теле.
    settle(signature, metas, instances, declaring, ty, span)?;
    settle(signature, metas, instances, declaring, term, span)?;
    // Проверка ещё раз - по решениям, которые поиск только что вставил. Их
    // собственные аргументы уровня иначе не свяжет никто: `infer` у дырки
    // читает объявленный тип, а не решение, и уровень рекурсивной ссылки
    // остался бы нерешённым до самого объявления.
    // По **зонканному**: решение живёт внутри дырки, а `infer` у дырки читает
    // объявленный тип, не решение. Пока решение не подставлено, его
    // собственные аргументы уровня не связывает никто.
    let zonked = zonk_term(metas, term);
    let _ = adamas_core::check::check_within(
        &adamas_core::ctx::Ctx::new(signature),
        metas,
        &zonked,
        ty,
    );
    Ok(())
}

/// Заполняет словари по уже проверенному терму.
fn settle(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    declaring: Option<&Declaring>,
    term: &Term,
    span: Span,
) -> Result<(), ElabError> {
    // Дырки, заведённые самим разрешением: их в терме нет - они живут в
    // решении той дырки, ради которой заведены, - а решать их надо тем же
    // циклом. Так рекурсия по контексту инстанса получается из очереди.
    let mut pending: Vec<adamas_core::term::TermMeta> = Vec::new();
    loop {
        let meta = match pending.pop() {
            Some(meta) if metas.term_solution(meta).is_none() => meta,
            Some(_) => continue,
            None => match unsolved_term_meta(metas, term) {
                Some(meta) => meta,
                None => return Ok(()),
            },
        };
        // Тип дырки замкнут по построению, поэтому читается на нулевой
        // глубине; зонканье подставляет всё, что решила проверка.
        let ty = zonk_term(metas, &quote(0, metas.term_type(meta)));
        // Цель **вычисляется**: зонканье подставляет решение дырки лямбдой, и
        // `Eqv ((\m -> Nat) x)` синтаксически головы не имеет. Тот же порядок,
        // что у носителей: сперва вычислить, потом читать голову.
        let goal = normalized(signature, &ty);
        // Дырка не про класс - её сюда и не звали: решить её могла только
        // унификация, и о том, что не решила, скажет объявление.
        let Some((class, head)) = applied(&goal) else {
            return Ok(());
        };
        if !instances.is_class(&class) {
            return Ok(());
        }
        // Локальный словарь **раньше** глобального инстанса: он и есть тот,
        // о котором договорилась сигнатура, а искать инстанс для переменной
        // всё равно негде. Так пишется всякая полиморфная функция над
        // классом - `same : {Eqv a} => a -> a -> Bool`.
        if let Some(solution) = from_context(signature, metas, instances, &ty) {
            metas.solve_term(meta, solution);
            continue;
        }
        let head = match head {
            Head::Named(name) => name,
            // Голова-переменная: инстанса для неё нет и быть не может, а
            // словарь из контекста уже не нашёлся.
            Head::Rigid => {
                return Err(ElabError::NoInstance {
                    class,
                    head: Rc::from("переменная"),
                    span,
                });
            }
            // Голова не определилась вовсе - решать её должна была
            // унификация, и о том, что не решила, скажет объявление.
            Head::Unknown => return Ok(()),
        };
        // Объявляемый сейчас инстанс собой сослаться не может - в сигнатуре
        // его ещё нет, - и словарь для него собирается **записью из членов**.
        if let Some(inner) = declaring.filter(|it| it.matches(&class, &head)) {
            let Some(solution) = inner.dictionary(signature, metas, &ty) else {
                return Err(ElabError::NoInstance { class, head, span });
            };
            metas.solve_term(meta, solution);
            continue;
        }
        let name = match instances.candidate(&class, &head) {
            Candidate::One(name) => name,
            Candidate::None => return Err(ElabError::NoInstance { class, head, span }),
            Candidate::Many(candidates) => {
                return Err(ElabError::AmbiguousInstance {
                    class,
                    head,
                    candidates,
                    span,
                });
            }
        };
        let Some(dictionary) = signature.instantiate(&name, metas) else {
            return Err(ElabError::NoInstance { class, head, span });
        };
        let Some((solution, fresh)) = applied_candidate(signature, metas, &ty, &dictionary) else {
            return Err(ElabError::NoInstance { class, head, span });
        };
        metas.solve_term(meta, solution);
        pending.extend(fresh);
    }
}

/// Цель дырки - то, чем оканчивается телескоп её типа.
fn goal_of(ty: &Term) -> &Term {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    current
}

/// Связывание контекста, чей тип и есть цель.
///
/// Тип дырки - телескоп по контексту, оканчивающийся целью, а сама дырка
/// применена к контексту целиком. Значит подходящее связывание - решение:
/// `\x0 … xn -> xk`, и применение к спайну выдаёт ровно его.
///
/// `Let` в телескопе обрывает поиск: определённое связывание в спайн дырки не
/// попадает (`fresh_term_over`), и числа лямбд по телескопу уже не посчитать.
/// Названная граница - словарь, объявленный `let`-ом, отсюда не виден.
fn from_context(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    ty: &Term,
) -> Option<Rc<Value>> {
    let mut ctx = adamas_core::ctx::Ctx::new(signature);
    let mut binders = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, name, domain, _, codomain) = current {
        let value = ctx.eval(domain);
        binders.push((binder.mult, Rc::clone(name), Rc::clone(&value)));
        ctx = ctx.bind(Rc::clone(name), binder.mult, value);
        current = codomain;
    }
    if matches!(current, Term::Let(..)) {
        return None;
    }
    let goal = ctx.eval(current);
    let arity = binders.len();
    // Сперва прямое совпадение, потом путь через суперкласс: словарь `Ord a`
    // несёт `Eqv a` полем, и §3.5 разряжает его именно так - проекцией, а не
    // отдельным поиском.
    let mut taken = None;
    for (at, (_, _, domain)) in binders.iter().enumerate() {
        if adamas_core::conv::convertible(signature, metas, ctx.size(), domain, &goal) {
            taken = Some((at, Vec::new()));
            break;
        }
        if let Some(path) =
            superclass_path(signature, metas, instances, domain, &goal, ctx.size(), 8)
        {
            taken = Some((at, path));
            break;
        }
    }
    let (found, path) = taken?;
    let index = u32::try_from(arity - 1 - found).ok()?;
    let taken = path.into_iter().fold(Term::var(index), |inner, field| {
        Term::Project(Rc::new(inner), field)
    });
    let solution = binders.iter().rev().fold(taken, |body, (mult, name, _)| {
        Term::Lam(*mult, Rc::clone(name), Rc::new(body))
    });
    Some(adamas_core::eval::eval(
        &adamas_core::value::Env::default(),
        &solution,
    ))
}

/// Имя класса и голова его первого аргумента: `Eqv Nat` даёт `(Eqv, Some(Nat))`.
///
/// Внешний `None` - тип не применение определения, то есть словарём он не
/// является вовсе. Внутренний - голова аргумента переменная, и кандидата для
/// неё искать негде.
fn applied(ty: &Term) -> Option<(Symbol, Head)> {
    let Term::App(callee, argument) = ty else {
        return None;
    };
    let Term::Const(class, _) = &**callee else {
        return None;
    };
    let mut head = &**argument;
    while let Term::App(inner, _) = head {
        head = inner;
    }
    let found = match head {
        Term::Const(name, _) => Head::Named(Rc::clone(name)),
        // Переменная - полиморфный случай: словарь приходит из контекста.
        Term::Var(_) => Head::Rigid,
        _ => Head::Unknown,
    };
    Some((Rc::clone(class), found))
}

/// Голова аргумента цели.
enum Head {
    /// Определение - по нему и ищется кандидат.
    Named(Symbol),
    /// Переменная: кандидата для неё нет и быть не может.
    Rigid,
    /// Ещё не определилась.
    Unknown,
}

/// Цель дырки, приведённая к нормальной форме под своим телескопом.
fn normalized(signature: &Signature, ty: &Term) -> Term {
    let binders = binders_of(ty);
    let mut ctx = adamas_core::ctx::Ctx::new(signature);
    for (mult, name, domain) in &binders {
        let value = ctx.eval(domain);
        ctx = ctx.bind(Rc::clone(name), *mult, value);
    }
    let goal = ctx.eval(goal_of(ty));
    quote(ctx.size(), &goal)
}

/// Инстанс, который объявляется прямо сейчас.
///
/// Ссылаться на него именем нельзя - в сигнатуре его ещё нет, - поэтому
/// словарь собирается записью из членов. Самореференция члена при этом
/// обычная: он объявляется определением и видит себя (решение 2026-08-31).
#[derive(Clone, Debug)]
pub struct Declaring {
    /// Имя класса.
    pub class: Symbol,
    /// Голова аргумента.
    pub head: Symbol,
    /// Сколько ведущих связываний у словаря: столько же у каждого члена.
    pub prefix: usize,
    /// Члены: короткое имя поля и терм, которым член берётся.
    pub members: Vec<(Symbol, Term)>,
}

impl Declaring {
    /// Про этот ли инстанс цель.
    fn matches(&self, class: &Symbol, head: &Symbol) -> bool {
        self.class == *class && self.head == *head
    }

    /// Словарь записью из членов, применённых к ведущим связываниям цели.
    ///
    /// Телескоп цели начинается ровно теми связываниями, что стоят у членов:
    /// член объявлен под тем же префиксом, что и сам словарь. Значит аргументы
    /// - первые `prefix` переменных телескопа.
    fn dictionary(&self, signature: &Signature, metas: &mut Metas, ty: &Term) -> Option<Rc<Value>> {
        let binders = binders_of(ty);
        let size = binders.len();
        if size < self.prefix {
            return None;
        }
        let mut written = Vec::with_capacity(self.members.len());
        for (field, member) in &self.members {
            let mut term = member.clone();
            for position in 0..self.prefix {
                let index = u32::try_from(size - 1 - position).ok()?;
                term = Term::App(Rc::new(term), Rc::new(Term::var(index)));
            }
            written.push((Rc::clone(field), Rc::new(term)));
        }
        let object = Term::Object(written.into());
        let solution = abstracted(&binders, object);
        let _ = (signature, metas);
        Some(adamas_core::eval::eval(
            &adamas_core::value::Env::default(),
            &solution,
        ))
    }
}

/// Связывания телескопа дырки: кратность, имя и тип на своей глубине.
fn binders_of(ty: &Term) -> Vec<(adamas_core::mult::Mult, adamas_core::term::Name, Rc<Term>)> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, name, domain, _, codomain) = current {
        found.push((binder.mult, Rc::clone(name), Rc::clone(domain)));
        current = codomain;
    }
    found
}

/// Оборачивает тело лямбдами по телескопу.
fn abstracted(
    binders: &[(adamas_core::mult::Mult, adamas_core::term::Name, Rc<Term>)],
    body: Term,
) -> Term {
    binders.iter().rev().fold(body, |inner, (mult, name, _)| {
        Term::Lam(*mult, Rc::clone(name), Rc::new(inner))
    })
}

/// Кандидат, применённый к дыркам на каждое ведущее выводимое связывание.
///
/// Инстанс с контекстом - не значение, а функция от словарей (§3.5), поэтому
/// сослаться на него именем мало: `Eqv#List` надо применить к `?a` и к словарю
/// `Eqv ?a`, а сам этот словарь вернётся в цикл и решится следующим шагом.
/// Так рекурсия разрешения получается из цикла, а не из отдельного обхода.
fn applied_candidate(
    signature: &Signature,
    metas: &mut Metas,
    ty: &Term,
    candidate: &Term,
) -> Option<(Rc<Value>, Vec<adamas_core::term::TermMeta>)> {
    let binders = binders_of(ty);
    let size = u32::try_from(binders.len()).ok()?;
    let mut ctx = adamas_core::ctx::Ctx::new(signature);
    for (mult, name, domain) in &binders {
        let value = ctx.eval(domain);
        ctx = ctx.bind(Rc::clone(name), *mult, value);
    }
    let goal = ctx.eval(goal_of(ty));
    let mut term = candidate.clone();
    let mut fresh = Vec::new();
    let (mut current, _) =
        adamas_core::check::infer(&ctx, metas, adamas_core::mult::Mult::Zero, candidate).ok()?;
    while let Value::Pi(binder, _, domain, _, codomain) = &*current.clone() {
        if !binder.visibility.is_implicit() {
            break;
        }
        // Тип дырки - тот же телескоп, но оканчивающийся доменом связывания.
        let over = abstracted_pi(&binders, quote(size, domain));
        let argument = metas.fresh_term(ctx.eval(&over), size);
        if let Some(created) = head_meta(&argument) {
            fresh.push(created);
        }
        let value = ctx.eval(&argument);
        term = Term::App(Rc::new(term), Rc::new(argument));
        current = codomain.clone().apply(value);
    }
    if !adamas_core::conv::convertible(signature, metas, size, &current, &goal) {
        return None;
    }
    Some((
        adamas_core::eval::eval(
            &adamas_core::value::Env::default(),
            &abstracted(&binders, term),
        ),
        fresh,
    ))
}

/// Дырка в голове написанного применения.
fn head_meta(term: &Term) -> Option<adamas_core::term::TermMeta> {
    let mut current = term;
    while let Term::App(callee, _) = current {
        current = callee;
    }
    match current {
        Term::Meta(meta) => Some(*meta),
        _ => None,
    }
}

/// Телескоп `Pi` над написанным телом - тип дырки, стоящей в том же контексте.
fn abstracted_pi(
    binders: &[(adamas_core::mult::Mult, adamas_core::term::Name, Rc<Term>)],
    body: Term,
) -> Term {
    binders.iter().rev().fold(body, |inner, (mult, name, ty)| {
        Term::Pi(
            adamas_core::term::Binder::explicit(*mult),
            Rc::clone(name),
            Rc::clone(ty),
            adamas_core::row::Row::empty(),
            Rc::new(inner),
        )
    })
}

/// Путь по полям-суперклассам от словаря `domain` к цели.
///
/// Пустой путь означал бы сам словарь, и его проверяет вызывающий; здесь
/// путь всегда непуст. Топливо - от класса, объявленного суперклассом самому
/// себе: язык этого не запрещает, а поиск обязан закончиться.
fn superclass_path(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    domain: &Rc<Value>,
    goal: &Rc<Value>,
    size: u32,
    fuel: u32,
) -> Option<Vec<adamas_core::term::Name>> {
    if fuel == 0 {
        return None;
    }
    let quoted = quote(size, domain);
    let (class, _) = applied(&quoted)?;
    let count = instances.class(&class)?.superclasses;
    if count == 0 {
        return None;
    }
    let record = adamas_core::conv::whnf(signature, domain);
    let Value::Record(telescope) = &*record else {
        return None;
    };
    for index in 0..count {
        // Поля суперклассов идут первыми и друг от друга не зависят, поэтому
        // предыдущие значения им безразличны.
        let earlier: Vec<Rc<Value>> = (0..index)
            .map(|at| {
                Value::var(adamas_core::value::Lvl(
                    size + u32::try_from(at).unwrap_or(0),
                ))
            })
            .collect();
        let field = telescope.at(index, &earlier);
        let name = adamas_core::term::Name::from(format!("#super{index}").as_str());
        if adamas_core::conv::convertible(signature, metas, size, &field, goal) {
            return Some(vec![name]);
        }
        if let Some(mut path) =
            superclass_path(signature, metas, instances, &field, goal, size, fuel - 1)
        {
            path.insert(0, name);
            return Some(path);
        }
    }
    None
}
