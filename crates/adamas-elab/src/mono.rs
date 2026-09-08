//! Мономорфизация имплиситов: специализация по словарям (§4.11, §6).
//!
//! Проход core → core. На входе - **зонканный** терм, на выходе - терм, в
//! котором имплиситных применений словарей не осталось: всякий вызов, чей
//! словарь известен на месте, заменён ссылкой на производное определение, где
//! словарь уже подставлен. Производные объявляются в той же сигнатуре и
//! проверяются ею же - специализация обязана типизироваться, иначе это не
//! подстановка, а другая программа.
//!
//! # Почему это обязательство, а не оптимизация
//!
//! §4.11: обобщённый код над `{Flat a}` получает дескриптор layout обычным
//! имплиситом и индексирует с рантайм-stride'ом, а константой stride делает
//! специализация. §6 называет её обязательством для release и платит за неё
//! неограниченным временем сборки. Размен ограничен режимом: `adamas check`
//! специализации не делает вовсе, debug компилирует по дескриптору - и обе
//! петли обратной связи за неё не платят.
//!
//! # Что подставляется
//!
//! **Ведущий ряд имплиситных связываний целиком**, если хоть одно из них -
//! словарь. Не один только словарь: у `same : {0 a : Type} -> {ω d : Eqv a} ->
//! …` словарь стоит под своим же типовым параметром, и подстановка одного `d`
//! оставила бы замкнутый терм под связыванием, от которого его тип зависит.
//!
//! Граница названа: имплисит, стоящий **после** написанного аргумента, не
//! специализируется - подстановка обязана поднять аргумент в определение
//! верхнего уровня, а написанный аргумент до неё уже связан. Сегодня такой
//! формы не бывает, констрейнт пишется слева от стрелки (§4.1), и о её
//! появлении скажет [`residual`].
//!
//! # Чего проход не трогает
//!
//! **Стёртые позиции.** Тип связывания, мотив разбора, телескоп записи -
//! рантайма в них нет, а с ним нет и словаря, который куда-то передаётся.
//! Обход идёт по тем позициям, где значение доживает до исполнения.
//!
//! **Запечатанное** (§3.5). Специализация есть δ-разворот, а снаружи `:>` он
//! запрещён; произвести определение из скрытого тела значило бы обойти запрет.
//!
//! **Не ground место вызова.** Аргументы уровня, row или кратности, несущие
//! параметры вызывающего, оставляются как есть: производное определение живёт
//! наверху, и параметру вызывающего в нём не на что указывать. Ground корень
//! это свойство сохраняет - тело специализации получается подстановкой ground
//! аргументов, - поэтому проход, начатый на замкнутой программе, доходит до
//! конца.
//!
//! **Ссылку с недописанной арностью** и всё, что её содержит. Такие ссылки
//! есть в элаборированной программе: словарь объявляемого инстанса собирается
//! записью из членов, которых в сигнатуре ещё нет, и член выходит без
//! row-аргумента. На месте использования это законно - параметр остаётся
//! параметром и сравнивается как есть, - а в производном определении ему не на
//! что указывать: параметров у него нет.
//!
//! **Определение с параметром кратности** (§10 вопрос 115). Переход `Field(i)`
//! в `Var(i)` делается на границе объявления метода, и производное определение
//! без параметров эту связь теряет: проекция в его теле осталась бы с `q0`,
//! которого тип уже не несёт.
//!
//! Границы наблюдаемы: `mono::residual` называет то, что после прохода всё ещё
//! получает словарь. На golden-корпусе под них попадают четыре программы из
//! сорока шести.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use adamas_core::error::TypeError;
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::{Definition, DefinitionKind, Group, Member, Signature};
use adamas_core::term::{Args, Branch, Case, Field, Fields, Index, Name, Term};

use crate::class::{Instances, applied, goal_of};

/// Отказ прохода.
#[derive(Debug, thiserror::Error)]
pub enum MonoError {
    /// Специализаций больше предела: цепочка типов не убывает.
    #[error(
        "специализаций больше {limit}: обобщённый код зовёт себя на всё новых типах, \
         и мономорфизация не заканчивается"
    )]
    Runaway {
        /// Сам предел.
        limit: usize,
    },
    /// Производное определение не прошло проверку ядром.
    #[error("специализация не типизируется: {error}")]
    Refused {
        /// Отказ ядра.
        error: Box<TypeError>,
    },
}

/// Результат прохода.
#[derive(Debug)]
pub struct Specialised {
    /// Терм после подстановки словарей.
    pub term: Term,
    /// Имена произведённых определений в порядке появления.
    ///
    /// Возвращаются потому, что обещание прохода - про них тоже: словарь,
    /// уехавший из корня в тело специализации, никуда не делся, и остаток
    /// проверяется по всей произведённой группе.
    pub created: Vec<Name>,
}

/// Сколько производных определений разрешено произвести на один терм.
///
/// Предел стоит потому, что мономорфизация в общем случае не заканчивается:
/// полиморфная рекурсия под констрейнтом - `f : {Eqv a} => a -> Bool`, зовущая
/// себя на `List a`, - требует специализации на каждом слое, и цепочка типов не
/// убывает. Отвечать на это надо отказом, а не бесконечной сборкой; так же
/// отвечает Rust. Порядок величины взят с запасом от живого кода: специализаций
/// у него столько, сколько пар «определение - словарь», то есть сотни.
const LIMIT: usize = 4096;

/// Сколько проекций подряд разрешено развернуть, добираясь до члена.
///
/// Цепочка конечна - словарь суперкласса лежит полем словаря, - но замыкать её
/// конечность на честность объявления не стоит: класс, объявленный
/// суперклассом самому себе, языком не запрещён. Тот же довод, что у топлива в
/// [`crate::class`].
const PROJECTIONS: u32 = 16;

/// Подставляет известные словари, объявляя производные определения.
///
/// Терм обязан быть зонканным и ground: аргументы уровня, row и кратности в
/// нём - значения, а не параметры. Так его отдаёт драйвер, инстанцируя тело
/// определения перед вычислением.
///
/// # Errors
///
/// Специализаций оказалось больше предела; производное определение не прошло
/// проверку ядром.
pub fn specialise(
    signature: &mut Signature,
    metas: &mut Metas,
    instances: &Instances,
    term: &Term,
) -> Result<Specialised, MonoError> {
    let mut made: Vec<Special> = Vec::new();
    let term = {
        let mut pass = Pass {
            signature,
            instances,
            made: &mut made,
            carried: HashMap::new(),
        };
        let term = pass.rewrite(term)?;
        // Тела произведённых определений идут тем же проходом: словарь,
        // подставленный в одно, открывает следующий. Очередь, а не рекурсия, -
        // специализация заводится посреди обхода, и обход её же тела был бы
        // рекурсией по цепочке инстансов.
        let mut at = 0;
        while at < pass.made.len() {
            let written = pass.made[at].body.clone();
            let body = pass.rewrite(&written)?;
            pass.made[at].body = body;
            at += 1;
        }
        term
    };
    let created = made.iter().map(|it| Rc::clone(&it.name)).collect();
    declare(signature, metas, &made)?;
    Ok(Specialised { term, created })
}

/// Определения, которым программа под термом всё ещё передаёт словарь
/// имплиситом.
///
/// Обещание прохода в наблюдаемой форме: список пуст - словарей не передаётся
/// нигде, куда терм дотягивается. Транзитивно, и иначе нельзя: `main`, зовущий
/// `logged`, сам словаря не передаёт, а `logged` передаёт, и ответ «в корне
/// чисто» был бы правдой ни о чём.
///
/// Смотрит на **написанное** связывание, а не на то, специализируемо ли оно:
/// вопрос «остался ли словарь» от границ прохода не зависит.
#[must_use]
pub fn residual(signature: &Signature, instances: &Instances, term: &Term) -> Vec<Name> {
    let mut found = Found::default();
    scan(signature, instances, term, &mut found);
    let mut seen: HashSet<Name> = HashSet::new();
    while let Some(name) = found.called.pop() {
        if !seen.insert(Rc::clone(&name)) {
            continue;
        }
        let Some(body) = signature.lookup(&name).and_then(|it| it.body.as_ref()) else {
            continue;
        };
        scan(signature, instances, body, &mut found);
    }
    found.dictionaries
}

/// Присваивания полей записи, как они лежат в терме.
type Assignments = Rc<[(Name, Rc<Term>)]>;

/// Производное определение: тело оригинала с подставленными имплиситами.
#[derive(Debug)]
struct Special {
    /// Имя, под которым оно объявляется: `same@Nat,Eqv#Nat`.
    name: Name,
    /// Определение, от которого оно произведено.
    origin: Name,
    /// Аргументы уровня места вызова.
    levels: Rc<[Level]>,
    /// Аргументы-row места вызова.
    rows: Vec<Row<Term>>,
    /// Аргументы-кратности места вызова.
    mults: Vec<Mult>,
    /// Подставленные имплиситные аргументы - они же ключ.
    arguments: Vec<Term>,
    /// Тип после подстановки.
    ty: Term,
    /// Тело: сперва подставленное, потом - оно же после собственного прохода.
    body: Term,
}

/// Состояние обхода.
struct Pass<'a> {
    signature: &'a Signature,
    instances: &'a Instances,
    made: &'a mut Vec<Special>,
    /// Что известно про определения: тянется ли из-под них словарь.
    carried: HashMap<Name, bool>,
}

impl Pass<'_> {
    /// Терм с подставленными словарями.
    fn rewrite(&mut self, term: &Term) -> Result<Term, MonoError> {
        match term {
            // Сорта, переменные и дырки словарей не несут. Типы - тоже: они
            // стёрты, передавать в них нечего.
            Term::Var(_)
            | Term::Meta(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Pi(..)
            | Term::Record(_)
            | Term::Row(_) => Ok(term.clone()),
            Term::App(..) | Term::Const(..) => self.call(term),
            Term::Lam(mult, name, body) => Ok(Term::Lam(
                *mult,
                Rc::clone(name),
                Rc::new(self.rewrite(body)?),
            )),
            // Тип связывания не трогается по той же причине, что и `Pi`.
            Term::Let(mult, name, ty, value, body) => Ok(Term::Let(
                *mult,
                Rc::clone(name),
                Rc::clone(ty),
                Rc::new(self.rewrite(value)?),
                Rc::new(self.rewrite(body)?),
            )),
            Term::Object(fields) => Ok(Term::Object(self.assignments(fields)?)),
            Term::With(base, fields) => Ok(Term::With(
                Rc::new(self.rewrite(base)?),
                self.assignments(fields)?,
            )),
            Term::Project(base, field) => match self.projected(base, field, PROJECTIONS) {
                // Развёрнутая проекция - другой терм со своей головой, и
                // специализировать её обязан тот же проход.
                Some(found) => self.rewrite(&found),
                None => Ok(Term::Project(
                    Rc::new(self.rewrite(base)?),
                    Rc::clone(field),
                )),
            },
            Term::Case(case) => {
                let mut branches = Vec::with_capacity(case.branches.len());
                for branch in &case.branches {
                    branches.push(Branch {
                        constructor: Rc::clone(&branch.constructor),
                        body: Rc::new(self.rewrite(&branch.body)?),
                    });
                }
                Ok(Term::Case(Rc::new(Case {
                    data: Rc::clone(&case.data),
                    levels: Rc::clone(&case.levels),
                    params: case.params,
                    consumed: case.consumed,
                    scrutinee: Rc::new(self.rewrite(&case.scrutinee)?),
                    // Мотив стёрт: он про тип результата, а не про значение.
                    motive: Rc::clone(&case.motive),
                    branches,
                })))
            }
        }
    }

    /// Присваивания полей записи - общее у значения и у переопределения.
    fn assignments(&mut self, fields: &[(Name, Rc<Term>)]) -> Result<Assignments, MonoError> {
        let mut written = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            written.push((Rc::clone(name), Rc::new(self.rewrite(value)?)));
        }
        Ok(written.into())
    }

    /// Применение: голова специализируется, аргументы идут своим чередом.
    fn call(&mut self, term: &Term) -> Result<Term, MonoError> {
        let (head, arguments) = spine(term);
        let Term::Const(name, levels, args) = head else {
            let mut built = self.rewrite(head)?;
            for argument in arguments {
                built = Term::App(Rc::new(built), Rc::new(self.rewrite(argument)?));
            }
            return Ok(built);
        };
        let (mut built, rest) = match self.plan(name, levels, args, &arguments)? {
            Some((found, taken)) => (
                Term::Const(found, Rc::from([]), Args::none()),
                &arguments[taken..],
            ),
            None => (head.clone(), &arguments[..]),
        };
        for argument in rest {
            built = Term::App(Rc::new(built), Rc::new(self.rewrite(argument)?));
        }
        Ok(built)
    }

    /// Имя специализации для этого места вызова и сколько аргументов она съела.
    ///
    /// `None` - подставлять нечего либо нельзя. Нечего: словаря под именем нет
    /// ни в связываниях, ни глубже. Нельзя: имя без тела, запечатанное,
    /// конструктор, параметр кратности, недописанная арность, не ground место
    /// вызова, незамкнутый аргумент, недописанная ссылка в теле. Каждая из
    /// границ названа там, где стоит.
    fn plan(
        &mut self,
        name: &Name,
        levels: &Rc<[Level]>,
        args: &Args,
        arguments: &[&Term],
    ) -> Result<Option<(Name, usize)>, MonoError> {
        let Some(definition) = self.signature.lookup(name) else {
            return Ok(None);
        };
        // Конструктор и операция копированию не подлежат: по имени
        // конструктора выбирается ветвь разбора, и производное имя выбирало бы
        // её мимо. Тела у них и нет, но сказать это вслух дешевле, чем
        // полагаться на отсутствие.
        if !matches!(definition.kind, DefinitionKind::Regular) {
            return Ok(None);
        }
        if definition.opaque || definition.body.is_none() || !ground(definition, levels, args) {
            return Ok(None);
        }
        // Параметр кратности не подставляется. Связь его с параметром **поля**
        // записи держит объявление метода: пространства у них раздельные (§10
        // вопрос 115), и переход `Field(i)` в `Var(i)` делается на границе
        // определения. Производное определение объявляется без параметров, и
        // проекция в его теле осталась бы с `q0`, которого тип уже не несёт.
        if !definition.mult_allowed.is_empty() {
            return Ok(None);
        }
        let ty = definition
            .ty
            .substitute_levels(levels)
            .substitute_rows(args.row_args())
            .substitute_mults(args.mult_args());
        let taken = leading(self.signature, self.instances, &ty);
        if arguments.len() < taken {
            return Ok(None);
        }
        // Ведущих словарей нет - копия всё равно нужна, если словарь стоит
        // глубже: `main` зовёт `logged`, а имплисит стоит в теле `logged`.
        // Определение, из-под которого словарь не тянется, остаётся собой.
        if taken == 0 && !self.carries(name) {
            return Ok(None);
        }
        // Словарь суперкласса приходит проекцией - `d.#super0`, - и до
        // подстановки она сводится: иначе одна и та же специализация заводится
        // дважды, под именем словаря и под именем поля, из которого он взят.
        let given: Vec<Term> = arguments[..taken]
            .iter()
            .map(|argument| match argument {
                Term::Project(base, field) => self
                    .projected(base, field, PROJECTIONS)
                    .unwrap_or_else(|| (*argument).clone()),
                _ => (*argument).clone(),
            })
            .collect();
        // Замкнутость обязательна: производное определение стоит наверху, и
        // связыванию вызывающего в нём не на что указывать. Промах здесь не
        // молчит - объявление отвергает терм со свободным индексом.
        if given.iter().any(open) {
            return Ok(None);
        }
        let rows: Vec<Row<Term>> = args.row_args().to_vec();
        let mults: Vec<Mult> = args.mult_args().to_vec();
        let known = self.made.iter().find(|it| {
            it.origin == *name
                && it.levels == *levels
                && it.rows == rows
                && it.mults == mults
                && it.arguments == given
        });
        if let Some(known) = known {
            return Ok(Some((Rc::clone(&known.name), taken)));
        }
        let Some((ty, body)) = instantiated(definition, levels, &rows, &mults, &given) else {
            return Ok(None);
        };
        // Недописанная ссылка внутри оставляет в теле параметр, а производное
        // определение объявляется без параметров: тип его разошёлся бы с телом
        // ровно на этот `e0`. Такое тело не подставляется - место вызова
        // остаётся написанным, и о словаре в нём скажет [`residual`].
        let mut inside = Found::default();
        scan(self.signature, self.instances, &body, &mut inside);
        for argument in &given {
            scan(self.signature, self.instances, argument, &mut inside);
        }
        if inside.short {
            return Ok(None);
        }
        if self.made.len() >= LIMIT {
            return Err(MonoError::Runaway { limit: LIMIT });
        }
        let derived = self.fresh(name, &given);
        self.made.push(Special {
            name: Rc::clone(&derived),
            origin: Rc::clone(name),
            levels: Rc::clone(levels),
            rows,
            mults,
            arguments: given,
            ty,
            body,
        });
        Ok(Some((derived, taken)))
    }

    /// Тянется ли из-под определения словарь, передаваемый имплиситом.
    ///
    /// Транзитивно по графу вызовов и с памятью: без неё цепочка определений
    /// обходилась бы заново на каждом упоминании.
    ///
    /// Имя, чей ответ ещё считается, отвечает «нет». Цикл в графе вызовов
    /// нового словаря не добавляет: словарь стоит в чьём-то теле, и это тело
    /// обходится своим чередом.
    fn carries(&mut self, name: &Name) -> bool {
        if let Some(known) = self.carried.get(name) {
            return *known;
        }
        let signature = self.signature;
        let Some(body) = signature.lookup(name).and_then(|it| it.body.as_ref()) else {
            return false;
        };
        self.carried.insert(Rc::clone(name), false);
        let mut found = Found::default();
        scan(signature, self.instances, body, &mut found);
        let mut carries = !found.dictionaries.is_empty();
        for called in found.called {
            if carries {
                break;
            }
            carries = self.carries(&called);
        }
        self.carried.insert(Rc::clone(name), carries);
        carries
    }

    /// Свободное имя для специализации.
    fn fresh(&self, origin: &Name, arguments: &[Term]) -> Name {
        let base = mangled(origin, arguments);
        let taken = |candidate: &str| {
            self.signature.lookup(candidate).is_some()
                || self.made.iter().any(|it| &*it.name == candidate)
        };
        if !taken(&base) {
            return Rc::from(base.as_str());
        }
        // Головы аргументов совпали, а сами аргументы нет: `f (List Nat)` и
        // `f (List Bool)` дают одно имя. Различает их номер.
        let mut at = 2;
        loop {
            let candidate = format!("{base}#{at}");
            if !taken(&candidate) {
                return Rc::from(candidate.as_str());
            }
            at += 1;
        }
    }

    /// Член словаря, к которому сводится проекция. `None` - не свелась.
    ///
    /// Проекция бывает вложена с обеих сторон, и обе разбираются здесь: база
    /// сама бывает проекцией - `d.#super0.eq` берёт метод из словаря
    /// суперкласса, - и полученное поле тоже, если словарь суперкласса взят
    /// полем. Результат поэтому заведомо не проекция: не свелось - `None`, и
    /// написанное остаётся написанным.
    fn projected(&self, base: &Term, field: &Name, fuel: u32) -> Option<Term> {
        let fuel = fuel.checked_sub(1)?;
        let reduced;
        let base = match base {
            Term::Project(inner, name) => {
                reduced = self.projected(inner, name, fuel)?;
                &reduced
            }
            _ => base,
        };
        let found = self.member(base, field)?;
        match &found {
            Term::Project(inner, name) => self.projected(inner, name, fuel),
            _ => Some(found),
        }
    }

    /// Один δ-шаг: поле словаря, чьё имя известно.
    fn member(&self, base: &Term, field: &Name) -> Option<Term> {
        let (head, arguments) = spine(base);
        let Term::Const(name, levels, args) = head else {
            return None;
        };
        let definition = self.signature.lookup(name)?;
        if definition.opaque || !ground(definition, levels, args) {
            return None;
        }
        if !dictionary(self.signature, self.instances, goal_of(&definition.ty)) {
            return None;
        }
        if arguments.iter().any(|it| open(it)) {
            return None;
        }
        let body = definition
            .body
            .as_ref()?
            .substitute_levels(levels)
            .substitute_rows(args.row_args())
            .substitute_mults(args.mult_args());
        let Term::Object(fields) = peeled(&body, arguments.len())? else {
            return None;
        };
        let (_, found) = fields.iter().find(|(it, _)| it == field)?;
        let given: Vec<Term> = arguments.iter().rev().map(|it| (*it).clone()).collect();
        Some(substituted(found, &Substitution::Closed(&given), 0))
    }
}

/// Тип и тело определения с подставленными аргументами места вызова.
///
/// Подстановка **синтаксическая**, а не вычислением, и это не выбор из двух
/// одинаковых. `NbE` подставил бы дешевле - окружение вместо обхода, - но заодно
/// и посчитал бы: `let u : Unit = emit Zero` в теле, чьё связывание дальше не
/// упоминается, вычислением исчезает вместе с операцией, которую `emit`
/// производит. Ядро считает чистый фрагмент (§9 Фаза 1), а проход обязан
/// сохранить программу целиком, включая порядок эффектов (§3.4). Свидетель -
/// договор двух вычислителей: разница видна ровно на нём.
fn instantiated(
    definition: &Definition,
    levels: &[Level],
    rows: &[Row<Term>],
    mults: &[Mult],
    given: &[Term],
) -> Option<(Term, Term)> {
    let instance = |term: &Term| {
        term.substitute_levels(levels)
            .substitute_rows(rows)
            .substitute_mults(mults)
    };
    let ty = instance(&definition.ty);
    let body = instance(definition.body.as_ref()?);
    // Аргументы идут снаружи внутрь, индексы - изнутри наружу: под всеми
    // связываниями ближайшее и есть последний написанный аргумент.
    let inner: Vec<Term> = given.iter().rev().cloned().collect();
    let mut codomain = &ty;
    for _ in given {
        let Term::Pi(_, _, _, row, next) = codomain else {
            return None;
        };
        // Непустая row на подставляемом связывании означает, что **само**
        // применение что-то производит, а деть это некуда: у производного
        // определения аргумента, на котором эффект случился бы, уже нет.
        // Названная граница, и сегодня за неё не заходит никто: имплиситное
        // связывание пишется чистым.
        if !row.is_empty() {
            return None;
        }
        codomain = next;
    }
    let ty = substituted(codomain, &Substitution::Closed(&inner), 0);
    // Лямбд у тела бывает меньше, чем связываний у типа: метод класса с
    // собственными имплиситами - `map : {0 f} -> {ω d} -> {0 a} -> {0 b} -> …`
    // - объявлен телом из двух лямбд. Принятые подставляются, остальные
    // дописываются применением: то же значение, только не приведённое.
    let (under, opened) = opened(&body, given.len());
    let head: Vec<Term> = given[..opened].iter().rev().cloned().collect();
    let body = substituted(under, &Substitution::Closed(&head), 0);
    let body = given[opened..].iter().fold(body, |callee, argument| {
        Term::App(Rc::new(callee), Rc::new(argument.clone()))
    });
    Some((ty, body))
}

/// Тело под ведущими лямбдами и сколько их снялось - не больше `count`.
fn opened(term: &Term, count: usize) -> (&Term, usize) {
    let mut current = term;
    let mut found = 0;
    while found < count {
        let Term::Lam(_, _, body) = current else {
            break;
        };
        current = body;
        found += 1;
    }
    (current, found)
}

/// Тело под ровно `count` ведущими лямбдами. `None` - их там меньше.
fn peeled(term: &Term, count: usize) -> Option<&Term> {
    let (under, found) = opened(term, count);
    (found == count).then_some(under)
}

/// Чем заменяются ближайшие связывания.
#[derive(Debug)]
enum Substitution<'a> {
    /// Замкнутые аргументы: сдвигать их не приходится, и это проверяет тот,
    /// кто их собрал.
    Closed(&'a [Term]),
    /// Одна переменная вместо ближайшего связывания - сведение редекса. Её
    /// сдвигать приходится: под связываниями она видна дальше.
    Variable(u32),
}

impl Substitution<'_> {
    /// Сколько связываний заменяется.
    fn count(&self) -> u32 {
        match self {
            Self::Closed(arguments) => u32::try_from(arguments.len()).unwrap_or(u32::MAX),
            Self::Variable(_) => 1,
        }
    }

    /// Чем заменяется связывание с этим смещением на этой глубине.
    fn at(&self, offset: u32, depth: u32) -> Term {
        match self {
            Self::Closed(arguments) => arguments[offset as usize].clone(),
            Self::Variable(index) => Term::Var(Index(index + depth)),
        }
    }
}

/// Подставляет аргументы вместо ближайших связываний.
///
/// `depth` - сколько связываний пройдено внутри самого терма; индекс глубже
/// подставляемых сдвигается на их число.
///
/// Заодно сводится редекс, и ровно в двух случаях, ни один из которых не
/// меняет ни порядка вычислений, ни их числа. **Аргумент-переменная**: она уже
/// вычислена и эффекта не производит. **Стёртое связывание** при замкнутом
/// аргументе: такой аргумент не вычисляется вовсе (§3.3), подставить его - то
/// же, что выбросить. Замкнутость здесь обязательна: сдвигать аргумент
/// подстановка умеет только для переменной, в том её случай и состоит.
///
/// Сводится это не ради красоты. Редексы оставляет зонканье - решение дырки
/// есть замкнутая цепочка лямбд, применённая к контексту (§4.1), - и терм с
/// лямбдой в голове применения проверку не проходит: типа у неё не вывести.
/// Тела, объявленные элаборацией, такой формы и есть, а производное
/// определение проверяется заново.
fn substituted(term: &Term, subst: &Substitution<'_>, depth: u32) -> Term {
    let count = subst.count();
    let here = |inner: &Rc<Term>| Rc::new(substituted(inner, subst, depth));
    let under = |inner: &Rc<Term>| Rc::new(substituted(inner, subst, depth + 1));
    let rowed = |row: &Row<Term>| row.map(|argument| substituted(argument, subst, depth));
    let assignments = |fields: &Rc<[(Name, Rc<Term>)]>| -> Rc<[(Name, Rc<Term>)]> {
        fields
            .iter()
            .map(|(name, value)| (Rc::clone(name), here(value)))
            .collect()
    };
    match term {
        Term::Var(Index(index)) => {
            if *index < depth {
                term.clone()
            } else if *index < depth + count {
                subst.at(index - depth, depth)
            } else {
                Term::Var(Index(index - count))
            }
        }
        Term::Meta(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind => term.clone(),
        Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), under(body)),
        Term::App(callee, argument) => {
            let callee = substituted(callee, subst, depth);
            let argument = substituted(argument, subst, depth);
            match (&callee, &argument) {
                (Term::Lam(_, _, body), Term::Var(Index(index))) => {
                    substituted(body, &Substitution::Variable(*index), 0)
                }
                (Term::Lam(Mult::Zero, _, body), _) if !open(&argument) => substituted(
                    body,
                    &Substitution::Closed(std::slice::from_ref(&argument)),
                    0,
                ),
                _ => Term::App(Rc::new(callee), Rc::new(argument)),
            }
        }
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            here(domain),
            rowed(row),
            under(codomain),
        ),
        Term::Let(mult, name, ty, value, body) => {
            Term::Let(*mult, Rc::clone(name), here(ty), here(value), under(body))
        }
        Term::Const(name, levels, args) => Term::Const(
            Rc::clone(name),
            Rc::clone(levels),
            Args::new(
                args.row_args().iter().map(rowed),
                args.mult_args().iter().copied(),
            ),
        ),
        Term::Record(fields) => Term::Record(telescope(fields, subst, depth)),
        Term::Row(fields) => Term::Row(telescope(fields, subst, depth)),
        Term::Object(fields) => Term::Object(assignments(fields)),
        Term::With(base, fields) => Term::With(here(base), assignments(fields)),
        Term::Project(record, name) => Term::Project(here(record), Rc::clone(name)),
        // Собственных связываний разбор не вводит: и мотив, и ветви - обычные
        // термы функционального типа.
        Term::Case(case) => Term::Case(Rc::new(Case {
            data: Rc::clone(&case.data),
            levels: Rc::clone(&case.levels),
            params: case.params,
            consumed: case.consumed,
            scrutinee: here(&case.scrutinee),
            motive: here(&case.motive),
            branches: case
                .branches
                .iter()
                .map(|branch| Branch {
                    constructor: Rc::clone(&branch.constructor),
                    body: here(&branch.body),
                })
                .collect(),
        })),
    }
}

/// Телескоп полей: тип `i`-го стоит под `i` связываниями предыдущих.
fn telescope(fields: &Fields, subst: &Substitution<'_>, depth: u32) -> Fields {
    let at = |index: usize| depth + u32::try_from(index).unwrap_or(u32::MAX);
    Fields {
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, field)| Field {
                name: Rc::clone(&field.name),
                mult: field.mult,
                shape: field.shape,
                ty: Rc::new(substituted(&field.ty, subst, at(index))),
            })
            .collect(),
        tail: fields
            .tail
            .as_ref()
            .map(|tail| Rc::new(substituted(tail, subst, at(fields.len())))),
    }
}

/// Объявляет произведённые определения одной группой.
///
/// Группой, а не по одному: две специализации бывают взаимно рекурсивны, и
/// фаза A обязана положить типы обеих раньше, чем проверится первое тело.
fn declare(
    signature: &mut Signature,
    metas: &mut Metas,
    made: &[Special],
) -> Result<(), MonoError> {
    let Some((first, rest)) = made.split_first() else {
        return Ok(());
    };
    let member = |special: &Special| {
        Member::definition(&special.name, Mult::Many, special.ty.clone())
            .with_arity(0, 0)
            .with_body(special.body.clone())
    };
    let group = rest
        .iter()
        .fold(Group::of(member(first)), |group, special| {
            group.and(member(special))
        });
    signature
        .declare(metas, &group)
        .map_err(|error| MonoError::Refused {
            error: Box::new(error),
        })
}

/// Сколько ведущих имплиситных связываний подставляется. `0` - ни одного либо
/// словаря среди них нет.
fn leading(signature: &Signature, instances: &Instances, ty: &Term) -> usize {
    let mut count = 0;
    let mut seen = false;
    let mut current = ty;
    while let Term::Pi(binder, _, domain, _, codomain) = current {
        if !binder.visibility.is_implicit() {
            break;
        }
        if dictionary(signature, instances, domain) {
            seen = true;
        }
        count += 1;
        current = codomain;
    }
    if seen { count } else { 0 }
}

/// Применение объявленного класса - то есть тип словаря (§3.5).
fn dictionary(signature: &Signature, instances: &Instances, ty: &Term) -> bool {
    applied(signature, ty).is_some_and(|(class, _)| instances.is_class(&class))
}

/// Дописана ли арность ссылки: аргументов уровня, row и кратности ровно
/// столько, сколько объявлено.
///
/// Недописанные встречаются, и это не порча терма: подстановка по короткому
/// списку оставляет параметр на месте, а место использования сравнивает его
/// как есть. Производному определению так нельзя - параметров у него нет, и
/// `e0` в его типе указывать не на что.
fn written(definition: &Definition, levels: &[Level], args: &Args) -> bool {
    levels.len() == definition.level_arity as usize
        && args.row_args().len() == definition.row_arity as usize
        && args.mult_args().len() == definition.mult_allowed.len()
}

/// Годится ли место вызова для подстановки: арность дописана, а сами аргументы
/// ground - ни параметров, ни дырок.
fn ground(definition: &Definition, levels: &[Level], args: &Args) -> bool {
    if !written(definition, levels, args) {
        return false;
    }
    let rows = args.row_args().iter().all(|row| {
        row.tail().is_none()
            && row
                .labels()
                .iter()
                .flat_map(|label| &label.arguments)
                .all(|argument| !open(argument))
    });
    let mults = args
        .mult_args()
        .iter()
        .all(|mult| matches!(mult, Mult::Zero | Mult::One | Mult::Many));
    levels.iter().all(settled) && rows && mults
}

/// Уровень без параметров и дырок.
fn settled(level: &Level) -> bool {
    match level {
        Level::Zero => true,
        Level::Succ(inner) => settled(inner),
        Level::Max(left, right) => settled(left) && settled(right),
        Level::Var(_) | Level::Meta(_) => false,
    }
}

/// Есть ли в терме свободное связывание.
fn open(term: &Term) -> bool {
    term.mentions_recent(0, u32::MAX)
}

/// Имя специализации: `same@Nat,Eqv#Nat`.
///
/// Головы аргументов, а не аргументы целиком: имя читается человеком, а
/// однозначность держит не оно, а ключ - список самих аргументов.
fn mangled(origin: &Name, arguments: &[Term]) -> String {
    let mut out = String::from(&**origin);
    out.push('@');
    for (position, argument) in arguments.iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        let (head, _) = spine(argument);
        match head {
            Term::Const(name, ..) => out.push_str(name),
            _ => out.push('_'),
        }
    }
    out
}

/// Разбирает применение на голову и аргументы.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut current = term;
    while let Term::App(callee, argument) = current {
        arguments.push(argument.as_ref());
        current = callee;
    }
    arguments.reverse();
    (current, arguments)
}

/// Что обход собрал с одного терма.
#[derive(Debug, Default)]
struct Found {
    /// Определения, которым терм передаёт словарь имплиситом.
    dictionaries: Vec<Name>,
    /// Имена, которые терм зовёт: по ним обход идёт дальше.
    called: Vec<Name>,
    /// Есть ли ссылка с **недописанной** арностью.
    ///
    /// Такие встречаются: словарь объявляемого инстанса собирается записью из
    /// членов, которых в сигнатуре ещё нет, и ссылка на член выходит без
    /// row-аргументов. Тип у неё поэтому несёт свободный `e0` - параметр,
    /// которому в производном определении не на что указывать, - и подставлять
    /// такое тело нельзя.
    short: bool,
}

/// Обход одного терма - по тем же позициям, что и сам проход.
fn scan(signature: &Signature, instances: &Instances, term: &Term, found: &mut Found) {
    match term {
        Term::Var(_)
        | Term::Meta(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Pi(..)
        | Term::Record(_)
        | Term::Row(_) => {}
        Term::Lam(_, _, body) => scan(signature, instances, body, found),
        Term::Let(_, _, _, value, body) => {
            scan(signature, instances, value, found);
            scan(signature, instances, body, found);
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                scan(signature, instances, value, found);
            }
        }
        Term::With(base, fields) => {
            scan(signature, instances, base, found);
            for (_, value) in fields.iter() {
                scan(signature, instances, value, found);
            }
        }
        Term::Project(base, _) => scan(signature, instances, base, found),
        Term::Case(case) => {
            scan(signature, instances, &case.scrutinee, found);
            for branch in &case.branches {
                scan(signature, instances, &branch.body, found);
            }
        }
        Term::App(..) | Term::Const(..) => {
            let (head, arguments) = spine(term);
            for argument in &arguments {
                scan(signature, instances, argument, found);
            }
            let Term::Const(name, levels, args) = head else {
                scan(signature, instances, head, found);
                return;
            };
            found.called.push(Rc::clone(name));
            let Some(definition) = signature.lookup(name) else {
                return;
            };
            if !written(definition, levels, args) {
                found.short = true;
            }
            let mut supplied = arguments.len();
            let mut current = &definition.ty;
            while let Term::Pi(binder, _, domain, _, codomain) = current {
                if supplied == 0 {
                    break;
                }
                if binder.visibility.is_implicit() && dictionary(signature, instances, domain) {
                    found.dictionaries.push(Rc::clone(name));
                    break;
                }
                supplied -= 1;
                current = codomain;
            }
        }
    }
}
