//! Аллоцирует ли определение в куче Perceus - вердикт для `@noalloc` (§5.1).
//!
//! Жанр тот же, что у [`crate::total`]: считает ядро по телу и графу вызовов,
//! а атрибут поверхностного языка требует, чтобы ответ был «нет». Хранится
//! вердикт не булевым, а первым найденным источником
//! ([`Definition::allocates`]): §5.1 требует от диагностики назвать, что именно
//! аллоцирует, иначе атрибут превращается в загадку.
//!
//! # Где проходит линия
//!
//! По видимости в сигнатуре, а не по цене. Запрещена аллокация, не названная в
//! типе, - куча Perceus. Аллокация в регионе (`{Alloc r}`, §3.6) нарушением не
//! считается: она объявлена в row и видна автору. Стек не в счёт вовсе - о
//! глубине рекурсии атрибут не говорит ничего, поэтому рекурсивное определение
//! под ним законно.
//!
//! # Что проверка видит
//!
//! - применение конструктора и построение записи: значение уходит в кучу;
//! - замыкание - лямбда сверх параметров определения либо частичное применение;
//! - вызов определения с отрицательным вердиктом: это и есть вывод по графу
//!   вызовов внутри пакета (§5.1);
//! - вызов определения без тела: обязательство §5.1 объявляется, а не выводится
//!   из чужого кода;
//! - вызов операции эффекта.
//!
//! Стёртое не считается: определение кратности `0`, аргумент на связывании `0`,
//! `let 0`, мотив разбора, всякий тип. Иначе индекс `Succ n` в аргументе
//! отвергал бы любую функцию над индексированным семейством.
//!
//! # Что не покрыто
//!
//! **Reuse.** §5.1 разрешает конструктор там, где reuse гарантирован, - на
//! линейном или unique входе. Perceus'а нет, уникальность в точке разбора никто
//! не считает, поэтому конструктор аллоцирует здесь всегда. Направление
//! консервативно: отвергается часть законных определений, но не принимается ни
//! одно аллоцирующее.
//!
//! **Хвостовая резумптивность** (§3.4). Ветка хендлера, зовущая `resume` вне
//! хвостовой позиции, снимает продолжение в кучу; абортивная не снимает ничего.
//! Вердикт тут трёхзначный, анализа нет, и поэтому всякая операция и всякий
//! элиминатор хендлера считаются аллоцирующими.
//!
//! **Боксирование** в указательную позицию (§4.11) требует класса `Flat`, а
//! `Lazy` в языке ещё нет вовсе. Оба источника §5.1 перечисляет, и оба здесь
//! отсутствуют не по решению, а по отсутствию предмета.
//!
//! **Release-lowering.** §5.1 говорит, что проверка идёт по нему: мономорфизация
//! обязательна в release, а debug вправе боксировать. Понижения нет, и считается
//! вердикт по терму ядра; появится - проверке переезжать туда.
//!
//! **Граница пакета.** Пакетов нет, и объявить обязательство извне негде.
//! Постулат под `@noalloc` поэтому отвергается: проверить обещание нечем.

use std::fmt;
use std::rc::Rc;

use crate::meta::{Metas, zonk_term};
use crate::mult::Mult;
use crate::sig::{Definition, DefinitionKind, Signature};
use crate::term::{Case, Name, Term, spine};

/// Чем определение аллоцирует.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// Применение конструктора: значение семейства строится в куче.
    Construct(Name),
    /// Литерал записи или её обновление.
    Record,
    /// Лямбда сверх параметров: окружение уходит в кучу.
    Closure,
    /// Частичное применение: недостающие аргументы ждут в замыкании.
    Partial(Name),
    /// Вызов операции эффекта.
    Operation(Name),
    /// Тела нет у самого определения.
    Postulate,
    /// Вызов определения без тела.
    Opaque(Name),
    /// Вызов определения, чей вердикт отрицателен.
    Call(Name),
}

/// Цепочка от определения к тому, что аллоцирует на самом деле.
///
/// «`f` зовёт аллоцирующее `g`» без продолжения не говорит, что чинить, поэтому
/// цепочка идёт по графу вызовов до первого не-вызова.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Blame {
    /// Кого зовут по пути. Само определение сюда не входит.
    through: Vec<Name>,
    /// Что аллоцирует в конце пути.
    source: Source,
}

/// Чем определение нарушает `@noalloc`. `None` - не нарушает.
///
/// Читает сохранённые вердикты и тел не трогает: зовут её после границы
/// объявления, где дырки уже освобождены, а зонканье там падает.
#[must_use]
pub fn blame(signature: &Signature, name: &Name) -> Option<Blame> {
    let mut source = signature.lookup(name)?.allocates.clone()?;
    let mut through: Vec<Name> = Vec::new();
    while let Source::Call(callee) = &source {
        let callee = Rc::clone(callee);
        // Цикл взаимной рекурсии обрывает цепочку: по нему идут те же имена.
        if callee == *name || through.contains(&callee) {
            break;
        }
        let Some(next) = signature
            .lookup(&callee)
            .and_then(|it| it.allocates.clone())
        else {
            break;
        };
        through.push(callee);
        source = next;
    }
    Some(Blame { through, source })
}

impl fmt::Display for Blame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for callee in &self.through {
            write!(f, "зовёт `{callee}`, а та ")?;
        }
        match &self.source {
            Source::Construct(name) => write!(
                f,
                "строит значение конструктором `{name}` - это куча Perceus. Выходов три (§5.1): \
                 линейный или unique вход, где reuse гарантирован; регион `{{Alloc r}}`; отказ от \
                 конструирования. Первых двух в компиляторе пока нет, так что остаётся третий"
            ),
            Source::Record => write!(
                f,
                "строит запись - это куча Perceus. Выходов три (§5.1): линейный или unique вход, \
                 где reuse гарантирован; регион `{{Alloc r}}`; отказ от конструирования. Первых \
                 двух в компиляторе пока нет, так что остаётся третий"
            ),
            Source::Closure => write!(
                f,
                "создаёт замыкание: лямбда стоит сверх параметров, и окружение её уходит в кучу"
            ),
            Source::Partial(name) => write!(
                f,
                "применяет `{name}` частично, а недостающие аргументы ждут в замыкании"
            ),
            Source::Operation(name) => write!(
                f,
                "зовёт операцию `{name}`: аллоцирует ли она, решает форма ветки хендлера, а \
                 анализа хвостовой резумптивности (§3.4) ещё нет"
            ),
            Source::Postulate => write!(
                f,
                "не имеет тела: `@noalloc` через границу пакета объявляется в сигнатуре, но самой \
                 границы в компиляторе ещё нет, и проверить обещание нечем (§5.1)"
            ),
            Source::Opaque(name) => write!(
                f,
                "зовёт `{name}`, у которой нет тела: вердикт выводить не из чего"
            ),
            Source::Call(name) => write!(f, "зовёт `{name}`, а та аллоцирует"),
        }
    }
}

/// Первый источник аллокации определения. `None` - не аллоцирует.
///
/// Зовётся на границе объявления, где дырки ещё живы: тело зонкается, потому что
/// словарь метода инстанса стоит в нём дыркой (§10 вопрос 134), а за ней прячутся
/// и вызовы, и конструкторы.
///
/// Вердикт вызываемых берётся из сигнатуры. Внутри объявляемой группы он там
/// оптимистичный - «не аллоцирует», - и понижает его неподвижная точка
/// вызывающего: цикл не аллоцирующих функций не аллоцирует, поэтому старт сверху
/// верен.
#[must_use]
pub fn source(
    signature: &Signature,
    metas: &Metas,
    name: &Name,
    definition: &Definition,
) -> Option<Source> {
    let Some(body) = &definition.body else {
        return match &definition.kind {
            // Формер - тип: значений в рантайме у него нет.
            DefinitionKind::Data { .. } | DefinitionKind::Effect { .. } => None,
            DefinitionKind::Constructor { .. } => Some(Source::Construct(Rc::clone(name))),
            DefinitionKind::Operation { .. } => Some(Source::Operation(Rc::clone(name))),
            DefinitionKind::Regular => Some(Source::Postulate),
        };
    };
    let body = zonk_term(metas, body);
    let mut walk = Walk {
        signature,
        found: None,
    };
    walk.parameters(&body);
    walk.found
}

/// Обход тела до первого источника.
struct Walk<'a> {
    signature: &'a Signature,
    /// Найденное. Дальше первого не ищется: диагностика называет одно место.
    found: Option<Source>,
}

impl Walk<'_> {
    /// Снимает лямбды-параметры и обходит остаток.
    ///
    /// Снимаются **все** ведущие. `mk n = \m -> plus n m` и `mk n m = plus n m`
    /// дают один и тот же терм ядра, и отличить возвращённое замыкание от лишнего
    /// параметра здесь нечем; понижение с известной арностью поступает так же.
    fn parameters(&mut self, term: &Term) {
        let mut current = term;
        while let Term::Lam(_, _, body) = current {
            current = body;
        }
        self.term(current);
    }

    fn record(&mut self, source: Source) {
        if self.found.is_none() {
            self.found = Some(source);
        }
    }

    fn term(&mut self, term: &Term) {
        if self.found.is_some() {
            return;
        }
        match term {
            // Переменная берёт готовое, а универсум, сорт ряда, `Effect`, тип
            // записи, ряд и стрелка - типы: в рантайме их нет вовсе. Дырка
            // здесь же: тело зонкано, и пережившая зонканье дырка - это
            // нерешённое, которое объявление отвергнет своим чередом.
            Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Meta(_)
            | Term::Record(_)
            | Term::Row(_)
            | Term::Pi(..) => {}

            Term::Object(fields) => {
                self.record(Source::Record);
                for (_, value) in fields.iter() {
                    self.term(value);
                }
            }
            Term::With(base, fields) => {
                self.record(Source::Record);
                self.term(base);
                for (_, value) in fields.iter() {
                    self.term(value);
                }
            }
            Term::Project(record, _) => self.term(record),

            Term::Lam(..) => self.record(Source::Closure),

            Term::Const(name, _, _) => self.constant(name, 0),

            Term::App(..) => {
                let (head, arguments) = spine(term);
                match head {
                    Term::Const(name, _, _) => {
                        self.constant(name, arguments.len());
                        self.applied(name, &arguments);
                    }
                    // Convoy: разбор применён к соседним аргументам, и ветви
                    // связывают их лямбдами сверх полей.
                    Term::Case(case) => {
                        self.case(case, arguments.len());
                        for argument in &arguments {
                            self.term(argument);
                        }
                    }
                    other => {
                        self.term(other);
                        for argument in &arguments {
                            self.term(argument);
                        }
                    }
                }
            }

            Term::Let(mult, _, _, value, body) => {
                // Тип связывания - тип. Стёртое значение в рантайме не
                // возникает вовсе (§3.2), и аллоцировать ему нечем.
                if *mult != Mult::Zero {
                    self.term(value);
                }
                self.term(body);
            }

            Term::Case(case) => self.case(case, 0),
        }
    }

    /// Что стоит за именем в спайне.
    fn constant(&mut self, name: &Name, arguments: usize) {
        let Some(definition) = self.signature.lookup(name) else {
            return;
        };
        // Определение кратности `0` живёт только на этапе проверки типов: в
        // рантайме его вызова нет, аллоцировать нечему.
        if definition.mult == Mult::Zero {
            return;
        }
        match &definition.kind {
            // Тип-формер и метка эффекта - типы.
            DefinitionKind::Data { .. } | DefinitionKind::Effect { .. } => {}
            DefinitionKind::Constructor { .. } => self.record(Source::Construct(Rc::clone(name))),
            DefinitionKind::Operation { .. } => self.record(Source::Operation(Rc::clone(name))),
            DefinitionKind::Regular => {
                if definition.allocates.is_some() {
                    self.record(if definition.body.is_none() {
                        Source::Opaque(Rc::clone(name))
                    } else {
                        Source::Call(Rc::clone(name))
                    });
                } else if arguments < telescope(&definition.ty) {
                    // Недостающие аргументы ждут в замыкании - и оно в куче.
                    self.record(Source::Partial(Rc::clone(name)));
                }
            }
        }
    }

    /// Обходит аргументы спайна, пропуская стёртые связыванием позиции.
    ///
    /// Позиции читаются по телескопу вызываемого и совпадают с аргументами, пока
    /// спайн насыщается по порядку - то же допущение, на котором стоит
    /// [`crate::carrier`].
    fn applied(&mut self, callee: &Name, arguments: &[&Term]) {
        let mut binders: Vec<Mult> = Vec::new();
        if let Some(definition) = self.signature.lookup(callee) {
            let mut current = &definition.ty;
            while let Term::Pi(binder, _, _, _, codomain) = current {
                binders.push(binder.mult);
                current = codomain;
            }
        }
        for (position, argument) in arguments.iter().enumerate() {
            if binders.get(position) == Some(&Mult::Zero) {
                continue;
            }
            self.term(argument);
        }
    }

    /// Обходит разбор: мотив - тип, ветви связывают поля и соседей convoy.
    fn case(&mut self, case: &Case, applied: usize) {
        self.term(&case.scrutinee);
        for branch in &case.branches {
            let binders = self.fields(&branch.constructor, case.params) + applied;
            self.branch(binders, &branch.body);
        }
    }

    /// Сколько полей связывает ветвь конструктора.
    fn fields(&self, constructor: &Name, params: u32) -> usize {
        let Some(declaration) = self.signature.lookup(constructor) else {
            return 0;
        };
        telescope(&declaration.ty).saturating_sub(params as usize)
    }

    /// Снимает связывания ветви и обходит её тело.
    ///
    /// Связывания ветви - не замыкания: это поля разобранного значения и
    /// соседние аргументы, к которым разбор применён. Записаны лямбдами они не
    /// обязаны (η), и что не снялось, обходится как обычный терм.
    fn branch(&mut self, binders: usize, term: &Term) {
        match (binders, term) {
            (0, other) => self.term(other),
            (_, Term::Lam(_, _, body)) => self.branch(binders - 1, body),
            (_, other) => self.term(other),
        }
    }
}

/// Длина телескопа типа.
fn telescope(ty: &Term) -> usize {
    let mut found = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        found += 1;
        current = codomain;
    }
    found
}
