//! Совместимость с FBIP: что стоит за атрибутом `@fbip` (§5.1).
//!
//! FBIP - исполнение, при котором код, синтаксически создающий новую
//! структуру, переписывает слоты уже разобранной. Условий у reuse два:
//! уникальность разобранного в момент разбора и совпадение формы нового
//! конструктора со старым (`Node` → `Node`, не `Node` → `Cons`). Первое -
//! свойство места вызова и для ω-входа проверяется рантаймом; второе -
//! свойство самого тела, и проверяется здесь.
//!
//! # Что проверяется
//!
//! Ветвь разбора вправе переписать разобранный конструктор ровно однажды.
//! Поэтому у каждой ветви есть **слот** - форма того, что она разобрала, - и
//! всякая структура, построенная внутри ветви, обязана этот слот занять:
//! столько же полей, и разобранное значение больше нигде не употреблено.
//! Не нашлось слота - функция аллоцирует там, где обещала переписывать, и
//! обязательство не выполнено. Второй структуре той же формы слота уже нет:
//! разобранная ячейка одна, и переписать её дважды нечем.
//!
//! Слоты копятся по пути: вложенный разбор добавляет свой к слотам объемлющих
//! ветвей, а ветви-соседи делят их независимо - они исключают друг друга.
//!
//! # Чего атрибут не обещает
//!
//! Что RC действительно равен 1 в момент вызова: это свойство места вызова, а
//! не функции (§5.1). Проверка говорит только о том, что форма кода reuse'у не
//! мешает.
//!
//! # Границы
//!
//! **Аллокация вне разбора не рассматривается.** §5.1 квантифицирует обе
//! половины обязательства по ветвям pattern-matching'а, и функция, не
//! разобравшая ничего, переписывать не обязана: reuse в ней структурно
//! невозможен. Аллокацию как таковую ограничивает `@noalloc` - соседнее
//! обязательство того же раздела.
//!
//! **Стёртые позиции не в счёт.** Конструктор в мотиве разбора, в домене `Pi`
//! или в аргументе `{0 a : Type}` значения в рантайме не имеет и ничего не
//! аллоцирует; уровень, употреблённый только там, разобранное живым не держит.
//!
//! **Употребление считается по всему телу, а не по ветви.** Разобранное
//! значение, названное где-то ещё, - алиас, и переписать его слоты нечем, где
//! бы второе упоминание ни стояло. Цена - консерватизм на взаимно
//! исключающих путях: два разбора одной переменной в разных ветвях считаются
//! двумя употреблениями, хотя случается ровно один.
//!
//! # Вердикт не хранится
//!
//! В отличие от тотальности (§4.7, [`crate::total`]), ядру ответ не нужен ни
//! для чего: ни δ-разворот, ни стёртый фрагмент про FBIP не спрашивают.
//! Считать его каждому определению значило бы платить за всех ради тех
//! немногих, где атрибут написан, поэтому проверка зовётся по требованию, а в
//! [`Definition`](crate::sig::Definition) поля нет. Отдаёт она при этом не
//! «нет», а причину и маршрут: диагностика §5.1 обязана называть место.
//!
//! У постулата тела нет - переписывать нечего, и обязательство пусто. Так же
//! устроена тотальность.

use std::rc::Rc;

use crate::error::Frame;
use crate::mult::Mult;
use crate::sig::{DefinitionKind, Signature};
use crate::term::{Case, Index, Name, Term, spine};

/// Почему тело несовместимо с FBIP.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Fault {
    /// Построенный конструктор не той формы, что разобранный.
    #[error(
        "разобран `{matched}` (полей: {matched_fields}), а строится `{built}` (полей: {fields}): \
         reuse переписывает слоты разобранного, и форма обязана совпасть"
    )]
    Shape {
        /// Что строится.
        built: Name,
        /// Сколько полей у построенного.
        fields: usize,
        /// Что разобрано ближайшим разбором.
        matched: Name,
        /// Сколько полей у разобранного.
        matched_fields: usize,
    },

    /// Форма совпадает, но разобранное значение употреблено ещё раз.
    #[error(
        "разобранное `{matched}` употребляется ещё раз, то есть остаётся живым: \
         переписать его слоты нечем, и `{built}` (полей: {fields}) аллоцируется заново"
    )]
    Alive {
        /// Что строится.
        built: Name,
        /// Сколько полей у построенного.
        fields: usize,
        /// Что разобрано, но не потреблено.
        matched: Name,
    },

    /// Форма совпадает, но разобранное уже переписано соседней структурой.
    #[error(
        "разобранный `{matched}` уже переписан: `{built}` (полей: {fields}) строится вторым, \
         и переписывать ему нечего - ветвь аллоцирует"
    )]
    Taken {
        /// Что строится.
        built: Name,
        /// Сколько полей у построенного.
        fields: usize,
        /// Что разобрано и уже отдано.
        matched: Name,
    },
}

/// Несовместимость: что не сошлось и где.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Incompatible {
    /// Что не сошлось.
    pub fault: Fault,
    /// Маршрут до места - снаружи внутрь, как у
    /// [`TypeError::path`](crate::check::TypeError::path).
    pub route: Vec<Frame>,
}

/// Совместимо ли тело с FBIP (§5.1).
///
/// `body` - терм определения, тот самый, что уходит в сигнатуру: маршрут
/// отказа считается по нему и ложится на дерево разбора, собранное
/// [`crate::pattern`].
///
/// # Errors
///
/// Ветвь строит конструктор, для которого разобранной формы нет, либо
/// разобранное значение остаётся живым.
pub fn compatible(signature: &Signature, body: &Term) -> Result<(), Incompatible> {
    let walk = Walk { signature, body };
    walk.region(body, 0, &mut Vec::new(), &mut Vec::new())
}

/// Разобранная форма, которую ветвь вправе переписать.
#[derive(Clone, Debug)]
struct Slot {
    /// Конструктор, который ветвь разобрала.
    constructor: Name,
    /// Сколько у него полей.
    fields: usize,
    /// Разобранное значение употреблено ещё где-то - переписать его нечем.
    alive: bool,
    /// Слот уже отдан построенной структуре.
    taken: bool,
}

struct Walk<'a> {
    signature: &'a Signature,
    /// Тело целиком: употребления разобранного считаются по нему.
    body: &'a Term,
}

impl Walk<'_> {
    /// Обходит участок пути с его слотами.
    fn region(
        &self,
        term: &Term,
        depth: u32,
        slots: &mut Vec<Slot>,
        route: &mut Vec<Frame>,
    ) -> Result<(), Incompatible> {
        if let Term::Case(case) = term {
            return self.case(case, depth, slots, route);
        }
        // Слот занимает **внешняя** структура: обход идёт снаружи внутрь, и
        // результат ветви спрашивает раньше, чем то, что стоит у него внутри.
        if let Some((built, fields)) = self.built(term) {
            if fields > 0 && !slots.is_empty() {
                take(slots, &built, fields).map_err(|fault| Incompatible {
                    fault,
                    route: route.clone(),
                })?;
            }
        }
        for (path, child, bound) in self.children(term) {
            let before = route.len();
            route.extend(path);
            self.region(child, depth + bound, slots, route)?;
            route.truncate(before);
        }
        Ok(())
    }

    /// Обходит разбор: каждая ветвь получает свой слот и свою копию пути.
    fn case(
        &self,
        case: &Case,
        depth: u32,
        slots: &mut Vec<Slot>,
        route: &mut Vec<Frame>,
    ) -> Result<(), Incompatible> {
        route.push(Frame::Scrutinee);
        self.region(&case.scrutinee, depth, slots, route)?;
        route.pop();
        let scrutinee = level(&case.scrutinee, depth);
        // Разобранное, названное ещё раз, - алиас: одно упоминание есть сам
        // разбор, всё сверх него держит старое значение живым.
        let alive = scrutinee.is_some_and(|it| self.uses(self.body, 0, it) > 1);
        for (index, branch) in case.branches.iter().enumerate() {
            let mut inner = slots.clone();
            inner.push(Slot {
                constructor: Rc::clone(&branch.constructor),
                fields: self.fields(&branch.constructor, case.params),
                alive,
                taken: false,
            });
            route.push(Frame::Branch(u32::try_from(index).unwrap_or(u32::MAX)));
            self.region(&branch.body, depth, &mut inner, route)?;
            route.pop();
        }
        Ok(())
    }

    /// Конструктор, который терм строит, и число его полей.
    ///
    /// Насыщенность не спрашивается: недонасыщенный конструктор - замыкание,
    /// которое ту же структуру и построит, только позже.
    fn built(&self, term: &Term) -> Option<(Name, usize)> {
        let (head, _) = spine(term);
        let Term::Const(name, _, _) = head else {
            return None;
        };
        let definition = self.signature.lookup(name)?;
        let DefinitionKind::Constructor { data } = &definition.kind else {
            return None;
        };
        let (params, _) = self.signature.lookup(data)?.data_shape()?;
        Some((
            Rc::clone(name),
            arity(&definition.ty).saturating_sub(params as usize),
        ))
    }

    /// Сколько полей связывает ветвь конструктора.
    fn fields(&self, constructor: &Name, params: u32) -> usize {
        let Some(declaration) = self.signature.lookup(constructor) else {
            return 0;
        };
        arity(&declaration.ty).saturating_sub(params as usize)
    }

    /// Сколько раз уровень назван в рантайм-позициях терма.
    ///
    /// Ветви складываются, хотя случается ровно одна: путь здесь не отслежен, и
    /// консервативный ответ - «названо дважды».
    fn uses(&self, term: &Term, depth: u32, wanted: u32) -> usize {
        match term {
            Term::Var(index) => usize::from(names(depth, *index, wanted)),
            Term::Case(case) => {
                self.uses(&case.scrutinee, depth, wanted)
                    + case
                        .branches
                        .iter()
                        .map(|branch| self.uses(&branch.body, depth, wanted))
                        .sum::<usize>()
            }
            other => self
                .children(other)
                .into_iter()
                .map(|(_, child, bound)| self.uses(child, depth + bound, wanted))
                .sum(),
        }
    }

    /// Подтермы, у которых есть значение в рантайме, - вместе с маршрутом до
    /// каждого и числом связываний, которые он вводит.
    ///
    /// Типов здесь нет: стёртое не аллоцирует и живым ничего не держит.
    fn children<'a>(&self, term: &'a Term) -> Vec<(Vec<Frame>, &'a Term, u32)> {
        match term {
            // Разбор пуст здесь не по забывчивости: ему нужны номер ветви и
            // слот, и оба читателя перехватывают его раньше.
            Term::Case(_)
            | Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Meta(_)
            | Term::Const(..)
            | Term::Pi(..)
            | Term::Record(_)
            | Term::Row(_) => Vec::new(),
            Term::Lam(_, _, body) => vec![(vec![Frame::Body], &**body, 1)],
            Term::Let(mult, _, _, value, body) => {
                let mut found = Vec::with_capacity(2);
                if *mult != Mult::Zero {
                    found.push((vec![Frame::BindingValue], &**value, 0));
                }
                found.push((vec![Frame::BindingBody], &**body, 1));
                found
            }
            // У полей записи кадра нет: маршрут обрывается здесь, и спан
            // получится тот, до которого он дошёл (§10 вопрос 49б).
            Term::Object(fields) => fields
                .iter()
                .map(|(_, value)| (Vec::new(), &**value, 0))
                .collect(),
            Term::With(base, fields) => std::iter::once((Vec::new(), &**base, 0))
                .chain(fields.iter().map(|(_, value)| (Vec::new(), &**value, 0)))
                .collect(),
            Term::Project(record, _) => vec![(Vec::new(), &**record, 0)],
            Term::App(..) => self.applied(term),
        }
    }

    /// То же для применения: спайн разбирается целиком, стёртые аргументы
    /// отбрасываются.
    fn applied<'a>(&self, term: &'a Term) -> Vec<(Vec<Frame>, &'a Term, u32)> {
        let (head, arguments) = spine(term);
        let erased = self.erased(head, arguments.len());
        let mut found = Vec::with_capacity(arguments.len() + 1);
        // Голова-имя разобрана в [`Walk::built`]; спускаться в неё незачем.
        if !matches!(head, Term::Const(..)) {
            found.push((vec![Frame::Callee; arguments.len()], head, 0));
        }
        for (at, argument) in arguments.iter().enumerate() {
            if erased.get(at).copied().unwrap_or(false) {
                continue;
            }
            let mut path = vec![Frame::Callee; arguments.len() - 1 - at];
            path.push(Frame::Argument);
            found.push((path, *argument, 0));
        }
        found
    }

    /// Какие позиции спайна стёрты. Голова не имя - ничего не известно, и все
    /// позиции считаются рантайм-позициями.
    fn erased(&self, head: &Term, count: usize) -> Vec<bool> {
        let Term::Const(name, _, _) = head else {
            return vec![false; count];
        };
        let Some(definition) = self.signature.lookup(name) else {
            return vec![false; count];
        };
        let mut found = Vec::with_capacity(count);
        let mut current = &definition.ty;
        while found.len() < count {
            let Term::Pi(binder, _, _, _, codomain) = current else {
                break;
            };
            found.push(binder.mult == Mult::Zero);
            current = codomain;
        }
        found.resize(count, false);
        found
    }
}

/// Занимает слот под структуру из `fields` полей.
fn take(slots: &mut [Slot], built: &Name, fields: usize) -> Result<(), Fault> {
    if let Some(slot) = slots
        .iter_mut()
        .rev()
        .find(|slot| !slot.taken && !slot.alive && slot.fields == fields)
    {
        slot.taken = true;
        return Ok(());
    }
    // Форма подошла, помешало что-то другое: причина у отказа своя, и назвать
    // её обязаны ею, а не несовпадением полей.
    if let Some(slot) = slots
        .iter()
        .rev()
        .find(|slot| !slot.taken && slot.fields == fields)
    {
        return Err(Fault::Alive {
            built: Rc::clone(built),
            fields,
            matched: Rc::clone(&slot.constructor),
        });
    }
    if let Some(slot) = slots.iter().rev().find(|slot| slot.fields == fields) {
        return Err(Fault::Taken {
            built: Rc::clone(built),
            fields,
            matched: Rc::clone(&slot.constructor),
        });
    }
    match slots.last() {
        // Слотов нет вовсе - вызывающий сюда не заходит.
        None => Ok(()),
        Some(slot) => Err(Fault::Shape {
            built: Rc::clone(built),
            fields,
            matched: Rc::clone(&slot.constructor),
            matched_fields: slot.fields,
        }),
    }
}

/// Уровень де Брёйна, если терм - переменная.
fn level(term: &Term, depth: u32) -> Option<u32> {
    let Term::Var(Index(index)) = term else {
        return None;
    };
    depth.checked_sub(*index)?.checked_sub(1)
}

/// Указывает ли индекс на уровень `wanted` при глубине `depth`.
fn names(depth: u32, Index(index): Index, wanted: u32) -> bool {
    depth
        .checked_sub(index)
        .and_then(|it| it.checked_sub(1))
        .is_some_and(|level| level == wanted)
}

/// Длина телескопа типа.
fn arity(ty: &Term) -> usize {
    let mut found = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        found += 1;
        current = codomain;
    }
    found
}
