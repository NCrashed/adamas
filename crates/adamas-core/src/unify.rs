//! Унификация индексов при разборе (§9 Фаза 1, §10 вопрос 44).
//!
//! Разбирая `xs : Vect A (succ n)`, надо ответить на два вопроса про каждый
//! конструктор: бывает ли такая ветвь вообще (`vnil : Vect A zero` - не
//! бывает) и что в ней известно про переменные (`vcons` даёт `n = k`). Ответ
//! здесь один и тот же независимо от того, чем он потом реализуется: мотивом
//! `case` (так делает [`crate::pattern`]) или уравнениями, если они когда-либо
//! понадобятся. Поэтому решение и его реализация разделены - здесь решение.
//!
//! # Что умеет
//!
//! Сопоставление одностороннее и первого порядка: форма индекса разбираемого
//! значения ([`Shape`]) против индекса конструктора. Переменная в форме
//! принимает что угодно, конструктор требует того же конструктора, всё
//! остальное - [`Shape::Opaque`] - не требует ничего и ничего не даёт.
//!
//! # Чего не умеет
//!
//! Индекс конструктора, не приведённый к конструкторной форме против
//! конструктора в форме, - [`Match::Stuck`]. Так выглядит `mk : (k : Nat) ->
//! Foo k` при разборе `Foo (succ n)`: решением было бы `k := succ n`, то есть
//! подстановка **в поля ветви**, а ветвь - функция от всех своих полей, и
//! выкинуть одно из них не в чем. Это и есть граница фрагмента, доступного без
//! пропозиционального равенства.

use std::rc::Rc;

use crate::conv::whnf;
use crate::sig::{DefinitionKind, Signature};
use crate::term::{Name, Term};
use crate::value::{Elim, Head, Lvl, Value};

// Форма индекса, вердикт унификации и разбор конструкторного значения. Термы
// сюда не попадают вовсе: сопоставляются значения, а печатает их вызывающий -
// в своём контексте.

/// Форма индекса разбираемого значения.
#[derive(Clone, Debug)]
pub(crate) enum Shape {
    /// Переменная контекста. Принимает что угодно и уточняется тем, что
    /// приняла.
    Variable(u32),
    /// Конструктор и формы его полей - без параметров, они определены типом.
    Constructor(Name, Vec<Shape>),
    /// Всё прочее: застрявшее вычисление, применение, универсум. Уточнять по
    /// такой позиции нечего, и требовать по ней тоже нечего.
    Opaque,
}

impl Shape {
    /// Уровни переменных, встречающихся в форме.
    pub(crate) fn variables(&self, found: &mut Vec<u32>) {
        match self {
            Self::Variable(level) => found.push(*level),
            Self::Constructor(_, fields) => {
                for field in fields {
                    field.variables(found);
                }
            }
            Self::Opaque => {}
        }
    }

    /// Различается ли эта позиция разбором внутри мотива.
    pub(crate) fn is_rigid(&self) -> bool {
        matches!(self, Self::Constructor(..))
    }
}

/// Что стало с ветвью конструктора.
#[derive(Clone, Debug)]
pub(crate) enum Match {
    /// Индексы сошлись. Пары "уровень переменной формы, чем она оказалась";
    /// уровень может повторяться, и значит первое вхождение - остальные
    /// уточнения не получают.
    Solved(Vec<(u32, Rc<Value>)>),

    /// Головные конструкторы разошлись: такой ветви не бывает.
    Conflict {
        /// Номер позиции индекса.
        position: usize,
        /// Что стоит у разбираемого значения.
        expected: Name,
        /// Что даёт конструктор.
        found: Name,
    },

    /// Индекс конструктора не приведён к конструкторной форме - см. заголовок
    /// модуля.
    Stuck {
        /// Конструктор, которого требует разбираемое значение.
        expected: Name,
        /// Что стоит вместо него. Значение, а не строка: печатать его
        /// придётся в контексте ветви, а он здесь неизвестен.
        found: Rc<Value>,
    },
}

/// Форма значения, стоящего в индексе.
pub(crate) fn classify(signature: &Signature, value: &Rc<Value>) -> Shape {
    let reduced = whnf(signature, value);
    let Value::Neutral(head, spine) = &*reduced else {
        return Shape::Opaque;
    };
    match head {
        Head::Local(Lvl(level)) if spine.is_empty() => Shape::Variable(*level),
        Head::Global(name, _) => match applied_constructor(signature, name, spine) {
            Some(fields) => Shape::Constructor(
                Rc::clone(name),
                fields
                    .iter()
                    .map(|field| classify(signature, field))
                    .collect(),
            ),
            None => Shape::Opaque,
        },
        // Применённая переменная формы не имеет - как и дырка: чем она
        // окажется, ещё не решено, и различать по ней индексы значило бы
        // гадать.
        Head::Local(_) | Head::Meta(_) => Shape::Opaque,
    }
}

/// Сопоставляет формы индексов разбираемого значения с индексами конструктора.
///
/// Позиции сверяются слева направо, и первая же несошедшаяся отвечает за всех:
/// одного конфликта довольно, чтобы ветви не было.
pub(crate) fn matches(signature: &Signature, shapes: &[Shape], indices: &[Rc<Value>]) -> Match {
    let mut solved = Vec::new();
    for (position, (shape, index)) in shapes.iter().zip(indices).enumerate() {
        if let Err(outcome) = unify(signature, shape, index, position, &mut solved) {
            return outcome;
        }
    }
    Match::Solved(solved)
}

fn unify(
    signature: &Signature,
    shape: &Shape,
    index: &Rc<Value>,
    position: usize,
    solved: &mut Vec<(u32, Rc<Value>)>,
) -> Result<(), Match> {
    match shape {
        Shape::Opaque => Ok(()),
        Shape::Variable(level) => {
            solved.push((*level, Rc::clone(index)));
            Ok(())
        }
        Shape::Constructor(name, fields) => {
            let reduced = whnf(signature, index);
            let Value::Neutral(Head::Global(found, _), spine) = &*reduced else {
                return Err(stuck(name, &reduced));
            };
            let Some(arguments) = applied_constructor(signature, found, spine) else {
                return Err(stuck(name, &reduced));
            };
            if found != name {
                return Err(Match::Conflict {
                    position,
                    expected: Rc::clone(name),
                    found: Rc::clone(found),
                });
            }
            for (field, argument) in fields.iter().zip(&arguments) {
                unify(signature, field, argument, position, solved)?;
            }
            Ok(())
        }
    }
}

fn stuck(expected: &Name, found: &Rc<Value>) -> Match {
    Match::Stuck {
        expected: Rc::clone(expected),
        found: Rc::clone(found),
    }
}

/// Поля полностью применённого конструктора - без параметров.
///
/// `None` - имя не конструктор либо применение неполное: у недоприменённого
/// формы нет, сравнивать его не с чем.
fn applied_constructor<'a>(
    signature: &Signature,
    name: &Name,
    spine: &'a [Elim],
) -> Option<Vec<&'a Rc<Value>>> {
    let declaration = signature.lookup(name)?;
    let DefinitionKind::Constructor { data } = &declaration.kind else {
        return None;
    };
    let DefinitionKind::Data { params, .. } = &signature.lookup(data)?.kind else {
        return None;
    };
    let mut arity = 0;
    let mut current = &declaration.ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        arity += 1;
        current = codomain;
    }
    if spine.len() != arity {
        return None;
    }
    spine
        .iter()
        .skip(*params as usize)
        .map(|elim| match elim {
            Elim::App(argument) => Some(argument),
            Elim::Case(_) => None,
        })
        .collect()
}
