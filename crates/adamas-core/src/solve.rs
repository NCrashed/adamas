//! Решение метапеременных терма - паттерновая унификация (§4.1).
//!
//! Дырка терма замкнута, а её зависимость от контекста выражена **спайном**:
//! `?m x₀ … x_{n-1}`. Отсюда и форма задачи, и её решение.
//!
//! # Паттерновый фрагмент, и почему только он
//!
//! Решается `?m ū ≡ t`, где `ū` - **различные переменные контекста**. Тогда
//! решение единственно: `?m := λx₀ … λx_{n-1}. t`, где каждое вхождение
//! переменной из `ū` заменено на соответствующее связывание. Это фрагмент
//! Миллера.
//!
//! Вне его единственности нет: `?m (f y) ≡ y` имеет решений сколько угодно
//! (`λz. y` не хуже прочих, а есть ли обратная к `f` - неизвестно), и выбрать
//! одно значило бы принять программу по догадке. Отказ отвергает корректную,
//! и это та же граница, на которой стоит вывод уровней (§10 вопрос 39).
//!
//! # Две проверки, без которых решение неверно
//!
//! **Область видимости.** Правая часть не вправе упоминать переменные, не
//! попавшие в спайн: решение замкнуто, а такая переменная в нём оказалась бы
//! свободной. Возникает это на каждом шагу - `?m ≡ x` под связыванием `x`, -
//! и молча подставленное решение уносило бы индекс в чужой контекст.
//!
//! **Вхождение самой дырки.** `?m ≡ f ?m` решения не имеет: подстановка
//! породила бы бесконечный терм. Проверка идёт тем же проходом, что и
//! переименование, потому что смотрят они одно и то же.
//!
//! # Решение записывается один раз
//!
//! Backtracking'а в проверке нет (см. [`Metas`]), поэтому решение
//! окончательно. Порядок, в котором проверка добралась до ограничений, на
//! результат влияет - но не на корректность: неверная догадка невозможна,
//! потому что догадок здесь не делается вовсе.

use std::collections::HashMap;
use std::rc::Rc;

use crate::eval::apply;
use crate::meta::Metas;
use crate::mult::Mult;
use crate::row::{Label, Row};
use crate::term::{Term, TermMeta};
use crate::value::{Elim, Head, Lvl, Value};

/// Разворачивает решённые дырки в голове значения.
///
/// `None` - разворачивать нечего, и это подавляющее большинство вызовов:
/// сравнение зовёт `force` на каждом шаге, а дырка в голове - редкость.
/// Возвращать `Rc::clone` вместо `None` значило бы платить за неё на каждом
/// сравнении; замерено - около десяти процентов на цепочке лямбд.
///
/// Спайн при развороте переигрывается: решение - обычное значение, и применить
/// его к накопленным аргументам значит продолжить вычисление с того места, где
/// оно застряло.
#[must_use]
pub fn force(metas: &Metas, value: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(Head::Meta(meta), spine) = &**value else {
        return None;
    };
    let solution = metas.term_solution(*meta)?;
    let replayed = spine
        .iter()
        .fold(Rc::clone(solution), |head, elim| match elim {
            Elim::App(argument) => apply(&head, Rc::clone(argument)),
            Elim::Case(case) => crate::eval::eliminate_case(case, &head),
        });
    Some(force(metas, &replayed).unwrap_or(replayed))
}

/// Пытается решить `?m ū ≡ right`.
///
/// `false` - задача вне паттернового фрагмента либо решения не существует;
/// вызывающий тогда продолжает обычным сравнением или отказывается.
pub fn solve(
    metas: &mut Metas,
    size: u32,
    meta: TermMeta,
    spine: &[Elim],
    right: &Rc<Value>,
) -> bool {
    let Some(renaming) = pattern(spine) else {
        return false;
    };
    // Переименование строится по спайну, поэтому арность решения - его длина,
    // а не размер контекста: дырка могла быть заведена уже, чем контекст, в
    // котором её встретили.
    let arity = u32::try_from(renaming.len()).unwrap_or(u32::MAX);
    let Some(body) = read(metas, meta, &renaming, size, arity, 0, right) else {
        return false;
    };
    // Кратность лямбд решения не значит ничего: тип дырки её и несёт, а
    // проверка кратностей идёт по типу, а не по решению.
    let abstracted = (0..arity).fold(body, |body, index| {
        Term::Lam(Mult::Many, format!("m{index}").into(), Rc::new(body))
    });
    metas.solve_term(
        meta,
        crate::eval::eval(&crate::value::Env::default(), &abstracted),
    );
    true
}

/// Спайн как паттерн: различные переменные контекста и ничего больше.
///
/// Возвращает отображение «уровень → позиция в решении».
fn pattern(spine: &[Elim]) -> Option<HashMap<u32, u32>> {
    let mut renaming = HashMap::with_capacity(spine.len());
    for (position, elim) in spine.iter().enumerate() {
        let Elim::App(argument) = elim else {
            // Разбор в спайне дырки - не паттерн: обратить его нечем.
            return None;
        };
        let Value::Neutral(Head::Local(Lvl(level)), inner) = &**argument else {
            return None;
        };
        if !inner.is_empty() {
            return None;
        }
        let position = u32::try_from(position).ok()?;
        // Повтор переменной снимает единственность: `?m x x ≡ x` не различает,
        // какое из двух связываний имелось в виду.
        if renaming.insert(*level, position).is_some() {
            return None;
        }
    }
    Some(renaming)
}

/// Читает значение обратно, переводя переменные спайна в связывания решения.
///
/// `outer` - размер контекста, в котором живёт правая часть. Он и арность
/// решения - разные величины: спайн мог накрыть не весь контекст, и уровень,
/// в него не попавший, есть побег.
///
/// `None` - переменная вне спайна либо вхождение самой дырки.
fn read(
    metas: &Metas,
    meta: TermMeta,
    renaming: &HashMap<u32, u32>,
    outer: u32,
    arity: u32,
    depth: u32,
    value: &Rc<Value>,
) -> Option<Term> {
    let forced = force(metas, value);
    let value = forced.as_ref().unwrap_or(value);
    // Контекст решения: его параметры плюс связывания, под которые спустились.
    let size = arity + depth;
    let recur = |value| read(metas, meta, renaming, outer, arity, depth, value);
    match &**value {
        Value::Neutral(head, spine) => {
            let base = match head {
                Head::Local(Lvl(level)) => {
                    // Уровни ниже `outer` пришли из контекста правой части и
                    // обязаны найтись в спайне; уровни выше введены спуском
                    // под связывание и переезжают на ту же глубину решения.
                    let level = if *level < outer {
                        *renaming.get(level)?
                    } else {
                        arity + (level - outer)
                    };
                    Term::Var(Lvl(level).to_index(size))
                }
                Head::Global(name, levels) => Term::Const(Rc::clone(name), Rc::clone(levels)),
                // Вхождение самой дырки: подстановка дала бы бесконечный терм.
                Head::Meta(found) if *found == meta => return None,
                Head::Meta(found) => Term::Meta(*found),
            };
            spine.iter().try_fold(base, |callee, elim| match elim {
                Elim::App(argument) => Some(Term::App(Rc::new(callee), Rc::new(recur(argument)?))),
                // Разбор переписывать нечем: мотив и ветви - значения, и
                // обратное чтение под переименованием для них не написано.
                // Отказ консервативен и сузится вместе с первым потребителем.
                Elim::Case(_) => None,
            })
        }
        Value::Lam(mult, name, closure) => {
            let body = closure.apply(Value::var(Lvl(outer + depth)));
            Some(Term::Lam(
                *mult,
                Rc::clone(name),
                Rc::new(read(metas, meta, renaming, outer, arity, depth + 1, &body)?),
            ))
        }
        Value::Pi(binder, name, domain, row, closure) => {
            let mut labels = Vec::new();
            for label in row.labels() {
                let mut arguments = Vec::new();
                for argument in &label.arguments {
                    arguments.push(recur(argument)?);
                }
                labels.push(Label {
                    name: Rc::clone(&label.name),
                    arguments,
                });
            }
            let codomain = closure.apply(Value::var(Lvl(outer + depth)));
            Some(Term::Pi(
                *binder,
                Rc::clone(name),
                Rc::new(recur(domain)?),
                Row::new(labels),
                Rc::new(read(
                    metas,
                    meta,
                    renaming,
                    outer,
                    arity,
                    depth + 1,
                    &codomain,
                )?),
            ))
        }
        Value::Universe(level) => Some(Term::Universe(level.clone())),
    }
}
