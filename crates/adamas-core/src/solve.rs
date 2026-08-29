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
//! # Три проверки, без которых решение неверно
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
//! **Тип решения.** Сравнение `?m ≡ t` типов не касается - оно сводит
//! значения, - поэтому проверка решения есть единственное место, где тип дырки
//! вообще предъявляется. Без неё `?a : Type ?u`, решённая `Nat`, оставляет `?u`
//! свободным, и определение отвергается за нерешённый уровень при полностью
//! выведенном имплисите. См. `well_typed`.
//!
//! # Решение записывается один раз
//!
//! Backtracking'а в проверке нет (см. [`Metas`]), поэтому решение
//! окончательно. Порядок, в котором проверка добралась до ограничений, на
//! результат влияет - но не на корректность: неверная догадка невозможна,
//! потому что догадок здесь не делается вовсе.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ctx::Ctx;
use crate::eval::apply;
use crate::meta::Metas;
use crate::mult::Mult;
use crate::row::{Label, Row};
use crate::sig::Signature;
use crate::term::{Field, Fields, Term, TermMeta};
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
            Elim::Project(name) => crate::eval::project(&head, name),
            Elim::With(fields) => crate::eval::with(&head, fields.to_vec()),
        });
    Some(force(metas, &replayed).unwrap_or(replayed))
}

/// Пытается решить `?m ū ≡ right`.
///
/// `false` - задача вне паттернового фрагмента либо решения не существует;
/// вызывающий тогда продолжает обычным сравнением или отказывается.
pub fn solve(
    sig: &Signature,
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
    let arity = u32::try_from(spine.len()).unwrap_or(u32::MAX);
    let Some(body) = read(metas, meta, &renaming, size, arity, 0, right) else {
        return false;
    };
    // Кратности лямбд берутся из телескопа: `check` требует, чтобы лямбда
    // совпадала с `Pi` по кратности, а решение обязано пройти эту проверку.
    let mults = multiplicities(metas, meta, arity);
    let abstracted = (0..arity).fold(body, |body, index| {
        let depth = usize::try_from(arity - 1 - index).unwrap_or(0);
        Term::Lam(
            mults.get(depth).copied().unwrap_or(Mult::Many),
            format!("m{index}").into(),
            Rc::new(body),
        )
    });
    if !well_typed(sig, metas, meta, &abstracted) {
        return false;
    }
    metas.solve_term(
        meta,
        crate::eval::eval(&crate::value::Env::default(), &abstracted),
    );
    true
}

/// Читает телескоп полей под переименованием - по одному полю.
///
/// Хвост читается на исходной глубине: открытый ряд зависимостей не имеет
/// (§4.2, решение 2026-08-29), и под поля он не заходит.
#[allow(clippy::too_many_arguments)]
fn read_fields(
    metas: &Metas,
    meta: TermMeta,
    renaming: &HashMap<u32, u32>,
    outer: u32,
    arity: u32,
    depth: u32,
    telescope: &crate::value::Telescope,
) -> Option<Fields> {
    let mut earlier = Vec::with_capacity(telescope.fields().len());
    let mut written = Vec::with_capacity(telescope.fields().len());
    for (index, field) in telescope.fields().iter().enumerate() {
        let ty = telescope.at(index, &earlier);
        let step = u32::try_from(index).unwrap_or(0);
        written.push(Field {
            name: Rc::clone(&field.name),
            mult: field.mult,
            ty: Rc::new(read(
                metas,
                meta,
                renaming,
                outer,
                arity,
                depth + step,
                &ty,
            )?),
        });
        earlier.push(Value::var(Lvl(outer + depth + step)));
    }
    let tail = match telescope.tail() {
        Some(tail) => Some(Rc::new(read(
            metas, meta, renaming, outer, arity, depth, &tail,
        )?)),
        None => None,
    };
    Some(Fields {
        fields: written.into(),
        tail,
    })
}

/// Кратности телескопа типа дырки, снаружи внутрь.
///
/// Короче `arity`, если тип дырки телескопа такой длины не имеет: тогда
/// оставшимся лямбдам достаётся `ω`, и отвергнет их проверка решения.
fn multiplicities(metas: &Metas, meta: TermMeta, arity: u32) -> Vec<Mult> {
    let mut found = Vec::new();
    let mut ty = Rc::clone(metas.term_type(meta));
    for depth in 0..arity {
        let Value::Pi(binder, _, _, _, codomain) = &*ty else {
            break;
        };
        found.push(binder.mult);
        let codomain = codomain.clone();
        ty = codomain.apply(Value::var(Lvl(depth)));
    }
    found
}

/// Проверяет решение против типа дырки.
///
/// Проверка здесь не подстраховка, а **единственное место, где тип решения
/// вообще смотрят**. Сравнение `?m ≡ t` типов не касается: оно сводит значения,
/// а `?m` подходит по форме к чему угодно. Между тем тип дырки несёт свои
/// ограничения - `?a : Type ?u` от implicit-параметра, - и решение `?a := Nat`
/// и есть то, что даёт `?u = 0`. Без этой проверки уровень остаётся свободным,
/// и определение отвергается за нерешённый уровень при полностью выведенном
/// имплисите.
///
/// И дырка, и решение замкнуты - первая по построению ([`Metas::fresh_term`]),
/// второе как цепочка лямбд, - поэтому проверять их можно в пустом контексте.
/// `0` в судейской кратности: решение стоит там же, где стояла дырка, а
/// расходование считается по типу вокруг неё, не здесь.
fn well_typed(sig: &Signature, metas: &mut Metas, meta: TermMeta, solution: &Term) -> bool {
    let ty = Rc::clone(metas.term_type(meta));
    crate::check::check(&Ctx::new(sig), metas, Mult::Zero, solution, &ty).is_ok()
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
        // Не переменная - позиция **отбрасывается**, а не отвергается вся
        // задача. Возникает это на разборе: индекс, уточнённый ветвью
        // (`n := Zero` в ветви `Nil`), приходит в спайн своим значением, а
        // дырка заводилась, когда он был переменной. Решение, не зависящее от
        // такой позиции, равенство удовлетворяет; если правая часть без неё не
        // читается, откажет `read` - там, где это видно.
        let Value::Neutral(Head::Local(Lvl(level)), inner) = &**argument else {
            continue;
        };
        if !inner.is_empty() {
            continue;
        }
        let position = u32::try_from(position).ok()?;
        // Повтор переменной снимает единственность: `?m x x ≡ x` не различает,
        // какое из двух связываний имелось в виду. Это, в отличие от не-
        // переменной, отказ: обе позиции подходят, и выбор был бы догадкой.
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
                Elim::Project(name) => Some(Term::Project(Rc::new(callee), Rc::clone(name))),
                Elim::With(fields) => Some(Term::With(
                    Rc::new(callee),
                    fields
                        .iter()
                        .map(|(name, value)| Some((Rc::clone(name), Rc::new(recur(value)?))))
                        .collect::<Option<Vec<_>>>()?
                        .into(),
                )),
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
        // Телескоп читается по одному полю, как и при обычном обратном
        // чтении: тип следующего живёт под предыдущими, поэтому глубина растёт
        // вместе с ними, а переименование остаётся тем же.
        Value::Record(telescope) => Some(Term::Record(read_fields(
            metas, meta, renaming, outer, arity, depth, telescope,
        )?)),
        Value::Row(telescope) => Some(Term::Row(read_fields(
            metas, meta, renaming, outer, arity, depth, telescope,
        )?)),
        Value::Object(fields) => {
            let mut written = Vec::with_capacity(fields.len());
            for (name, value) in fields.iter() {
                written.push((Rc::clone(name), Rc::new(recur(value)?)));
            }
            Some(Term::Object(written.into()))
        }
        Value::Universe(level) => Some(Term::Universe(level.clone())),
        Value::RowKind(level) => Some(Term::RowKind(level.clone())),
    }
}
