//! Вставка счётчика ссылок и переиспользование блока (§5.1).
//!
//! Проход **IR → IR**, и это требование, а не стиль. Устрой вставку эмиттером -
//! и LLVM-бэкенд Фазы 7 (`docs/phase7-plan.md`) получил бы понижение без RC, то
//! есть писать пришлось бы второй Perceus, а не второй эмиттер. Ядра этот модуль
//! не читает; он живёт по ту же сторону шва, что и [`ir`](crate::ir), и это
//! проверено `tests/seam.rs`.
//!
//! # Договор о владении
//!
//! Одно правило на всё понижение: **аргумент приходит владением, ответ уходит
//! владением**. Функция обязана потребить каждый живой параметр ровно однажды -
//! отдав его дальше либо дропнув, - и вернуть ссылку, которой владеет
//! вызывающий.
//!
//! Из правила следует всё остальное. `adamas_set_field` и `adamas_closure_set`
//! владение забирают, поэтому построение ничего не дропает. `adamas_apply`
//! замыкание **заимствует** (`adamas.h`), поэтому применение дропает его само:
//! в IR это `Bind` вокруг [`Expr::Apply`] и [`Expr::Drop`] после него.
//! Трамплин замыкания достаёт среду из слотов, которыми замыкание владеет, -
//! значит `dup` на каждый слот, и его ставит эмиттер, потому что трамплина в IR
//! нет вовсе.
//!
//! # Как считается, где `dup`
//!
//! Обход несёт множество `owned` - связывания, которые это выражение обязано
//! потребить ровно по разу. Дальше три правила:
//!
//! - Связывание в `owned` потребляется своим **последним** употреблением;
//!   каждое употребление до него берёт лишнюю ссылку.
//! - Связывание, которое выражение не называет вовсе, дропается сразу.
//! - Ветвь разбора получает своё `owned`: соседние ветви исключают друг друга, и
//!   то, что не понадобилось этой, дропается на входе в неё.
//!
//! Дроп стоит там, где связывание перестало быть нужным по построению обхода, а
//! не раньше: раннего дропа Perceus'а (Reinking et al. 2021, §2.3) здесь нет, и
//! горячий путь от этого держит значения дольше оптимального.
//!
//! # Где срабатывает reuse
//!
//! Правило - §5.1 и [`adamas_core::fbip`]: ветвь, потребившая разобранное,
//! вправе переписать его ячейку структурой **той же формы**, а формой считается
//! число полей. Отличие от `@fbip` одно и существенное: там проверяется
//! обещание и отказ - ответ, здесь reuse либо ставится, либо нет, и правило
//! поэтому **консервативнее**. Блок придерживается только тогда, когда его
//! занимает каждый путь через ветвь; путь, на котором занять некому, оставил бы
//! блок висеть, и течь вернулась бы через reuse.
//!
//! # Плоское значение считать нечем
//!
//! Счётчик лежит в заголовке, а у плоского значения заголовка нет вовсе
//! (§4.11, §13 от 2026-09-08). Поэтому связывание с представлением
//! [`Repr::Flat`](crate::ir::Repr) в `owned` не входит и `dup` с `drop` по нему
//! не эмитятся - не как оптимизация, а потому что эмитить нечего: `adamas_dup`
//! от битов числа `42` есть запись по адресу `42`. Тем же правилом плоский слот
//! не дропается при разборе и не дублируется при разделении.
//!
//! Уникальность спрашивается **в рантайме** (`rc == 0`), а не у
//! [`Unique`](crate::ir::Unique): статически она есть только у производства -
//! unique-тип либо локально свежий объект (§10 вопрос 149, закрыт), - а вывод
//! от этих источников заводит пункт B Фазы 7. Кратность её не даёт: `swap :
//! (1 t : Two) -> Two`, позванная от ω-значения, законна, и объект внутри неё
//! разделён. Замер - `tests/perceus.rs`, одна и та же `swap` стоит лишнюю
//! ячейку.

use std::collections::BTreeSet;

use adamas_core::mult::Mult;
use adamas_core::prim::PrimTy;

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Expr, Fact, Function, LocalId, Program, Stride,
};

/// Вставляет RC и переиспользование во все функции программы.
#[must_use]
pub fn insert(program: Program) -> Program {
    let Program {
        constructors,
        packings,
        functions,
        entry,
    } = program;
    let functions = functions
        .into_iter()
        .map(|function| owned(&constructors, function))
        .collect();
    Program {
        constructors,
        packings,
        functions,
        entry,
    }
}

/// Переводит одну функцию в форму, где владение соблюдено.
fn owned(constructors: &[Constructor], function: Function) -> Function {
    let scope: BTreeSet<LocalId> = function
        .live_captured()
        .chain(function.live_parameters())
        .filter(|binding| binding.fact.repr.counted())
        .map(|binding| binding.local)
        .collect();
    let mut pass = Pass {
        constructors,
        next: ceiling(&function),
        flat: flat(&function),
    };
    let Function {
        id,
        name,
        form,
        captured,
        parameters,
        result,
        body,
    } = function;
    let body = pass.expr(body, &scope);
    Function {
        id,
        name,
        form,
        captured,
        parameters,
        result,
        body,
    }
}

/// Плоские связывания функции - те, по которым счёта не бывает вовсе.
///
/// Собираются заранее и все разом: `dup` ставится в месте употребления, а там
/// объявления уже не видно.
fn flat(function: &Function) -> BTreeSet<LocalId> {
    let mut found = BTreeSet::new();
    for binding in function.captured.iter().chain(&function.parameters) {
        if !binding.fact.repr.counted() {
            found.insert(binding.local);
        }
    }
    inner(&function.body, &mut found);
    found
}

/// То же по телу: связывания `let` и поля ветвей.
fn inner(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    match expr {
        Expr::Local(_)
        | Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::LayoutField { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => {}
        Expr::Unpack { value, .. } => inner(value, out),
        Expr::RegionLast { region } => inner(region, out),
        Expr::RegionAlloc { region, value, .. } => {
            inner(region, out);
            inner(value, out);
        }
        Expr::RegionRead { region, at, .. } => {
            inner(region, out);
            inner(at, out);
        }
        Expr::RegionWrite {
            region, at, value, ..
        } => {
            inner(region, out);
            inner(at, out);
            inner(value, out);
        }
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => {
            for argument in arguments {
                inner(argument, out);
            }
        }
        Expr::ArrayNew { count, initial, .. } => {
            inner(count, out);
            inner(initial, out);
        }
        Expr::ArraySet {
            array, at, value, ..
        } => {
            inner(array, out);
            inner(at, out);
            inner(value, out);
        }
        Expr::ArrayIndex { array, at, .. } => {
            inner(array, out);
            inner(at, out);
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                inner(capture, out);
            }
        }
        Expr::Primitive { left, right, .. } => {
            inner(left, out);
            inner(right, out);
        }
        Expr::Apply { callee, argument } => {
            inner(callee, out);
            inner(argument, out);
        }
        Expr::Bind {
            binding,
            value,
            body,
        } => {
            if !binding.fact.repr.counted() {
                out.insert(binding.local);
            }
            inner(value, out);
            inner(body, out);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            inner(scrutinee, out);
            for arm in arms {
                for field in &arm.fields {
                    if !field.fact.repr.counted() {
                        out.insert(field.local);
                    }
                }
                inner(&arm.body, out);
            }
        }
        Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
            inner(body, out);
        }
    }
}

/// Первый свободный номер связывания в функции.
///
/// Считается обходом, а не хранится: номера раздаёт понижение, и второй счётчик
/// разъехался бы с первым молча.
fn ceiling(function: &Function) -> u32 {
    let mut top = 0;
    let mut note = |local: LocalId| top = top.max(local.0 + 1);
    for binding in function.captured.iter().chain(&function.parameters) {
        note(binding.local);
    }
    bound(&function.body, &mut note);
    top
}

/// Все связывания, которые вводит выражение.
fn bound(expr: &Expr, note: &mut impl FnMut(LocalId)) {
    match expr {
        Expr::Local(_)
        | Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::LayoutField { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => {}
        Expr::Unpack { value, .. } => bound(value, note),
        Expr::RegionLast { region } => bound(region, note),
        Expr::RegionAlloc { region, value, .. } => {
            bound(region, note);
            bound(value, note);
        }
        Expr::RegionRead { region, at, .. } => {
            bound(region, note);
            bound(at, note);
        }
        Expr::RegionWrite {
            region, at, value, ..
        } => {
            bound(region, note);
            bound(at, note);
            bound(value, note);
        }
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => {
            for argument in arguments {
                bound(argument, note);
            }
        }
        Expr::ArrayNew { count, initial, .. } => {
            bound(count, note);
            bound(initial, note);
        }
        Expr::ArraySet {
            array, at, value, ..
        } => {
            bound(array, note);
            bound(at, note);
            bound(value, note);
        }
        Expr::ArrayIndex { array, at, .. } => {
            bound(array, note);
            bound(at, note);
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                bound(capture, note);
            }
        }
        Expr::Primitive { left, right, .. } => {
            bound(left, note);
            bound(right, note);
        }
        Expr::Apply { callee, argument } => {
            bound(callee, note);
            bound(argument, note);
        }
        Expr::Bind {
            binding,
            value,
            body,
        } => {
            note(binding.local);
            bound(value, note);
            bound(body, note);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            bound(scrutinee, note);
            for arm in arms {
                for field in &arm.fields {
                    note(field.local);
                }
                bound(&arm.body, note);
            }
        }
        Expr::Dup { body, .. } | Expr::Drop { body, .. } => bound(body, note),
        Expr::Reclaim { token, body, .. } => {
            note(*token);
            bound(body, note);
        }
    }
}

/// Связывания, которые выражение называет.
fn mentions(expr: &Expr) -> BTreeSet<LocalId> {
    let mut found = BTreeSet::new();
    named(expr, &mut found);
    found
}

/// То же, накопителем.
fn named(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    match expr {
        Expr::Local(local) => {
            out.insert(*local);
        }
        // Дескриптор укладки в `owned` не входит - счётчика у него нет
        // ([`Repr::Layout`]), - но упомянут он именно здесь, и обходу дешевле
        // это знать, чем полагаться на то, что дроп по нему не встанет.
        Expr::LayoutField { descriptor, .. } => {
            out.insert(*descriptor);
        }
        Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => {}
        Expr::Unpack { value, .. } => named(value, out),
        Expr::RegionLast { region } => named(region, out),
        Expr::RegionAlloc { region, value, .. } => {
            named(region, out);
            named(value, out);
        }
        Expr::RegionRead { region, at, .. } => {
            named(region, out);
            named(at, out);
        }
        Expr::RegionWrite {
            region, at, value, ..
        } => {
            named(region, out);
            named(at, out);
            named(value, out);
        }
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => {
            for argument in arguments {
                named(argument, out);
            }
        }
        Expr::ArrayNew { count, initial, .. } => {
            named(count, out);
            named(initial, out);
        }
        Expr::ArraySet {
            array, at, value, ..
        } => {
            named(array, out);
            named(at, out);
            named(value, out);
        }
        Expr::ArrayIndex { array, at, .. } => {
            named(array, out);
            named(at, out);
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                named(capture, out);
            }
        }
        Expr::Primitive { left, right, .. } => {
            named(left, out);
            named(right, out);
        }
        Expr::Apply { callee, argument } => {
            named(callee, out);
            named(argument, out);
        }
        Expr::Bind { value, body, .. } => {
            named(value, out);
            named(body, out);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            named(scrutinee, out);
            for arm in arms {
                named(&arm.body, out);
            }
        }
        Expr::Dup { local, body }
        | Expr::Drop { local, body }
        | Expr::Reclaim { local, body, .. } => {
            out.insert(*local);
            named(body, out);
        }
    }
}

/// Оборачивает выражение дропами: они срабатывают до него.
fn drops(locals: impl IntoIterator<Item = LocalId>, body: Expr) -> Expr {
    locals.into_iter().fold(body, |body, local| Expr::Drop {
        local,
        body: Box::new(body),
    })
}

/// Состояние прохода: таблица конструкторов и счётчик свежих связываний.
struct Pass<'a> {
    constructors: &'a [Constructor],
    next: u32,
    /// Связывания без заголовка: счётчика у них нет (§4.11).
    flat: BTreeSet<LocalId>,
}

impl Pass<'_> {
    /// Свежий номер: понижение раздало свои, эти идут за ними.
    fn fresh(&mut self) -> LocalId {
        let local = LocalId(self.next);
        self.next += 1;
        local
    }

    /// Свежее связывание, заведённое бэкендом.
    fn temporary(&mut self, name: &str) -> Binding {
        Binding {
            name: name.to_owned(),
            local: self.fresh(),
            fact: Fact::opaque(),
        }
    }

    /// Сколько слотов у объекта конструктора.
    fn shape(&self, constructor: CtorId) -> usize {
        self.constructors
            .get(usize::from(constructor.0))
            .map_or(0, Constructor::slots)
    }

    /// Переводит выражение, которое обязано потребить `owned` ровно по разу.
    fn expr(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        match expr {
            Expr::Local(local) => {
                let rest = owned.iter().copied().filter(|it| *it != local);
                // Плоское связывание не считается вовсе: счётчика у него нет,
                // и лишняя ссылка на биты числа была бы записью по их адресу.
                let taken = if owned.contains(&local) || self.flat.contains(&local) {
                    Expr::Local(local)
                } else {
                    // Связывание принадлежит соседу, который потребит его
                    // позже: своя ссылка берётся здесь.
                    Expr::Dup {
                        local,
                        body: Box::new(Expr::Local(local)),
                    }
                };
                drops(rest.collect::<Vec<_>>(), taken)
            }
            Expr::Erased
            | Expr::ConstructClosure { .. }
            | Expr::Literal { .. }
            | Expr::LayoutField { .. }
            // Пустая область блока ещё не занимает: аллокацию выдаст эмиттер,
            // а считать по ней нечего до первого её употребления.
            | Expr::RegionNew
            | Expr::Layout { .. } => drops(owned.iter().copied().collect::<Vec<_>>(), expr),
            Expr::ArrayNew { .. } | Expr::ArraySet { .. } | Expr::ArrayIndex { .. } => {
                self.array(expr, owned)
            }
            Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. } => self.region(expr, owned),
            Expr::Pack { .. } | Expr::Unpack { .. } => self.aggregate(expr, owned),
            Expr::Primitive {
                op,
                ty,
                left,
                right,
            } => {
                let (mut parts, spare) = self.sequence(vec![*left, *right], owned);
                let right = parts.pop().unwrap_or(Expr::Erased);
                let left = parts.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Primitive {
                        op,
                        ty,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            }
            Expr::Construct {
                constructor,
                reuse,
                arguments,
            } => {
                let (arguments, spare) = self.sequence(arguments, owned);
                drops(
                    spare,
                    Expr::Construct {
                        constructor,
                        reuse,
                        arguments,
                    },
                )
            }
            Expr::Call {
                function,
                arguments,
            } => {
                let (arguments, spare) = self.sequence(arguments, owned);
                drops(
                    spare,
                    Expr::Call {
                        function,
                        arguments,
                    },
                )
            }
            Expr::Closure { function, captured } => {
                let (captured, spare) = self.sequence(captured, owned);
                drops(spare, Expr::Closure { function, captured })
            }
            Expr::Apply { callee, argument } => self.applied(*callee, *argument, owned),
            Expr::Bind {
                binding,
                value,
                body,
            } => self.bound(binding, *value, *body, owned),
            Expr::Match {
                scrutinee,
                consumed,
                arms,
            } => self.analysis(*scrutinee, consumed, arms, owned),
            // Проход зовётся однажды и по построенному понижением: своих узлов
            // он на входе не встречает.
            Expr::Dup { .. } | Expr::Drop { .. } | Expr::Reclaim { .. } => expr,
        }
    }

    /// Операция над массивом (§4.11).
    ///
    /// Массив - объект кучи с одним заголовком на всю длину (§5.1), и владение
    /// по нему то же, что по всякому объекту: аргумент приходит владением,
    /// ответ уходит владением. Поэлементного RC у плоского массива нет вовсе -
    /// считать там нечего.
    ///
    /// Порядок подвыражений тот же, что у [`Pass::sequence`] везде, и он
    /// **значим**: массив стоит первым, а читающее из него значение - последним,
    /// поэтому к записи массив приходит со счётчиком, который чтение уже
    /// вернуло, и запись идёт по месту.
    /// Сборка и разбор плоского агрегата (§4.11).
    ///
    /// Счётчика у агрегата нет вовсе, поэтому считать надо только то, что в нём
    /// собрано либо из чего он прочитан.
    fn aggregate(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        match expr {
            Expr::Pack {
                packing,
                variant,
                fields,
            } => {
                let (fields, spare) = self.sequence(fields, owned);
                drops(
                    spare,
                    Expr::Pack {
                        packing,
                        variant,
                        fields,
                    },
                )
            }
            Expr::Unpack {
                packing,
                variant,
                field,
                value,
            } => {
                let (mut parts, spare) = self.sequence(vec![*value], owned);
                let value = parts.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Unpack {
                        packing,
                        variant,
                        field,
                        value: Box::new(value),
                    },
                )
            }
            other => other,
        }
    }

    fn array(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        /// Какая из трёх операций разобрана: узел собирается обратно тем же.
        enum Shape {
            New,
            Set,
            Index,
        }
        let (shape, stride, parts) = match expr {
            Expr::ArrayNew {
                stride,
                count,
                initial,
            } => (Shape::New, stride, vec![*count, *initial]),
            Expr::ArraySet {
                stride,
                array,
                at,
                value,
            } => (Shape::Set, stride, vec![*array, *at, *value]),
            Expr::ArrayIndex { stride, array, at } => (Shape::Index, stride, vec![*array, *at]),
            other => return other,
        };
        let (mut done, spare) = self.sequence(parts, owned);
        // Подвыражения снимаются с конца, поэтому и разбираются справа налево.
        let mut next = || Box::new(done.pop().unwrap_or(Expr::Erased));
        let node = match shape {
            Shape::New => {
                let initial = next();
                Expr::ArrayNew {
                    stride,
                    count: next(),
                    initial,
                }
            }
            Shape::Set => {
                let value = next();
                let at = next();
                Expr::ArraySet {
                    stride,
                    array: next(),
                    at,
                    value,
                }
            }
            Shape::Index => {
                let at = next();
                Expr::ArrayIndex {
                    stride,
                    array: next(),
                    at,
                }
            }
        };
        drops(spare, node)
    }

    /// Операция над регионом (§3.6).
    ///
    /// Владение то же, что у массива, и по той же причине: блок - объект кучи
    /// с одним заголовком на всю область. Нагрузка внутри области счёта не
    /// платит вовсе - счётчика у неё нет (`{Flat a}`), - и это то самое, ради
    /// чего §3.6 написан: «освобождение одно на всю область».
    ///
    /// Порядок подвыражений значим ровно как у массива: блок стоит первым, а
    /// читающее из него - последним, поэтому к записи блок приходит со
    /// счётчиком, который чтение уже вернуло, и запись идёт по месту.
    fn region(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        /// Какая из четырёх операций разобрана.
        enum Shape {
            Alloc,
            Last,
            Read,
            Write,
        }
        let (shape, stride, parts) = match expr {
            Expr::RegionAlloc {
                stride,
                region,
                value,
            } => (Shape::Alloc, stride, vec![*region, *value]),
            Expr::RegionLast { region } => {
                (Shape::Last, Stride::Static(PrimTy::UInt64), vec![*region])
            }
            Expr::RegionRead { stride, region, at } => (Shape::Read, stride, vec![*region, *at]),
            Expr::RegionWrite {
                stride,
                region,
                at,
                value,
            } => (Shape::Write, stride, vec![*region, *at, *value]),
            other => return other,
        };
        let (mut done, spare) = self.sequence(parts, owned);
        let mut next = || Box::new(done.pop().unwrap_or(Expr::Erased));
        let node = match shape {
            Shape::Alloc => {
                let value = next();
                Expr::RegionAlloc {
                    stride,
                    region: next(),
                    value,
                }
            }
            Shape::Last => Expr::RegionLast { region: next() },
            Shape::Read => {
                let at = next();
                Expr::RegionRead {
                    stride,
                    region: next(),
                    at,
                }
            }
            Shape::Write => {
                let value = next();
                let at = next();
                Expr::RegionWrite {
                    stride,
                    region: next(),
                    at,
                    value,
                }
            }
        };
        drops(spare, node)
    }

    /// Переводит подвыражения, вычисляемые по порядку.
    ///
    /// Владение достаётся **последнему** употреблению: до него связывание
    /// дублируется, потому что понадобится ещё. Отдаёт заодно то, чего не
    /// называет ни одно подвыражение, - дропать его вызывающему.
    fn sequence(
        &mut self,
        items: Vec<Expr>,
        owned: &BTreeSet<LocalId>,
    ) -> (Vec<Expr>, Vec<LocalId>) {
        let uses: Vec<BTreeSet<LocalId>> = items.iter().map(mentions).collect();
        let mut done = Vec::with_capacity(items.len());
        for (at, item) in items.into_iter().enumerate() {
            let mine: BTreeSet<LocalId> = owned
                .iter()
                .copied()
                .filter(|local| uses[at].contains(local))
                .filter(|local| !uses[at + 1..].iter().any(|later| later.contains(local)))
                .collect();
            done.push(self.expr(item, &mine));
        }
        let spare = owned
            .iter()
            .copied()
            .filter(|local| !uses.iter().any(|used| used.contains(local)))
            .collect();
        (done, spare)
    }

    /// Применение значения-функции.
    ///
    /// `adamas_apply` замыкание заимствует (`adamas.h`), поэтому дропает его
    /// применение - и **после** вызова, а не до: связывание ответа для того тут
    /// и заводится.
    fn applied(&mut self, callee: Expr, argument: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        let (mut parts, spare) = self.sequence(vec![callee, argument], owned);
        let argument = parts.pop().unwrap_or(Expr::Erased);
        let callee = parts.pop().unwrap_or(Expr::Erased);
        let held = self.temporary("применяемое");
        let answer = self.temporary("ответ");
        let (borrowed, given) = (held.local, answer.local);
        let node = Expr::Bind {
            binding: held,
            value: Box::new(callee),
            body: Box::new(Expr::Bind {
                binding: answer,
                value: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Local(borrowed)),
                    argument: Box::new(argument),
                }),
                body: Box::new(Expr::Drop {
                    local: borrowed,
                    body: Box::new(Expr::Local(given)),
                }),
            }),
        };
        drops(spare, node)
    }

    /// Связывание значения.
    fn bound(
        &mut self,
        binding: Binding,
        value: Expr,
        body: Expr,
        owned: &BTreeSet<LocalId>,
    ) -> Expr {
        let inside = mentions(&body);
        let outside = mentions(&value);
        let mine: BTreeSet<LocalId> = owned
            .iter()
            .copied()
            .filter(|local| outside.contains(local) && !inside.contains(local))
            .collect();
        let spare: Vec<LocalId> = owned
            .iter()
            .copied()
            .filter(|local| !outside.contains(local) && !inside.contains(local))
            .collect();
        let value = self.expr(value, &mine);
        let mut under: BTreeSet<LocalId> = owned
            .iter()
            .copied()
            .filter(|local| inside.contains(local))
            .collect();
        if binding.fact.present && binding.fact.repr.counted() {
            under.insert(binding.local);
        }
        let body = self.expr(body, &under);
        drops(
            spare,
            Expr::Bind {
                binding,
                value: Box::new(value),
                body: Box::new(body),
            },
        )
    }

    /// Разбор.
    ///
    /// Разбираемое сперва становится связыванием: отдать можно связывание, а не
    /// выражение. Дальше каждая ветвь получает своё владение - поля, которые она
    /// называет, приходят к ней `dup`'ом, а разобранное отдаётся ею же, если
    /// назвать его больше некому.
    fn analysis(
        &mut self,
        scrutinee: Expr,
        consumed: Mult,
        arms: Vec<Arm>,
        owned: &BTreeSet<LocalId>,
    ) -> Expr {
        let Expr::Local(subject) = scrutinee else {
            let binding = self.temporary("разбираемое");
            let local = binding.local;
            let node = Expr::Bind {
                binding,
                value: Box::new(scrutinee),
                body: Box::new(Expr::Match {
                    scrutinee: Box::new(Expr::Local(local)),
                    consumed,
                    arms,
                }),
            };
            return self.expr(node, owned);
        };
        let mut done = Vec::with_capacity(arms.len());
        for arm in arms {
            done.push(self.arm(subject, arm, owned));
        }
        Expr::Match {
            scrutinee: Box::new(Expr::Local(subject)),
            consumed,
            arms: done,
        }
    }

    /// Одна ветвь разбора.
    fn arm(&mut self, subject: LocalId, arm: Arm, owned: &BTreeSet<LocalId>) -> Arm {
        let Arm {
            constructor,
            fields,
            body,
        } = arm;
        let called = mentions(&body);
        // Плоское поле не дублируется: оно лежит в слоте по значению, и своей
        // ссылки у него нет (§4.11).
        let kept: Vec<LocalId> = fields
            .iter()
            .filter(|field| field.fact.present && field.fact.repr.counted())
            .filter(|field| called.contains(&field.local))
            .map(|field| field.local)
            .collect();
        // Разобранное отдаёт эта ветвь, если владение у нас и назвать его в теле
        // некому: названное остаётся живым, и переписывать было бы нечего.
        let ours = owned.contains(&subject) && !called.contains(&subject);
        let mut under: BTreeSet<LocalId> = owned.clone();
        if ours {
            under.remove(&subject);
        }
        under.extend(kept.iter().copied());
        let mut body = self.expr(body, &under);

        if ours {
            let slots = self.shape(constructor);
            let cell = (slots > 0 && self.plans(&body, slots)).then(|| self.fresh());
            body = match cell {
                Some(cell) => {
                    self.attach(&mut body, slots, cell);
                    Expr::Reclaim {
                        local: subject,
                        token: cell,
                        body: Box::new(body),
                    }
                }
                None => Expr::Drop {
                    local: subject,
                    body: Box::new(body),
                },
            };
        }
        // `dup` полей ставится снаружи дропа разобранного: иначе дроп унёс бы их
        // с собой.
        for field in kept.into_iter().rev() {
            body = Expr::Dup {
                local: field,
                body: Box::new(body),
            };
        }
        Arm {
            constructor,
            fields,
            body,
        }
    }

    /// Займёт ли придержанную ячейку **каждый** путь через выражение.
    ///
    /// Консерватизм здесь несимметричен нарочно: ложное «да» оставляет блок
    /// висеть на том пути, где занять его некому, то есть возвращает течь;
    /// ложное «нет» стоит одной аллокации.
    fn plans(&self, expr: &Expr, slots: usize) -> bool {
        match expr {
            Expr::Construct {
                constructor,
                reuse,
                arguments,
            } => {
                if reuse.is_none() && self.shape(*constructor) == slots {
                    return true;
                }
                arguments.iter().any(|argument| self.plans(argument, slots))
            }
            Expr::Call { arguments, .. } => {
                arguments.iter().any(|argument| self.plans(argument, slots))
            }
            Expr::Closure { captured, .. } => {
                captured.iter().any(|capture| self.plans(capture, slots))
            }
            Expr::Primitive { left, right, .. } => {
                self.plans(left, slots) || self.plans(right, slots)
            }
            Expr::Apply { callee, argument } => {
                self.plans(callee, slots) || self.plans(argument, slots)
            }
            Expr::Bind { value, body, .. } => self.plans(value, slots) || self.plans(body, slots),
            // Ветви исключают друг друга, поэтому «каждый путь» требует всех.
            Expr::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|arm| self.plans(&arm.body, slots))
            }
            Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
                self.plans(body, slots)
            }
            // Ячейка массива под переписывание не годится: придержанный блок
            // размером в `slots` полей, а массив - в свою длину.
            Expr::ArrayNew { count, initial, .. } => {
                self.plans(count, slots) || self.plans(initial, slots)
            }
            Expr::ArraySet {
                array, at, value, ..
            } => self.plans(array, slots) || self.plans(at, slots) || self.plans(value, slots),
            Expr::ArrayIndex { array, at, .. } => self.plans(array, slots) || self.plans(at, slots),
            // Плоский агрегат ячейки кучи не занимает вовсе (§4.11), и
            // придержать её ему нечем.
            Expr::Local(_)
            | Expr::Erased
            | Expr::ConstructClosure { .. }
            | Expr::Literal { .. }
            | Expr::LayoutField { .. }
            | Expr::Pack { .. }
            | Expr::Unpack { .. }
            // Область региона под переписывание тоже не годится, и по тому же
            // счёту: придержанный блок размером в `slots` полей.
            | Expr::RegionNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. }
            | Expr::Layout { .. } => false,
        }
    }

    /// Раздаёт ячейку тем же обходом, каким [`Pass::plans`] её обещал.
    fn attach(&self, expr: &mut Expr, slots: usize, token: LocalId) -> bool {
        match expr {
            Expr::Construct {
                constructor,
                reuse,
                arguments,
            } => {
                if reuse.is_none() && self.shape(*constructor) == slots {
                    *reuse = Some(token);
                    return true;
                }
                arguments
                    .iter_mut()
                    .any(|argument| self.attach(argument, slots, token))
            }
            Expr::Call { arguments, .. } => arguments
                .iter_mut()
                .any(|argument| self.attach(argument, slots, token)),
            Expr::Closure { captured, .. } => captured
                .iter_mut()
                .any(|capture| self.attach(capture, slots, token)),
            Expr::Primitive { left, right, .. } => {
                self.attach(left, slots, token) || self.attach(right, slots, token)
            }
            Expr::Apply { callee, argument } => {
                self.attach(callee, slots, token) || self.attach(argument, slots, token)
            }
            Expr::Bind { value, body, .. } => {
                self.attach(value, slots, token) || self.attach(body, slots, token)
            }
            Expr::Match { arms, .. } => {
                if arms.is_empty() || !arms.iter().all(|arm| self.plans(&arm.body, slots)) {
                    return false;
                }
                for arm in arms.iter_mut() {
                    self.attach(&mut arm.body, slots, token);
                }
                true
            }
            Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
                self.attach(body, slots, token)
            }
            Expr::ArrayNew { count, initial, .. } => {
                self.attach(count, slots, token) || self.attach(initial, slots, token)
            }
            Expr::ArraySet {
                array, at, value, ..
            } => {
                self.attach(array, slots, token)
                    || self.attach(at, slots, token)
                    || self.attach(value, slots, token)
            }
            Expr::ArrayIndex { array, at, .. } => {
                self.attach(array, slots, token) || self.attach(at, slots, token)
            }
            // Плоский агрегат ячейки кучи не занимает вовсе (§4.11), и
            // придержать её ему нечем.
            Expr::Local(_)
            | Expr::Erased
            | Expr::ConstructClosure { .. }
            | Expr::Literal { .. }
            | Expr::LayoutField { .. }
            | Expr::Pack { .. }
            | Expr::Unpack { .. }
            // Область региона под переписывание тоже не годится, и по тому же
            // счёту: придержанный блок размером в `slots` полей.
            | Expr::RegionNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. }
            | Expr::Layout { .. } => false,
        }
    }
}
