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
//! # Пара `dup`/`drop` на разборе схлопывается
//!
//! Ветвь берёт ссылку на каждое поле, которое называет, а дроп разобранного на
//! последней ссылке обходит поля и возвращает эти же ссылки обратно. На
//! **уникальном** родителе пара сокращается целиком: взятые поля переходят
//! ветви даром, невзятые дропает сам дроп, блок освобождается, счётчиков никто
//! не трогает. На разделённом не сокращается ничего - поля живут дальше в
//! родителе, и ссылка каждому нужна своя.
//!
//! Различаются два случая в рантайме - `adamas_is_unique`, то есть `rc == 0`, -
//! и это то же условие, на котором стоит reuse ниже, и та же развилка, которую
//! §5.1 описывает на месте разбора. Узла под неё не заведено: списки полей
//! лежат на самом дропе ([`Salvage`](crate::ir::Salvage)), и различать
//! схлопнутый дроп от обычного обязана одна печать.
//!
//! Мера - `benches/native.rs`: пара стоила **13%** времени символьного замера
//! (3.54 мс из 26.92, размах 0.13 по пяти прогонам). Ветвь, чей конструктор
//! несёт слот, ей не видный, схлопывание не берёт - см. [`Pass::covered`].
//!
//! # Где срабатывает reuse
//!
//! Правило - §5.1 и [`adamas_core::fbip`]: ветвь, потребившая разобранное,
//! вправе переписать его ячейку структурой **той же формы**, а формой считается
//! число полей. Отличие от `@fbip` одно и существенное: там проверяется
//! обещание и отказ - ответ, здесь reuse либо ставится, либо нет, и правило
//! поэтому **консервативнее**. Блок придерживается, когда его занимает хоть
//! один путь через ветвь; путь, которому занять его нечем, **возвращает** блок
//! куче ([`Expr::Discard`](crate::ir::Expr::Discard)).
//!
//! Раньше спрашивалось «каждый путь», и ветвь с односторонним построением -
//! `filter`, то есть `case p x of True -> Cons x (sift xs); False -> sift xs` -
//! теряла переиспользование целиком, хотя на занимающем пути оно законно (§10
//! вопрос 173, закрыт). Мера закрытия: на корпусе придержаний стало 76 → 85,
//! мест переиспользования 83 → 98, возвратов 9; тронуто шесть программ из 101,
//! пять из них выдают меньше блоков, и ни одна - больше. На стенде `sift`, где
//! занимающий путь идёт каждой ячейкой, выдано 6 500 000 блоков против
//! 100 000, время 70 → 16 мс.
//!
//! Цена возврата мерена отдельно, стендом, где **каждая** ячейка идёт
//! незанимающим путём: функция выросла на три инструкции (95 → 98 у gcc
//! `-O2`), время не сдвинулось - отношение 0.988 при размахе 0.079 по пяти
//! блокам чередования, то есть единица внутри интервала. Дешевизна не
//! случайна: на уникальном пути освобождение не добавилось, а **переехало** -
//! `adamas_free` ушёл с места разбора в незанимающую ветвь; сверх прежнего
//! платится только вызов `adamas_free(NULL)` на разделённом разобранном.
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
//! Уникальность **эта вставка** спрашивает в рантайме (`rc == 0`), а не у
//! [`Unique`](crate::ir::Unique), и порядок тут обратный ожидаемому: вывод
//! уникальности ([`crate::unique`]) идёт **после** неё, потому что судит по
//! отсутствию поставленных ею узлов [`Expr::Dup`](crate::ir::Expr::Dup).
//! Статически уникальность есть только у производства - unique-тип либо
//! локально свежий объект (§10 вопрос 149, закрыт). Кратность её не даёт:
//! `swap : (1 t : Two) -> Two`, позванная от ω-значения, законна, и объект
//! внутри неё разделён. Замер - `tests/perceus.rs`, одна и та же `swap` стоит
//! лишнюю ячейку.

use std::collections::BTreeSet;

use adamas_core::mult::Mult;
use adamas_core::prim::PrimTy;

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Expr, Fact, Function, LocalId, Program, Salvage, Stride,
};
use crate::split::Suspension;

/// Вставляет RC и переиспользование во все функции программы.
#[must_use]
pub fn insert(program: Program) -> Program {
    let suspending = crate::split::suspending(&program);
    let Program {
        constructors,
        packings,
        labels,
        handlers,
        functions,
        entry,
        source,
    } = program;
    let functions = functions
        .into_iter()
        .map(|function| owned(&constructors, &suspending, function))
        .collect();
    Program {
        constructors,
        packings,
        labels,
        handlers,
        functions,
        entry,
        source,
    }
}

/// Переводит одну функцию в форму, где владение соблюдено.
fn owned(constructors: &[Constructor], suspending: &Suspension, function: Function) -> Function {
    let scope: BTreeSet<LocalId> = function
        .live_captured()
        .chain(function.live_parameters())
        .filter(|binding| binding.fact.repr.counted())
        .map(|binding| binding.local)
        .collect();
    let mut pass = Pass {
        constructors,
        suspending,
        next: ceiling(&function),
        flat: flat(&function),
    };
    let Function {
        id,
        name,
        position,
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
        position,
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
///
/// Обход по [`Expr::children`], а не свой: узел, забытый здесь, сделал бы
/// плоское связывание считаемым - то есть отдал бы биты числа счётчику.
fn inner(expr: &Expr, out: &mut BTreeSet<LocalId>) {
    match expr {
        Expr::Bind { binding, .. } => {
            if !binding.fact.repr.counted() {
                out.insert(binding.local);
            }
        }
        Expr::Match { arms, .. } => {
            for field in arms.iter().flat_map(|arm| &arm.fields) {
                if !field.fact.repr.counted() {
                    out.insert(field.local);
                }
            }
        }
        _ => {}
    }
    for child in expr.children() {
        inner(child, out);
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
        Expr::Bind { binding, .. } => note(binding.local),
        Expr::Match { arms, .. } => {
            for field in arms.iter().flat_map(|arm| &arm.fields) {
                note(field.local);
            }
        }
        Expr::Reclaim { token, .. } => note(*token),
        _ => {}
    }
    for child in expr.children() {
        bound(child, note);
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
        Expr::Local(local)
        // Дескриптор укладки в `owned` не входит - счётчика у него нет
        // ([`Repr::Layout`]), - но упомянут он именно здесь, и обходу дешевле
        // это знать, чем полагаться на то, что дроп по нему не встанет.
        | Expr::LayoutField {
            descriptor: local, ..
        }
        | Expr::Dup { local, .. } => {
            out.insert(*local);
        }
        // Схлопнутый дроп называет сверх разобранного его поля: `dup` по ним
        // уехал внутрь, и обход, не знающий этого, счёл бы их несчитанными.
        Expr::Drop { local, salvage, .. } | Expr::Reclaim { local, salvage, .. } => {
            out.insert(*local);
            out.extend(salvage.locals());
        }
        _ => {}
    }
    for child in expr.children() {
        named(child, out);
    }
}

/// Оборачивает выражение дропами: они срабатывают до него.
fn drops(locals: impl IntoIterator<Item = LocalId>, body: Expr) -> Expr {
    locals.into_iter().fold(body, |body, local| Expr::Drop {
        local,
        salvage: Salvage::default(),
        body: Box::new(body),
    })
}

/// Состояние прохода: таблица конструкторов и счётчик свежих связываний.
struct Pass<'a> {
    constructors: &'a [Constructor],
    /// Функции, чей вызов есть точка приостановки ([`crate::split`]).
    suspending: &'a Suspension,
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
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => self.region(expr, owned),
            Expr::Pack { .. } | Expr::Unpack { .. } => self.aggregate(expr, owned),
            Expr::SimdSplat { .. }
            | Expr::SimdSet { .. }
            | Expr::SimdLane { .. }
            | Expr::SimdArith { .. } => self.vector(expr, owned),
            Expr::Primitive { .. } | Expr::Compare { .. } => self.binary(expr, owned),
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
            Expr::Perform { .. }
            | Expr::Handle { .. }
            | Expr::Closing { .. }
            | Expr::Nursery { .. }
            | Expr::Fiber { .. }
            | Expr::Cancel { .. }
            | Expr::Mask { .. } => self.effectful(expr, owned),
            Expr::Resume { .. } => self.resumed(expr, owned),
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
            Expr::Dup { .. } | Expr::Drop { .. } | Expr::Reclaim { .. } | Expr::Discard { .. } => {
                expr
            }
        }
    }

    /// Арифметика и сравнение (§4.3): два подвыражения, узел прежний.
    ///
    /// Считать в самом узле нечего - оба аргумента плоские, а ответ либо
    /// плоский, либо непосредственный конструктор `Bool`, - но подвыражения
    /// вправе называть связывания, и порядок их тот же, что у всех:
    /// [`Pass::sequence`] решает, кто из двух потребляет.
    fn binary(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        let (op, ty, left, right, verdict) = match expr {
            Expr::Primitive {
                op,
                ty,
                left,
                right,
            } => (Some(op), ty, *left, *right, None),
            Expr::Compare {
                op,
                ty,
                left,
                right,
                yes,
                no,
            } => (None, ty, *left, *right, Some((op, yes, no))),
            other => return other,
        };
        let (mut parts, spare) = self.sequence(vec![left, right], owned);
        let right = Box::new(parts.pop().unwrap_or(Expr::Erased));
        let left = Box::new(parts.pop().unwrap_or(Expr::Erased));
        let rebuilt = match (op, verdict) {
            (_, Some((op, yes, no))) => Expr::Compare {
                op,
                ty,
                left,
                right,
                yes,
                no,
            },
            (Some(op), None) => Expr::Primitive {
                op,
                ty,
                left,
                right,
            },
            (None, None) => unreachable!("узел не арифметика и не сравнение"),
        };
        drops(spare, rebuilt)
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
    /// Операция над вектором (§4.9).
    ///
    /// Счётчика нет ни у одного участника: вектор плоский, дорожка плоская,
    /// номер плоский. Поэтому вся работа прохода здесь - порядок подвыражений
    /// ([`Pass::sequence`]), ровно как у [`Pass::binary`]: ни `dup`, ни `drop`
    /// по вектору не эмитится, и это наблюдаемо счётчиком пар.
    fn vector(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        /// Какая из четырёх операций разобрана.
        enum Shape {
            Splat,
            Set,
            Lane,
            Arith(adamas_core::prim::PrimOp),
        }
        let (shape, lanes, lane, parts) = match expr {
            Expr::SimdSplat { lanes, lane, value } => (Shape::Splat, lanes, lane, vec![*value]),
            Expr::SimdSet {
                lanes,
                lane,
                vector,
                at,
                value,
            } => (Shape::Set, lanes, lane, vec![*vector, *at, *value]),
            Expr::SimdLane {
                lanes,
                lane,
                vector,
                at,
            } => (Shape::Lane, lanes, lane, vec![*vector, *at]),
            Expr::SimdArith {
                op,
                lanes,
                lane,
                left,
                right,
            } => (Shape::Arith(op), lanes, lane, vec![*left, *right]),
            other => return other,
        };
        let (mut done, spare) = self.sequence(parts, owned);
        let mut next = || Box::new(done.remove(0));
        let rebuilt = match shape {
            Shape::Splat => Expr::SimdSplat {
                lanes,
                lane,
                value: next(),
            },
            Shape::Set => Expr::SimdSet {
                lanes,
                lane,
                vector: next(),
                at: next(),
                value: next(),
            },
            Shape::Lane => Expr::SimdLane {
                lanes,
                lane,
                vector: next(),
                at: next(),
            },
            Shape::Arith(op) => Expr::SimdArith {
                op,
                lanes,
                lane,
                left: next(),
                right: next(),
            },
        };
        drops(spare, rebuilt)
    }

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
        // Плоское чтение с локала-невладельца **заимствует** (§10 вопрос 171):
        // наружу уходят биты без заголовка, а сам массив потребит его владелец
        // - позже по порядку исполнения, иначе владение было бы здесь. Ни
        // `dup` перед чтением, ни дропа внутри: пара записей счётчика на
        // каждой ячейке стоила 178.6 мс из 228.8 на колонном проходе и
        // отнимала у gcc векторизацию - зависимость «запись - чтение» через
        // одно поле заголовка сериализовала виток. Замер пробной правкой:
        // 224 -> 91 мс, ответ тот же.
        //
        // Локал, которым владеет **это** место (последнее употребление), и
        // составной операнд (своя временная ссылка) идут прежним владеющим
        // путём: заимствовать там не у кого. Указательный массив тоже - его
        // чтение дублирует ячейку, и это другой узел по построению.
        let expr = match expr {
            Expr::ArrayIndex {
                stride,
                owned: _,
                array,
                at,
            } if stride.is_some()
                && matches!(&*array, Expr::Local(local) if !owned.contains(local)) =>
            {
                let (mut done, spare) = self.sequence(vec![*at], owned);
                let at = Box::new(done.pop().unwrap_or(Expr::Erased));
                return drops(
                    spare,
                    Expr::ArrayIndex {
                        stride,
                        owned: false,
                        array,
                        at,
                    },
                );
            }
            other => other,
        };
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
            Expr::ArrayIndex {
                stride, array, at, ..
            } => (Shape::Index, stride, vec![*array, *at]),
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
                    owned: true,
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
        /// Какая из шести операций разобрана.
        enum Shape {
            Alloc,
            Last,
            Read,
            Write,
            Recycle,
            Pop,
        }
        let word = Stride::Static(PrimTy::UInt64);
        let (shape, stride, parts) = match expr {
            Expr::RegionAlloc {
                stride,
                region,
                value,
            } => (Shape::Alloc, stride, vec![*region, *value]),
            Expr::RegionLast { region } => (Shape::Last, word, vec![*region]),
            Expr::RegionRead { stride, region, at } => (Shape::Read, stride, vec![*region, *at]),
            Expr::RegionWrite {
                stride,
                region,
                at,
                value,
            } => (Shape::Write, stride, vec![*region, *at, *value]),
            // Нагрузки у возврата ячейки нет вовсе: шаг здесь - заглушка,
            // которую не читает ни одна из двух ветвей ниже.
            Expr::RegionRecycle { region, at } => (Shape::Recycle, word, vec![*region, *at]),
            Expr::RegionPop { region, at } => (Shape::Pop, word, vec![*region, *at]),
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
            Shape::Recycle => {
                let at = next();
                Expr::RegionRecycle { region: next(), at }
            }
            Shape::Pop => {
                let at = next();
                Expr::RegionPop { region: next(), at }
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
        // Владельца каждого связывания выбирает не последнее упоминание, а
        // **голое** - `Expr::Local` целой частью (§10 вопрос 171). Голую часть
        // потребляет сам узел, и потребляет **после** вычисления всех частей:
        // вызов забирает аргументы собранными, `arraySet` спрашивает
        // уникальность после значения, конструктор кладёт поля готовыми.
        // Позже голой части не исполняется ничего, поэтому владение у неё
        // законно при любых дальнейших упоминаниях - те возьмут `dup`, как
        // брала прежде она сама, счёт ссылок не меняется. Меняется одно:
        // плоское чтение с невладеющего локала становится заимствованием
        // ([`Pass::array`]), и в витке `x[i] := x[i]·g + b` не остаётся ни
        // одной записи счётчика.
        let mut mine: Vec<BTreeSet<LocalId>> = vec![BTreeSet::new(); uses.len()];
        let mut spare = Vec::new();
        for local in owned.iter().copied() {
            let bare = items
                .iter()
                .rposition(|item| matches!(item, Expr::Local(it) if *it == local));
            let holder = bare.or_else(|| uses.iter().rposition(|used| used.contains(&local)));
            match holder {
                Some(at) => {
                    mine[at].insert(local);
                }
                None => spare.push(local),
            }
        }
        let mut done = Vec::with_capacity(items.len());
        for (at, item) in items.into_iter().enumerate() {
            done.push(self.expr(item, &mine[at]));
        }
        (done, spare)
    }

    /// Хендлер и операция: владение по ним то же, что у прямого вызова.
    ///
    /// Аргументы операции уходят ветке владением, среда хендлера - кадру, и
    /// порядок подвыражений значим: среда ложится в кадр **до** того, как под
    /// ним считается вычисление. Хоронить её во временные связывания нельзя -
    /// кадра тогда ещё нет, - поэтому здесь тот же [`Pass::sequence`], что у
    /// конструктора, и ничего сверх него.
    fn effectful(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        match expr {
            Expr::Perform {
                label,
                operation,
                arguments,
            } => {
                let (arguments, spare) = self.sequence(arguments, owned);
                drops(
                    spare,
                    Expr::Perform {
                        label,
                        operation,
                        arguments,
                    },
                )
            }
            Expr::Handle {
                handler,
                captured,
                computation,
            } => {
                let mut items = captured;
                items.push(*computation);
                let (mut items, spare) = self.sequence(items, owned);
                let computation = items.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Handle {
                        handler,
                        captured: items,
                        computation: Box::new(computation),
                    },
                )
            }
            Expr::Closing {
                closer,
                captured,
                body,
            } => {
                // Среда деструктора считается **до** тела: кадр стоит всё
                // время, пока тело идёт, и владение ею переходит кадру.
                let mut items = captured;
                items.push(*body);
                let (mut items, spare) = self.sequence(items, owned);
                let body = items.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Closing {
                        closer,
                        captured: items,
                        body: Box::new(body),
                    },
                )
            }
            // У маски подвыражение одно, и владение по нему сквозное: вектор
            // ей строит рантайм, а значений маска не потребляет ни одного.
            Expr::Mask { label, computation } => {
                let (mut items, spare) = self.sequence(vec![*computation], owned);
                let computation = items.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Mask {
                        label,
                        computation: Box::new(computation),
                    },
                )
            }
            other => self.fibered(other, owned),
        }
    }

    /// Питомник и его операции (§5.2): владение то же, что у прочих эффектных.
    ///
    /// Тело круга уходит ему владением - применит его к единице он сам;
    /// аргументы операции уходят владением ветке либо кругу; отмена берёт
    /// разбираемое владением и им же отвечает - значение пережидает раскрутку в
    /// кадре и выходит обратно.
    fn fibered(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        match expr {
            Expr::Fiber {
                op,
                label,
                operation,
                arguments,
            } => {
                let (arguments, spare) = self.sequence(arguments, owned);
                drops(
                    spare,
                    Expr::Fiber {
                        op,
                        label,
                        operation,
                        arguments,
                    },
                )
            }
            Expr::Nursery { body } => {
                let (mut items, spare) = self.sequence(vec![*body], owned);
                let body = items.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Nursery {
                        body: Box::new(body),
                    },
                )
            }
            Expr::Cancel { at, value } => {
                let (mut items, spare) = self.sequence(vec![*value], owned);
                let value = items.pop().unwrap_or(Expr::Erased);
                drops(
                    spare,
                    Expr::Cancel {
                        at,
                        value: Box::new(value),
                    },
                )
            }
            other => other,
        }
    }

    /// Возобновление потребляет обе стороны: резумпцию - потому что она аффинна
    /// и второго вызова не имеет, значение - потому что уходит возобновлённому
    /// вычислению владением.
    fn resumed(&mut self, expr: Expr, owned: &BTreeSet<LocalId>) -> Expr {
        let Expr::Resume { resumption, value } = expr else {
            return expr;
        };
        let (mut parts, spare) = self.sequence(vec![*resumption, *value], owned);
        let value = parts.pop().unwrap_or(Expr::Erased);
        let resumption = parts.pop().unwrap_or(Expr::Erased);
        drops(
            spare,
            Expr::Resume {
                resumption: Box::new(resumption),
                value: Box::new(value),
            },
        )
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
                    salvage: Salvage::default(),
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
        let counted = || {
            fields
                .iter()
                .filter(|field| field.fact.present && field.fact.repr.counted())
        };
        let kept: Vec<LocalId> = counted()
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

        // Пара «`dup` поля, потом дроп родителя» схлопывается, если родитель
        // достаётся этой ветви и хоть одно поле она берёт ([`Salvage`]).
        let collapsing = ours && !kept.is_empty() && self.covered(constructor, &fields);
        let salvage = if collapsing {
            Salvage {
                taken: kept.clone(),
                spare: counted()
                    .filter(|field| !called.contains(&field.local))
                    .map(|field| field.local)
                    .collect(),
            }
        } else {
            Salvage::default()
        };
        if ours {
            let slots = self.shape(constructor);
            let cell = (slots > 0 && self.plans(&body, slots)).then(|| self.fresh());
            body = match cell {
                Some(cell) => {
                    self.attach(&mut body, slots, cell);
                    Expr::Reclaim {
                        local: subject,
                        token: cell,
                        salvage,
                        body: Box::new(body),
                    }
                }
                None => Expr::Drop {
                    local: subject,
                    salvage,
                    body: Box::new(body),
                },
            };
        }
        // `dup` полей ставится снаружи дропа разобранного: иначе дроп унёс бы их
        // с собой. Схлопнутый дроп берёт их себе, и второй раз их дупать нечем.
        if !collapsing {
            for field in kept.into_iter().rev() {
                body = Expr::Dup {
                    local: field,
                    body: Box::new(body),
                };
            }
        }
        Arm {
            constructor,
            fields,
            body,
        }
    }

    /// Видит ли ветвь каждый слот, который дропнул бы release.
    ///
    /// Схлопнутый дроп освобождает блок минуя release и потому обязан дропнуть
    /// невзятое своими силами - то есть знать его всё. Видит он только
    /// связывания ветви, а слотов у объекта бывает больше, и оба случая
    /// встречаются в корпусе.
    ///
    /// **Параметр семейства.** Ветвь его не связывает
    /// ([`Constructor::params`]), а слот он занимает: модуль-аргумент функтора
    /// доживает до рантайма записью (`tests/golden/eval/module-family.adamas`,
    /// `Counting.Put`). Такую ветвь схлопывание не берёт.
    ///
    /// **Поле не счётное и не примитивное.** Release решает по сорту слота
    /// (`release.c`), и этот счёт расходится с [`Repr::counted`] на плотном
    /// агрегате и дескрипторе укладки: там оба ответа «дропать», а счётчика
    /// нет. Расхождение принадлежит не схлопыванию, но полагаться на него
    /// схлопывание не вправе.
    fn covered(&self, constructor: CtorId, fields: &[Binding]) -> bool {
        let Some(described) = self.constructors.get(usize::from(constructor.0)) else {
            return false;
        };
        let params = (described.params as usize).min(described.binders.len());
        if described.binders[..params].iter().any(|fact| fact.present) {
            return false;
        }
        fields.iter().all(|field| {
            !field.fact.present
                || field.fact.repr.counted()
                || field.fact.repr.primitive().is_some()
        })
    }

    /// Займёт ли придержанную ячейку **хоть один** путь через выражение.
    ///
    /// Раньше спрашивалось «каждый», и ветвь с односторонним построением
    /// теряла переиспользование целиком (§10 вопрос 173). Сегодня хватает
    /// одного пути: [`Pass::attach`] обходит те же узлы и ставит
    /// [`Expr::Discard`] на каждом пути, которому занять ячейку нечем, - течь
    /// закрывается им, а не отказом придержать.
    ///
    /// Консерватизм остаётся несимметричным, но сдвинулся: ложное «да» теперь
    /// опасно только тем, что [`Pass::attach`] обязан пройти **те же** узлы -
    /// разойдись они, блок остался бы висеть. Поэтому обходы пишутся парой и
    /// правятся парой; ложное «нет» по-прежнему стоит одной аллокации.
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
            Expr::Primitive { left, right, .. }
            | Expr::Compare { left, right, .. }
            | Expr::SimdArith { left, right, .. } => {
                self.plans(left, slots) || self.plans(right, slots)
            }
            Expr::Apply { callee, argument } => {
                self.plans(callee, slots) || self.plans(argument, slots)
            }
            // Точку приостановки придержанный блок не переживает: он сырой -
            // ни заголовка, ни счётчика, - а слот кадра держит **значения**.
            // Тот же консерватизм, что у хендлера и операции ниже, и цена та
            // же: одна аллокация там, где ячейка нашлась бы за кадром.
            Expr::Bind { value, body, .. } => {
                self.plans(value, slots)
                    || (!crate::split::halts(value, self.suspending) && self.plans(body, slots))
            }
            // Ветви исключают друг друга, поэтому довольно одной: остальным
            // [`Pass::attach`] поставит [`Expr::Discard`].
            Expr::Match { arms, .. } => arms.iter().any(|arm| self.plans(&arm.body, slots)),
            Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. }
            | Expr::Discard { body, .. } => self.plans(body, slots),
            // Ячейка массива под переписывание не годится: придержанный блок
            // размером в `slots` полей, а массив - в свою длину.
            Expr::ArrayNew { count, initial, .. } => {
                self.plans(count, slots) || self.plans(initial, slots)
            }
            Expr::ArraySet {
                array, at, value, ..
            } => self.plans(array, slots) || self.plans(at, slots) || self.plans(value, slots),
            Expr::ArrayIndex { array, at, .. } => self.plans(array, slots) || self.plans(at, slots),
            // Вектор (§4.9) ячейки не занимает - он плоский и живёт в регистре,
            // - но подвыражения его обходятся тем же правилом, каким их обходит
            // арифметика: под ними стоит `Bind`, а под ним что угодно.
            Expr::SimdSplat { value, .. } => self.plans(value, slots),
            Expr::SimdLane { vector, at, .. } => {
                self.plans(vector, slots) || self.plans(at, slots)
            }
            Expr::SimdSet {
                vector, at, value, ..
            } => self.plans(vector, slots) || self.plans(at, slots) || self.plans(value, slots),
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
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. }
            // Хендлер и операция ячейку не придерживают, и это осознанный
            // консерватизм: путь через ветку понижению отсюда не виден - её
            // тело своя функция, - а ложное «да» вернуло бы течь.
            // Выход из scope - тот же консерватизм: тело его вправе оборваться
            // обрывом в полёте, и обещанная ячейка осталась бы висеть.
            | Expr::Closing { .. }
            | Expr::Handle { .. }
            | Expr::Perform { .. }
            | Expr::Resume { .. }
            | Expr::Mask { .. }
            | Expr::Nursery { .. }
            | Expr::Fiber { .. }
            | Expr::Cancel { .. }
            | Expr::Layout { .. } => false,
        }
    }

    /// Ветви разбора: занимающей уходит ячейка, незанимающей - её возврат.
    ///
    /// Без возврата блок висел бы на всяком пути, кроме занимающего, - и
    /// потому [`Pass::plans`] до закрытия вопроса 173 требовал занятости от
    /// **каждого** пути, то есть терял переиспользование на всей ветви разом.
    /// Возврат снимает требование, оставляя его цену на одном пути из двух.
    fn branches(&self, arms: &mut [Arm], slots: usize, token: LocalId) -> bool {
        if !arms.iter().any(|arm| self.plans(&arm.body, slots)) {
            return false;
        }
        for arm in arms {
            if self.plans(&arm.body, slots) {
                self.attach(&mut arm.body, slots, token);
            } else {
                let body = std::mem::replace(&mut arm.body, Expr::Erased);
                arm.body = Expr::Discard {
                    token,
                    body: Box::new(body),
                };
            }
        }
        true
    }

    /// Раздаёт ячейку тем же обходом, каким [`Pass::plans`] её обещал.
    ///
    /// Договор ровно один и он сильнее, чем «где-то поставил»: вернув `true`,
    /// обход обязан оставить выражение таким, что **всякий** путь через него
    /// либо занимает ячейку под конструктор, либо отдаёт её [`Expr::Discard`].
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
            Expr::Primitive { left, right, .. }
            | Expr::Compare { left, right, .. }
            | Expr::SimdArith { left, right, .. } => {
                self.attach(left, slots, token) || self.attach(right, slots, token)
            }
            Expr::Apply { callee, argument } => {
                self.attach(callee, slots, token) || self.attach(argument, slots, token)
            }
            // Обход тот же, что у [`Pass::plans`], и граница та же.
            Expr::Bind { value, body, .. } => {
                self.attach(value, slots, token)
                    || (!crate::split::halts(value, self.suspending)
                        && self.attach(body, slots, token))
            }
            Expr::Match { arms, .. } => self.branches(arms, slots, token),
            Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. }
            | Expr::Discard { body, .. } => self.attach(body, slots, token),
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
            // Обход тот же, что у [`Pass::plans`] выше, и по тому же доводу.
            Expr::SimdSplat { value, .. } => self.attach(value, slots, token),
            Expr::SimdLane { vector, at, .. } => {
                self.attach(vector, slots, token) || self.attach(at, slots, token)
            }
            Expr::SimdSet {
                vector, at, value, ..
            } => {
                self.attach(vector, slots, token)
                    || self.attach(at, slots, token)
                    || self.attach(value, slots, token)
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
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. }
            // Обход тот же, что у [`Pass::plans`], и отвечает он то же.
            // Выход из scope - тот же консерватизм: тело его вправе оборваться
            // обрывом в полёте, и обещанная ячейка осталась бы висеть.
            | Expr::Closing { .. }
            | Expr::Handle { .. }
            | Expr::Perform { .. }
            | Expr::Resume { .. }
            | Expr::Mask { .. }
            | Expr::Nursery { .. }
            | Expr::Fiber { .. }
            | Expr::Cancel { .. }
            | Expr::Layout { .. } => false,
        }
    }
}
