//! Уникальность производства: кто заполняет
//! [`Fact::unique`](crate::ir::Fact::unique) (§9 Фаза 7, трек B; §10 вопрос
//! 149).
//!
//! # Из кратности - никогда
//!
//! Вопрос 149 закрыт замером, и замер отрицательный: `both : (1 x : Two) ->
//! (1 y : Two) -> Two`, позванная как `both shared shared`, принимается и
//! считается. Кратность ограничивает, сколько раз связывание употребит
//! **вызываемый**, и про то, указывают ли два связывания на один объект, не
//! говорит ничего. Прежнее `Certain` по кратности `1` было ложью, которую никто
//! не читал; читать её начал бы этот проход, и поэтому оно снято раньше.
//!
//! Законных источника вопрос 149 назвал два, и оба про **производство**:
//! значения `unique data`/`resource` (§3.3 - ω-значений такого типа не
//! существует) и локально свежие объекты. Взят второй.
//!
//! Свежий объект - тот, что только что выдал `adamas_alloc` либо переписал
//! `adamas_reuse`: `rc == 0` по тексту рантайма (`object.c`), и ссылка на него
//! ровно одна - та, которую держит связывание.
//!
//! **Первый источник отсюда недоступен, и это не выбор.** Таблица владения
//! живёт в `adamas-elab` (`own.rs`) по явному решению «ядро о `unique data` не
//! знает и знать не обязано»; в сигнатуре ядра её нет, и до понижения маркер не
//! доезжает. Достать его - значит либо класть владение в ядро, либо тянуть
//! таблицу параметром через все точки входа компиляции, и то и другое шире
//! этого прохода. Мерить потерю не понадобилось: на `resource-cleanup` факт
//! достался деструкторам `closeNote` и `closeTag` **вторым** источником, потому
//! что их аргумент всюду - свежий `Written`/`Marked`.
//!
//! # Почему `rc` больше не растёт, и чем это проверяется
//!
//! Счётчик поднимает **только** `adamas_dup` - других мест в `object.c` нет.
//! Значит достаточно убедиться, что `dup`'а на это связывание в программе не
//! стоит. Отсюда весь проход: он не доказывает уникальность анализом кучи, он
//! проверяет отсутствие единственной операции, которая её ломает.
//!
//! Второй способ получить вторую ссылку - второе **имя** на тот же объект.
//! Вставка RC (`crate::perceus`) его не заводит: употребить связывание дважды
//! без `dup` она не даёт. Но `let y = x` в IR выразимо, и такое `x` проход
//! отвергает наравне с дуплицированным - довод один и тот же.
//!
//! # Свежесть переносится через вызов, и это не расширение источника
//!
//! Параметр функции - то же производство, увиденное с другой стороны: если
//! **каждое** место вызова кладёт в позицию свежий объект, то на входе `rc == 0`
//! ровно так же, как у конструктора на месте.
//!
//! Перенос обязателен, а не приятен, и это считано по корпусу до самого
//! прохода: из двадцати восьми мест, где спрашивался `adamas_is_unique` на
//! двадцати одной программе LLVM-пути, двадцать семь спрашивают
//! про **параметр**, одно - про результат вызова, и **ни одного** - про
//! локально построенный объект. Свежий объект уходит аргументом, и разбирает
//! его вызываемый; без переноса факт не достался бы ни одной программе. Отсюда
//! и то, что проход пишет [`Fact::unique`](crate::ir::Fact::unique) только у
//! параметров: у связывания `let` его читать было бы некому.
//!
//! Двадцать восьмое место - результат вызова - взял бы третий источник:
//! функция, **всякий** выход которой свеж. Он законен и не заведён: одно место
//! на корпусе цены прохода не оправдывает, и мерить там нечего.
//!
//! Перенос законен только там, где места вызова видны все. Функция, чей номер
//! попал в замыкание, в ветку хендлера, в деструктор scope'а или в точку входа,
//! зовётся мимо [`Expr::Call`] - её параметры проход не судит вовсе.
//!
//! # Нульарный конструктор свежим не считается
//!
//! `adamas_con0` отдаёт **непосредственное** значение с тегом в младшем бите, а
//! `adamas_is_unique` на непосредственном отвечает ложью. Объяви такое значение
//! уникальным - и статическая ветвь разошлась бы с рантаймом в обратную
//! сторону. Поэтому свежим считается конструктор со слотами, а нульарный - нет.
//!
//! # Что факт даёт и чего не даёт
//!
//! Даёт: [`crate::emit_llvm`] перестаёт спрашивать `adamas_is_unique` там, где
//! ответ известен, и ветвь разделённого не печатается вовсе. Измерено на трёх
//! программах корпуса, штатный конвейер. `resource-cleanup`: вызовов рантайма
//! после `-O2` 61 против 55, инструкций 321 против 301. `case-over-a-computation`:
//! 19 против 15 и 92 против 80. `nested-case-on-a-field`: 12 против 9 и 60
//! против 49.
//!
//! **Не даёт: счётчика выданных блоков.** Он не меняется ни на одной программе
//! корпуса, и это не недоработка прохода, а свойство величины: число выданных
//! блоков - наблюдаемое состояние, которое рантайм пишет на пути аллокации, а
//! решение «переписать или выдать» принимает `rc == 0` в рантайме и принимает
//! его **верно**. Статический факт снимает цену вопроса, а не меняет ответ.
//! Свидетель - `tests/alias.rs`.
//!
//! Метаданных алиасинга от факта тоже не появляется. `noalias` и
//! `dereferenceable` на `Certain`-параметре законны, но первый даёт ноль
//! инструкций, а второй верен лишь потому, что `Certain` исключает
//! непосредственное значение, - и тоже даёт ноль. Мерено там же.

use std::collections::{HashMap, HashSet};

use crate::ir::{Expr, FuncId, LocalId, Program, Unique};

/// Заполняет [`Fact::unique`](crate::ir::Fact::unique) у параметров.
///
/// Стоит **после** вставки RC (`crate::perceus`): узлы [`Expr::Dup`], по
/// отсутствию которых проход и судит, ставит она.
#[must_use]
pub fn infer(mut program: Program) -> Program {
    let seen = Sites::of(&program);
    let mut certain: Vec<Vec<bool>> = program
        .functions
        .iter()
        .map(|function| {
            let judged = !seen.escaping.contains(&function.id);
            function
                .parameters
                .iter()
                .map(|binding| {
                    judged
                        && binding.fact.present
                        && binding.fact.repr.pointer()
                        && seen.intact(function.id, binding.local)
                })
                .collect()
        })
        .collect();

    // Убывающая неподвижная точка: начинаем с «все свежи» и снимаем тех, кому
    // хоть одно место вызова кладёт несвежее. Направление именно это, потому
    // что рекурсивный вызов иначе доказывал бы свежесть сам собой.
    let mut settled = false;
    while !settled {
        settled = true;
        for site in &seen.calls {
            for (at, argument) in site.arguments.iter().enumerate() {
                let judged = certain
                    .get(site.callee.0)
                    .and_then(|row| row.get(at).copied())
                    .unwrap_or(false);
                if !judged || fresh(argument, site.caller, &seen, &certain) {
                    continue;
                }
                certain[site.callee.0][at] = false;
                settled = false;
            }
        }
    }

    for (function, row) in program.functions.iter_mut().zip(&certain) {
        for (binding, &flag) in function.parameters.iter_mut().zip(row) {
            if flag {
                binding.fact.unique = Unique::Certain;
            }
        }
    }
    program
}

/// Свежо ли то, что место вызова кладёт в позицию.
fn fresh(argument: &Expr, caller: FuncId, seen: &Sites<'_>, certain: &[Vec<bool>]) -> bool {
    match argument {
        Expr::Construct { constructor, .. } => seen.slotted.contains(constructor.0.into()),
        Expr::Local(local) => {
            if !seen.intact(caller, *local) {
                return false;
            }
            if seen.made.contains(&(caller, *local)) {
                return true;
            }
            seen.positions
                .get(&(caller, *local))
                .and_then(|&at| certain.get(caller.0)?.get(at).copied())
                .unwrap_or(false)
        }
        _ => false,
    }
}

/// Одно место вызова: кто зовёт, кого и с чем.
struct Site<'a> {
    caller: FuncId,
    callee: FuncId,
    arguments: &'a [Expr],
}

/// Что проход вычитал из программы за один обход.
struct Sites<'a> {
    /// Функции, чьи параметры судить нельзя: их зовут мимо [`Expr::Call`].
    escaping: HashSet<FuncId>,
    /// Связывания, чьё значение - конструктор со слотами.
    made: HashSet<(FuncId, LocalId)>,
    /// Связывания, про которые свежесть утверждать нельзя: на них стоит `dup`,
    /// либо они второе имя чужого объекта, либо их значение не конструктор.
    broken: HashSet<(FuncId, LocalId)>,
    /// Позиция параметра в своей функции.
    positions: HashMap<(FuncId, LocalId), usize>,
    /// Теги конструкторов, у которых есть хоть один живой слот.
    slotted: SlottedTags,
    /// Места вызова.
    calls: Vec<Site<'a>>,
}

/// Теги конструкторов со слотами - битовым набором по номеру.
struct SlottedTags(Vec<bool>);

impl SlottedTags {
    fn contains(&self, tag: usize) -> bool {
        self.0.get(tag).copied().unwrap_or(false)
    }
}

impl<'a> Sites<'a> {
    /// Цело ли связывание: ни `dup`, ни второго имени.
    fn intact(&self, function: FuncId, local: LocalId) -> bool {
        !self.broken.contains(&(function, local))
    }

    fn of(program: &'a Program) -> Self {
        let mut seen = Self {
            escaping: HashSet::from([program.entry]),
            made: HashSet::new(),
            broken: HashSet::new(),
            positions: HashMap::new(),
            slotted: SlottedTags(
                program
                    .constructors
                    .iter()
                    .map(|described| described.slots() > 0)
                    .collect(),
            ),
            calls: Vec::new(),
        };
        for handler in &program.handlers {
            seen.escaping.insert(handler.returned);
            for branch in &handler.branches {
                seen.escaping.insert(branch.function);
            }
        }
        for function in &program.functions {
            for (at, binding) in function.parameters.iter().enumerate() {
                seen.positions.insert((function.id, binding.local), at);
            }
            seen.read(function.id, &function.body);
        }
        seen
    }

    /// Обходит тело, собирая всё сразу: одним проходом, а не четырьмя.
    fn read(&mut self, function: FuncId, expr: &'a Expr) {
        match expr {
            Expr::Bind { binding, value, .. } => match &**value {
                Expr::Construct { constructor, .. }
                    if self.slotted.contains(constructor.0.into()) =>
                {
                    self.made.insert((function, binding.local));
                }
                // Всё прочее связывание - несвежее, и помечается им же, а не
                // просто не помечается свежим. Разница видна там, где один
                // номер связан дважды - в двух ветвях: одна половина попала бы
                // в свежие, а вторая осталась бы неучтённой. Пометка их сводит:
                // `intact` перевешивает `made`.
                Expr::Local(named) => {
                    // Второе имя на тот же объект: ссылок становится две, и
                    // дальше `dup` может стоять на любом из них.
                    self.broken.insert((function, *named));
                    self.broken.insert((function, binding.local));
                }
                _ => {
                    self.broken.insert((function, binding.local));
                }
            },
            Expr::Dup { local, .. } => {
                self.broken.insert((function, *local));
            }
            Expr::Call {
                function: callee,
                arguments,
            } => self.calls.push(Site {
                caller: function,
                callee: *callee,
                arguments,
            }),
            Expr::Closure { function: code, .. } => {
                self.escaping.insert(*code);
            }
            Expr::Closing { closer, .. } => {
                self.escaping.insert(*closer);
            }
            _ => {}
        }
        for child in expr.children() {
            self.read(function, child);
        }
    }
}
