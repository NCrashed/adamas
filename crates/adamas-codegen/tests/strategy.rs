//! Три базовые стратегии §3.6 над native malloc: Arena, Pool, `StackAlloc`.
//!
//! Утверждений здесь четыре, и каждое - прогон, а не текст.
//!
//! - *Стратегии различимы поведением, а не именем.* Тело пробы одно, слово в
//!   слово, и подставляется в него только имя модуля
//!   ([`three_strategies_answer_three_different_ways`]). Три ответа выходят
//!   попарно разными, и каждый по дороге сверен с `adamas eval`.
//! - *Каждая обещает своё, и обещание проверено.* Arena - подъём курсора и
//!   освобождение области целиком ([`an_arena_never_hands_a_cell_back`]); Pool -
//!   переиспользование ячеек **равного размера**
//!   ([`a_pool_reuses_only_cells_of_the_same_size`]); `StackAlloc` - LIFO, то есть
//!   возврат **только с вершины** ([`a_stack_gives_back_the_top_only`]).
//! - *Стандартный набор доходит до C.* Всякий прогон здесь компилируется
//!   настоящим компилятором, линкуется с рантаймом и запускается; ответ его
//!   обязан сойтись с интерпретатором, а живых блоков остаться ноль.
//! - *Пользовательская стратегия принимается языком и отвергается понижением
//!   названной причиной* ([`a_handled_strategy_is_refused_by_name`]) - решение
//!   §10 вопроса 161. Ближайший проходящий сосед стоит рядом: тот же набор
//!   стратегий, написанный без эффектов.
//!
//! Числа в ответе - **хендлы**, а не значения по ним. Это существенно: хендл,
//! посчитанный не по правилу, ведёт себя как ключ - пишут и читают по нему
//! одним выражением, и ошибка сокращается. Тот же довод завёл
//! `adamas-runtime/tests/region.rs`, где видны уже адреса.

mod harness;

/// Общее начало: класс представления, `Unit` и три стратегии одной сигнатурой.
///
/// Аннотация `:`, а не `:>`, и это названная граница, а не небрежность:
/// запечатанный член специализации не получает (`adamas-elab/src/mono.rs`), а
/// без неё обобщённый по нагрузке `store` понижением не берётся. Запечатанный
/// вариант считает интерпретатор - `eval/region-strategy-in-io`.
const SHAPE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

data Unit where
  MkUnit : Unit

data Pair where
  MkPair : Ptr -> Ptr -> Pair

module type AllocStrategy where
  type Block
  new   : Unit -> Block
  store : {Flat a} => Block -> a -> Block
  here  : Block -> Ptr
  load  : {Flat a} => Block -> Ptr -> a
  free  : Block -> Ptr -> Block

module Arena : AllocStrategy where
  type Block = Block
  new : Unit -> Block
  new u = regionNew
  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x
  here : Block -> Ptr
  here r = regionLast r
  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p
  free : Block -> Ptr -> Block
  free r p = r

module Pool : AllocStrategy where
  type Block = Block
  new : Unit -> Block
  new u = regionNew
  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x
  here : Block -> Ptr
  here r = regionLast r
  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p
  free : Block -> Ptr -> Block
  free r p = regionRecycle r p

module StackAlloc : AllocStrategy where
  type Block = Block
  new : Unit -> Block
  new u = regionNew
  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x
  here : Block -> Ptr
  here r = regionLast r
  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p
  free : Block -> Ptr -> Block
  free r p = regionPop r p
";

/// Все три стратегии.
const STRATEGIES: [&str; 3] = ["Arena", "Pool", "StackAlloc"];

/// Проба, различающая всех троих сразу.
///
/// Возврат случается дважды. Первый - **не с вершины**: отдаётся ячейка `a`,
/// когда последней лежит `b`. Только Pool умеет отдавать из середины, поэтому
/// первый хендл различает его. Второй - **с вершины**: у Arena курсор всё равно
/// не опускается, у `StackAlloc` опускается, - и второй хендл различает Arena.
///
/// Меньшего не хватило бы: с одним возвратом Pool и `StackAlloc` отвечают
/// одинаково, и трёх разных ответов не выходит.
const PROBE: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let c : Int64 = 4
  let d : Int64 = 8
  let r0 : S.Block = S.new MkUnit
  let r1 : S.Block = S.store r0 a
  let h1 : Ptr = S.here r1
  let r2 : S.Block = S.store r1 b
  let r3 : S.Block = S.free r2 h1
  let r4 : S.Block = S.store r3 c
  let h3 : Ptr = S.here r4
  let r5 : S.Block = S.free r4 h3
  let r6 : S.Block = S.store r5 d
  let h4 : Ptr = S.here r6
  MkPair h3 h4
";

/// Тело с подставленной стратегией. Подстановка одна на все три - иначе
/// «одна и та же программа» держалось бы на глазах читателя.
fn with_strategy(body: &str, strategy: &str) -> String {
    format!("{SHAPE}{}", body.replace("S.", &format!("{strategy}.")))
}

/// Ответ прогона на C вместе с числом выданных блоков.
///
/// Ответ по дороге сверяется с `adamas eval` ([`harness::agreed`]), а живых
/// блоков после прогона обязан остаться ноль.
fn run(name: &str, source: &str) -> (String, usize) {
    let answer = harness::printed(source);
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    (answer, allocated)
}

/// Три стратегии, одно тело, три разных ответа.
///
/// Это критерий различимости целиком: программа, чей ответ зависит от того,
/// какая стратегия подставлена. Три одинаковых числа свидетелем не были бы.
#[test]
fn three_strategies_answer_three_different_ways() {
    let mut answers = Vec::new();
    for strategy in STRATEGIES {
        let (answer, allocated) = run(strategy, &with_strategy(PROBE, strategy));
        // Область - один блок, пара ответа - второй. Число одно на все три:
        // цена стратегии в блоках не меняется, меняются хендлы.
        assert_eq!(
            allocated, 2,
            "{strategy}: область и пара ответа - два блока, выдано {allocated}"
        );
        answers.push((strategy, answer));
    }
    assert_eq!(
        answers[0].1, "MkPair 16 24",
        "Arena: курсор обязан идти вверх все четыре раза"
    );
    assert_eq!(
        answers[1].1, "MkPair 0 0",
        "Pool: отданная ячейка обязана достаться следующей нагрузке того же размера"
    );
    assert_eq!(
        answers[2].1, "MkPair 16 16",
        "StackAlloc: возврат не с вершины пуст, возврат с вершины опускает курсор"
    );
    for (left, right) in [(0, 1), (0, 2), (1, 2)] {
        assert_ne!(
            answers[left].1, answers[right].1,
            "`{}` и `{}` ответили одинаково - различать их нечем",
            answers[left].0, answers[right].0
        );
    }
}

/// Arena: подъём курсора и освобождение области целиком.
///
/// Обещание §3.6 из двух половин, и обе - числом. *Ячейка обратно не берётся*:
/// шесть значений с возвратом после каждого дают хендл шестой аллокации `40`,
/// то есть курсор шёл вверх всякий раз. *Освобождение одно на всю область*: те
/// же шесть значений стоят **один** блок, и после прогона живых ноль.
const ARENA_BUMPS: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let r0 : Arena.Block = Arena.new MkUnit
  let r1 : Arena.Block = Arena.store r0 a
  let h1 : Ptr = Arena.here r1
  let r2 : Arena.Block = Arena.free r1 h1
  let r3 : Arena.Block = Arena.store r2 a
  let r4 : Arena.Block = Arena.free r3 (Arena.here r3)
  let r5 : Arena.Block = Arena.store r4 a
  let r6 : Arena.Block = Arena.free r5 (Arena.here r5)
  let r7 : Arena.Block = Arena.store r6 a
  let r8 : Arena.Block = Arena.free r7 (Arena.here r7)
  let r9 : Arena.Block = Arena.store r8 a
  let rA : Arena.Block = Arena.free r9 (Arena.here r9)
  let rB : Arena.Block = Arena.store rA a
  MkPair h1 (Arena.here rB)
";

/// Тот же счёт значений ячейками кучи - для сравнения цены.
const BOXED_SIX: &str = "\
data Cell where
  MkCell : Int64 -> Cell

peel : Cell -> Ptr
peel (MkCell n) = 0

main : Pair
main =
  let a : Cell = MkCell 1
  let b : Cell = MkCell 2
  let c : Cell = MkCell 4
  let d : Cell = MkCell 8
  let e : Cell = MkCell 16
  let f : Cell = MkCell 32
  MkPair (peel a) (peel f)
";

#[test]
fn an_arena_never_hands_a_cell_back() {
    let (answer, allocated) = run("арена-подъём", &format!("{SHAPE}{ARENA_BUMPS}"));
    assert_eq!(
        answer, "MkPair 0 40",
        "возврат у Arena обязан быть пуст: шестая аллокация стоит по сорока байтам"
    );
    assert_eq!(
        allocated, 2,
        "шесть значений в области - один блок, пара ответа - второй"
    );
    // Дифференциальная половина: те же шесть значений ячейками кучи.
    let (_, boxed) = run("арена-ячейки", &format!("{SHAPE}{BOXED_SIX}"));
    assert_eq!(
        boxed, 7,
        "ячейка кучи обязана стоить блок: шесть значений плюс пара ответа"
    );
}

/// Pool: ячейка достаётся нагрузке **равного** размера, и только ей.
///
/// Восьмибайтовая ячейка отдана. Следом кладётся четырёхбайтовое - ячейка ему
/// не достаётся, и хендл выходит `8`, а не `0`. Потом восьмибайтовое - и
/// достаётся, хендл `0`. Сними сверку размеров, и оба числа станут нулями.
const POOL_SIZED: &str = "\
main : Pair
main =
  let wide : Int64 = 1
  let narrow : Float32 = 0.5
  let again : Int64 = 2
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 wide
  let h1 : Ptr = Pool.here r1
  let r2 : Pool.Block = Pool.free r1 h1
  let r3 : Pool.Block = Pool.store r2 narrow
  let h2 : Ptr = Pool.here r3
  let r4 : Pool.Block = Pool.store r3 again
  let h3 : Ptr = Pool.here r4
  MkPair h2 h3
";

#[test]
fn a_pool_reuses_only_cells_of_the_same_size() {
    let (answer, allocated) = run("пул-размер", &format!("{SHAPE}{POOL_SIZED}"));
    assert_eq!(
        answer, "MkPair 8 0",
        "узкая нагрузка обязана лечь мимо отданной ячейки, а равная - в неё"
    );
    assert_eq!(allocated, 2);
}

/// Ячейка равного размера, но чужой границы, тоже не достаётся.
///
/// Сверка границ у примитива **ненаблюдаема**: у всякого из §4.11 размер равен
/// выравниванию, поэтому равный по размеру всегда и выровнен - тот же случай,
/// что у шага массива в 3б. Различающее значение появляется у **агрегата**:
/// `Quad` - шестнадцать байт по границе четыре, `Padded` - те же шестнадцать по
/// границе восемь (§4.11: граница агрегата есть максимум границ полей).
///
/// Ячейка `Quad` отводится по смещению 4 - её туда двигает `Float32` перед
/// ней, - и отдаётся. `Padded` того же размера её не берёт: 4 на восемь не
/// делится. Сними сверку границ, и хендл станет `4`, то есть `Padded` лёг бы
/// по нечётному слову.
const POOL_ALIGNED: &str = "\
type Quad = { a : Float32, b : Float32, c : Float32, d : Float32 }

type Padded = { wide : Int64, tag : Int8 }

main : Pair
main =
  let edge : Float32 = 0.5
  let quad : Quad = { a = 1.0, b = 2.0, c = 3.0, d = 4.0 }
  let padded : Padded = { wide = 7, tag = 1 }
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 edge
  let r2 : Pool.Block = Pool.store r1 quad
  let h1 : Ptr = Pool.here r2
  let r3 : Pool.Block = Pool.free r2 h1
  let r4 : Pool.Block = Pool.store r3 padded
  let h2 : Ptr = Pool.here r4
  MkPair h1 h2
";

#[test]
fn a_pool_refuses_a_cell_of_the_wrong_bound() {
    let (answer, allocated) = run("пул-граница", &format!("{SHAPE}{POOL_ALIGNED}"));
    assert_eq!(
        answer, "MkPair 4 24",
        "равный по размеру, но не по границе, обязан лечь мимо отданной ячейки"
    );
    assert_eq!(allocated, 2);
}

/// Отданная ячейка выдаётся **однажды**: вторая нагрузка идёт подъёмом.
///
/// Утверждение про безопасность, а не про экономию: выдай ячейку дважды, и два
/// живых значения легли бы в одни байты. Проба поэтому размещает после возврата
/// **дважды** - все прочие размещают по разу, и на них ошибка ненаблюдаема, что
/// и показал мутант.
const POOL_ONCE: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let c : Int64 = 4
  let d : Int64 = 8
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 a
  let h1 : Ptr = Pool.here r1
  let r2 : Pool.Block = Pool.store r1 b
  let r3 : Pool.Block = Pool.free r2 h1
  let r4 : Pool.Block = Pool.store r3 c
  let taken : Ptr = Pool.here r4
  let r5 : Pool.Block = Pool.store r4 d
  MkPair taken (Pool.here r5)
";

#[test]
fn a_recycled_cell_is_handed_out_once() {
    let (answer, allocated) = run("пул-однажды", &format!("{SHAPE}{POOL_ONCE}"));
    assert_eq!(
        answer, "MkPair 0 16",
        "вторая нагрузка обязана пойти подъёмом: занятую ячейку второй раз не выдают"
    );
    assert_eq!(allocated, 2);
}

/// Из равных по размеру берётся **самая поздняя по размещению**.
///
/// Правило деталь, но деталь наблюдаемая, и записана она в двух местах сразу -
/// в машине и в рантайме. Здесь свободных ячеек **две**, и обе подходят: обход
/// с другого конца отдал бы `0` вместо `8`.
const POOL_ORDER: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let c : Int64 = 4
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 a
  let lower : Ptr = Pool.here r1
  let r2 : Pool.Block = Pool.store r1 b
  let upper : Ptr = Pool.here r2
  let r3 : Pool.Block = Pool.free r2 lower
  let r4 : Pool.Block = Pool.free r3 upper
  let r5 : Pool.Block = Pool.store r4 c
  MkPair upper (Pool.here r5)
";

#[test]
fn a_pool_takes_the_latest_free_cell() {
    let (answer, allocated) = run("пул-порядок", &format!("{SHAPE}{POOL_ORDER}"));
    assert_eq!(
        answer, "MkPair 8 8",
        "из двух свободных равных обязана достаться поздняя по размещению"
    );
    assert_eq!(allocated, 2);
}

/// `StackAlloc`: отдаётся только вершина.
///
/// Две аллокации, возврат **нижней** - и он пуст: третья ложится за верхней,
/// хендл `16`. Следом возврат верхней, теперь настоящей вершины, - и четвёртая
/// ложится на её место, хендл тот же `16`. Разница двух возвратов и есть LIFO;
/// у Pool оба сработали бы.
const STACK_TOP: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let r0 : StackAlloc.Block = StackAlloc.new MkUnit
  let r1 : StackAlloc.Block = StackAlloc.store r0 a
  let bottom : Ptr = StackAlloc.here r1
  let r2 : StackAlloc.Block = StackAlloc.store r1 b
  let r3 : StackAlloc.Block = StackAlloc.free r2 bottom
  let r4 : StackAlloc.Block = StackAlloc.store r3 a
  let above : Ptr = StackAlloc.here r4
  let r5 : StackAlloc.Block = StackAlloc.free r4 above
  let r6 : StackAlloc.Block = StackAlloc.store r5 b
  MkPair above (StackAlloc.here r6)
";

#[test]
fn a_stack_gives_back_the_top_only() {
    let (answer, allocated) = run("стек-вершина", &format!("{SHAPE}{STACK_TOP}"));
    assert_eq!(
        answer, "MkPair 16 16",
        "возврат не с вершины обязан быть пуст, возврат с вершины - опустить курсор"
    );
    assert_eq!(allocated, 2);
}

/// После возврата вершины последней аллокацией становится предыдущая.
///
/// Хендл спрашивается **сразу после** возврата, а не после следующего
/// размещения, - и в этом весь свидетель: спроси его позже, и подъём курсора
/// поставил бы то же число сам. Правило записано дважды, в машине и в рантайме,
/// и разойдись они, сверка с `adamas eval` это покажет.
const STACK_BACK: &str = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let r0 : StackAlloc.Block = StackAlloc.new MkUnit
  let r1 : StackAlloc.Block = StackAlloc.store r0 a
  let bottom : Ptr = StackAlloc.here r1
  let r2 : StackAlloc.Block = StackAlloc.store r1 b
  let top : Ptr = StackAlloc.here r2
  let r3 : StackAlloc.Block = StackAlloc.free r2 top
  MkPair top (StackAlloc.here r3)
";

#[test]
fn a_pop_hands_the_handle_back_to_the_cell_below() {
    let (answer, allocated) = run("стек-хендл", &format!("{SHAPE}{STACK_BACK}"));
    assert_eq!(
        answer, "MkPair 8 0",
        "после возврата вершины последней аллокацией обязана стать нижняя"
    );
    assert_eq!(allocated, 2);
}

/// Возврат ячейки байт не трогает: живая нагрузка читается сквозь него.
///
/// Два чтения, и оба нужны. Первое - по хендлу **живой** ячейки, через возврат
/// соседней: возврат правит журнал, а не нагрузку, и прежнее значение обязано
/// дойти. Второе - по хендлу **переиспользованной**: там теперь новое значение,
/// и выигрывает последняя запись, а не первая.
///
/// Свидетель нашёлся мутантом: без чтения после возврата обход машины мог не
/// проходить сквозь `regionRecycle` вовсе, и корпус этого не замечал - `store`
/// с `here` до нагрузки не добираются.
const POOL_READS: &str = "\
data Seen where
  MkSeen : Int64 -> Int64 -> Seen

main : Seen
main =
  let a : Int64 = 11
  let b : Int64 = 22
  let c : Int64 = 33
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 a
  let h1 : Ptr = Pool.here r1
  let r2 : Pool.Block = Pool.store r1 b
  let h2 : Ptr = Pool.here r2
  let r3 : Pool.Block = Pool.free r2 h1
  let r4 : Pool.Block = Pool.store r3 c
  MkSeen (Pool.load r4 h2) (Pool.load r4 h1)
";

/// То же у `StackAlloc`: чтение проходит и сквозь опускание курсора.
const STACK_READS: &str = "\
data Seen where
  MkSeen : Int64 -> Int64 -> Seen

main : Seen
main =
  let a : Int64 = 11
  let b : Int64 = 22
  let c : Int64 = 33
  let r0 : StackAlloc.Block = StackAlloc.new MkUnit
  let r1 : StackAlloc.Block = StackAlloc.store r0 a
  let h1 : Ptr = StackAlloc.here r1
  let r2 : StackAlloc.Block = StackAlloc.store r1 b
  let h2 : Ptr = StackAlloc.here r2
  let r3 : StackAlloc.Block = StackAlloc.free r2 h2
  let r4 : StackAlloc.Block = StackAlloc.store r3 c
  MkSeen (StackAlloc.load r4 h1) (StackAlloc.load r4 h2)
";

#[test]
fn a_returned_cell_leaves_the_bytes_alone() {
    let (answer, allocated) = run("пул-чтение", &format!("{SHAPE}{POOL_READS}"));
    assert_eq!(
        answer, "MkSeen 22 33",
        "живая ячейка обязана дожить до чтения, а переиспользованная - отдать новое"
    );
    assert_eq!(allocated, 2);
    let (answer, allocated) = run("стек-чтение", &format!("{SHAPE}{STACK_READS}"));
    assert_eq!(answer, "MkSeen 11 33");
    assert_eq!(allocated, 2);
}

/// Пользовательская стратегия отвергается понижением названной причиной.
///
/// Форма её - решение §10 вопроса 161: интерфейс один, и различает встроенное с
/// пользовательским понижение. Здесь `Chosen` спрашивает у хендлера, что делать
/// с ячейкой, - то есть гасится хендлером, - а хендлер требует второй формы
/// понижения. Отказ обязан назвать причину, а не молча выдать что-нибудь.
///
/// Считает эту программу интерпретатор, и её ответ стоит в
/// `tests/golden/eval/region-strategy-handled.adamas`.
const HANDLED: &str = "\
data Bool where
  False : Bool
  True : Bool

effect IO where
  keep : Bool

module Chosen : AllocStrategy where
  type Block = Block
  new : Unit -> Block
  new u = regionNew
  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x
  here : Block -> Ptr
  here r = regionLast r
  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p
  free : Block -> Ptr -> Block
  free r p = r

asked : Block -> Ptr -> {IO} Block
asked r p = case keep MkUnit of
  True -> r
  False -> regionRecycle r p

probe : (ω u : Unit) -> {IO} Pair
probe u =
  let a : Int64 = 1
  let b : Int64 = 2
  let r0 : Chosen.Block = Chosen.new MkUnit
  let r1 : Chosen.Block = Chosen.store r0 a
  let h1 : Ptr = Chosen.here r1
  let r2 : Block = asked r1 h1
  let r3 : Block = Chosen.store r2 b
  MkPair h1 (Chosen.here r3)

main : Pair
main = handle probe with
  return v -> v
  keep -> resume False
";

#[test]
fn a_handled_strategy_is_refused_by_name() {
    let source = format!("{SHAPE}{HANDLED}");
    // Языком она принимается: интерфейс тот же, и машина её считает.
    assert_eq!(harness::printed(&source), "MkPair 0 0");
    let error = harness::compiled(&source).expect_err("хендлер второй формой не берётся");
    let text = error.to_string();
    assert!(
        text.contains("вторая форма понижения этим срезом не берётся"),
        "отказ не назвал причину второй формой: {text}"
    );
}

/// Ближайший проходящий сосед: та же проба встроенной стратегией.
///
/// Отличие от соседа сверху одно - решение про ячейку стоит в теле, а не в
/// хендлере, - и понижение ту же программу берёт.
#[test]
fn the_same_probe_without_a_handler_passes() {
    let source = "\
main : Pair
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let r0 : Pool.Block = Pool.new MkUnit
  let r1 : Pool.Block = Pool.store r0 a
  let h1 : Ptr = Pool.here r1
  let r2 : Pool.Block = Pool.free r1 h1
  let r3 : Pool.Block = Pool.store r2 b
  MkPair h1 (Pool.here r3)
";
    let (answer, allocated) = run("сосед-без-хендлера", &format!("{SHAPE}{source}"));
    assert_eq!(answer, "MkPair 0 0");
    assert_eq!(allocated, 2);
}
