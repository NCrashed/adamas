//! Мультишот: возобновление ставит копию сегмента (§3.4, «Стоимость multi-shot»).
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что понижение считает то же,
//! что машина, и три его фикстуры - `effects`, `multi-over-oneshot`, `fibers` -
//! написаны про язык. Здесь стоит то, чего корпус не различает.
//!
//! **Свидетель обязан быть асимметричен.** Два возобновления, дающие одинаковый
//! ответ, не различают, скопирован сегмент или переиспользован: ошибка
//! сокращается на симметричном пути. Поэтому у каждой пробы захваченный участок
//! **считает** после развилки, и ответы у ходов разные.
//!
//! **Цена названа числом.** §3.4 обещает O(глубины стека) на `resume`, и
//! обещание это меряется, а не пересказывается: одна и та же программа с одним
//! и с двумя возобновлениями, на двух глубинах, - прирост на уровень ровно один
//! блок, потому что звено сегмента и есть блок кучи.
//!
//! **Копия переписывает вектор.** Запись evidence называет кадр хендлера, у
//! копии кадр свой, и вторая операция под возобновлённым сегментом обязана
//! найти копию, а не оригинал. Различает это программа, где операция идёт
//! **после** развилки, - её и ловит мутант, снимающий переписывание.
//!
//! **Ресурс отвергается раньше копирования.** §3.4 запрещает resource-типы в
//! scope `handleMulti` статически, и проверка стоит в элаборации: до понижения
//! такая программа не доходит вовсе.
//!
//! # Оба бэкенда, одни программы (§9 Фаза 7, волна 2, трек G)
//!
//! Половина файла считает C-бэкендом, половина - LLVM, и **программы у них
//! одни**: константы ниже читают обе. Вторая копия текстов разъехалась бы с
//! первой молча, и «LLVM считает то же» держалось бы на совпадении двух
//! исходников, а не на их тождестве.
//!
//! Ответ у LLVM-половины сверяется с машиной тем же
//! [`harness::llvm_agreed`], каким сверяется корпус; здесь сверх него -
//! **счётчики блоков**, и сверяются они с C. Мультишот - ровно то место, где
//! ответ обманчив: повреждённый кадр, поделённый между ходами, даёт верное
//! число на первом проходе. Число блоков различает копию от переиспользования
//! там, где ответ уже не различает.

mod harness;

use adamas_codegen::llvm::Pipeline;

/// Общая шапка: списки, числа, единица и метка развилки.
const SHAPE: &str = "\
data Bool where
  False : Bool
  True : Bool

data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)

append : List Nat -> List Nat -> List Nat
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

effect Amb where
  toss : Bool
";

/// Ответ программы по мнению машины и число выданных блоков.
fn run(name: &str, source: &str) -> (String, usize) {
    let answer = harness::printed(source);
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    (answer, allocated)
}

/// Развилка, после которой захваченный участок **считает**.
///
/// Считает намеренно: ответы ходов обязаны разойтись. Верни оба хода одно и то
/// же - и «сегмент скопирован» стало бы неотличимо от «сегмент переиспользован»
/// и от «второй ход не исполнялся вовсе». Здесь `n + n` даёт `2` и `4`.
const RECOMPUTED: &str = "\
twice : Nat -> List Nat
twice n = Cons (n + n) Nil

probe : {Amb} List Nat
probe =
  let b : Bool = toss
  case b of
    True -> twice (Succ Zero)
    False -> twice (Succ (Succ Zero))

main : List Nat
main = handleMulti probe with
  return v -> v
  toss -> append (resume True) (resume False)
";

/// Двойное возобновление проходит захваченный участок заново, и ответы разные.
#[test]
fn a_second_resume_walks_the_captured_part_again() {
    let (answer, _) = run("мультишот-повтор", &format!("{SHAPE}{RECOMPUTED}"));
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)",
        "второй ход не пересчитал захваченный участок"
    );
}

/// Операция **после** развилки: её хендлер ищется в скопированном сегменте.
///
/// Здесь и живёт переписывание вектора. Кадры копии несут вектор, чья запись
/// называет кадр хендлера; у копии он свой, и не перепиши его - разрез пошёл бы
/// по кадру оригинала, которого на стеке нет вовсе. Развилок поэтому две, а
/// ответы всех четырёх ходов различны: `1, 2, 3, 4`.
const NESTED_TOSS: &str = "\
pair : Bool -> Bool -> List Nat
pair True True = Cons (Succ Zero) Nil
pair True False = Cons (Succ (Succ Zero)) Nil
pair False True = Cons (Succ (Succ (Succ Zero))) Nil
pair False False = Cons (Succ (Succ (Succ (Succ Zero)))) Nil

probe : {Amb} List Nat
probe =
  let first : Bool = toss
  let second : Bool = toss
  pair first second

main : List Nat
main = handleMulti probe with
  return v -> v
  toss -> append (resume True) (resume False)
";

#[test]
fn an_operation_after_the_fork_finds_the_handler_of_its_own_copy() {
    let (answer, _) = run("мультишот-вложенный", &format!("{SHAPE}{NESTED_TOSS}"));
    assert_eq!(
        answer,
        "Cons (Succ Zero) (Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ Zero))) \
         (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)))",
        "четыре хода развилки разошлись не так, как у машины"
    );
}

/// Проба глубины: `depth` кадров продолжения между операцией и её хендлером.
///
/// `hold` ничего не аллоцирует и ответ первого аргумента отдаёт как есть -
/// значит каждый уровень стоит ровно **кадра**, и прирост цены копии виден
/// чистым. Возобновлений столько, сколько написано в `branch`.
fn ladder(depth: usize, branch: &str) -> String {
    let mut rungs = String::new();
    for _ in 0..depth {
        rungs.push_str("hold (");
    }
    rungs.push_str("toss");
    for _ in 0..depth {
        rungs.push(')');
    }
    format!(
        "{SHAPE}\
hold : Bool -> Bool
hold b = b

deep : {{Amb}} List Nat
deep =
  let b : Bool = {rungs}
  case b of
    True -> Cons (Succ Zero) Nil
    False -> Cons (Succ (Succ Zero)) Nil

main : List Nat
main = handleMulti deep with
  return v -> v
  toss -> {branch}
"
    )
}

/// Цена возобновления - O(глубины сегмента), и это измерено, а не сказано.
///
/// Меряется **разность**: одно возобновление против двух на одной глубине.
/// Первое копии не делает вовсе - ссылка на ручку последняя, и сегмент
/// достаётся ему сам (договор об уникальности, §5.1). Второе платит копию, и
/// цена её растёт со глубиной ровно по звену на уровень.
///
/// Числа ряда: 9/21 на двух уровнях, 13/29 на шести. Второй ход стоит 12 и 16
/// блоков - ровно `+1` на уровень, и это и есть O(глубины) §3.4. Сними у копии
/// разделение вектора между звеньями - и станет `+2`: вектор поехал бы на
/// каждое звено. Измерено мутантом.
///
/// Здесь же цена решения «вердикт всех веток мультишота общий»: одноходовая
/// проба платит за неё **один блок** (9 против 8, 13 против 12) - ручку
/// сегмента, который тут же и тратится. Двуходовая не платит ничего: у неё
/// вердикт общий и так. Свидетеля у самого решения нет - вычисленный вердикт
/// проходит корпус целиком, - и цена его записана здесь числом.
#[test]
fn a_resume_costs_the_depth_of_its_segment() {
    let single = "resume True";
    let double = "append (resume True) (resume False)";

    let (_, near_once) = run("лестница-1-раз", &ladder(2, single));
    let (_, near_twice) = run("лестница-1-два", &ladder(2, double));
    let (_, far_once) = run("лестница-5-раз", &ladder(6, single));
    let (_, far_twice) = run("лестница-5-два", &ladder(6, double));

    let near = near_twice - near_once;
    let far = far_twice - far_once;
    // Четыре уровня глубины - четыре лишних звена в копии, и ни одного блока
    // сверх них: работа второго хода одна и та же на обеих глубинах.
    assert_eq!(
        far - near,
        4,
        "цена второго возобновления не линейна по глубине: {near} против {far}"
    );
    // Одно возобновление копии не стоит: разность глубин у однохода - ровно
    // кадры самой лестницы, которых на четыре больше.
    assert_eq!(
        far_once - near_once,
        4,
        "одноходовая проба заплатила за копию: {near_once} против {far_once}"
    );
}

/// Плоское значение переживает копию сегмента.
///
/// Слот кадра со счётчиком и слот с битами различает **число счётных слотов**,
/// которое кадр носит рядом с числом слотов. Дупни копия всё подряд - и `40`
/// поехало бы указателем: младший бит нулевой, заголовка нет. Мутант,
/// снимающий это различие, роняет прогон.
const FLAT_ACROSS: &str = "\
data Row where
  Empty : Row
  Item : Int64 -> Row -> Row

joined : Row -> Row -> Row
joined Empty ys = ys
joined (Item x xs) ys = Item x (joined xs ys)

probe : {Amb} Row
probe =
  let n : Int64 = 40
  let b : Bool = toss
  case b of
    True -> Item (addInt64 n 1) Empty
    False -> Item (addInt64 n 2) Empty

main : Row
main = handleMulti probe with
  return v -> v
  toss -> joined (resume True) (resume False)
";

#[test]
fn a_flat_slot_crosses_the_copy_without_a_counter() {
    let (answer, _) = run("мультишот-плоский", &format!("{SHAPE}{FLAT_ACROSS}"));
    assert_eq!(
        answer, "Item 41 (Item 42 Empty)",
        "плоский слот не пережил копию сегмента"
    );
}

/// Одношотная резумпция **внутри** мультишотного участка достаётся каждому ходу.
///
/// Внутренний хендлер общего вида: `resume` не в хвосте, значит его резумпция
/// овеществлена и лежит в кадре, который внешний разрез уносит с собой. Копия
/// дупает эту ручку, и обоим ходам она достаётся живой. Не пометь копия её
/// мультишотной - второй ход получил бы потраченную, и прогон оборвался бы
/// «резумпция возобновлена дважды»; ровно этот дефект машина закрыла признаком
/// `multishot` (`eval/multi-over-oneshot`).
///
/// Ответы ходов различны по построению: `pick` отвечает единицей на `True` и
/// двойкой на `False`, а внутренний удваивает.
const ONESHOT_INSIDE: &str = "\
effect Ask where
  ask : Nat

asking : {Ask} Nat
asking =
  let a : Nat = ask
  a + a

pick : Unit -> {Amb} Nat
pick u =
  let b : Bool = toss
  case b of
    True -> Succ Zero
    False -> Succ (Succ Zero)

inner : {Amb} List Nat
inner = handle asking with
  return v -> Cons v Nil
  ask -> resume (pick MkUnit)

main : List Nat
main = handleMulti inner with
  return v -> v
  toss -> append (resume True) (resume False)
";

#[test]
fn a_oneshot_resumption_inside_the_copy_serves_every_walk() {
    let (answer, _) = run(
        "мультишот-над-одношотом",
        &format!("{SHAPE}{ONESHOT_INSIDE}"),
    );
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)",
        "второй ход не получил живой одношотной резумпции"
    );
}

/// Ресурс под мультишотом отвергается **элаборацией**, а не копированием.
///
/// Порядок здесь и есть утверждение: §3.4 запрещает resource-типы в scope
/// `handleMulti` статически, и отказ обязан прийти раньше, чем что-либо
/// скопирует сегмент. Читается это единственным способом - программа не
/// доходит до понижения вовсе.
///
/// Отсюда же следствие, которое стоит записать: свидетеля «двойное
/// возобновление с ресурсом, у каждой копии свой деструктор» **не существует**.
/// Такую программу не написать - её отвергает проверка, и отвергает по делу:
/// деструктор был бы позван дважды.
const RESOURCE_UNDER_MULTI: &str = "\
closeFile : (1 b : Bool) -> Bool
closeFile b = b

resource File where
  Open : Bool -> File
  drop : File -> Bool
  drop (Open b) = closeFile b

choose : Bool -> List Nat
choose True = Cons (Succ Zero) Nil
choose False = Cons (Succ (Succ Zero)) Nil

kept : {Amb} List Nat
kept =
  let h : File = Open True
  let b : Bool = toss
  choose b

main : List Nat
main = handleMulti kept with
  return v -> v
  toss -> append (resume True) (resume False)
";

#[test]
fn a_resource_under_multishot_is_refused_before_any_copy() {
    let error = harness::rejected(&format!("{SHAPE}{RESOURCE_UNDER_MULTI}"));
    assert!(
        error.contains("handleMulti"),
        "отказ не назвал мультишот: {error}"
    );
}

/// Питомник под мультишотом отвергается там же и по тому же поводу.
///
/// §10 вопрос 125 закрыт вариантом (а): вычисление, достигающее `withNursery`,
/// в scope `handleMulti` отвергается. Причина - та же, что у ресурса, только
/// про состояние: копия мультишотного сегмента копирует кадр питомника, но не
/// его очередь, и второй проход получил бы выпитый круг.
///
/// Стоит здесь рядом с ресурсом намеренно: оба запрета живут в элаборации, и
/// оба, значит, действуют на **обоих** бэкендах одинаково - до понижения такая
/// программа не доходит вовсе. Молча разрешённый питомник на LLVM-пути был бы
/// ровно тем дефектом, которого ни один ответ не показывает.
const NURSERY_UNDER_MULTI: &str = "\
effect Async where
  suspend : Unit

withNursery : ({Async} Unit) -> Unit

nursed : {Async} Unit
nursed = suspend

kept : {Amb} Unit
kept =
  let b : Bool = toss
  withNursery nursed

main : Unit
main = handleMulti kept with
  return v -> v
  toss -> resume True
";

#[test]
fn a_nursery_under_multishot_is_refused_before_either_backend() {
    let error = harness::rejected(&format!("{SHAPE}{NURSERY_UNDER_MULTI}"));
    assert!(
        error.contains("handleMulti"),
        "отказ не назвал мультишот: {error}"
    );
    assert!(
        error.contains("питомник"),
        "отказ назвал не питомник: {error}"
    );
}

// --- Тот же мультишот через LLVM (§9 Фаза 7, волна 2, трек G) -------------

/// Ответ LLVM-пути и число выданных блоков.
///
/// Ответ сверяет с машиной сам [`harness::llvm_agreed`] - тем же договором, в
/// котором стоят первые два вычислителя. Здесь сверх него читаются счётчики:
/// живых блоков обязан быть ноль, иначе копия сегмента течёт, а ответ об этом
/// молчит.
fn through_llvm(
    name: &str,
    source: &str,
    tools: &adamas_codegen::llvm::Toolchain,
) -> (String, usize) {
    let pipeline = Pipeline::optimised();
    let (answer, stderr) = harness::llvm_agreed(name, source, tools, &pipeline, name)
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон LLVM оставил блоки живыми");
    (answer, allocated)
}

/// Двойное возобновление на LLVM-пути проходит захваченный участок заново.
///
/// Свидетель **различает ходы**: `twice` считает `n + n` после развилки, и
/// ответы ходов - `2` и `4`. Верни оба хода одно и то же, и «сегмент
/// скопирован» стало бы неотличимо от «сегмент переиспользован» и от «второй
/// ход не исполнялся вовсе». Порядок их сбора тоже наблюдаем: `append` кладёт
/// ход `True` перед ходом `False`.
///
/// Число блоков сверяется с C: модель кадра у двух бэкендов одна, и разойдись
/// она - разошёлся бы счёт, даже когда ответ цел.
#[test]
fn the_llvm_path_walks_the_captured_part_again() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = format!("{SHAPE}{RECOMPUTED}");
    let (expected, by_c) = run("мультишот-повтор-C", &source);
    let (answer, by_llvm) = through_llvm("llvm-мультишот-повтор", &source, &tools);
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)",
        "второй ход LLVM не пересчитал захваченный участок"
    );
    assert_eq!(answer, expected, "LLVM и C разошлись ответом");
    assert_eq!(
        by_llvm, by_c,
        "LLVM и C разошлись числом выданных блоков: копия сегмента не та же"
    );
}

/// Операция **после** развилки находит хендлер своей копии.
///
/// Здесь живёт переписывание вектора evidence: запись называет кадр хендлера, у
/// копии он свой, и не перепиши его рантайм - разрез пошёл бы по кадру
/// оригинала, которого на стеке нет вовсе. Развилок две, ходов четыре, и
/// ответы всех четырёх различны: `1, 2, 3, 4` в порядке обхода.
#[test]
fn the_llvm_path_finds_the_handler_of_its_own_copy() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = format!("{SHAPE}{NESTED_TOSS}");
    let (expected, by_c) = run("мультишот-вложенный-C", &source);
    let (answer, by_llvm) = through_llvm("llvm-мультишот-вложенный", &source, &tools);
    assert_eq!(
        answer,
        "Cons (Succ Zero) (Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ Zero))) \
         (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)))",
        "четыре хода развилки на LLVM разошлись не так, как у машины"
    );
    assert_eq!(answer, expected, "LLVM и C разошлись ответом");
    assert_eq!(by_llvm, by_c, "LLVM и C разошлись числом выданных блоков");
}

/// Плоское значение переживает копию сегмента и на LLVM-пути.
///
/// Слот кадра со счётчиком и слот с битами различает **число счётных слотов**,
/// которое эмиттер передаёт `adamas_kont_push`. Дупни копия всё подряд - и `40`
/// поехало бы указателем: младший бит нулевой, заголовка нет.
#[test]
fn a_flat_slot_crosses_the_copy_on_the_llvm_path() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = format!("{SHAPE}{FLAT_ACROSS}");
    let (expected, by_c) = run("мультишот-плоский-C", &source);
    let (answer, by_llvm) = through_llvm("llvm-мультишот-плоский", &source, &tools);
    assert_eq!(
        answer, "Item 41 (Item 42 Empty)",
        "плоский слот не пережил копию сегмента на LLVM-пути"
    );
    assert_eq!(answer, expected, "LLVM и C разошлись ответом");
    assert_eq!(by_llvm, by_c, "LLVM и C разошлись числом выданных блоков");
}

/// Одношотная резумпция внутри мультишотного участка достаётся каждому ходу.
///
/// Копия дупает ручку, лежащую в счётном слоте копируемого звена, и обоим ходам
/// она достаётся живой. Не пометь копия её мультишотной - второй ход получил бы
/// потраченную, и прогон оборвался бы.
#[test]
fn a_oneshot_resumption_inside_the_copy_serves_every_walk_on_llvm() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = format!("{SHAPE}{ONESHOT_INSIDE}");
    let (expected, by_c) = run("мультишот-над-одношотом-C", &source);
    let (answer, by_llvm) = through_llvm("llvm-мультишот-над-одношотом", &source, &tools);
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) (Cons (Succ (Succ (Succ (Succ Zero)))) Nil)",
        "второй ход LLVM не получил живой одношотной резумпции"
    );
    assert_eq!(answer, expected, "LLVM и C разошлись ответом");
    assert_eq!(by_llvm, by_c, "LLVM и C разошлись числом выданных блоков");
}

/// Цена возобновления на LLVM-пути - та же O(глубины сегмента).
///
/// Меряется **разность**, как и у C: одно возобновление против двух на одной
/// глубине. Первое копии не делает вовсе - ссылка на ручку последняя, - второе
/// платит копию, и цена её растёт по звену на уровень.
#[test]
fn a_resume_costs_the_depth_of_its_segment_on_llvm() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let single = "resume True";
    let double = "append (resume True) (resume False)";

    let (_, near_once) = through_llvm("llvm-лестница-1-раз", &ladder(2, single), &tools);
    let (_, near_twice) = through_llvm("llvm-лестница-1-два", &ladder(2, double), &tools);
    let (_, far_once) = through_llvm("llvm-лестница-5-раз", &ladder(6, single), &tools);
    let (_, far_twice) = through_llvm("llvm-лестница-5-два", &ladder(6, double), &tools);

    let near = near_twice - near_once;
    let far = far_twice - far_once;
    assert_eq!(
        far - near,
        4,
        "цена второго возобновления на LLVM не линейна по глубине: {near} против {far}"
    );
    assert_eq!(
        far_once - near_once,
        4,
        "одноходовая проба на LLVM заплатила за копию: {near_once} против {far_once}"
    );
    // Те же четыре числа, что у C: модель кадра одна, и счёт обязан совпасть
    // не «в среднем», а поштучно.
    for (name, llvm, source) in [
        ("лестница-1-раз", near_once, ladder(2, single)),
        ("лестница-1-два", near_twice, ladder(2, double)),
        ("лестница-5-раз", far_once, ladder(6, single)),
        ("лестница-5-два", far_twice, ladder(6, double)),
    ] {
        let (_, by_c) = run(&format!("{name}-C"), &source);
        assert_eq!(llvm, by_c, "{name}: LLVM выдал {llvm} блоков, C - {by_c}");
    }
}

/// Сломанная копия видна **только на втором ходе**, и мутанты это показывают.
///
/// Жанр здесь тот же, что у мутантов объектного слоя, и повод другой: мультишот
/// есть место, где ответ обманчив по построению. Три правки порождённого `.ll`,
/// и ни одна не меняет первого прохода.
///
/// - **Ручка не помечена мультишотной.** `adamas_segment_multi` снят: первый
///   `resume` тратит сегмент, второму достаётся потраченный.
/// - **Счётные слоты кадра посчитаны все.** Число счётных, переданное
///   `adamas_kont_push`, поднято до полного размера среды: копия дупает
///   плоские биты как указатель.
/// - **Дроп резумпции перед возобновлением.** Порядок двух вызовов у
///   `Expr::Resume` перевёрнут: сегмент раскручивается раньше, чем встанет.
///
/// Честный прогон и мутант сверяются **ответом и счётчиками сразу**: ответ у
/// правки бывает тот же, и тогда различает число блоков.
#[test]
fn a_broken_copy_of_the_segment_shows_only_on_the_second_walk() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let source = format!("{SHAPE}{FLAT_ACROSS}");
    let artefacts = harness::llvm_text("мутант-мультишот", &source).unwrap();
    let honest = harness::llvm_printed(
        "multimutant.honest",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        honest.printed, "Item 41 (Item 42 Empty)",
        "честный прогон мутантного стенда не совпал с прогоном корпуса"
    );

    let mutants = [
        (
            "unmarked",
            "ручка не помечена мультишотной",
            swapped(
                &artefacts.ll,
                "%op0.seized = call ptr @adamas_segment_multi(ptr %op0.val)",
                "%op0.seized = select i1 true, ptr %op0.val, ptr null",
            ),
        ),
        (
            "counted",
            "счётные слоты кадра посчитаны все",
            swapped(
                &artefacts.ll,
                "i64 1, i64 0, ptr %ev) ; продолжение",
                "i64 1, i64 1, ptr %ev) ; продолжение",
            ),
        ),
        (
            "order",
            "дроп резумпции перед возобновлением",
            swapped(
                &artefacts.ll,
                "  call void @adamas_kont_resume(ptr %kont, ptr %v0)\n  \
                 call void @adamas_resumption_drop(ptr %kont, ptr %v0)",
                "  call void @adamas_resumption_drop(ptr %kont, ptr %v0)\n  \
                 call void @adamas_kont_resume(ptr %kont, ptr %v0)",
            ),
        ),
    ];

    for (stem, why, mutant) in mutants {
        let broken = harness::llvm_printed(
            &format!("multimutant.{stem}"),
            &mutant,
            &artefacts.support,
            &tools,
            &pipeline,
        );
        let same = broken.printed == honest.printed
            && broken.allocated == honest.allocated
            && broken.live == honest.live;
        assert!(
            !same,
            "{why}: ответ и счётчики не изменились, и проверка не различает"
        );
        eprintln!(
            "мутант «{why}»: {} (выдано {:?}, живо {:?}, причина `{}`) против {} ({:?}, {:?})",
            broken.printed,
            broken.allocated,
            broken.live,
            broken.reason.trim_end(),
            honest.printed,
            honest.allocated,
            honest.live
        );
        // Первый мутант обязан упасть **названным** обрывом, и имя это -
        // единственное, что говорит, на каком проходе он упал: «возобновлена
        // дважды» достижимо только после того, как первый ход ручку потратил.
        // Без этой строки свидетель различал бы «сломалось» от «не сломалось»,
        // но не различал бы первый проход от второго - ровно ту разницу, ради
        // которой мультишот и проверяется.
        if stem == "unmarked" {
            assert!(
                broken.reason.contains("возобновлена дважды"),
                "снятая пометка мультишота оборвала прогон не вторым ходом: `{}`",
                broken.reason.trim_end()
            );
        }
    }
}

/// Текст с единственной заменой. Не найденная подстрока роняет тест.
fn swapped(text: &str, from: &str, to: &str) -> String {
    assert_eq!(
        text.matches(from).count(),
        1,
        "мутант не применился: `{from}` встречается в порождённом IR не один раз"
    );
    text.replace(from, to)
}
