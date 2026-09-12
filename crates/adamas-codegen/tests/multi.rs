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

mod harness;

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

infixl 6 +
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
