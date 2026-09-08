//! Свидетель reuse: переиспользование видно **числом аллокаций** (§5.1).
//!
//! «Течи нет» про reuse не говорит ничего - ноль живых блоков даётся и при
//! полном его отсутствии, потому что показывает только `drop`. Поэтому здесь
//! считается другое число, которое рантайм печатает рядом: сколько блоков
//! **выдано**. Переписанная ячейка выдачей не считается, и разница видна.
//!
//! Свидетельствуют три прогона одной и той же `map`-по-дереву (§5.1,
//! каноническая механика FBIP):
//!
//! - [`grown`] строит дерево и на этом останавливается - база;
//! - [`unique`] строит его и отдаёт `map` **единственной** ссылкой;
//! - [`shared`] называет дерево ещё раз, поэтому `map` получает разделённое.
//!
//! У [`unique`] и [`shared`] ответ **один и тот же** - `map` от одного и того
//! же дерева, - и различает их только счётчик. Программа, у которой обе цифры
//! совпали бы, свидетелем не была бы.
//!
//! # Почему тождество, а не приращение
//!
//! `map` отдаётся `id`, а не `Succ`: строящая функция добавила бы к счётчику
//! свои ячейки, и «ноль новых» пришлось бы вычитать из чужого числа. С `id`
//! утверждение прямое - [`unique`] выдаёт ровно на один блок больше базы, и
//! этот один есть замыкание `id`, одно на весь обход.

mod harness;

/// Глубина дерева. Узлов у полного двоичного - `2^depth - 1`.
const DEPTH: usize = 4;

/// Узлов в дереве: столько ячеек `Node` reuse обязан сберечь.
const NODES: usize = (1 << DEPTH) - 1;

/// Общая часть трёх программ: дерево, обход, вспомогательные имена.
///
/// `grow` метит узлы `Zero` нарочно: нульарный конструктор непосредствен и
/// блока не занимает, поэтому в счётчике видны только ячейки `Node` и разбор
/// самого счётчика глубины.
const COMMON: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Tree
  Node : Tree -> Nat -> Tree -> Tree

grow : Nat -> Tree
grow Zero = Leaf
grow (Succ k) = Node (grow k) Zero (grow k)

map : (Nat -> Nat) -> Tree -> Tree
map f Leaf = Leaf
map f (Node l x r) = Node (map f l) (f x) (map f r)

id : Nat -> Nat
id x = x

first : Tree -> Tree -> Tree
first a b = a
";

/// База: дерево построено, и больше ничего не происходит.
fn grown() -> String {
    format!("{COMMON}\nmain : Tree\nmain = grow {DEPTH}\n")
}

/// Уникальный вход: дерево уходит в `map` единственной ссылкой.
fn unique() -> String {
    format!("{COMMON}\nmain : Tree\nmain = map id (grow {DEPTH})\n")
}

/// Разделённый вход: дерево названо ещё раз, и `map` получает его с лишней
/// ссылкой.
///
/// `first` отбрасывает второй аргумент, поэтому **ответ тот же**, что у
/// [`unique`]: разошлись программы только владением.
fn shared() -> String {
    format!("{COMMON}\nmain : Tree\nmain =\n  let t : Tree = grow {DEPTH}\n  first (map id t) t\n")
}

/// Сколько блоков выдал прогон. Ответ по дороге сверяется с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// `map` по уникальному дереву не строит ни одной новой ячейки `Node`.
#[test]
fn reuse_shows_up_as_allocations_not_saved() {
    let base = allocated("grown", &grown());
    let unique = allocated("unique", &unique());
    let shared = allocated("shared", &shared());

    // Свидетель сперва обязан быть непустым: дерево без узлов не показало бы
    // ничего, и тест остался бы зелёным и пустым.
    assert!(
        base >= NODES,
        "дерево мельче собственного счёта: выдано {base}, узлов {NODES}"
    );

    assert_eq!(
        unique - base,
        1,
        "на уникальном входе `map` построил ячейки: база {base}, обход {unique}, \
         а сверх базы законно ровно одно замыкание `id`"
    );
    assert_eq!(
        shared - unique,
        NODES,
        "разделённый вход обязан стоить по ячейке на узел: уникальный {unique}, \
         разделённый {shared}, узлов {NODES}"
    );
}

/// Разобранное, названное ветвью ещё раз, ячейки не отдаёт.
///
/// Ветвь строит структуру **той же формы**, что разобрала, и reuse тут
/// напрашивается - но `t` названо в теле, значит остаётся живым, и переписывать
/// его слоты нечем. То же правило, что `Fault::Alive` у `@fbip`
/// (`adamas-core/src/fbip.rs`), только там оно отказ, а здесь решение: ячейка
/// просто не придерживается.
///
/// Свидетельствует **ответ**, а не счётчик: перепиши ветвь ячейку - и `spread`
/// увидит вторым аргументом то, что положил первый, то есть `MkFour b a b a`
/// вместо `MkFour b a a b`. Счётчик тут не годился бы: он показал бы экономию,
/// а не порчу.
const ALIVE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Two where
  MkTwo : Nat -> Nat -> Two

data Four where
  MkFour : Nat -> Nat -> Nat -> Nat -> Four

spread : Two -> Two -> Four
spread (MkTwo a b) (MkTwo c d) = MkFour a b c d

keep : Two -> Four
keep t = case t of
  MkTwo a b -> spread (MkTwo b a) t

main : Four
main = keep (MkTwo Zero (Succ Zero))
";

/// Ветвь, назвавшая разобранное, переписывает его ячейку - и отвечает не то.
#[test]
fn a_scrutinee_named_again_keeps_its_cell() {
    let stderr = harness::agreed("alive", ALIVE).unwrap_or_else(|error| panic!("живое: {error}"));
    let (_, live) = harness::blocks("alive", &stderr);
    assert_eq!(live, 0, "живое: прогон оставил блоки живыми");
}

/// Ячейка придерживается только там, где её занимает **каждый** путь.
///
/// Ветвь `MkTwo` разбирает ячейку на два слота, а дальше ветвится: `Zero`
/// отвечает `L b` и ничего двухслотового не строит, `Succ k` строит `MkTwo k b`.
/// Придержи ячейку - и на первом пути занять её будет некому: она не вернётся
/// куче, потому что `adamas_drop_reuse` её не освобождает, и течь вернётся через
/// reuse.
///
/// Прогон идёт именно первым путём (`a = Zero`): свидетель, не заходящий на
/// пустой путь, не показал бы ничего.
const PARTIAL: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Two where
  MkTwo : Nat -> Nat -> Two

data Or where
  L : Nat -> Or
  R : Two -> Or

branch : Two -> Or
branch (MkTwo a b) = case a of
  Zero -> L b
  Succ k -> R (MkTwo k b)

main : Or
main = branch (MkTwo Zero (Succ Zero))
";

/// Путь, которому ячейку занять нечем, оставил бы её висеть.
#[test]
fn a_cell_is_held_only_when_every_path_takes_it() {
    let stderr =
        harness::agreed("partial", PARTIAL).unwrap_or_else(|error| panic!("ветвление: {error}"));
    let (_, live) = harness::blocks("partial", &stderr);
    assert_eq!(live, 0, "ветвление: прогон оставил блоки живыми");
}

/// Общая часть замера кратности: у `swap` параметр объявлен единицей.
const LINEAR: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Two where
  MkTwo : Nat -> Nat -> Two

swap : (1 t : Two) -> Two
swap (MkTwo a b) = MkTwo b a

hold : Two -> Two -> Two
hold x y = x
";

/// Единственная ссылка: `swap` переписывает разобранную ячейку.
fn sole() -> String {
    format!("{LINEAR}\nmain : Two\nmain = swap (MkTwo Zero Zero)\n")
}

/// Та же `swap` с той же кратностью, но значение названо дважды.
fn twice() -> String {
    format!("{LINEAR}\nmain : Two\nmain =\n  let p : Two = MkTwo Zero Zero\n  hold (swap p) p\n")
}

/// Кратность `1` уникальности объекта не обещает - замер, а не рассуждение.
///
/// §5.1 говорит: «линейные значения обходятся без RC вообще: компилятор знает
/// уникальность статически», и [`Unique::Certain`](adamas_codegen::ir::Unique)
/// ставится ровно по кратности `1`. Но кратность лежит на **связывании**, а
/// `1` здесь аффинна (§3.3): `ω`-значение, названное однажды, в позицию `1`
/// проходит, и объект внутри вызываемой функции разделён.
///
/// Обе программы зовут **одну и ту же** `swap` с одним и тем же параметром
/// кратности `1` и отвечают одним и тем же `MkTwo Zero Zero`. Разошлись они
/// только числом выданных блоков - значит уникальность здесь свойство места
/// вызова, а не сигнатуры, и спрашивать её приходится счётчиком.
#[test]
fn a_linear_binder_does_not_promise_a_unique_object() {
    let sole = allocated("sole", &sole());
    let twice = allocated("twice", &twice());
    assert_eq!(
        twice - sole,
        1,
        "разделённое значение в позиции кратности 1 обязано стоить ячейку: \
         единственная ссылка {sole}, две {twice}"
    );
}
