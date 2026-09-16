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

/// Ячейка придерживается и на том пути, которому занять её нечем.
///
/// Ветвь `MkTwo` разбирает ячейку на два слота, а дальше ветвится: `Zero`
/// отвечает `L b` и ничего двухслотового не строит, `Succ k` строит `MkTwo k b`.
/// Занимающий путь ячейку переписывает, незанимающий **возвращает** её куче
/// ([`Expr::Discard`](adamas_codegen::ir::Expr::Discard), §10 вопрос 173).
/// Забудь проход этот возврат - и блок повис бы: `adamas_drop_reuse` куче его
/// не отдаёт, и течь вернулась бы через reuse.
///
/// Прогон идёт именно незанимающим путём (`a = Zero`): свидетель, не заходящий
/// на него, не показал бы ничего.
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

/// Путь, которому ячейку занять нечем, обязан её вернуть.
#[test]
fn a_path_with_nothing_to_take_gives_the_cell_back() {
    let stderr =
        harness::agreed("partial", PARTIAL).unwrap_or_else(|error| panic!("ветвление: {error}"));
    let (_, live) = harness::blocks("partial", &stderr);
    assert_eq!(live, 0, "ветвление: прогон оставил блоки живыми");
}

/// Ячеек в списке свидетеля односторонней ветви.
const CELLS: usize = 32;

/// Общая часть свидетеля: список, построение, свёртка и сама односторонняя
/// ветвь.
///
/// `sift` разбирает `Cons` и строит `Cons` **только на одном из двух путей**:
/// оставленный элемент переписывает разобранную ячейку, отброшенный её
/// возвращает. Порог решает, каким путём пойдёт каждая ячейка, и подставляется
/// он числом - свидетель обязан пройти оба пути и смесь из них.
fn sift(threshold: i64) -> String {
    format!(
        "\
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

keep : Int64 -> Bool
keep x = ltInt64 {threshold} x

sift : List -> List -> List
sift Nil acc = acc
sift (Cons x xs) acc = case keep x of
  True -> sift xs (Cons x acc)
  False -> sift xs acc

total : List -> Int64 -> Int64
total Nil acc = acc
total (Cons x xs) acc = total xs (addInt64 (mulInt64 acc 3) x)

main : Int64
main = total (sift (build {CELLS} Nil) Nil) 0
"
    )
}

/// База: тот же список построен и свёрнут, а `sift` не звана.
const UNSIFTED: &str = "\
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

total : List -> Int64 -> Int64
total Nil acc = acc
total (Cons x xs) acc = total xs (addInt64 (mulInt64 acc 3) x)

main : Int64
main = total (build 32 Nil) 0
";

/// Ветвь с односторонним построением переиспользует ячейку (§10 вопрос 173).
///
/// Свидетельствует **счётчик**, и иначе нельзя: ответ у обеих редакций прохода
/// один и тот же. Мера - три порога, и каждый свой:
///
/// - `0` - каждая ячейка идёт занимающим путём; до закрытия вопроса `sift`
///   платил здесь по аллокации на ячейку, потому что ветвь не придерживала
///   ничего;
/// - `32` - каждая идёт незанимающим; придержанная ячейка возвращается куче, и
///   ноль живых блоков - единственное, чем эта сторона свидетельствует;
/// - `16` - половина туда, половина сюда; без неё прогон не прошёл бы оба пути
///   **в одной** программе, а ошибка живёт именно на их стыке.
///
/// Ни один из трёх не вправе выдать ни одного блока сверх базы.
#[test]
fn a_one_sided_branch_reuses_the_cell_it_took_apart() {
    let base = allocated("unsifted", UNSIFTED);
    // Свидетель сперва обязан быть непустым: список короче собственного счёта
    // не показал бы ни переиспользования, ни течи.
    assert!(
        base >= CELLS,
        "список мельче собственного счёта: выдано {base}, ячеек {CELLS}"
    );
    for (name, threshold) in [("sift-all", 0), ("sift-none", 32), ("sift-half", 16)] {
        let sifted = allocated(name, &sift(threshold));
        assert_eq!(
            sifted, base,
            "{name}: односторонняя ветвь выдала блоки сверх базы {base}, \
             хотя разобранную ячейку занимает сама"
        );
    }
}

/// То же самое на LLVM-пути: вставка RC общая, и счётчик обязан сойтись.
///
/// Свидетель здесь **второй**, а не дубль первого: §5.1 и сам проход стоят до
/// эмиттеров (`tests/seam.rs`), но раздаёт придержанную ячейку каждый эмиттер
/// своими печатями - у C это `adamas_free` по имени связывания, у LLVM
/// `phi` и вызов по SSA-значению. Промахнись один из двух - счётчик разойдётся
/// только у него.
#[test]
fn the_llvm_path_reuses_the_same_cell() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = adamas_codegen::llvm::Pipeline::optimised();
    let counted = |name: &str, source: &str| {
        let (_, stderr) = harness::llvm_agreed(
            name,
            source,
            &tools,
            &pipeline,
            &format!("{name}.reuse-173.llvm"),
        )
        .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (allocated, live) = harness::blocks(name, &stderr);
        assert_eq!(live, 0, "{name}: прогон LLVM оставил блоки живыми");
        allocated
    };
    let base = counted("unsifted-llvm", UNSIFTED);
    assert!(
        base >= CELLS,
        "список мельче собственного счёта: выдано {base}, ячеек {CELLS}"
    );
    for (name, threshold) in [
        ("sift-all-llvm", 0),
        ("sift-none-llvm", 32),
        ("sift-half-llvm", 16),
    ] {
        let sifted = counted(name, &sift(threshold));
        assert_eq!(
            sifted, base,
            "{name}: односторонняя ветвь выдала блоки сверх базы {base}"
        );
    }
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
/// Мера §10 вопроса 149 (закрыт: уникальность из производства, из кратности -
/// никогда; [`Unique::Certain`](adamas_codegen::ir::Unique) по кратности
/// больше не ставится). Кратность ограничивает употребление **вызываемым**, а
/// не алиасинг: `ω`-значение, названное однажды, в позицию `1` проходит, и
/// объект внутри вызываемой функции разделён.
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
