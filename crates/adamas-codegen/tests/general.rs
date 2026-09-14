//! Одношот общего вида: дробление тел кадрами (трек D волны 4, §3.4).
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что понижение считает то же,
//! что машина. Здесь стоит то, чего корпус не различает, и различий этих два
//! жанра: **время** и **форма порождённого кода**.
//!
//! Время - несущий критерий трека, а не украшение. Сегмент общей ветки растёт
//! с глубиной рекурсии под хендлером, и всякое действие над ним ценой в его
//! длину даёт квадрат: 17/53/164/921 мс на 3200/6400/12800/25600 операций
//! мерено ровно так, обходом в `adamas_kont_cut`. Корпус этого не видит - его
//! программы мелки, - а ряд видит.
//!
//! Форма - потому что вердикт ветки решает, **что случается с сегментом**, и
//! три ответа §3.4 различаются одной строкой порождённого C каждый.

mod harness;

use std::path::Path;
use std::process::Command;
use std::time::Instant;

/// Общая часть свидетелей: числа, единица и метка.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

effect Ask where
  ask : Nat
";

/// Три вердикта, три программы, три разные строки порождённого C.
///
/// Различие тут не косметическое: сегмент у хвостовой цел, у абортивной
/// раскручен, у общей отдан веткой значением. Одна строка на каждый - и она
/// же то место, где вердикт наблюдаем читателем.
#[test]
fn the_three_verdicts_do_three_different_things_to_the_segment() {
    let tail = harness::text(&format!(
        "{SHAPE}\
asked : {{Ask}} Nat
asked = ask

main : Nat
main = handle asked with
  return v -> v
  ask -> resume (Succ Zero)
"
    ))
    .unwrap_or_else(|error| panic!("хвостовая: {error}"));
    let abortive = harness::text(&format!(
        "{SHAPE}\
asked : {{Ask}} Nat
asked = ask

main : Nat
main = handle asked with
  return v -> v
  ask -> Succ Zero
"
    ))
    .unwrap_or_else(|error| panic!("абортивная: {error}"));
    let general = harness::text(&format!(
        "{SHAPE}\
asked : {{Ask}} (List Nat)
asked = Cons ask Nil

main : List Nat
main = handle asked with
  return v -> v
  ask -> Cons Zero (resume Zero)
"
    ))
    .unwrap_or_else(|error| panic!("общая: {error}"));

    // Хвостовая сегмента не трогает вовсе: ответ ветки и есть значение
    // операции, продолжение остаётся стоять как стояло.
    assert!(
        !tail.contains("adamas_kont_cut"),
        "хвостовая ветка режет сегмент:\n{tail}"
    );
    // Абортивная режет и **сразу** кладёт раскрутку: деструкторы побегут после
    // ветки, потому что её кадры лягут выше кадра раскрутки.
    assert!(
        abortive.contains("adamas_segment_unwind(kont, adamas_kont_cut(kont, h))"),
        "абортивная ветка не раскручивает срезанное:\n{abortive}"
    );
    assert!(
        !abortive.contains("adamas_segment_value"),
        "абортивная ветка овеществила сегмент, а звать его некому:\n{abortive}"
    );
    // Общая режет в **значение**: дальше решает владение.
    assert!(
        general.contains("adamas_segment_value(adamas_kont_cut(kont, h))"),
        "общая ветка не получила сегмент значением:\n{general}"
    );
    assert!(
        general.contains("adamas_kont_resume(kont,"),
        "общая ветка не возобновляет:\n{general}"
    );
}

/// Резумпция, до которой ветка не дожила, раскручивается своим дропом.
///
/// Кадра решения о смерти резумпции у понижения нет и не нужно (§10 вопрос
/// 129): у машины его требовал признак «резумпцию не позвали», считаемый на
/// возврате ветки, а здесь на тот же вопрос отвечает владение. Видно это в
/// тексте: дроп резумпции - **не** общий `adamas_drop_value`, потому что
/// отдать её значит раскрутить её сегмент, а раскрутке нужна ручка стека.
#[test]
fn a_resumption_is_dropped_by_its_own_path() {
    let text = harness::text(&format!(
        "{SHAPE}\
flag : Nat
flag = Zero

asked : {{Ask}} (List Nat)
asked = Cons ask Nil

main : List Nat
main = handle asked with
  return v -> v
  ask -> case flag of
    Zero -> Nil
    Succ k -> Cons Zero (resume Zero)
"
    ))
    .unwrap_or_else(|error| panic!("брошенная резумпция: {error}"));
    assert!(
        text.contains("adamas_resumption_drop(kont, v"),
        "брошенная резумпция дропается общим путём: раскрутке нужна ручка\n{text}"
    );
}

/// Плоское значение через границу кадра не всякое: агрегат шире слова.
///
/// Граница названа отказом, а не молчанием: слот кадра - слово, и плотный
/// агрегат §4.11 в него не влезает. Ближайший проходящий сосед - тот же
/// агрегат, не переживающий точки приостановки; он в корпусе (`flat`).
///
/// Резумпция здесь **не** в хвосте намеренно: с хвостовой веткой программа
/// тиха (§3.4, вопрос 74), операция перестаёт быть точкой приостановки, и
/// границы кадра, которую стережёт свидетель, не возникает вовсе.
#[test]
fn a_packed_aggregate_does_not_survive_a_suspension() {
    let source = format!(
        "{SHAPE}\
type V3 (a : Type) = {{ x : a, y : a, z : a }}
type Vec3 = V3 Float32

data Boxed where
  MkBoxed : Float32 -> Nat -> Boxed

first : Vec3
first = {{ x = 1.0, y = 2.0, z = 3.0 }}

built : Array 3 Vec3
built = arrayNew 3 first

probe : Array 3 Vec3 -> {{Ask}} Boxed
probe xs =
  let v : Vec3 = arrayIndex xs 0
  let n : Nat = ask
  MkBoxed v.z n

held : {{Ask}} Boxed
held = probe built

main : List Boxed
main = handle held with
  return v -> Cons v Nil
  ask -> Cons (MkBoxed 0.0 Zero) (resume Zero)
"
    );
    let error = harness::compiled(&source).expect_err("агрегат в слоте кадра - названная граница");
    let text = error.to_string();
    assert!(
        text.contains("переживает точку приостановки"),
        "отказ не назвал границу: {text}"
    );
}

/// Ряд времени: операция под рекурсией при вчетверо большей работе.
///
/// Линейному исполнению отвечает восьмикратное время на восьмикратной работе,
/// квадратичному - шестидесятичетырёхкратное. Порог взят посередине с большим
/// запасом в обе стороны: свидетель ловит **класс**, а не константу, и на
/// разной машине константа разная.
///
/// Две точки, а не четыре: класс читается по отношению, а каждая точка стоит
/// сборки `-O2`. Полный ряд гоняется руками, когда есть что сравнивать; на
/// нём мерены 2/3/7/12 мс при 3200/6400/12800/25600 операций.
///
/// Верхняя точка - 25600, и потолок этот **чужой**: ответ здесь глубиной в
/// число операций, а дроп его рекурсивен (названный долг шапки `lib.rs`).
/// Сотня тысяч кладёт C-стек на освобождении ответа, а не на счёте.
#[test]
fn an_operation_under_recursion_stays_linear() {
    let small = timed("linear-small", 8, 4);
    let large = timed("linear-large", 16, 16);
    assert!(
        small > 0,
        "мелкая точка ушла в ноль: мерить нечего, ряд не показателен"
    );
    let ratio = large / small;
    assert!(
        ratio < 24,
        "восьмикратная работа стоила {ratio}-кратного времени: {small} мс против {large} - \
         это не линия (квадрат дал бы около шестидесяти четырёх)"
    );
}

/// Программа: `counted n` производит операцию на каждом уровне рекурсии, и
/// сегмент её резумпции растёт вместе с глубиной.
///
/// Хендлер параметризован (`state`): его ветка зовёт резумпцию **позже**
/// собственного возврата, то есть вердикт у неё общий, и сегмент режется на
/// каждой операции. Хвостово-резумптивный сосед сегмента не режет вовсе и
/// этого ряда не мерит.
///
/// Число операций пишется **произведением**: сотня нанизанных `Succ` в
/// разборе упирается в предел вложенности, а произведение - нет.
fn source(left: usize, right: usize) -> String {
    let literal = |count: usize| -> String {
        let mut out = String::new();
        for _ in 0..count {
            out.push_str("(Succ ");
        }
        out.push_str("Zero");
        for _ in 0..count {
            out.push(')');
        }
        out
    };
    format!(
        "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

infixl 6 +
(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)

infixl 7 *
(*) : Nat -> Nat -> Nat
(*) Zero m = Zero
(*) (Succ k) m = m + k * m

effect State where
  get : Nat
  put : Nat -> Unit

counted : Nat -> {{State}} Nat
counted Zero = Zero
counted (Succ k) =
  let one : Nat = get
  one + counted k

hundred : Nat
hundred = {}

left : Nat
left = {}

right : Nat
right = {}

held : {{State}} Nat
held = counted (hundred * (left * right))

threaded : Nat
threaded = handle held with
  state (Succ Zero)
  return v -> v
  get -> resume state state
  put x -> resume MkUnit x

main : Nat
main = threaded
",
        literal(100),
        literal(left),
        literal(right)
    )
}

/// Собирает `-O2` и меряет прогон в миллисекундах.
///
/// `-O2`, а не `-O1` корпуса: мерится порождённый код, а не работа компилятора
/// над ним, и на `-O1` в числе больше шума, чем сигнала.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn timed(name: &str, left: usize, right: usize) -> u128 {
    let text =
        harness::text(&source(left, right)).unwrap_or_else(|error| panic!("{name}: {error}"));
    let dir = Path::new(env!("OUT_DIR")).join(env!("CARGO_CRATE_NAME"));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&file, &text).unwrap();

    let mut compile = Command::new(env!("ADAMAS_CC"));
    compile
        .args(["-std=c11", "-O2", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&file);
    let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    // Список приходит от самого рантайма (`build.rs`), а не написан здесь.
    for unit in env!("ADAMAS_RUNTIME_UNITS").split(',') {
        compile.arg(sources.join(unit));
    }
    let compiled = compile.arg("-o").arg(&binary).output().unwrap();
    assert!(
        compiled.status.success(),
        "{name}: порождённый C не собрался:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let started = Instant::now();
    let run = Command::new(&binary).output().unwrap();
    let elapsed = started.elapsed().as_millis();
    assert!(run.status.success(), "{name}: прогон оборвался");
    // Ответ печатается, и печатать его есть чем: выброси компилятор C работу -
    // печатать стало бы нечего, а ряд мерил бы пустоту.
    assert!(
        !run.stdout.is_empty(),
        "{name}: ответа нет - мерился не счёт"
    );
    elapsed
}
