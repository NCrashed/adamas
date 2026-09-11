//! Абортивная ветка и исключительные exit-points (трек C волны 4, §3.3, §3.4).
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что понижение считает то же,
//! что машина. Здесь стоит то, чего корпус не различает.
//!
//! Различать приходится **цену**, а не ответ, и причина та же, что у соседа
//! `cleanup.rs`: ответ деструктора §3.3 отбрасывает, поэтому различающей по
//! ответу программы в чистом фрагменте не существует. Обрыв к этому добавляет
//! свою половину - его наблюдаемый след и есть то, чего **не** случилось, - и
//! пробы здесь дифференциальные: отличаются одним словом, а сравнивается
//! разница.
//!
//! **Чего здесь нет и почему.** Порядок «ветка, потом деструкторы» - тот же,
//! что у машины (`adamas-interp/src/effect.rs`, `buried`), - свидетеля не имеет
//! и назван таковым: мутант, раскручивающий сегмент до ветки, выжил. Каналов
//! наблюдения два, ответ и число блоков, и ни один его не видит. Ответ - потому
//! что деструкторы отвечают мимо (§3.3); число - потому что кадр хендлера жив
//! до конца раскрутки и держит среду ветки, так что уникальным общее значение
//! не достаётся ни тому, ни другому. Различающая программа появится с живой
//! резумпцией (трек D), где вердикт становится динамическим.

mod harness;

/// Сколько блоков выдал прогон. Течь проверяется по дороге.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Общая шапка проб: список, число, пара и обрывающая метка.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

flip : (1 p : Pair) -> Pair
flip (MkPair a b) = MkPair b a

fst : (1 p : Pair) -> Nat
fst (MkPair a b) = a

effect Fail where
  fail : Nat -> Nat
";

/// Ответ ветки есть ответ **хендлера**, а не значение операции.
///
/// Ответ - список, а не сумма: остаток вычисления за операцией строит `Cons`, и
/// прими понижение ответ ветки за значение операции - список вышел бы длиннее
/// на один элемент, а не другим числом. На сумме та же ошибка сократилась бы.
const ANSWER: &str = "\
asked : {Fail} (List Nat)
asked = Cons (fail Zero) (Cons (Succ Zero) Nil)

main : List Nat
main = handle asked with
  return v -> v
  fail e -> Cons (Succ (Succ Zero)) Nil
";

#[test]
fn the_branch_answers_for_the_handler() {
    let answer = harness::printed(&format!("{SHAPE}{ANSWER}"));
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) Nil",
        "остаток вычисления пережил обрыв"
    );
    allocated("abortive-answer", &format!("{SHAPE}{ANSWER}"));
}

/// Обрыв проходит мимо чужого места `handle` и ловится своим.
///
/// Между операцией и её хендлером стоит второй, живой и хвостово-резумптивный:
/// его кадр срезается тем же сегментом, но ответ обрыва не его. Ответ различает
/// это по построению - ветка `return` внутреннего дописала бы к списку свой
/// элемент, а ветка `return` внешнего свой. Ни один не дописан: обе не бежали.
const NESTED: &str = "\
effect Ask where
  ask : Nat

asked : {Ask, Fail} (List Nat)
asked = Cons ask (Cons (fail Zero) Nil)

nested : {Fail} (List Nat)
nested = handle asked with
  return v -> Cons (Succ Zero) v
  ask -> resume Zero

main : List Nat
main = handle nested with
  return v -> Cons (Succ (Succ Zero)) v
  fail e -> Cons (Succ (Succ (Succ Zero))) Nil
";

#[test]
fn an_alien_abort_passes_the_inner_handler() {
    let source = format!("{SHAPE}{NESTED}");
    assert_eq!(
        harness::printed(&source),
        "Cons (Succ (Succ (Succ Zero))) Nil",
        "обрыв поймал не тот хендлер"
    );
    allocated("abortive-nested", &source);
}

/// Уход отдаёт и **временное**, посчитанное до операции.
///
/// Первый аргумент `Cons` построен, второй обрывается: ячейка первого живёт в
/// C-кадре, узла в IR у неё нет вовсе, и отдать её обязан сам уход. Течь видна
/// числом живых блоков.
const HELD: &str = "\
asked : {Fail} (List Nat)
asked = Cons (Succ (Succ Zero)) (Cons (fail Zero) Nil)

main : List Nat
main = handle asked with
  return v -> v
  fail e -> Nil
";

#[test]
fn the_escape_gives_back_what_it_holds() {
    let source = format!("{SHAPE}{HELD}");
    assert_eq!(harness::printed(&source), "Nil", "обрыв не унёс остаток");
    allocated("abortive-held", &source);
}

/// Раскрутка кончается там, где стоял хендлер, а не на дне стека.
///
/// Под абортивным хендлером стоит второй, живой: его кадр лежит **ниже** и в
/// срезанный сегмент не входит. Раскрути сегмент без пола - и она сняла бы
/// заодно его, а выход из него оказался бы не с вершины.
const FLOOR: &str = "\
effect Ask where
  ask : Nat

inner : {Fail, Ask} Nat
inner = fail ask

middle : {Ask} Nat
middle = handle inner with
  return v -> v
  fail e -> Succ e

main : Nat
main = handle middle with
  return v -> Succ v
  ask -> resume (Succ (Succ Zero))
";

#[test]
fn the_unwinding_stops_where_the_handler_stood() {
    let source = format!("{SHAPE}{FLOOR}");
    assert_eq!(
        harness::printed(&source),
        "Succ (Succ (Succ (Succ Zero)))",
        "живой хендлер под абортивным не пережил раскрутки"
    );
    allocated("abortive-floor", &source);
}

/// Деструктор на исключительном пути: работает и оплачен.
///
/// Проба одна, подставляется тело деструктора - пустое против трёх ячеек.
/// Разница ровно три, и обе половины названы числом: усохни проба до
/// «деструктор ничего не строит» с обеих сторон - разница осталась бы нулём и
/// молчала бы вместе с ним.
const PAID: &str = "\
resource Opened where
  Held : Nat -> Opened
  closeOpened : (1 o : Opened) -> List Nat
  closeOpened (Held n) = ТЕЛО

broken : Opened -> {Fail} Nat
broken o = fail Zero

runFail : ({Fail} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail e -> Succ Zero

main : Nat
main = runFail (broken (Held Zero))
";

#[test]
fn the_destructor_runs_on_the_exceptional_path() {
    let empty = allocated(
        "abortive-empty",
        &format!("{SHAPE}{}", PAID.replace("ТЕЛО", "Nil")),
    );
    let full = allocated(
        "abortive-full",
        &format!(
            "{SHAPE}{}",
            PAID.replace("ТЕЛО", "Cons n (Cons Zero (Cons Zero Nil))")
        ),
    );
    assert_eq!(
        full - empty,
        3,
        "деструктор на обрыве не отработал: {empty} против {full}"
    );
    assert_eq!(
        empty, 13,
        "пустой деструктор на обрыве стоит не тринадцать блоков"
    );
}

/// Нормальный выход второй формы: кадр снимает тот же код, что поставил.
///
/// Обрыва здесь нет вовсе, а кадр `MARK_CLOSING` стоит: его требует
/// **исключительный** путь, и на нормальном он всё равно обязан быть снят.
/// Числа те же дифференциальные - пустое тело деструктора против трёх ячеек.
const NORMAL: &str = "\
resource Opened where
  Held : Nat -> Opened
  closeOpened : (1 o : Opened) -> List Nat
  closeOpened (Held n) = ТЕЛО

quietly : Opened -> {Fail} Nat
quietly o = Succ Zero

runFail : ({Fail} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail e -> Zero

main : Nat
main = runFail (quietly (Held Zero))
";

#[test]
fn the_normal_exit_of_the_second_form_closes_its_frame() {
    let empty = allocated(
        "abortive-normal-empty",
        &format!("{SHAPE}{}", NORMAL.replace("ТЕЛО", "Nil")),
    );
    let full = allocated(
        "abortive-normal-full",
        &format!(
            "{SHAPE}{}",
            NORMAL.replace("ТЕЛО", "Cons n (Cons Zero (Cons Zero Nil))")
        ),
    );
    assert_eq!(
        full - empty,
        3,
        "деструктор на нормальном выходе не отработал: {empty} против {full}"
    );
    assert_eq!(
        empty, 8,
        "пустой деструктор второй формы стоит не восемь блоков"
    );
}

/// Порядок LIFO на исключительном пути: закрывается связанный последним.
///
/// Числа разные потому, что порядок решает, кому пара достанется уникальной:
/// закройся `Note` первым - `flip` копирует, и блоков больше; закройся вторым -
/// переписывает по месту. Следы у деструкторов разные нарочно: `closeNote`
/// строит, `closeTag` разбирает. Два одинаковых дали бы одно число при любом
/// порядке - ровно та форма ошибки, которая сокращается на симметричном пути.
const LIFO: &str = "\
resource Note where
  Written : Pair -> Note
  closeNote : (1 n : Note) -> Pair
  closeNote (Written p) = flip p

resource Tag where
  Marked : Pair -> Tag
  closeTag : (1 t : Tag) -> Nat
  closeTag (Marked p) = fst p

broken : Pair -> {Fail} Nat
broken p =
  let x : ПЕРВЫЙ = СНАЧАЛА p
  let y : ВТОРОЙ = ПОТОМ p
  fail Zero

runFail : ({Fail} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail e -> Succ Zero

main : Nat
main = runFail (broken (MkPair Zero (Succ Zero)))
";

/// Проба с ресурсом `ВТОРОЙ`, связанным последним.
fn lifo(last: &str) -> String {
    let (first, order) = match last {
        "Tag" => ("Note", ("Written", "Marked")),
        _ => ("Tag", ("Marked", "Written")),
    };
    format!(
        "{SHAPE}{}",
        LIFO.replace("ПЕРВЫЙ", first)
            .replace("ВТОРОЙ", last)
            .replace("СНАЧАЛА", order.0)
            .replace("ПОТОМ", order.1)
    )
}

#[test]
fn the_inner_resource_closes_first_when_the_body_aborts() {
    let tag_last = allocated("abortive-tag-last", &lifo("Tag"));
    let note_last = allocated("abortive-note-last", &lifo("Note"));
    assert_eq!(
        tag_last, 20,
        "`Tag` связан последним: закрыться ему первым, и `flip` перепишет пару по месту"
    );
    assert_eq!(note_last, 21, "`Note` связан последним: `flip` копирует");
}

/// Тот же порядок в порождённом коде: кадры ставятся так, как их снимают.
///
/// Раскрутка идёт от вершины (`adamas.h`), поэтому кадр, поставленный
/// **последним**, снимается первым. Текст показывает порядок постановки, цена
/// выше - что наблюдаем именно он.
#[test]
fn the_frames_stand_in_that_order() {
    let text = harness::text(&lifo("Tag")).unwrap_or_else(|error| panic!("{error}"));
    let body = text
        .split_once("/* broken */\nstatic ")
        .and_then(|(_, rest)| rest.split_once("\n}\n"))
        .map_or_else(
            || panic!("`broken` не порождена:\n{text}"),
            |(body, _)| body,
        );
    let note = body
        .find("/* деструктор closeNote */")
        .unwrap_or_else(|| panic!("`closeNote` кадром не стоит:\n{body}"));
    let tag = body
        .find("/* деструктор closeTag */")
        .unwrap_or_else(|| panic!("`closeTag` кадром не стоит:\n{body}"));
    assert!(
        note < tag,
        "кадр `Tag` поставлен не последним, а снимается первым:\n{body}"
    );
}

/// Обрыв деструктора: операция к погибшему хендлеру рубит его остаток.
///
/// `closeLoud` производит `fail`, а его хендлер ответ уже дал - запись вектора
/// подавлена, и `adamas_kont_abort` снимает кадры **этого** деструктора.
/// Остаток его не бежит, а раскрутка ниже продолжается.
///
/// Наблюдается это тем, чего не случилось, поэтому проба тройная. Хвост
/// `closeLoud` - подставляемый: пустой против трёх ячеек. Обрыв есть - числа
/// равны; обрыва нет - разница три. Соседний `closeQuiet` меняется тем же
/// подстановочным хвостом отдельно, и его три ячейки платятся всегда: это и
/// значит «раскрутка ниже продолжается».
const SUPPRESSED: &str = "\
resource Loud where
  Shouted : Nat -> Loud
  closeLoud : (1 l : Loud) -> {Fail} List Nat
  closeLoud (Shouted n) =
    let heard : Nat = ОПЕРАЦИЯ
    ГРОМКО

resource Quiet where
  Hushed : Nat -> Quiet
  closeQuiet : (1 q : Quiet) -> List Nat
  closeQuiet (Hushed n) = ТИХО

broken : Loud -> Quiet -> {Fail} Nat
broken l q = fail Zero

runFail : ({Fail} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail e -> Succ Zero

main : Nat
main = runFail (broken (Shouted Zero) (Hushed Zero))
";

/// Проба: зовёт ли `closeLoud` операцию и что строят оба деструктора.
fn suppressed(operation: bool, loud: bool, quiet: bool) -> String {
    let cells = "Cons n (Cons Zero (Cons Zero Nil))";
    format!(
        "{SHAPE}{}",
        SUPPRESSED
            .replace("ОПЕРАЦИЯ", if operation { "fail Zero" } else { "Zero" })
            .replace("ГРОМКО", if loud { cells } else { "Nil" })
            .replace("ТИХО", if quiet { cells } else { "Nil" })
    )
}

#[test]
fn a_dead_handler_cuts_the_rest_of_its_destructor() {
    // Обрыва нет: хвост `closeLoud` оплачен, разница три.
    let quiet_short = allocated("abortive-live-short", &suppressed(false, false, false));
    let quiet_long = allocated("abortive-live-long", &suppressed(false, true, false));
    assert_eq!(
        quiet_long - quiet_short,
        3,
        "хвост деструктора не оплачен и без обрыва: {quiet_short} против {quiet_long}"
    );

    // Обрыв есть: тот же хвост не бежит вовсе, и числа равны.
    let cut_short = allocated("abortive-cut-short", &suppressed(true, false, false));
    let cut_long = allocated("abortive-cut-long", &suppressed(true, true, false));
    assert_eq!(
        cut_long, cut_short,
        "остаток оборванного деструктора всё-таки побежал"
    );

    // Раскрутка ниже продолжается: сосед платит свои три при том же обрыве.
    let next = allocated("abortive-cut-next", &suppressed(true, false, true));
    assert_eq!(
        next - cut_short,
        3,
        "раскрутка встала на обрыве: сосед не отработал"
    );
}
