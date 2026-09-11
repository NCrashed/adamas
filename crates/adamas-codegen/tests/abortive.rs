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
