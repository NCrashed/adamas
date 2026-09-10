//! Вставка деструктора ресурса на нормальном выходе (§3.3) в понижении.
//!
//! # Чем здесь вообще можно свидетельствовать
//!
//! Ответ деструктора §3.3 отбрасывает. Чистое вычисление, чей ответ отброшен,
//! значения программы не меняет, поэтому **различающей по ответу программы в
//! чистом фрагменте не существует**: наблюдаемого следа, кроме ответа, у
//! чистого вычисления нет. Это не «свидетель не нашёлся» - это свойство
//! фрагмента, и оно измерено, а не предположено: `eval/resource` различает
//! порядок деструкторов эффектом `Log`, а эффектов понижение не берёт (§10
//! вопрос 161).
//!
//! Наблюдаема поэтому **цена**, и она наблюдаема числом - тем же счётчиком
//! блоков, каким считают reuse (`perceus.rs`), плоское значение (`flat.rs`) и
//! массив (`array.rs`). Утверждений четыре, и все дифференциальные: одно
//! число не говорит ничего, говорит разница между двумя программами, которые
//! отличаются одним словом.
//!
//! - *Деструктор отработал, и его работа оплачена.* Проба одна, подставляется
//!   в неё только тело деструктора: пустое против трёх ячеек
//!   ([`the_destructor_body_is_paid_for`]). Разница ровно три - те самые
//!   ячейки. Не позови понижение деструктор - обе пробы стоили бы одинаково.
//! - *Порядок LIFO.* Проба одна, и меняется в ней только то, какой ресурс
//!   связан последним ([`the_inner_resource_closes_first`]). Оба деструктора
//!   держат **одну** пару, и уникальной она достаётся тому, кто зовётся
//!   вторым; ячейку переиспользует только он. Отсюда 5 против 6.
//! - *Тот же порядок виден в порождённом коде* ([`the_calls_stand_in_that_order`]).
//!   Текстовый свидетель стоит рядом с ценовым нарочно: цена говорит, что
//!   порядок наблюдаем, текст - что наблюдаем именно порядок вызовов, а не
//!   что-то ещё.
//! - *Оба ответа scope'а везут своё представление* - свой и деструкторский
//!   ([`each_answer_keeps_its_own_representation`]). Проба идёт двумя
//!   подстановками, и обе внутри себя несимметричны: на симметричной
//!   перестановка двух представлений сокращается, и мутант выживает.
//!
//! Договор с `adamas eval` каждая проба проходит по дороге ([`harness::agreed`]),
//! и живых блоков после неё ноль. Корпусный свидетель -
//! `tests/golden/eval/resource-cleanup.adamas`, он же в списке `TAKEN`
//! соседнего файла.

mod harness;

/// Сколько блоков выдал прогон. Ответ по дороге сверен с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Ресурс, чей деструктор строит список. Подставляется его тело.
///
/// `n` в теле называется однажды: поле линейного связывания линейно (§3.3), и
/// три упоминания отверглись бы учётом использований, а не понижением.
const LEDGER: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

resource Ledger where
  Opened : Nat -> Ledger
  closeLedger : (1 l : Ledger) -> List Nat
  closeLedger (Opened n) = ТЕЛО

held : Ledger -> List Nat
held l = Cons Zero Nil

main : List Nat
main = held (Opened Zero)
";

/// Ячеек, которые строит непустое тело деструктора.
const CELLS: usize = 3;

/// Два ресурса на одну пару; меняется только порядок связывания.
///
/// Пара разделена между `Written` и `Marked`, поэтому `flip` переписывает
/// ячейку по месту только у того деструктора, которому пара досталась
/// **уникальной**, - то есть у второго. Первый платит ячейку.
///
/// Следы у деструкторов разные нарочно: `closeNote` строит, `closeTag`
/// разбирает. Два одинаковых деструктора дали бы одно число при любом порядке.
const LIFO: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

flip : (1 p : Pair) -> Pair
flip (MkPair a b) = MkPair b a

fst : (1 p : Pair) -> Nat
fst (MkPair a b) = a

resource Note where
  Written : Pair -> Note
  closeNote : (1 n : Note) -> Pair
  closeNote (Written p) = flip p

resource Tag where
  Marked : Pair -> Tag
  closeTag : (1 t : Tag) -> Nat
  closeTag (Marked p) = fst p

sealed : ПЕРВЫЙ -> ВТОРОЙ -> Nat
sealed x y = Succ Zero

main : Nat
main =
  let p : Pair = MkPair Zero (Succ Zero)
  sealed (СНАЧАЛА p) (ПОТОМ p)
";

/// Проба с ресурсом `ВТОРОЙ`, связанным последним.
fn lifo(last: &str) -> String {
    let (first, order) = match last {
        "Tag" => ("Note", ("Written", "Marked")),
        _ => ("Tag", ("Marked", "Written")),
    };
    LIFO.replace("ПЕРВЫЙ", first)
        .replace("ВТОРОЙ", last)
        .replace("СНАЧАЛА", order.0)
        .replace("ПОТОМ", order.1)
}

/// Представления двух ответов scope'а: своего и деструкторского (§4.11).
///
/// Вставка берёт представление **у значения**, а не назначает указательным.
/// Назначь ответу scope'а - и плоское значение поехало бы через слот, которого
/// у него нет; назначь ответу деструктора - и биты числа попали бы в
/// `adamas_drop_value`.
///
/// Проба идёт **двумя** подстановками, и обе внутри себя **несимметричны**:
/// плоский ответ при указательном деструкторе и наоборот. Симметричная - обе
/// позиции одного представления - не показывает ничего: перестановка двух
/// представлений между собой на ней сокращается, и мутант выживает. Измерено, а
/// не предположено.
const SHAPES: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

resource Gauge where
  Set : Int64 -> Gauge
  closeGauge : (1 g : Gauge) -> ТИПЗАКРЫТИЯ
  closeGauge (Set v) = ТЕЛОЗАКРЫТИЯ

reading : Gauge -> ОТВЕТ
reading g =
  let seen : ОТВЕТ = ВИДНО
  seen

main : ОТВЕТ
main =
  let start : Int64 = 3
  reading (Set start)
";

/// Проба с плоским ответом scope'а либо с плоским ответом деструктора.
fn shapes(flat_answer: bool) -> String {
    let (answer, seen, closed, closing) = if flat_answer {
        ("Int64", "7", "Nat", "Succ Zero")
    } else {
        ("Nat", "Succ Zero", "Int64", "v")
    };
    SHAPES
        .replace("ОТВЕТ", answer)
        .replace("ВИДНО", seen)
        .replace("ТИПЗАКРЫТИЯ", closed)
        .replace("ТЕЛОЗАКРЫТИЯ", closing)
}

/// Работа деструктора оплачена: пустое тело против трёх ячеек.
///
/// Разница ровно [`CELLS`], потому что ничего другого между пробами не
/// меняется: ячейка самого `Opened` выдаётся и там, и там, а ответ у обеих
/// один - `Cons Zero Nil`. Не звался бы деструктор - разницы не было бы вовсе.
#[test]
fn the_destructor_body_is_paid_for() {
    let empty = allocated("cleanup-empty", &LEDGER.replace("ТЕЛО", "Nil"));
    let full = allocated(
        "cleanup-full",
        &LEDGER.replace("ТЕЛО", "Cons n (Cons Zero (Cons Zero Nil))"),
    );
    assert_eq!(
        full - empty,
        CELLS,
        "работа деструктора не оплачена: {empty} против {full}"
    );
    // Обе половины названы числом, а не только их разница: усохни проба до
    // «деструктор ничего не строит» с обеих сторон - разница осталась бы нулём
    // и молчала бы вместе с ним.
    assert_eq!(empty, 2, "пустой деструктор стоит не два блока");
}

/// Порядок LIFO: закрывается тот, кто связан последним.
///
/// Числа разные потому, что порядок решает, кому пара достанется уникальной:
/// закройся `Note` первым - `flip` копирует, и блоков шесть; закройся вторым -
/// переписывает по месту, и блоков пять.
#[test]
fn the_inner_resource_closes_first() {
    let tag_last = allocated("cleanup-tag-last", &lifo("Tag"));
    let note_last = allocated("cleanup-note-last", &lifo("Note"));
    assert_eq!(tag_last, 5, "`Tag` связан последним: закрыться ему первым");
    assert_eq!(note_last, 6, "`Note` связан последним: `flip` копирует");
}

/// Каждый из двух ответов доезжает своим представлением.
///
/// Главное здесь не число, а сверка с `adamas eval` по дороге: объяви вставка
/// позицию не тем представлением - не сошлось бы ничего. Числа тем не менее
/// названы, и они разные. **Один** блок там, где ответ scope'а плоский:
/// деструктор строит `Succ Zero` на ячейке `Set`, потому что слот у обоих один
/// и ячейка достаётся переиспользованием (§5.1). **Два** там, где плоский
/// ответ деструктора: указательный ответ scope'а построен до него, ячейку `Set`
/// занять нечем, и она просто освобождается.
#[test]
fn each_answer_keeps_its_own_representation() {
    assert_eq!(allocated("cleanup-flat-answer", &shapes(true)), 1);
    assert_eq!(allocated("cleanup-flat-closing", &shapes(false)), 2);
}

/// Тот же порядок в порождённом коде: вызовы стоят так, как их зовут.
///
/// Читается по комментариям эмиттера - именам определений рядом с вызовом.
/// Свидетель текстовый, и это названо: цена выше показывает, что порядок
/// наблюдаем, а текст - что наблюдаем именно он.
#[test]
fn the_calls_stand_in_that_order() {
    let text = harness::text(&lifo("Tag")).unwrap_or_else(|error| panic!("{error}"));
    // Тело `sealed`: от её заголовка до закрывающей скобки. Заголовок ищется
    // вместе со `static`, потому что то же имя стоит комментарием у **места
    // вызова**, и оно в тексте раньше.
    let body = text
        .split_once("/* sealed */\nstatic ")
        .and_then(|(_, rest)| rest.split_once("\n}\n"))
        .map_or_else(
            || panic!("`sealed` не порождена:\n{text}"),
            |(body, _)| body,
        );
    let closes_tag = body
        .find("/* closeTag */")
        .unwrap_or_else(|| panic!("`closeTag` не зовётся:\n{body}"));
    let closes_note = body
        .find("/* closeNote */")
        .unwrap_or_else(|| panic!("`closeNote` не зовётся:\n{body}"));
    assert!(closes_tag < closes_note, "порядок вызовов не LIFO:\n{body}");
}
