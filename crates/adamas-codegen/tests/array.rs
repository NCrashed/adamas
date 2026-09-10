//! Плоские массивы и дескрипторы layout в понижении (§4.11).
//!
//! §4.11 говорит про массив три вещи, и каждая здесь показана прогоном.
//!
//! - *При `Flat a` - `n × size(a)` байт подряд.* Один объект кучи на всю
//!   длину: счётчик блоков показывает **одну** аллокацию
//!   ([`a_flat_array_costs_one_block`]).
//! - *Иначе - `n` указателей.* Та же программа над не-`Flat` элементом стоит
//!   ячейку на элемент сверх самого массива
//!   ([`a_pointer_array_costs_a_block_per_element`]). Свидетель
//!   дифференциальный: одно число не говорит ничего, говорит разница.
//! - *Обобщённый код получает дескриптор обычным имплиситом.* Одна и та же
//!   функция понижается двумя путями - специализированным и по дескриптору, -
//!   и оба дают тот же ответ, что `adamas eval`
//!   ([`generic_code_indexes_by_the_descriptor`]).
//!
//! Ответ каждой программы по дороге сверяется с `adamas eval`
//! ([`harness::agreed`]): счётчик показывает цену, а сверка - что цена
//! заплачена за то же самое значение.

mod harness;

/// Сколько блоков выдал прогон специализированного терма.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// То же для терма без специализации - обобщённого пути (§4.11).
fn allocated_as_written(name: &str, source: &str) -> usize {
    let stderr =
        harness::as_written(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Ячеек в массиве. Три - чтобы разница считалась, а не угадывалась.
const CELLS: usize = 3;

/// Одна и та же программа над плоским элементом и над указательным.
///
/// Форма у обеих одна дословно: массив на три ячейки, две перезаписи, чтение
/// нулевой. Разошлись они только элементом - `Int64` против `Cell`, - и по
/// этому же разошлись в цене.
///
/// `Cell` завёрнут нарочно тонко: одно поле, и то плоское. Возьми элемент
/// потолще - разница показывала бы вес элемента, а не наличие у него
/// заголовка.
const SHAPE: &str = "\
type Int = Int64

data Cell where
  MkCell : Int64 -> Cell

peel : Cell -> Int64
peel (MkCell n) = n
";

/// Плоский массив: `n × size` байт подряд, одна аллокация на всю длину.
///
/// `arraySet` при этом не аллоцирует вовсе: блок уникален (`rc == 0`), и
/// запись идёт по месту - тот же договор, что у reuse (§5.1). Число поэтому
/// **одно** независимо от числа перезаписей.
const FLAT: &str = "\
built : Array 3 Int64
built = arraySet (arraySet (arrayNew 3 7) 1 8) 2 9

main : Int64
main = arrayIndex built 0
";

/// Та же программа над не-`Flat` элементом.
const BOXED: &str = "\
built : Array 3 Cell
built = arraySet (arraySet (arrayNew 3 (MkCell 7)) 1 (MkCell 8)) 2 (MkCell 9)

main : Int64
main = peel (arrayIndex built 0)
";

/// Плоский массив - один блок на всю длину.
///
/// Это ABI, а не оптимизация: у плоского элемента заголовка нет вовсе, а
/// заголовок и есть то, ради чего выдаётся блок.
#[test]
fn a_flat_array_costs_one_block() {
    assert_eq!(
        allocated("массив-плоский", &format!("{SHAPE}{FLAT}")),
        1,
        "плоский массив обошёлся не в один блок: элементы лежат подряд (§4.11)"
    );
}

/// Указательный массив стоит ячейку на элемент - и это тот же тип в исходнике.
///
/// Совпади оба числа, первый свидетель не показывал бы ничего: «один блок»
/// бывает и у массива, чьи элементы просто дешёвые.
#[test]
fn a_pointer_array_costs_a_block_per_element() {
    let flat = allocated("массив-плоский-цена", &format!("{SHAPE}{FLAT}"));
    let boxed = allocated("массив-указательный", &format!("{SHAPE}{BOXED}"));
    assert_eq!(
        boxed - flat,
        CELLS,
        "указательный элемент обязан стоить блок: плоский {flat}, указательный \
         {boxed}, ячеек {CELLS}"
    );
}

/// Обобщённая функция над `{Flat a}` рядом с той же программой без неё.
const GENERIC: &str = "\
type Int = Int64

type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

rotate : {Flat a} => Array 3 a -> Array 3 a
rotate xs = arraySet xs 0 (arrayIndex xs 1)

built : Array 3 Int64
built = arraySet (arraySet (arrayNew 3 7) 1 8) 2 9

main : Int64
main = arrayIndex (rotate built) 0
";

/// Обобщённый код индексирует с рантайм-шагом и отвечает то же.
///
/// Три утверждения, и ни одно не выводится из остальных. Ответ сходится с
/// `adamas eval` на **обоих** путях - до специализации и после, - то есть
/// договор `mono` держится и на массивах. Цена одна и та же: дескриптор блока
/// не занимает. И шаг в порождённом коде действительно рантаймовый - иначе
/// первые два утверждения выполнялись бы и у понижения, втихую взявшего
/// указательный путь.
#[test]
fn generic_code_indexes_by_the_descriptor() {
    let specialised = allocated("массив-обобщённый-после", GENERIC);
    let written = allocated_as_written("массив-обобщённый-до", GENERIC);
    assert_eq!(
        (specialised, written),
        (1, 1),
        "дескриптор стоил блока: он значение, а не объект (§4.11)"
    );

    let text = harness::written_text(GENERIC).unwrap_or_else(|error| panic!("{error}"));
    let generic = body_of(&text, "rotate");
    // Читается **текст**, и это единственный способ здесь: шаг, взятый у
    // `align` вместо `size`, ни одним значением не отличим - у всякого
    // примитива §4.11 размер равен выравниванию. Отличать их станет чем, когда
    // плоским элементом станет агрегат.
    assert!(
        generic.contains(".size"),
        "обобщённая функция индексирует не по дескриптору:\n{generic}"
    );
    assert!(
        generic.contains("adamas_array_at"),
        "обобщённая функция вовсе не индексирует:\n{generic}"
    );
    // Специализированный путь обязан от него отличаться, иначе «два пути» -
    // одно и то же понижение под двумя именами.
    let specialised = harness::text(GENERIC).unwrap_or_else(|error| panic!("{error}"));
    assert!(
        !body_of(&specialised, "rotate").contains(".size"),
        "специализация шаг не сняла: константы в ней нет"
    );
}

/// Плоский массив не проходит туда, где ждут указательный.
///
/// Граница названа §5.1: передача значения в позицию, скомпилированную по
/// указательному представлению, есть **боксирование**, и боксирования этот
/// срез не делает. Функция без `{Flat a}` компилируется по указательному
/// представлению - так §4.11 и говорит, - поэтому плоский массив в неё не
/// уходит, и отказ это называет.
const CROSSING: &str = "\
type Int = Int64

same : Array 3 a -> Array 3 a
same xs = xs

through : Array 3 Int64 -> Array 3 Int64
through xs = same xs

built : Array 3 Int64
built = arrayNew 3 7

main : Int64
main = arrayIndex (through built) 0
";

/// Отказ на переходе плоского массива в указательный код назван.
#[test]
fn a_flat_array_does_not_enter_pointer_code() {
    let error = harness::compiled(CROSSING).expect_err("плоский массив в указательный код");
    let text = error.to_string();
    assert!(
        text.contains("§4.11") && text.contains("плоский массив"),
        "отказ не назвал причину представлением: {text}"
    );
}

/// Шаг индексации - ширина элемента, а не ширина слова.
///
/// `Int64` этого не различает: восемь байт у него и так, и так, - и мутант
/// «индексировать словом» на нём выживает. Здесь элемент **узкий**: три
/// `Int16` занимают шесть байт целиком, и чтение словом ушло бы за них.
/// Ответ различает не длину массива, а адрес ячейки: читаются первая и вторая,
/// и множитель разводит их между собой.
const NARROW: &str = "\
-- Умолчание литерала идёт **по имени** (§4.3), и заслонившее объявление его
-- меняет: здесь `Int` есть `Int16`, поэтому написанные числа узкие.
type Int = Int16

narrow : Array 3 Int16
narrow = arraySet (arraySet (arrayNew 3 1) 1 2) 2 3

-- Массив передаётся аргументом однажды: определение без параметров понижение
-- не кеширует, и `narrow` дважды означало бы два массива.
read : Array 3 Int16 -> Int16
read xs = addInt16 (arrayIndex xs 1) (mulInt16 (arrayIndex xs 2) 10)

-- 2 + 3 * 10 = 32
main : Int16
main = read narrow
";

/// Узкий элемент индексируется своей шириной.
#[test]
fn a_narrow_element_keeps_its_own_stride() {
    assert_eq!(
        allocated("массив-узкий", NARROW),
        1,
        "узкий массив обошёлся не в один блок"
    );
    let text = harness::text(NARROW).unwrap_or_else(|error| panic!("{error}"));
    assert!(
        text.contains("adamas_array_alloc((size_t)t0, 2u)"),
        "массив `Int16` заведён не шагом в два байта:\n{text}"
    );
}

/// То же **эта-свёрнуто**: аргумент не написан, а достроен по типу.
///
/// Свидетель другого стража: написанный аргумент проверяет `shaped`, а
/// достроенный - отдельная сверка в `given`, у которой до массивов свидетеля
/// не было вовсе (измерено: сними её, и корпус оставался зелёным). Разойтись
/// им стало чем ровно теперь: один и тот же написанный тип `Array 3 a`
/// читается плоским там, где в контексте есть `Flat a`, и указательным там,
/// где его нет.
///
/// Ответ у обеих сторон **не массив**, и это существенно: с массивом в ответе
/// раньше сработала бы сверка результата, а страж аргумента остался бы без
/// свидетеля - мутант это и показал.
const FOLDED: &str = "\
type Int = Int64

size : Array 3 a -> UInt64
size xs = 3

through : Array 3 Int64 -> UInt64
through = size

built : Array 3 Int64
built = arrayNew 3 7

main : UInt64
main = through built
";

/// Достроенный аргумент сверяется по представлению так же, как написанный.
#[test]
fn a_supplied_argument_is_checked_by_its_representation() {
    let error = harness::compiled(FOLDED).expect_err("плоский массив в указательный код");
    let text = error.to_string();
    assert!(
        text.contains("§4.11") && text.contains("плоский массив"),
        "отказ не назвал причину представлением: {text}"
    );
}

/// Ближайший проходящий сосед: та же программа, где обе стороны плоские.
#[test]
fn the_same_program_with_both_sides_flat_passes() {
    let source = "\
type Int = Int64

same : Array 3 Int64 -> Array 3 Int64
same xs = xs

built : Array 3 Int64
built = arrayNew 3 7

main : Int64
main = arrayIndex (same built) 0
";
    assert_eq!(allocated("сосед-массив", source), 1);
}

/// Ответ программы массивом отвергается названной причиной.
///
/// Печать массива не сделана, и молчать об этом нельзя: `adamas eval` печатает
/// цепочку `arrayNew`/`arraySet`, а понижение - значение со слотами.
#[test]
fn an_array_answer_is_refused() {
    let source = "\
type Int = Int64

main : Array 3 Int64
main = arrayNew 3 7
";
    let error = harness::compiled(source).expect_err("массив в ответе");
    assert!(
        error.to_string().contains("печатать его нечем"),
        "отказ не назвал причину: {error}"
    );
}

/// Тело функции по имени из исходника: эмиттер пишет его комментарием.
///
/// По комментарию, а не по номеру `fn_N`: номера раздаёт понижение, и
/// специализированный путь нумерует иначе. Специализированное имя начинается
/// с исходного (`rotate@_,_`), поэтому ищется приставка.
fn body_of<'a>(text: &'a str, name: &str) -> &'a str {
    let head = format!("\n/* {name}");
    // Тем же комментарием эмиттер помечает **вызов**, поэтому годится лишь
    // тот, за которым идёт объявление: иначе свидетель читал бы тело
    // вызывающего.
    let mut from = 0;
    while let Some(at) = text[from..].find(&head) {
        let start = from + at + 1;
        from = start;
        let rest = &text[start..];
        if !rest
            .lines()
            .nth(1)
            .is_some_and(|it| it.starts_with("static "))
        {
            continue;
        }
        let Some(end) = rest.find("\n}\n") else {
            panic!("тело `{name}` не кончается");
        };
        return &rest[..end];
    }
    panic!("в порождённом C нет функции `{name}`");
}
