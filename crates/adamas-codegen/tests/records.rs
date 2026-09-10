//! Запись в понижении: объект кучи со слотом на поле (§4.2).
//!
//! Половина первая трека `Array n Vec3` (§10 вопрос 154): запись понижается
//! **обычным боксированным объектом**, плотной укладки здесь нет вовсе. Порядок
//! половин обязателен - иначе не видно, что чинит какая.
//!
//! Наблюдаемое здесь - числа и строки, а не «скомпилировалось». Слот от слота
//! отличает только значение: три поля одного типа типизируются одинаково, и
//! проекция, промахнувшаяся полем, проходит проверку молча. Поэтому у каждого
//! свидетеля ответ **зависит от номера слота**, а у печати - от порядка полей.

mod harness;

/// Построение и проекция: ответ называет тот слот, который написан.
///
/// Поля различны нарочно и все три: возьми проекция соседний слот - ответ
/// сменится, и сменится он на любом из двух соседей. `Colour` рекурсивен
/// нарочно - рекурсивное семейство не плоское (§4.11), - и потому запись
/// здесь **объект кучи**: плотную укладку меряет `packed.rs`.
const FIELDS: &str = "\
data Colour where
  Red : Colour
  Green : Colour
  Blue : Colour
  Deep : Colour -> Colour

type Triple = { first : Colour, second : Colour, third : Colour }

main : Colour
main =
  let made : Triple = { first = Red, second = Green, third = Blue }
  made.third
";

/// Печать: поля идут как написаны, значение поля скобок не требует.
///
/// Написаны они **не** по алфавиту нарочно: сортировка меток - первое, чем
/// хочется раздать слоты, и здесь она видна разошедшейся строкой. Отрицательное
/// поле - второе: аргумент конструктора берётся в скобки, поле записи нет
/// (§4.2, `Pos::Free` против `Pos::Atom`), и `(-1)` вместо `-1` показывает
/// промах позиции.
const PRINTED: &str = "\
type Answer = { total : Int64, delta : Int64 }

main : Answer
main = { total = 7, delta = -1 }
";

/// Запись под конструктором: скобки нужны, и они от позиции.
const NESTED: &str = "\
data Bit where
  Off : Bit
  On : Bit

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

type Point = { x : Bit, y : Bit }

main : List Point
main = Cons { x = Off, y = On } (Cons { x = On, y = Off } Nil)
";

/// Форма потеряна: поле полиморфного конструктора объявлено указательным.
const SHAPELESS: &str = "\
data Bit where
  Off : Bit
  On : Bit

data Box (a : Type) where
  MkBox : a -> Box a

type Point = { x : Bit }

taken : Box Point -> Bit
taken (MkBox p) = p.x

main : Bit
main = taken (MkBox { x = On })
";

/// Ближайший проходящий сосед: та же проекция без потери формы.
const SHAPED: &str = "\
data Bit where
  Off : Bit
  On : Bit

type Point = { x : Bit }

taken : Point -> Bit
taken p = p.x

main : Bit
main = taken { x = On }
";

/// Написанный порядок разошёлся с объявленным.
const REORDERED: &str = "\
data Bit where
  Off : Bit
  On : Bit

type Pair = { left : Bit, right : Bit }

made : Pair
made = { right = On, left = Off }

main : Bit
main = made.left
";

/// Ближайший проходящий сосед: тот же тип, написанный по порядку.
const ORDERED: &str = "\
data Bit where
  Off : Bit
  On : Bit

type Pair = { left : Bit, right : Bit }

made : Pair
made = { left = Off, right = On }

main : Bit
main = made.left
";

/// Слот от слота отличается значением, а не типом.
///
/// Три поля одного типа: промах проекции типизируется, и увидеть его можно
/// только ответом.
#[test]
fn a_projection_takes_the_named_slot_and_not_its_neighbour() {
    let stderr = harness::agreed("record-fields", FIELDS).unwrap_or_else(|error| {
        panic!("поля записи: {error}");
    });
    assert_eq!(
        harness::printed(FIELDS),
        "Blue",
        "свидетель перестал различать слоты"
    );
    let (allocated, live) = harness::blocks("record-fields", &stderr);
    // Одна запись - **один** блок: три поля лежат слотами внутри него, а не
    // тремя объектами. Значения полей ячеек не стоят - конструкторы нульарные
    // и непосредственны.
    assert_eq!(allocated, 1, "запись стоила не одного блока");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Печать записи совпадает с `adamas eval` формой, порядком и скобками.
#[test]
fn a_record_prints_as_the_interpreter_prints_it() {
    assert_eq!(
        harness::printed(PRINTED),
        "{total = 7, delta = -1}",
        "печать машины изменилась - свидетель говорит не о том"
    );
    harness::agreed("record-printed", PRINTED).unwrap_or_else(|error| {
        panic!("печать записи: {error}");
    });
}

/// Запись в позиции аргумента берётся в скобки, как всякое составное.
#[test]
fn a_record_under_a_constructor_is_parenthesised() {
    let printed = harness::printed(NESTED);
    assert!(
        printed.contains("({x = Off, y = On})"),
        "печать машины изменилась: {printed}"
    );
    harness::agreed("record-nested", NESTED).unwrap_or_else(|error| {
        panic!("вложенная запись: {error}");
    });
}

/// Проекция из значения без формы отвергается по имени.
#[test]
fn a_projection_without_a_shape_is_refused_by_name() {
    let refused = harness::compiled(SHAPELESS).expect_err("форма потеряна: слота брать неоткуда");
    let said = refused.to_string();
    assert!(
        said.contains("форма записи потеряна"),
        "отказ назвал не ту причину: {said}"
    );
    harness::agreed("record-shaped", SHAPED).unwrap_or_else(|error| {
        panic!("ближайший сосед: {error}");
    });
}

/// Запись, написанная не в порядке своего типа, отвергается.
///
/// Слоты раздаёт написанный порядок, а печать идёт по слотам; перестановка
/// молча разошлась бы с `adamas eval`. Названная граница, а не правило языка:
/// §4.2 такую запись разрешает, и снимается граница перестановкой печати, а не
/// перестановкой слотов.
#[test]
fn a_record_written_out_of_its_declared_order_is_refused() {
    let refused = harness::compiled(REORDERED).expect_err("порядок полей разошёлся с объявленным");
    let said = refused.to_string();
    // `Pair` из двух `Bit` укладывается плотно (§10 вопрос 157), и отказ
    // приходит от плоской записи; правило то же - позиция в позицию.
    assert!(
        said.contains("поля плоской записи") && said.contains("{right, left}"),
        "отказ назвал не ту причину: {said}"
    );
    // Сосед отличается одним - порядком написания, - и берёт то же поле.
    harness::agreed("record-ordered", ORDERED).unwrap_or_else(|error| {
        panic!("ближайший сосед: {error}");
    });
}
