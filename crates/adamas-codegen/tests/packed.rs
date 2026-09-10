//! Плоский агрегат и колонка `Array n Vec3` (§4.11, §10 вопрос 154).
//!
//! Половина вторая трека: запись из плоских полей укладывается **плотно**, а не
//! слотами объекта кучи, и массив из неё - один блок на всю длину. Первая
//! половина - `records.rs`, и без неё эта не читалась бы: там запись понижается
//! обычным объектом, здесь - становится байтами.
//!
//! # Чем это проверяется
//!
//! Тремя вещами, и все три - числа.
//!
//! *Ответ* сверяется с `adamas eval` и зависит **и от поля, и от номера
//! ячейки**: массив одинаковых `Vec3` не различал бы ячеек, чтение одного поля
//! - смещений.
//!
//! *Число блоков*: колонка из трёх `Vec3` стоит **один** блок, тот же код над
//! не-плоским элементом - четыре.
//!
//! *Байты* видны в порождённом тексте и проверены `_Static_assert`'ом в нём же:
//! `Vec3` - 12 байт при границе 4, шаг индексации 12, смещения 0/4/8. Числа
//! эти - вторая запись правила §4.11 (первая - `adamas-elab/src/flat.rs`), и
//! [`the_layout_matches_the_type_side`] требует, чтобы записи сошлись.

mod harness;

use std::path::Path;

/// Колонка `Vec3`: та же программа, что в корпусе, но здесь считаются блоки.
fn column() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval/array-aggregate.adamas");
    std::fs::read_to_string(path).unwrap_or_else(|error| panic!("корпус: {error}"))
}

/// Тот же код над **не-плоским** элементом.
///
/// `Cell` несёт указатель, и §4.11 велит компилировать такой массив в `n`
/// указателей на объекты Perceus. Разница с колонкой - ровно числом блоков, и
/// ради неё программы держатся одинаковыми во всём прочем.
const POINTING: &str = "\
-- Wrap рекурсивен нарочно: рекурсивное семейство не плоское (§4.11), и
-- запись с таким полем остаётся объектом кучи - семейство из одних плоских
-- полей теперь укладывается плотно само (§10 вопрос 157). Нульарный Tip
-- непосредственен и ячеек не занимает, поэтому в счёте блоков остаётся
-- ровно то, ради чего он ведётся, - массив и объект-запись на элемент.
data Wrap where
  Tip : Wrap
  W : Wrap -> Wrap

type Cell = { it : Wrap }

first : Cell
first = { it = Tip }

second : Cell
second = { it = Tip }

third : Cell
third = { it = Tip }

built : Array 3 Cell
built = arraySet (arraySet (arrayNew 3 first) 1 second) 2 third

read : Array 3 Cell -> Wrap
read xs = (arrayIndex xs 2).it

main : Wrap
main = read built
";

/// Плоский агрегат в поле конструктора: упаковка на границе указателя.
///
/// `Cons` берёт поле указателем, и агрегат туда не ложится байтами: §4.11
/// требует плотной укладки от **массива**, а список говорит слотами. Значение
/// печатается, и печать эта совпадает с `adamas eval` - то есть упаковка
/// сохранила и поля, и их порядок.
const BOXING: &str = "\
data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

type Pair = { lo : Int32, hi : Int32 }

low : Pair
low = { lo = 1, hi = 2 }

high : Pair
high = { lo = 30, hi = 40 }

main : List Pair
main = Cons low (Cons high Nil)
";

/// Два пути к одному шагу: дескриптор из контекста и константа из укладки.
///
/// Свидетель нужен ровно **размеру** агрегата. Ошибка в нём сокращается, когда
/// пишет и читает один и тот же путь: положи `Vec3` в 24 байта вместо
/// двенадцати - и статический путь останется согласован сам с собой. Здесь
/// путей два в одной программе: `built` укладывает ячейки константой понижения,
/// а `rotate` индексирует полем дескриптора, который посчитала **типовая
/// сторона**. Разойдись два числа - `rotate` возьмёт байты не с той ячейки.
const TWO_WAYS: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

type V3 (a : Type) = { x : a, y : a, z : a }
type Vec3 = V3 Float32

-- Ячейка 0 занимает то, что лежало в ячейке 1; ячейка 1 не трогается.
rotate : {Flat a} => Array 3 a -> Array 3 a
rotate xs = arraySet xs 0 (arrayIndex xs 1)

first : Vec3
first = { x = 1.0, y = 2.0, z = 3.0 }

second : Vec3
second = { x = 10.0, y = 20.0, z = 30.0 }

third : Vec3
third = { x = 100.0, y = 200.0, z = 300.0 }

built : Array 3 Vec3
built = arraySet (arraySet (arrayNew 3 first) 1 second) 2 third

-- 30.0: поле `z` ячейки, приехавшей из первой.
main : Float32
main = (arrayIndex (rotate built) 0).z
";

/// Агрегат с **дырой**: поля разной ширины, размер округляется до границы.
///
/// `Vec3` для двух правил §4.11 слеп: три равных поля не показывают ни
/// округления размера («выравнивание по максимальному `align` полей»), ни
/// порядка полей в укладке - перестановка трёх `Float32` ненаблюдаема. Здесь
/// поля разной ширины: `Int64` плюс `Int8` - это 9 байт, округлённых до 16, и
/// перестановка обрезала бы широкое поле до байта.
const PADDED: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

type Padded = { wide : Int64, tag : Int8 }

rotate : {Flat a} => Array 3 a -> Array 3 a
rotate xs = arraySet xs 0 (arrayIndex xs 1)

first : Padded
first = { wide = 1, tag = 1 }

second : Padded
second = { wide = 700, tag = 7 }

third : Padded
third = { wide = 900, tag = 9 }

built : Array 3 Padded
built = arraySet (arraySet (arrayNew 3 first) 1 second) 2 third

-- 700: широкое поле ячейки, приехавшей из первой. В байт оно не влезает, и
-- перестановка полей укладки обрезала бы его до 188.
main : Int64
main = (arrayIndex (rotate built) 0).wide
";

/// Округление размера и порядок полей видны на агрегате с дырой.
#[test]
fn a_padded_aggregate_rounds_up_and_keeps_its_order() {
    assert_eq!(
        harness::printed(PADDED),
        "700",
        "печать машины изменилась - свидетель говорит не о том"
    );
    harness::agreed("packed-padded-after", PADDED).unwrap_or_else(|error| {
        panic!("после специализации: {error}");
    });
    // Обобщённый путь берёт шаг у дескриптора типовой стороны - шестнадцать, -
    // а `built` укладывает ячейки размером понижения. Не округли понижение
    // девять до шестнадцати, и `rotate` возьмёт байты не с той ячейки.
    harness::as_written("packed-padded-before", PADDED).unwrap_or_else(|error| {
        panic!("до специализации: {error}");
    });
    let text = harness::text(PADDED).unwrap_or_else(|error| panic!("агрегат с дырой: {error}"));
    for written in [
        "_Alignas(8) unsigned char bytes[16];",
        // Широкое поле стоит первым и читается восемью байтами, узкое - за ним,
        // по восьмому байту. Сборка пишет `&значение`, чтение - ширину, отсюда
        // две разные формы строки.
        ".bytes + 0, 8u",
        ".bytes + 8, &",
    ] {
        assert!(
            text.contains(written),
            "в порождённом C нет `{written}`: укладка §4.11 разошлась"
        );
    }
}

/// Запись из одних примитивов: ячейки кучи не стоит вовсе.
const REGISTERS: &str = "\
type Triple = { first : Int64, second : Int64, third : Int64 }

main : Int64
main =
  let made : Triple = { first = 1, second = 20, third = 300 }
  subInt64 (subInt64 made.third made.second) made.first
";

/// Запись из примитивов живёт в регистрах: ноль блоков (§4.11).
///
/// Вычитание, а не сложение: перестановка полей на сложении ненаблюдаема, а
/// здесь `300 - 20 - 1 = 279` против `1 - 1 - 1` у проекции, всегда берущей
/// нулевое смещение.
#[test]
fn a_record_of_primitives_costs_no_block() {
    assert_eq!(
        harness::printed(REGISTERS),
        "279",
        "свидетель перестал различать смещения"
    );
    let stderr = harness::agreed("packed-registers", REGISTERS).unwrap_or_else(|error| {
        panic!("запись из примитивов: {error}");
    });
    let (allocated, live) = harness::blocks("packed-registers", &stderr);
    assert_eq!(allocated, 0, "плотная запись выдала блок кучи");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Колонка считается плоской, и ответ её сходится с интерпретатором.
#[test]
fn a_column_of_aggregates_is_one_block() {
    let source = column();
    assert_eq!(
        harness::printed(&source),
        "123.0",
        "свидетель перестал различать поле и ячейку"
    );
    let stderr = harness::agreed("packed-column", &source).unwrap_or_else(|error| {
        panic!("колонка: {error}");
    });
    let (allocated, live) = harness::blocks("packed-column", &stderr);
    // Один блок на всю колонку: три `Vec3` лежат в нём подряд, заголовков у них
    // нет. Сами `Vec3` ячеек не стоят вовсе - они плотные значения на кадре.
    assert_eq!(allocated, 1, "колонка стоила не одного блока");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Тот же код над указательным элементом стоит `n` объектов сверх массива.
#[test]
fn a_column_of_pointers_still_costs_an_object_per_cell() {
    let stderr = harness::agreed("packed-pointing", POINTING).unwrap_or_else(|error| {
        panic!("указательный массив: {error}");
    });
    let (allocated, live) = harness::blocks("packed-pointing", &stderr);
    // Массив плюс объект на ячейку - четыре против одного у колонки. Это и
    // есть та цена, которую §4.11 обещает снять плоской укладкой.
    assert_eq!(
        allocated, 4,
        "указательный массив обошёлся не четырьмя блоками - он перестал быть указательным"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Упаковка на границе указателя сохраняет поля и порядок.
#[test]
fn an_aggregate_crossing_a_pointer_is_boxed() {
    assert_eq!(
        harness::printed(BOXING),
        "Cons ({lo = 1, hi = 2}) (Cons ({lo = 30, hi = 40}) Nil)",
        "печать машины изменилась - свидетель говорит не о том"
    );
    harness::agreed("packed-boxing", BOXING).unwrap_or_else(|error| {
        panic!("упаковка: {error}");
    });
}

/// Байты §4.11 видны числом: размер, граница, шаг, смещения.
///
/// Текстом, а не ответом, и это названо ценой: ошибка укладки **сокращается**,
/// когда запись и чтение идут одним и тем же выражением, - на этом срезе такой
/// мутант уже был (`docs/phase6-plan.md`, пункт 3б). Число, стоящее в тексте
/// один раз, так не сокращается.
#[test]
fn the_layout_of_a_vector_is_twelve_bytes_at_four() {
    let text = harness::text(&column()).unwrap_or_else(|error| panic!("колонка: {error}"));
    for written in [
        // Тип агрегата: двенадцать байт по границе четыре.
        "_Alignas(4) unsigned char bytes[12];",
        // И то же самое утверждает сам порождённый код - компилятору C.
        "_Static_assert(sizeof(adamas_pack_0) == 12u,",
        "_Static_assert(_Alignof(adamas_pack_0) == 4u,",
        // Шаг индексации: три ячейки по двенадцать байт - тридцать шесть.
        "adamas_array_alloc((size_t)t0, 12u)",
        // Смещения полей: подряд, без дыр.
        "bytes + 0, 4u",
        "bytes + 4, 4u",
        "bytes + 8, 4u",
    ] {
        assert!(
            text.contains(written),
            "в порождённом C нет `{written}`: укладка §4.11 разошлась"
        );
    }
}

/// Размер агрегата один у обоих путей - иначе `rotate` возьмёт не ту ячейку.
#[test]
fn both_paths_agree_on_the_size_of_the_aggregate() {
    assert_eq!(
        harness::printed(TWO_WAYS),
        "30.0",
        "печать машины изменилась - свидетель говорит не о том"
    );
    // Специализированный путь: шаг - константа понижения на всём протяжении.
    harness::agreed("packed-two-ways-after", TWO_WAYS).unwrap_or_else(|error| {
        panic!("после специализации: {error}");
    });
    // Обобщённый: `rotate` берёт шаг у дескриптора, посчитанного элаборацией, а
    // `built` укладывает ячейки константой. Разойдись эти два числа - здесь и
    // видно, и видно **ответом**, а не текстом.
    harness::as_written("packed-two-ways-before", TWO_WAYS).unwrap_or_else(|error| {
        panic!("до специализации: {error}");
    });
}

/// Семейство с тегом в колонке (§4.11, §10 вопрос 157): `Option Int64` в
/// шестнадцать байт, только мономорфно - `OptInt`.
///
/// Ячейка несёт тег в байте и payload по своей границе: 1 + 7 дыры + 8. Ячейки
/// различимы и по тегу (нулевая - `None`), и по payload'у (700 против 900), а
/// множитель у последней делает порядок ячеек наблюдаемым.
const TAGGED: &str = "\
data OptInt where
  None : OptInt
  Some : Int64 -> OptInt

take : OptInt -> Int64
take None = 0
take (Some n) = n

built : Array 3 OptInt
built = arraySet (arraySet (arrayNew 3 None) 1 (Some 700)) 2 (Some 900)

-- Массив принимается параметром, а не читается трижды по имени: определение
-- без параметров пересчитывается на каждом упоминании, и число блоков
-- считало бы построения, а не ячейки.
read : Array 3 OptInt -> Int64
read xs =
  addInt64 (take (arrayIndex xs 0))
    (addInt64 (take (arrayIndex xs 1)) (mulInt64 (take (arrayIndex xs 2)) 10))

-- 0 + 700 + 9000 = 9700
main : Int64
main = read built
";

/// Колонка тегованных значений - один блок, тег байтом, payload за дырой.
#[test]
fn a_tagged_column_is_one_block_of_sixteens() {
    assert_eq!(
        harness::printed(TAGGED),
        "9700",
        "свидетель перестал различать тег, payload и ячейку"
    );
    let stderr = harness::agreed("packed-tagged", TAGGED).unwrap_or_else(|error| {
        panic!("тегованная колонка: {error}");
    });
    let (allocated, live) = harness::blocks("packed-tagged", &stderr);
    // Один блок - колонка; ещё два - названная цена переклада на границе:
    // `take` берёт указатель, и прочитанная ячейка `Some` боксируется
    // (`None` непосредственен и не стоит ничего).
    assert_eq!(allocated, 3, "цена колонки с тегом разошлась с §4.11");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
    let text = harness::text(TAGGED).unwrap_or_else(|error| panic!("тегованная колонка: {error}"));
    for written in [
        // Тип ячейки: тег в байте, payload из восьми за дырой выравнивания.
        "_Alignas(8) unsigned char bytes[16];",
        "_Static_assert(sizeof(adamas_pack_0) == 16u,",
        // Шаг индексации - шестнадцать.
        "adamas_array_alloc((size_t)t0, 16u)",
        // Тег пишется байтом в начало...
        ".bytes, &adamas_variant, 1u",
        // ...а payload встаёт по своей границе.
        ".bytes + 8, &",
    ] {
        assert!(
            text.contains(written),
            "в порождённом C нет `{written}`: укладка тега §4.11 разошлась"
        );
    }
}

/// Семейство из одних нульарных конструкторов: ячейка - один байт.
///
/// Это форма контрольных байт хеш-таблицы §4.11: сто значений - сто байт, а
/// не сто объектов.
const BYTES: &str = "\
data Colour where
  Red : Colour
  Green : Colour
  Blue : Colour

built : Array 3 Colour
built = arraySet (arraySet (arrayNew 3 Red) 1 Green) 2 Blue

main : Colour
main = arrayIndex built 2
";

/// Колонка нульарных тегов - байт на ячейку и один блок на всё.
#[test]
fn a_column_of_nullary_tags_is_a_byte_per_cell() {
    assert_eq!(
        harness::printed(BYTES),
        "Blue",
        "свидетель перестал различать ячейки"
    );
    let stderr = harness::agreed("packed-bytes", BYTES).unwrap_or_else(|error| {
        panic!("колонка тегов: {error}");
    });
    let (allocated, live) = harness::blocks("packed-bytes", &stderr);
    // Один блок - сама колонка; ответ - нульарный конструктор, он
    // непосредственен и блока не стоит и после переклада под печать.
    assert_eq!(allocated, 1, "колонка нульарных тегов стоила больше блока");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
    let text = harness::text(BYTES).unwrap_or_else(|error| panic!("колонка тегов: {error}"));
    for written in [
        "_Alignas(1) unsigned char bytes[1];",
        "adamas_array_alloc((size_t)t0, 1u)",
    ] {
        assert!(
            text.contains(written),
            "в порождённом C нет `{written}`: ячейка теговой колонки не байт"
        );
    }
}

/// Семейство с одним конструктором укладывается как запись: тега нет.
const SOLE: &str = "\
data P where
  MkP : Float32 -> Float32 -> P

built : Array 3 P
built = arraySet (arrayNew 3 (MkP 1.0 2.0)) 1 (MkP 10.0 20.0)

main : P
main = arrayIndex built 1
";

/// Один конструктор - как запись: восемь байт полей и ни байта тега.
#[test]
fn a_single_constructor_family_packs_like_a_record() {
    assert_eq!(
        harness::printed(SOLE),
        "MkP 10.0 20.0",
        "свидетель перестал различать ячейки и поля"
    );
    let stderr = harness::agreed("packed-sole", SOLE).unwrap_or_else(|error| {
        panic!("один конструктор: {error}");
    });
    let (allocated, live) = harness::blocks("packed-sole", &stderr);
    // Колонка плюс бокс ответа под печать: у плотного значения заголовка нет.
    assert_eq!(
        allocated, 2,
        "колонка одноконструкторного семейства разошлась в цене"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
    let text = harness::text(SOLE).unwrap_or_else(|error| panic!("один конструктор: {error}"));
    assert!(
        text.contains("_Alignas(4) unsigned char bytes[8];"),
        "поля MkP уложены не как запись §4.11"
    );
    assert!(
        !text.contains("adamas_variant"),
        "у единственного конструктора появился тег - различать ему нечего"
    );
}

/// Вложенный агрегат: запись в записи, слот - байты укладки целиком
/// (§4.11, §10 вопрос 157).
///
/// `Particle` - центральная запись §4.11: геометрия плюс скаляр. Проекция
/// сквозь вложенность - композиция двух чтений по смещению, а не путь.
const NESTED_COLUMN: &str = "\
type V3 (a : Type) = { x : a, y : a, z : a }
type Vec3 = V3 Float32

type Particle = { pos : Vec3, hp : Float32 }

first : Particle
first = { pos = { x = 1.0, y = 2.0, z = 3.0 }, hp = 10.0 }

second : Particle
second = { pos = { x = 4.0, y = 5.0, z = 6.0 }, hp = 20.0 }

built : Array 2 Particle
built = arraySet (arrayNew 2 first) 1 second

read : Array 2 Particle -> Float32
read xs = addFloat32 (arrayIndex xs 1).pos.z (arrayIndex xs 0).hp

-- 6.0 + 10.0 = 16.0: поле вложенного из одной ячейки, скаляр из другой.
main : Float32
main = read built
";

/// Колонка вложенных агрегатов - один блок, 16 байт на ячейку.
#[test]
fn a_nested_aggregate_packs_and_projects_by_composition() {
    assert_eq!(
        harness::printed(NESTED_COLUMN),
        "16.0",
        "свидетель перестал различать вложенность и ячейку"
    );
    let stderr = harness::agreed("packed-nested", NESTED_COLUMN).unwrap_or_else(|error| {
        panic!("вложенная колонка: {error}");
    });
    let (allocated, live) = harness::blocks("packed-nested", &stderr);
    assert_eq!(
        allocated, 1,
        "колонка вложенных агрегатов стоила не один блок"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
    let text =
        harness::text(NESTED_COLUMN).unwrap_or_else(|error| panic!("вложенная колонка: {error}"));
    for written in [
        // Particle: Vec3 в 12 байт плюс Float32 - шестнадцать по границе 4.
        "_Alignas(4) unsigned char bytes[16];",
        "adamas_array_alloc((size_t)t0, 16u)",
        // Вложенный агрегат копируется целиком: 12 байт одним memcpy.
        ".bytes + 0, 12u",
    ] {
        assert!(
            text.contains(written),
            "в порождённом C нет `{written}`: вложенная укладка §4.11 разошлась"
        );
    }
}

/// Вложенность семейств: плотное семейство полем плотного семейства.
///
/// Мономорфно, потому что читаемо: у параметрического плоского payload'а
/// боксированной формы нет по построению, и ячейка его не читается - см.
/// границу в §13.
const NESTED_FAMILY: &str = "\
data Inner where
  MkI : Int8 -> Inner

data Outer where
  MkO : Inner -> Int8 -> Outer

built : Array 2 Outer
built = arraySet (arrayNew 2 (MkO (MkI 7) 1)) 1 (MkO (MkI 9) 2)

read : Array 2 Outer -> Outer
read xs = arrayIndex xs 1

main : Outer
main = read built
";

/// Семейство в семействе укладывается и читается обратно объектом.
#[test]
fn a_family_nested_in_a_family_packs_and_unpacks() {
    assert_eq!(
        harness::printed(NESTED_FAMILY),
        "MkO (MkI 9) 2",
        "печать машины изменилась - свидетель говорит не о том"
    );
    let stderr = harness::agreed("packed-nested-family", NESTED_FAMILY).unwrap_or_else(|error| {
        panic!("вложенное семейство: {error}");
    });
    let (allocated, live) = harness::blocks("packed-nested-family", &stderr);
    // Колонка - один блок; ответ боксируется под печать: объект `MkO` и
    // объект `MkI` в его поле.
    assert_eq!(allocated, 3, "цена вложенного семейства разошлась");
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Две записи одного числа сошлись: понижение и типовая сторона.
///
/// `adamas-codegen` элаборацию не читает - шов, - поэтому правило §4.11
/// посчитано дважды. Совпадение поэтому проверяется, а не предполагается:
/// разойдись они, `layout @Vec3` говорил бы одно, а колонка укладывалась бы
/// иначе, и обе половины остались бы зелёными порознь.
#[test]
fn the_layout_matches_the_type_side() {
    let source = format!(
        "{}\n{}",
        "\
data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

type V3 (a : Type) = { x : a, y : a, z : a }
type Vec3 = V3 Float32

type Handle = { index : UInt32, generation : UInt32 }

type Padded = { wide : Int64, tag : Int8 }

data OptInt where
  None : OptInt
  Some : Int64 -> OptInt",
        "\
main : List Layout
main =
  Cons (layout @Vec3)
    (Cons (layout @Handle) (Cons (layout @Padded) (Cons (layout @OptInt) Nil)))"
    );
    assert_eq!(
        harness::printed(&source),
        "Cons ({size = 12, align = 4}) (Cons ({size = 8, align = 4}) \
         (Cons ({size = 16, align = 8}) (Cons ({size = 16, align = 8}) Nil)))",
        "типовая сторона считает укладку иначе"
    );
    harness::agreed("packed-layout", &source).unwrap_or_else(|error| {
        panic!("укладка: {error}");
    });
}

/// Размер тегованной ячейки один у обоих путей - дескриптора и константы.
///
/// Тот же жанр, что [`both_paths_agree_on_the_size_of_the_aggregate`]:
/// `rotate` берёт шаг у дескриптора типовой стороны, `built` укладывает
/// константой понижения. Тег - вторая запись правила §4.11, и разойтись ей
/// есть где: типовая сторона считает его в `flat.rs`, понижение - у себя.
const TAGGED_TWO_WAYS: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

data OptInt where
  None : OptInt
  Some : Int64 -> OptInt

take : OptInt -> Int64
take None = 0
take (Some n) = n

rotate : {Flat a} => Array 3 a -> Array 3 a
rotate xs = arraySet xs 0 (arrayIndex xs 1)

built : Array 3 OptInt
built = arraySet (arraySet (arrayNew 3 None) 1 (Some 700)) 2 (Some 900)

-- 700: ячейка, приехавшая из первой. Разойдись шаг - байты взялись бы не
-- с той ячейки, и тег с payload'ом перепутались бы.
main : Int64
main = take (arrayIndex (rotate built) 0)
";

/// Оба пути согласны о шаге тегованной ячейки.
#[test]
fn both_paths_agree_on_the_tagged_size() {
    assert_eq!(
        harness::printed(TAGGED_TWO_WAYS),
        "700",
        "печать машины изменилась - свидетель говорит не о том"
    );
    harness::agreed("packed-tagged-after", TAGGED_TWO_WAYS).unwrap_or_else(|error| {
        panic!("после специализации: {error}");
    });
    harness::as_written("packed-tagged-before", TAGGED_TWO_WAYS).unwrap_or_else(|error| {
        panic!("до специализации: {error}");
    });
}
