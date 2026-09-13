//! Граница куска дроблёного тела: что через неё едет и чем (§10 вопрос 164).
//!
//! Кадр носит слово и ничего кроме: `adamas_frame_code` берёт `adamas_value` и
//! им же отвечает. Половин у границы три - слот среды кадра, пришедшее в кусок
//! и ответ куска трамплину, - и до этого трека мера была написана у одной:
//! слот переводил плоское значение битами, а две другие отдавали его как есть.
//! Понижение при этом отвечало `Ok`, и несобирающийся C печатал **оно**, а не
//! ловил отказом.
//!
//! Корпус (`tests/agreement.rs`, `flat-across-a-suspension`) отвечает за то,
//! что ответ сходится с машиной. Здесь стоит то, чего ответ не различает:
//!
//! - **представление** - перевод в слово написан у всех трёх половин, и виден
//!   он в тексте C, а не в ответе ([`a_flat_value_crosses_the_boundary_as_a_word`]);
//! - **цена** - перевод не стоит ни одной ячейки кучи, потому что биты
//!   примитива ложатся в слово целиком ([`crossing_the_boundary_costs_no_cell`]);
//! - **позиции, которые остались отказом**, и их проходящие соседи
//!   ([`the_neighbouring_boundaries_are_still_named`]).
//!
//! Жанр «ошибка сокращается на симметричном пути» здесь ожидаем по построению:
//! перевод в слово и обратно стоят рядом и взаимно сокращаются. Поэтому
//! свидетель ширины смотрит на **`Float64`**: у него запись в слове - биты, а
//! не значение, и подмена ширины меняет ответ. У целых она его не меняет
//! никогда - C приводит число обратно.
//!
//! # Мутанты, которыми это мерено (2026-09-12)
//!
//! Четыре по коду, все пойманы, и пятый по свидетелю - он **выжил**.
//!
//! - *Перевод в слово тождествен* и, отдельно, *перевод из слова тождествен*:
//!   порождённый C не собирается. Первый ловит корпус, второй - все четыре
//!   свидетеля здесь.
//! - *`finish` не спрашивает представление* (всегда `Repr::Boxed`): то же.
//! - *Перевод всегда шириной `Int64`* - симметричный. Целые он не меняет
//!   вовсе; ловят его ровно двое - [`the_width_of_the_crossing_is_the_width_of_the_value`]
//!   по тексту C и корпусная фикстура по ответу `Float64`. Остальные три
//!   свидетеля и остальной корпус проходят его насквозь.
//! - *По свидетелю:* убери у переезжающего `Float64` дробную часть (2.5 → 3.0),
//!   и предыдущий мутант **проходит корпус целиком** - 69 из 84, зелено.
//!   Остаётся один текстовый свидетель. Это и есть цена симметричного пути,
//!   названная числом.

mod harness;

/// Объявления, общие свидетелям: метка, множитель, дерево.
///
/// Операция `quit` - глушитель тишины, и ветка её в каждой площадке ниже
/// абортивна намеренно: без неё программа тиха (все ветки хвостовые, §3.4,
/// вопрос 74), операция перестаёт быть точкой приостановки, тело не дробится -
/// и границы куска, которую стерегут эти свидетели, не возникает вовсе.
/// Не зовёт её никто.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Mult where
  Triple : Mult
  Double : Mult

effect Ask where
  ask : Mult
  quit : Mult

data Tree where
  Leaf : Int64 -> Tree
  Node : Tree -> Tree -> Tree

factor : Mult -> Int64
factor Triple = 3
factor Double = 2
";

/// Свидетель записи 164 дословно: арифметика стоит после операции.
const WITNESS: &str = "\
scaled : Tree -> {Ask} Tree
scaled (Leaf x) = Leaf (mulInt64 x (factor ask))
scaled (Node l r) = Node (scaled l) (scaled r)

grown : {Ask} Tree
grown = scaled (Node (Leaf 1) (Leaf 2))

main : Tree
main = handle grown with
  return v -> v
  ask -> resume Triple
  quit -> Leaf 0
";

/// Тот же алгоритм, но множитель приходит указательным.
///
/// Это тот самый обход, которым стенд `benches/native.rs` жил до правки:
/// арифметика уехала в чистую `scale`, и границу куска не пересекает ничего
/// плоского. Точек приостановки на лист поэтому одна против трёх.
const POINTERWISE: &str = "\
scale : Mult -> Int64 -> Tree
scale Triple x = Leaf (mulInt64 x 3)
scale Double x = Leaf (mulInt64 x 2)

scaled : Tree -> {Ask} Tree
scaled (Leaf x) = scale ask x
scaled (Node l r) = Node (scaled l) (scaled r)

grown : {Ask} Tree
grown = scaled (Node (Leaf 1) (Leaf 2))

main : Tree
main = handle grown with
  return v -> v
  ask -> resume Triple
  quit -> Leaf 0
";

/// Две ширины через ту же границу: у одной значение в слове, у другой биты.
const WIDTHS: &str = "\
narrow : Mult -> Int8
narrow Triple = -100
narrow Double = 7

real : Mult -> Float64
real Triple = 2.5
real Double = 1.5

data Widths where
  MkWidths : Int8 -> Float64 -> Widths

measured : {Ask} Widths
measured =
  let small : Int8 = mulInt8 3 (narrow ask)
  let fractional : Float64 = mulFloat64 2.5 (real ask)
  MkWidths small fractional

main : Widths
main = handle measured with
  return v -> v
  ask -> resume Triple
  quit -> MkWidths 0 0.0
";

/// Плоское значение обеими половинами: пришедшее в кусок и ответ куска.
#[test]
fn a_flat_value_crosses_the_boundary_as_a_word() {
    let text = harness::text(&format!("{SHAPE}{WITNESS}"))
        .unwrap_or_else(|error| panic!("свидетель 164: {error}"));

    // Пришедшее: кусок читает его битами объявленной ширины, а не собой.
    assert!(
        text.contains("int64_t v6 = adamas_bits_Int64(adamas_slot_word(incoming));"),
        "пришедшее плоское значение не переведено из слова:\n{text}"
    );
    assert!(
        !text.contains("int64_t v6 = incoming;"),
        "пришедшее плоское значение взято словом как есть:\n{text}"
    );

    // Ответ куска: он уходит трамплину словом.
    assert!(
        text.contains("return adamas_slot_of(adamas_word_Int64("),
        "плоский ответ куска не переведён в слово:\n{text}"
    );

    // И то и другое стоит внутри куска, а не в обычной функции: у первой формы
    // ответ остаётся плоским, и перевод там был бы лишней работой.
    assert!(
        text.contains("static int64_t fn_"),
        "плоский ответ первой формы куда-то делся:\n{text}"
    );
}

/// Ширина перевода есть ширина значения, а не ширина слова.
///
/// Свидетель именно этого утверждения нужен потому, что у целых оно
/// ненаблюдаемо: возьми граница слово вдвое шире - C приведёт число обратно, и
/// ответ не изменится. У `Float64` в слове лежат **биты**, и подмена ширины
/// меняет ответ; поэтому здесь стоит он.
#[test]
fn the_width_of_the_crossing_is_the_width_of_the_value() {
    let source = format!("{SHAPE}{WIDTHS}");
    let text = harness::text(&source).unwrap_or_else(|error| panic!("свидетель ширины: {error}"));
    for width in ["Int8", "Float64"] {
        assert!(
            text.contains(&format!("adamas_bits_{width}(adamas_slot_word(incoming))")),
            "пришедшее {width} переведено не своей шириной:\n{text}"
        );
        assert!(
            text.contains(&format!("return adamas_slot_of(adamas_word_{width}(")),
            "ответ куска шириной {width} переведён не своей шириной:\n{text}"
        );
    }
    let stderr = harness::agreed("boundary-widths", &source)
        .unwrap_or_else(|error| panic!("свидетель ширины: {error}"));
    let (_, live) = harness::blocks("boundary-widths", &stderr);
    assert_eq!(live, 0, "свидетель ширины оставил блоки живыми");
}

/// Перевод в слово не стоит ячейки кучи: разность двух путей - одни кадры.
///
/// Утверждение неочевидно: §5.1 называет боксирование источником аллокации, и
/// «граница боксирует» (§10 вопрос 158) читается как «ячейка на каждый
/// переход». У границы кадра это не так - слот там слово, и биты примитива
/// ложатся в него целиком.
///
/// Мерится разностью с [`POINTERWISE`], у которого точек приостановки на лист
/// **одна** против трёх: операция, вызов `factor` и умножение против одной
/// операции. Кадр - блок кучи (трек D), листа два, лишних кадров поэтому
/// четыре - ровно на столько путь с плоским значением и дороже. Перевода в
/// слово в этой разности нет ни одной ячейки.
#[test]
fn crossing_the_boundary_costs_no_cell() {
    let flat = harness::agreed("boundary-flat", &format!("{SHAPE}{WITNESS}"))
        .unwrap_or_else(|error| panic!("плоский множитель: {error}"));
    let (flat_blocks, flat_live) = harness::blocks("boundary-flat", &flat);
    assert_eq!(flat_live, 0, "плоский множитель оставил блоки живыми");

    let boxed = harness::agreed("boundary-boxed", &format!("{SHAPE}{POINTERWISE}"))
        .unwrap_or_else(|error| panic!("указательный множитель: {error}"));
    let (boxed_blocks, boxed_live) = harness::blocks("boundary-boxed", &boxed);
    assert_eq!(boxed_live, 0, "указательный множитель оставил блоки живыми");

    assert_eq!(
        flat_blocks - boxed_blocks,
        4,
        "разность путей не равна четырём лишним кадрам: {flat_blocks} против {boxed_blocks}"
    );
}

/// Соседние границы по-прежнему отказывают, и отказ у каждой свой.
///
/// Пункт волны: молчаливого `Ok` с несобирающимся C не остаётся нигде. Кусок
/// теперь переводит, а две соседние позиции переводить не умеют и **называют**
/// это - каждая своими словами: ответ второй формы (обрыв возвращает значение)
/// и вычисление под хендлером (ответ его принимает ветка `return`). Рядом
/// стоит проходящий сосед, отличающийся от обоих ровно представлением.
#[test]
fn the_neighbouring_boundaries_are_still_named() {
    // Ответ второй формы: обрыв возвращает значение, и плоским его не вернуть.
    let flat_answer = harness::text(&format!(
        "{SHAPE}\
weigh : Int64 -> {{Ask}} Int64
weigh x = mulInt64 x (factor ask)

scaled : Tree -> {{Ask}} Tree
scaled (Leaf x) = Leaf (weigh x)
scaled (Node l r) = Node (scaled l) (scaled r)

grown : {{Ask}} Tree
grown = scaled (Leaf 1)

main : Tree
main = handle grown with
  return v -> v
  ask -> resume Triple
  quit -> Leaf 0
"
    ))
    .expect_err("вторая форма с плоским ответом обязана быть отвергнута")
    .to_string();
    assert!(
        flat_answer.contains("операция в функции с плоским ответом"),
        "отказ ответа второй формы назван иначе: {flat_answer}"
    );

    // Вычисление под хендлером: ответ его принимает ветка `return`.
    //
    // Без общего `SHAPE` и с отдельным эффектом-глушителем: у площадки с
    // ответом `Int64` всякая абортивная ветка обязана была бы ответить
    // плоским, а тело ветки указательно по договору - отказ пришёл бы раньше
    // меряемого. Тишину поэтому гасит `Halt` со своей площадкой.
    let flat_computation = harness::text(
        "\
data Unit where
  MkUnit : Unit

data Mult where
  Triple : Mult
  Double : Mult

effect Ask where
  ask : Mult

effect Halt where
  halt : Mult

factor : Mult -> Int64
factor Triple = 3
factor Double = 2

muted : {Halt} Mult
muted = halt

noisy : Mult
noisy = handle muted with
  return v -> v
  halt -> Triple

pick : Mult -> Mult -> Mult
pick Triple m = m
pick Double m = m

weighed : {Ask} Int64
weighed = factor (pick noisy ask)

main : Int64
main = handle weighed with
  return v -> v
  ask -> resume Triple
",
    )
    .expect_err("плоское вычисление под хендлером обязано быть отвергнуто")
    .to_string();
    assert!(
        flat_computation.contains("вычисление под хендлером"),
        "отказ вычисления под хендлером назван иначе: {flat_computation}"
    );

    // Проходящий сосед у обоих: то же самое, завёрнутое в конструктор.
    let neighbour = harness::agreed(
        "boundary-neighbour",
        &format!(
            "{SHAPE}\
weighed : {{Ask}} Tree
weighed = Leaf (factor ask)

main : Tree
main = handle weighed with
  return v -> v
  ask -> resume Triple
  quit -> Leaf 0
"
        ),
    )
    .unwrap_or_else(|error| panic!("проходящий сосед: {error}"));
    let (_, live) = harness::blocks("boundary-neighbour", &neighbour);
    assert_eq!(live, 0, "проходящий сосед оставил блоки живыми");
}
