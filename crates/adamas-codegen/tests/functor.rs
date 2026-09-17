//! Член функтора за рекурсией: названная граница понижения (§4.8, §10 в. 163).
//!
//! Найдена капстоуном Фазы 7 (`eval/packets`), а не замыслом. Пробег по колонке
//! там писался один раз над `module type AllocStrategy` - ровно так, как
//! обещает вопрос 161, - и не понизился ни одним бэкендом.
//!
//! # Механизм
//!
//! Специализация есть δ-разворот от терма `main`: она переписывает его тело и
//! тела произведённых ею же определений (`mono::specialise`). Тело обычного
//! верхнего определения она не переписывает вовсе, и пока такое определение
//! **разворачивается** в `main`, это незаметно. Рекурсию развернуть нечем -
//! определение остаётся определением, - и проекция `OnArena.once` доезжает до
//! понижения неснятой, с записью модуля ведущим имплиситом. Вызов оказывается
//! недобранным, а трамплин замыкания говорит указателями: плоский параметр,
//! плоский ответ, агрегат и блок региона через него не проходят (§4.11).
//!
//! Симптомов поэтому два, и различает их только то, что первым не прошло:
//! плоский параметр у члена с числовым аргументом, блок региона у ответа
//! `S.new`. Корень один.
//!
//! # Что здесь утверждается
//!
//! Граница названа **отказом**, а не молчанием, и обе её стороны измерены: тот
//! же член, позванный с нерекурсивного пути, понижается и считается. Последнее
//! существенно - без него отказ читался бы как «функтор не понижается вовсе»,
//! а он понижается, и `eval/functor-strategy` тому свидетель.
//!
//! Чинится это в `adamas-elab`, а не в эмиттере: производное определение
//! пришлось бы заводить и для тех, кто модуль **употребляет**, а не только для
//! тех, кто его принимает. Цена такой правки не мерена, и трек капстоуна её не
//! брал.

mod harness;

/// Стратегия, функтор над ней и одно применение - общая часть трёх программ.
const SHAPE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Unit where
  MkUnit : Unit

type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

module type AllocStrategy where
  type Block
  new   : Unit -> Block
  store : {Flat a} => Block -> a -> Block
  here  : Block -> Ptr
  load  : {Flat a} => Block -> Ptr -> a
  free  : Block -> Ptr -> Block

module Arena :> AllocStrategy where
  type Block = Block

  new : Unit -> Block
  new u = regionNew

  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x

  here : Block -> Ptr
  here r = regionLast r

  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p

  free : Block -> Ptr -> Block
  free r p = r

module Probe (S : AllocStrategy) where
  once : UInt64 -> UInt64
  once x =
    let r0 : S.Block = S.new MkUnit
    let r1 : S.Block = S.store r0 x
    let h : Ptr = S.here r1
    S.load r1 h
";

/// Применение функтора: своей строкой, потому что [`INSIDE`] вклинивается перед
/// ней ещё одним членом.
const APPLIED: &str = "
module OnArena = Probe Arena
";

/// Нерекурсивный путь: обёртка есть, рекурсии нет - член понижается.
const STRAIGHT: &str = "\
relay : UInt64 -> UInt64
relay x = OnArena.once x

main : UInt64
main = addUInt64 (OnArena.once 7) (relay 5)
";

/// Тот же член из рекурсии: понижение отвергает.
const LOOPED: &str = "\
total : UInt64 -> UInt64 -> UInt64
total 0 acc = acc
total k acc = total (subUInt64 k 1) (addUInt64 acc (OnArena.once k))

main : UInt64
main = total 3 0
";

/// Рекурсивный член **внутри** функтора: тот же корень, другой симптом.
///
/// Стратегии он не трогает вовсе - и всё равно роняет весь функтор: рекурсия
/// достаточна сама по себе.
const INSIDE: &str = "
  tick : UInt64 -> UInt64 -> UInt64
  tick 0 acc = acc
  tick k acc = tick (subUInt64 k 1) (addUInt64 acc k)
";

/// Хвост программы с рекурсивным членом.
const INSIDE_MAIN: &str = "\
main : UInt64
main = addUInt64 (OnArena.once 7) (OnArena.tick 3 0)
";

/// С нерекурсивного пути член функтора понижается и считается.
#[test]
fn a_functor_member_lowers_off_a_straight_path() {
    let source = format!("{SHAPE}{APPLIED}{STRAIGHT}");
    assert_eq!(harness::printed(&source), "12", "машина посчитала не то");
    let stderr = harness::agreed("functor-straight", &source)
        .unwrap_or_else(|error| panic!("нерекурсивный путь отвергнут: {error}"));
    assert!(
        stderr.contains("живо 0"),
        "область не отдана: {}",
        stderr.trim_end()
    );
}

/// За рекурсией он отвергается, и отказ назван.
#[test]
fn a_functor_member_behind_recursion_is_refused() {
    let source = format!("{SHAPE}{APPLIED}{LOOPED}");
    // Машина её считает: граница принадлежит понижению, а не языку.
    assert_eq!(harness::printed(&source), "6", "машина посчитала не то");
    let why = harness::text(&source).err().map_or_else(
        || panic!("член функтора за рекурсией понизился: границы больше нет"),
        |error| error.to_string(),
    );
    assert!(
        why.contains("параметр недобранного вызова"),
        "отказ не тот: {why}"
    );
}

/// Рекурсивный член внутри функтора: тот же корень, ответ `S.new`.
#[test]
fn a_recursive_member_inside_a_functor_is_refused() {
    let source = format!("{SHAPE}{INSIDE}{APPLIED}{INSIDE_MAIN}");
    assert_eq!(harness::printed(&source), "13", "машина посчитала не то");
    let why = harness::text(&source).err().map_or_else(
        || panic!("рекурсивный член функтора понизился: границы больше нет"),
        |error| error.to_string(),
    );
    assert!(
        why.contains("недобранного вызова") && why.contains("блок региона"),
        "отказ не тот: {why}"
    );
}
