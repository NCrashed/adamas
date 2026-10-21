//! Значение семейства, объявленного в функторе, не несёт параметра функтора.
//!
//! Параметр семейства в значении не хранится (§10 вопрос 78), и функторному -
//! модулю-параметру - это правило досталось не сразу: семейство, поднятое из
//! функтора, получало его с кратностью ω, и всякий конструктор клал полем
//! запись `{T, #dict}` вместе со словарём класса. Узел HAMT стоил от этого
//! четырёх лишних блоков (лог 2026-10-21). Ответ при этом верен - лишнее поле
//! видно только счётчиком, поэтому свидетель и читает счётчик.

mod harness;

/// Пять узлов - пять блоков: ключ `Bool` живёт в самом указателе, и всё, что
/// сверх, - параметр функтора, уехавший в поле.
#[test]
fn a_node_of_a_functor_family_is_one_block() {
    let source = "\
module Sorted {K : Ord} where
  data Bag where
    Done : Bag
    One : K.T -> Bag -> Bag

  size : Bag -> UInt64
  size Done = 0
  size (One _ rest) = size rest + 1

  push : K.T -> Bag -> Bag
  push x b = One x b

main : UInt64
main = Sorted.size (Sorted.push True (Sorted.push False (Sorted.push True (Sorted.push True (Sorted.push False Sorted.Done)))))
";
    let blocks = harness::agreed("functor-family-node", source)
        .unwrap_or_else(|error| panic!("семейство в функторе не понизилось: {error}"));
    assert!(
        blocks.contains("blocks issued 5, alive 0"),
        "узел несёт сверх ключа и хвоста: параметр функтора уехал в поле ({blocks})"
    );
}
