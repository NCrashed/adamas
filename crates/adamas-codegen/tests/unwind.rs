//! Резумпция значением и её размотка `unwind` (§3.4, §10 вопрос 249).
//!
//! Резумпция уходит из ветки в поле ресурса, зовётся вне хендлера и, брошенная,
//! разматывается деструктором обёртки. Форм понижения у размотки две: во
//! второй она кадр на стеке вызывающего, в первой - дроп на своём корне, и
//! эффекту деструктора там уйти некуда, потому что ряд пуст. Ответ сам по себе
//! утечку не видит, поэтому каждый тест спрашивает и счёт блоков.

mod harness;

/// Обёртка, шаг и овеществление: общая часть обеих программ.
const SHAPE: &str = "\
resource Resumption (r : Type) where
  Suspended : (1 k : Unit -> r) -> Resumption r
  abandon : (1 s : Resumption r) -> Unit
  abandon (Suspended k) = unwind k

resource Step (a : Type) where
  Done : Step a
  Next : (ω x : a) -> Resumption (Step a) -> Step a
  dropStep : (1 s : Step a) -> Unit
  dropStep Done = MkUnit
  dropStep (Next _x r) = abandon r

reify : ({Yield a} Unit) -> Step a
reify prod = handle prod with
  yield x -> Next x (Suspended resume)
  return _v -> Done

advance : (1 r : Resumption (Step a)) -> Step a
advance (Suspended k) = k MkUnit

plusHead : UInt64 -> (1 s : Step UInt64) -> UInt64
plusHead acc Done = acc
plusHead acc (Next x r) =
  let 1 _gone : Unit = abandon r
  acc + x
";

/// Два первых элемента, остаток продюсера брошен: чистая программа, первая
/// форма.
const PURE: &str = "\
firstTwo : (1 s : Step UInt64) -> UInt64
firstTwo Done = 0
firstTwo (Next x r) = plusHead x (advance r)

main : UInt64
main = firstTwo (reify (each [10, 20, 30]))
";

/// То же под эффектом: брошенный продюсер держит ресурс, чей деструктор
/// отмечается, и отметка обязана дойти до хендлера вызывающего.
const EFFECTFUL: &str = "\
effect Log where
  note : UInt64 -> Unit

resource Guard where
  Held : (ω n : UInt64) -> Guard
  release : (1 g : Guard) -> {Log} Unit
  release (Held n) = note n

resource Parked (r : Type) where
  Kept : (1 k : Unit -> {Log} r) -> Parked r
  letGo : (1 s : Parked r) -> {Log} Unit
  letGo (Kept k) = unwind k

resource Pulled where
  Over : Pulled
  More : (ω x : UInt64) -> Parked Pulled -> Pulled
  dropPulled : (1 s : Pulled) -> {Log} Unit
  dropPulled Over = MkUnit
  dropPulled (More _x r) = letGo r

pulled : ({Yield UInt64, Log} Unit) -> {Log} Pulled
pulled prod = handle prod with
  yield x -> More x (Kept resume)
  return _v -> Over

guarded : {Yield UInt64, Log} Unit
guarded =
  let 1 _g : Guard = Held 7
  each [1, 2, 3]

headThen : UInt64 -> (1 s : Pulled) -> {Log} UInt64
headThen acc Over = acc
headThen acc (More x r) =
  let 1 _gone : Unit = letGo r
  acc + x

pair : (1 s : Pulled) -> {Log} UInt64
pair Over = 0
pair (More x (Kept k)) = headThen x (k MkUnit)

collect : ({Log} UInt64) -> (UInt64, List UInt64)
collect k = handle k with
  state Nil
  return v -> (v, state)
  note n -> resume MkUnit (Cons n state)

main : (UInt64, List UInt64)
main = collect (\\_u -> pair (pulled guarded))
";

/// Первая форма: размотка - дроп на своём корне, сегмент отдан.
#[test]
fn a_pure_abandoned_resumption_is_released() {
    let source = format!("{SHAPE}{PURE}");
    assert_eq!(harness::printed(&source), "30", "машина посчитала не то");
    let stderr = harness::agreed("unwind-pure", &source)
        .unwrap_or_else(|error| panic!("чистая размотка отвергнута: {error}"));
    assert!(
        stderr.contains("alive 0"),
        "сегмент не отдан: {}",
        stderr.trim_end()
    );
}

/// Вторая форма: деструктор внутри брошенного сегмента отмечается у `collect`.
#[test]
fn an_abandoned_resumption_runs_its_destructors_under_the_caller() {
    let source = format!("{SHAPE}{EFFECTFUL}");
    assert_eq!(
        harness::printed(&source),
        "{_1 = 3, _2 = Cons 7 Nil}",
        "машина посчитала не то"
    );
    let stderr = harness::agreed("unwind-effectful", &source)
        .unwrap_or_else(|error| panic!("размотка под эффектом отвергнута: {error}"));
    assert!(
        stderr.contains("alive 0"),
        "сегмент не отдан: {}",
        stderr.trim_end()
    );
}
