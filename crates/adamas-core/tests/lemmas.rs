//! Леммы арифметики прелюдии верны на слове (§10 вопрос 225).
//!
//! Лемма - аксиома: ядро её не проверяет, и ложная лемма доказала бы номер вне
//! длины. Здесь каждая проверяется **той же свёрткой**, какой примитивы
//! считают ядро и машина (`PrimOp::fold`, `PrimCmp::holds`), на граничных и
//! псевдослучайных словах. Строка леммы в прелюдии закреплена дословно: правка
//! утверждения без правки проверки здесь краснеет.

use adamas_core::prim::{PrimCmp, PrimOp, PrimTy};

const PRELUDE: &str = include_str!("../../../lib/Prelude.adamas");

const WORD: PrimTy = PrimTy::UInt64;

/// Слова, на которых леммы проверяются: края, соседи краёв и
/// псевдослучайные. Перебор пар - все со всеми.
fn words() -> Vec<u64> {
    let mut words = vec![0, 1, 2, 3, 7, 8, 9, u64::MAX - 1, u64::MAX, 1 << 63];
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..200 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        words.push(state);
        words.push(state % 64);
    }
    words
}

fn lt(a: u64, b: u64) -> bool {
    PrimCmp::Lt.holds(WORD, a, b)
}

fn le(a: u64, b: u64) -> bool {
    PrimCmp::Le.holds(WORD, a, b)
}

fn eq(a: u64, b: u64) -> bool {
    PrimCmp::Eq.holds(WORD, a, b)
}

#[expect(
    clippy::expect_used,
    reason = "заготовка теста: вычитание слова сводится всегда, и отказ - сломанное ядро"
)]
fn sub(a: u64, b: u64) -> u64 {
    PrimOp::Sub
        .fold(WORD, a, b)
        .expect("вычитание слова сводится всегда")
}

/// Строка прелюдии, которую лемма утверждает.
fn stated(line: &str) {
    assert!(
        PRELUDE.lines().any(|it| it == line),
        "лемма в прелюдии записана иначе, чем здесь проверено:\n{line}"
    );
}

#[test]
fn below_pred_holds_on_the_word() {
    stated(
        "belowPred : (0 i : UInt64) -> (0 n : UInt64) -> (0 p : Equal Bool (leUInt64 i n) True) -> (0 q : Equal Bool (eqUInt64 i 0) False) -> Equal Bool (ltUInt64 (subUInt64 i 1) n) True",
    );
    let words = words();
    for &i in &words {
        for &n in &words {
            if le(i, n) && !eq(i, 0) {
                assert!(lt(sub(i, 1), n), "belowPred ложна при i = {i}, n = {n}");
            }
        }
    }
}

#[test]
fn below_at_most_holds_on_the_word() {
    stated(
        "belowAtMost : (0 i : UInt64) -> (0 n : UInt64) -> (0 p : Equal Bool (ltUInt64 i n) True) -> Equal Bool (leUInt64 i n) True",
    );
    let words = words();
    for &i in &words {
        for &n in &words {
            if lt(i, n) {
                assert!(le(i, n), "belowAtMost ложна при i = {i}, n = {n}");
            }
        }
    }
}

#[test]
fn at_most_self_holds_on_the_word() {
    stated("atMostSelf : (0 n : UInt64) -> Equal Bool (leUInt64 n n) True");
    for n in words() {
        assert!(le(n, n), "atMostSelf ложна при n = {n}");
    }
}

/// Мутант по построению: лемма, ложная при заворачивании, этой проверкой
/// ловится. Без условия `i /= 0` номер `0 - 1` заворачивается в наибольшее
/// слово, и `belowPred` без второй посылки лгала бы.
#[test]
fn a_lemma_false_under_wrapping_is_caught() {
    let words = words();
    let broken = words
        .iter()
        .flat_map(|&i| words.iter().map(move |&n| (i, n)))
        .any(|(i, n)| le(i, n) && !lt(sub(i, 1), n));
    assert!(broken, "проверка не различает лемму без посылки `i /= 0`");
}

#[test]
fn not_below_holds_on_the_word() {
    stated(
        "notBelow : (0 i : UInt64) -> (0 n : UInt64) -> (0 p : Equal Bool (ltUInt64 i n) False) -> Equal Bool (leUInt64 n i) True",
    );
    let words = words();
    for &i in &words {
        for &n in &words {
            if !lt(i, n) {
                assert!(le(n, i), "notBelow ложна при i = {i}, n = {n}");
            }
        }
    }
}

#[test]
fn window_before_holds_on_the_word() {
    stated(
        "windowBefore : (0 i : UInt64) -> (0 n : UInt64) -> (0 m : UInt64) -> (0 p : Equal Bool (leUInt64 n i) True) -> (0 q : Equal Bool (leUInt64 i m) True) -> Equal Bool (leUInt64 (subUInt64 i n) (subUInt64 m n)) True",
    );
    let words = words();
    for &i in &words {
        for &n in &words {
            for &m in words.iter().step_by(7) {
                if le(n, i) && le(i, m) {
                    assert!(
                        le(sub(i, n), sub(m, n)),
                        "windowBefore ложна при i = {i}, n = {n}, m = {m}"
                    );
                }
            }
        }
    }
}

#[test]
fn step_at_most_holds_on_the_word() {
    stated(
        "stepAtMost : (0 i : UInt64) -> (0 n : UInt64) -> (0 m : UInt64) -> (0 p : Equal Bool (leUInt64 n i) True) -> (0 q : Equal Bool (leUInt64 i m) True) -> Equal Bool (leUInt64 (subUInt64 i n) m) True",
    );
    let words = words();
    for &i in &words {
        for &n in &words {
            for &m in words.iter().step_by(7) {
                if le(n, i) && le(i, m) {
                    assert!(
                        le(sub(i, n), m),
                        "stepAtMost ложна при i = {i}, n = {n}, m = {m}"
                    );
                }
            }
        }
    }
}

#[test]
fn at_most_trans_holds_on_the_word() {
    stated(
        "atMostTrans : (0 a : UInt64) -> (0 b : UInt64) -> (0 c : UInt64) -> (0 p : Equal Bool (leUInt64 a b) True) -> (0 q : Equal Bool (leUInt64 b c) True) -> Equal Bool (leUInt64 a c) True",
    );
    let words = words();
    for &a in &words {
        for &b in &words {
            for &c in words.iter().step_by(7) {
                if le(a, b) && le(b, c) {
                    assert!(le(a, c), "atMostTrans ложна при a = {a}, b = {b}, c = {c}");
                }
            }
        }
    }
}
