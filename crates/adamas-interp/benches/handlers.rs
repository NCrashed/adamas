//! Baseline для хендлера над глубокой рекурсией (§10 вопрос 94).
//!
//! Меряется то, что было квадратичным: операция под рекурсией, где сегмент
//! резумпции растёт с её глубиной. Точек три, и разделены они намеренно - класс
//! читается по их отношению, а не по одной цифре.
//!
//! - `deep_handler_1000` / `2000` / `4000` - одна и та же программа при трёх
//!   глубинах. Линейному исполнению отвечает удвоение времени на удвоении
//!   глубины; квадратичному - учетверение. До правки 2026-09-05 оно и было
//!   учетверением: 2500 операций стоили 0.12 с, 5000 - 0.51, 10000 - 2.12.
//!
//! Хендлер здесь одношотный: у мультишотного повтор сегмента и есть смысл
//! формы, и его стоимость - названная цена, а не дефект.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use criterion::{Criterion, criterion_group, criterion_main};

/// Программа: `counted n` производит операцию на каждом уровне рекурсии.
///
/// Число пишется умножением: литерал в `n` вложенных `Succ` упирается в предел
/// вложенности разбора, а произведение - нет.
fn source(hundreds: usize) -> String {
    let literal = |count: usize| -> String {
        let mut out = String::new();
        for _ in 0..count {
            out.push_str("(Succ ");
        }
        out.push_str("Zero");
        for _ in 0..count {
            out.push(')');
        }
        out
    };
    format!(
        "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

infixl 6 +
(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)

infixl 7 *
(*) : Nat -> Nat -> Nat
(*) Zero m = Zero
(*) (Succ k) m = m + k * m

effect Ask where
  ask : Nat

counted : Nat -> {{Ask}} Nat
counted Zero = Zero
counted (Succ k) =
  let one : Nat = ask
  one + counted k

hundred : Nat
hundred = {}

deep : {{Ask}} Nat
deep = counted ({} * hundred)

main : Nat
main = handle deep with
  return v -> v
  ask -> resume Zero
",
        literal(100),
        literal(hundreds)
    )
}

#[expect(
    clippy::expect_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный бенчмарк"
)]
fn prepared(hundreds: usize) -> (Signature, Term) {
    let text = source(hundreds);
    let module = adamas_parser::parse(&text).expect("исходник обязан разбираться");
    let signature = adamas_elab::elaborate(&module).expect("исходник обязан проходить проверку");
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    let body = body.substitute_levels(&levels).substitute_rows(&rows);
    (signature, body)
}

#[expect(
    clippy::expect_used,
    reason = "заготовка бенчмарка: непогашенная операция означает сломанный бенчмарк"
)]
fn deep_handler(criterion: &mut Criterion) {
    for hundreds in [10, 20, 40] {
        let (signature, body) = prepared(hundreds);
        criterion.bench_function(&format!("deep_handler_{}", hundreds * 100), |bencher| {
            bencher.iter(|| {
                adamas_interp::run(&signature, &body).expect("операция обязана встретить хендлер")
            });
        });
    }
}

criterion_group!(benches, deep_handler);
criterion_main!(benches);
