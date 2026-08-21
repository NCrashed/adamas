//! Первый бенчмарк, который меряет компилятор, а не fork/exec.
//!
//! Две точки отсчёта, разделённые намеренно:
//!
//! - `check` - лексер, парсер, вывод типов. Прокси для `adamas check` (§7.1),
//!   той самой быстрой обратной связи, ради которой команда существует.
//! - `run` - то же плюс вычисление. Разница между ними показывает, сколько
//!   стоит интерпретатор на подстановке; в Фазе 1 её же можно будет сравнить
//!   с `NbE`.
//!
//! Размер входа задан явно, чтобы число не зависело от того, что кто-то
//! допишет в примеры.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    reason = "бенчмарк не на user-facing пути компилятора"
)]

use std::fmt::Write as _;

use adamas_core::source::SourceFile;
use adamas_warmup_stlc::{check, run};
use criterion::{Criterion, criterion_group, criterion_main};

/// Цепочка из `bindings` полиморфных `let`-связываний. Каждое обобщается и
/// инстанцируется, то есть нагружает именно метаконтекст, а не парсер.
fn chain(bindings: usize) -> String {
    let mut source = String::new();
    for index in 0..bindings {
        let _ = writeln!(
            source,
            "let f{index} = \\x -> \\y -> if x < y then x + {index} else y in"
        );
        let _ = writeln!(source, "let g{index} = \\k -> k f{index} in");
    }
    let _ = write!(source, "f0 1 2");
    source
}

/// Рекурсия с реальным числом шагов: нагружает интерпретатор, а не типизацию.
const FIB: &str = "
    let rec fib = \\n -> if n < 2 then n else fib (n - 1) + fib (n - 2) in
    fib 18
";

fn pipeline(c: &mut Criterion) {
    let big = SourceFile::new("chain.stlc", chain(64));
    let fib = SourceFile::new("fib.stlc", FIB);

    check(&big).expect("бенчмарк-программа обязана типизироваться");
    run(&fib).expect("бенчмарк-программа обязана вычисляться");

    c.bench_function("check_let_chain_64", |b| {
        b.iter(|| check(&big).expect("типизируется"));
    });

    c.bench_function("run_fib_18", |b| {
        b.iter(|| run(&fib).expect("вычисляется"));
    });
}

criterion_group!(benches, pipeline);
criterion_main!(benches);
