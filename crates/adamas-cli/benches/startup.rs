//! Холодный старт драйвера — target §6 «старт компилятора < 100ms cold».
//!
//! Мерится полный цикл fork/exec/exit: пользователь ждёт в том числе накладные
//! расходы ОС. Точка отсчёта для того, что появится позже — линковки LLVM,
//! загрузки prelude, инициализации salsa.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    reason = "бенчмарк не на user-facing пути компилятора"
)]

use std::process::Command;

use criterion::{Criterion, criterion_group, criterion_main};

fn startup(c: &mut Criterion) {
    let exe = env!("CARGO_BIN_EXE_adamas");

    c.bench_function("cli_startup_version", |b| {
        b.iter(|| {
            let output = Command::new(exe)
                .arg("--version")
                .output()
                .expect("driver runs");
            assert!(
                output.status.success(),
                "driver exited with {}",
                output.status
            );
        });
    });
}

criterion_group!(benches, startup);
criterion_main!(benches);
