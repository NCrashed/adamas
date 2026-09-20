//! Чего стоит машине сходить наружу (§5.3, §10 вопрос 182).
//!
//! Стенд трека C волны 1 Фазы 8, устроенный по образцу
//! `crates/adamas-codegen/benches/foreign.rs`: мерится **одно** - цена похода за
//! границу, - и мерится она разностью с точкой разложения, а не в абсолютных
//! числах.
//!
//! # Точки
//!
//! | Имя | Что в ней | Зачем |
//! |---|---|---|
//! | `resolve` | `dlopen` + `dlsym` на **загруженной** библиотеке | цена повторного разрешения; холодная стоит отдельно, ниже |
//! | `bare` | вызов по разрешённому адресу мимо машины | цена собственно границы |
//! | `machine` | `cbrt 27.0` целиком машиной | цена границы вместе с машиной |
//! | `inside` | `id 27.0` целиком машиной | точка разложения: терм той же формы без похода наружу |
//! | `rust` | `f64::cbrt` из Rust | пол: кубический корень без всякого посредника |
//!
//! Читается таблица разностями. `machine − inside` есть цена **хождения
//! наружу** в машине; `bare − resolve` есть цена собственно вызова, а `resolve`
//! - цена того, что заготовка разрешает символ на каждом вызове заново.
//!
//! Пол `rust` берётся у **другой** реализации: Rust линкует собственный `cbrt`
//! из compiler-builtins и `libm.so.6` не подключает вовсе. Годится он поэтому
//! только как порядок величины самого корня, но не как оракул ответа
//! (`tests/outward.rs`, `the_answer_comes_from_glibc_and_not_from_rust`).
//!
//! # Холодная загрузка мерится один раз и вне criterion
//!
//! `dlopen` библиотеки, ещё не загруженной в процесс, случается в процессе
//! ровно однажды: второй `dlopen` того же имени попадает в счётчик ссылок
//! динамического загрузчика, а у нас - ещё раньше, в таблицу разрешённых. Взять
//! выборку негде, и стенд её не подделывает: печатается одно измерение с
//! `Instant`, и это честно названо одной выборкой. Порядок величины - то
//! единственное, о чём оно говорит.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::rc::Rc;
use std::time::Instant;

use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use adamas_core::value::Env;
use criterion::{Criterion, criterion_group};

use adamas_interp::{Foreign, Machine};

/// Библиотека и символ: обоснование выбора - в `docs/phase8-trackC-notes.md`.
const LIBRARY: &str = "libm.so.6";
/// Символ: `double cbrt(double)`.
const SYMBOL: &str = "cbrt";
/// Аргумент: 27 - куб, на котором `cbrt` glibc **не** точен, и это наблюдаемо.
const INPUT: f64 = 27.0;

/// Объявление чужой функции.
fn declared() -> Foreign {
    Foreign::new(LIBRARY, SYMBOL, &[PrimTy::Float64], PrimTy::Float64)
}

/// Сигнатура с постулатом `cbrt : Float64 -> Float64` и терм `cbrt 27.0`.
///
/// Постулат, а не определение: тело развернулось бы раньше, чем машина дошла бы
/// до внешнего вызова.
fn program(name: &str) -> (Signature, Term) {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(
            &mut metas,
            name,
            Mult::Many,
            0,
            Term::Pi(
                Binder::explicit(Mult::Many),
                "x".into(),
                Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
                Row::empty(),
                Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
            ),
        )
        .expect("постулат обязан объявляться");
    let term =
        Term::constant(name).apply([Term::Prim(Prim::literal(PrimTy::Float64, INPUT.to_bits()))]);
    (signature, term)
}

/// Точка разложения: тот же терм той же формы, за границу не ходящий.
///
/// `id 27.0` при `id = \x -> x`: **одно** применение и одно имя верхнего уровня,
/// как у `cbrt 27.0`. Арифметика ядра сюда не годится - у неё два аргумента, то
/// есть второе применение и второй кадр, и разность мерила бы форму терма, а не
/// поход наружу (измерено: `addFloat64 27.0 0.0` идёт 514 нс против 348 нс у
/// чужого вызова, то есть точка разложения оказывалась бы **дороже** мерянного).
fn decomposition() -> (Signature, Term) {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let ty = Term::Pi(
        Binder::explicit(Mult::Many),
        "x".into(),
        Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
        Row::empty(),
        Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
    );
    signature
        .define(
            &mut metas,
            "id",
            Mult::Many,
            0,
            ty,
            Some(Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)))),
        )
        .expect("тождество обязано объявляться");
    let term =
        Term::constant("id").apply([Term::Prim(Prim::literal(PrimTy::Float64, INPUT.to_bits()))]);
    (signature, term)
}

/// Холодная загрузка: одна выборка, печатается в stderr.
fn cold() {
    let it = declared();
    let started = Instant::now();
    it.resolve().expect("libm обязана загружаться");
    let took = started.elapsed();
    eprintln!("холодная загрузка {LIBRARY} + dlsym {SYMBOL}: {took:?} (одна выборка)");
}

fn outward(criterion: &mut Criterion) {
    cold();

    let it = declared();
    let bits = INPUT.to_bits();
    // Сверка до замера: мерить нечего, если путь отвечает не то. Тот же
    // порядок, что в `benches/foreign.rs`, - она стоит раньше наносекунд.
    //
    // Сверяется точный куб, а не `f64::cbrt`: `cbrt` в процессе **не один**.
    // Rust линкует собственный из compiler-builtins и `libm.so.6` не
    // подключает вовсе, а на 27 две реализации расходятся на один ULP
    // (`tests/outward.rs`, `the_answer_comes_from_glibc_and_not_from_rust`).
    assert_eq!(
        it.call(&[1000.0_f64.to_bits()])
            .expect("вызов обязан проходить"),
        10.0_f64.to_bits(),
        "чужой вызов ответил не кубический корень"
    );

    let mut group = criterion.benchmark_group("outward");

    group.bench_function("resolve", |bencher| {
        bencher.iter(|| it.resolve().unwrap());
    });
    group.bench_function("bare", |bencher| {
        bencher.iter(|| it.call(std::hint::black_box(&[bits])).unwrap());
    });

    let (signature, term) = program(SYMBOL);
    let mut machine = Machine::new(&signature);
    machine.declare_foreign(SYMBOL, declared());
    group.bench_function("machine", |bencher| {
        bencher.iter(|| machine.evaluate(&Env::default(), &term).unwrap());
    });

    let (plain, inside) = decomposition();
    let inner = Machine::new(&plain);
    group.bench_function("inside", |bencher| {
        bencher.iter(|| inner.evaluate(&Env::default(), &inside).unwrap());
    });

    group.bench_function("rust", |bencher| {
        bencher.iter(|| std::hint::black_box(std::hint::black_box(INPUT).cbrt()));
    });

    group.finish();
}

criterion_group!(benches, outward);

fn main() {
    benches();
    Criterion::default().configure_from_args().final_summary();
}
