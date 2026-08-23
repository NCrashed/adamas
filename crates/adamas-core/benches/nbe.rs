//! Baseline для нормализации и конвертируемости.
//!
//! Первый бенчмарк, который меряет ядро, а не warm-up: именно его ждала
//! публикация истории замеров (§9 Фаза 1). Три точки, разделённые намеренно.
//!
//! - `normalize_church_add` - β-редукция с реальной работой: замыкания
//!   создаются и применяются, спайны растут.
//! - `normalize_nested_pi` - обход без единого редекса. Стоимость самого
//!   `quote`, то есть цена "пройти по типу и ничего не упростить".
//! - `convertible_deep_pi` - definitional equality на паре одинаковых типов,
//!   то есть худший случай: расхождения нет, сравнение доходит до листьев.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]

use std::rc::Rc;

use adamas_core::conv::convertible;
use adamas_core::eval::{eval, normalize};
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_core::value::Env;
use criterion::{Criterion, criterion_group, criterion_main};

fn lam(body: Term) -> Term {
    Term::Lam(Mult::Many, "x".into(), Rc::new(body))
}

fn arrow(domain: Term, codomain: Term) -> Term {
    Term::Pi(Mult::Many, "_".into(), Rc::new(domain), Rc::new(codomain))
}

/// Числа Чёрча: `\f -> \x -> f (f (… x))`, `n` применений.
fn church(n: u32) -> Term {
    let body = (0..n).fold(Term::var(0), |acc, _| Term::var(1).apply([acc]));
    lam(lam(body))
}

/// `\m -> \n -> \f -> \x -> m f (n f x)` в применении к двум числам.
fn church_add(left: u32, right: u32) -> Term {
    let plus = lam(lam(lam(lam(Term::var(3)
        .apply([Term::var(1)])
        .apply([Term::var(2).apply([Term::var(1), Term::var(0)])])))));
    plus.apply([church(left), church(right)])
}

/// Цепочка стрелок `Type 0 -> Type 0 -> … -> Type 0` без редексов.
fn nested_pi(depth: u32) -> Term {
    (0..depth).fold(Term::universe(0), |acc, _| arrow(Term::universe(0), acc))
}

fn nbe(c: &mut Criterion) {
    let addition = church_add(16, 16);
    let pi_chain = nested_pi(256);
    let pi_value = eval(&Env::default(), &pi_chain);

    c.bench_function("normalize_church_add_16_16", |b| {
        b.iter(|| normalize(&addition));
    });

    c.bench_function("normalize_nested_pi_256", |b| {
        b.iter(|| normalize(&pi_chain));
    });

    c.bench_function("convertible_deep_pi_256", |b| {
        b.iter(|| assert!(convertible(&Signature::default(), 0, &pi_value, &pi_value)));
    });
}

criterion_group!(benches, nbe);
criterion_main!(benches);
