//! Baseline для пути проверки типов - того, что Фаза 1 собственно и сдала.
//!
//! `nbe.rs` меряет нормализацию и конвертируемость, то есть срез, готовый ещё
//! до Фазы 1. Ни `check`/`infer`, ни учёт кратностей, ни δ-разворот через
//! `instantiate_body`, ни дерево разбора им не покрыты, и три из них - места, о
//! стоимости которых есть догадки, а не числа. Здесь по точке на каждое.
//!
//! - `check_lambda_chain` - глубокий контекст без единого редекса. Меряет
//!   стоимость вектора использований: он плотный и длиной в контекст, а
//!   заводится заново на каждом узле.
//! - `normalize_case_tree` - полностью применённое дерево разбора. `eval`
//!   собирает застрявший разбор до того, как посмотрит на голову
//!   разбираемого, поэтому вычисляет мотив и все ветви, а не выбранную.
//! - `check_through_delta` - проверка, упирающаяся в δ-разворот рекурсивного
//!   определения. Каждый шаг заново инстанцирует тело.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    reason = "заготовка бенча - не пользовательский вход; отказ здесь означает \
              сломанный бенч, и падать он должен громко"
)]

use std::rc::Rc;

use adamas_core::check::check_closed;
use adamas_core::eval::normalize;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern, compile};
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use criterion::{Criterion, criterion_group, criterion_main};

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
}

fn arrow(domain: Term, codomain: Term) -> Term {
    pi(Mult::Many, "_", domain, codomain)
}

fn lam(mult: Mult, name: &str, body: Term) -> Term {
    Term::Lam(mult, name.into(), Rc::new(body))
}

fn c(name: &str) -> Term {
    Term::constant(name)
}

/// `Bool` с двумя конструкторами и `Nat` с `zero`/`succ`.
fn base() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .declare_data("Bool", 0, &mut metas, Term::universe(0))
        .expect("Bool");
    for name in ["true", "false"] {
        signature
            .declare_constructor("Bool", name, &mut metas, c("Bool"))
            .expect("конструктор Bool");
    }
    signature
        .declare_data("Nat", 0, &mut metas, Term::universe(0))
        .expect("Nat");
    signature
        .declare_constructor("Nat", "zero", &mut metas, c("Nat"))
        .expect("zero");
    signature
        .declare_constructor("Nat", "succ", &mut metas, arrow(c("Nat"), c("Nat")))
        .expect("succ");
    signature
}

/// `(ω x1 : Bool) -> … -> (ω xn : Bool) -> Bool` и `\x1 … xn -> x1`.
///
/// Тело трогает только самое внешнее связывание: интересна не работа с термом,
/// а цена вести учёт использований на контексте глубины `n`.
fn lambda_chain(depth: u32) -> (Term, Term) {
    let ty = (0..depth).fold(c("Bool"), |tail, _| pi(Mult::Many, "x", c("Bool"), tail));
    let body = Term::var(depth - 1);
    let term = (0..depth).fold(body, |inner, _| lam(Mult::Many, "x", inner));
    (term, ty)
}

/// Дерево разбора из `2^depth` клауз над `Bool`, **термом**, а не определением.
///
/// Именно термом: `eval` определений не разворачивает, поэтому применённое
/// определение осталось бы застрявшим и дерево не вычислилось бы ни разу.
fn case_tree(signature: &Signature, depth: u32) -> Term {
    let ty = (0..depth).fold(c("Bool"), |tail, _| arrow(c("Bool"), tail));
    let clauses: Vec<Clause> = (0..1u32 << depth)
        .map(|mask| Clause {
            patterns: (0..depth)
                .map(|bit| {
                    let name = if mask >> bit & 1 == 1 {
                        "true"
                    } else {
                        "false"
                    };
                    Pattern::Constructor(name.into(), Vec::new())
                })
                .collect(),
            body: if mask.count_ones() % 2 == 0 {
                c("true")
            } else {
                c("false")
            },
        })
        .collect();
    compile(signature, &mut Metas::default(), &ty, &clauses).expect("дерево собирается")
}

/// `plus` клаузами - рекурсивное определение, разворот которого стоит шаг на
/// каждую единицу.
fn plus(signature: &mut Signature) {
    let ty = arrow(c("Nat"), arrow(c("Nat"), c("Nat")));
    let clauses = [
        Clause {
            patterns: vec![
                Pattern::Constructor("zero".into(), Vec::new()),
                Pattern::Var("m".into()),
            ],
            body: Term::var(0),
        },
        Clause {
            patterns: vec![
                Pattern::Constructor("succ".into(), vec![Pattern::Var("k".into())]),
                Pattern::Var("m".into()),
            ],
            body: c("succ").apply([c("plus").apply([Term::var(1), Term::var(0)])]),
        },
    ];
    let body = compile(signature, &mut Metas::default(), &ty, &clauses).expect("plus собирается");
    signature
        .define("plus", Mult::Many, 0, ty, Some(body))
        .expect("plus типизируется");
}

fn number(value: u32) -> Term {
    (0..value).fold(c("zero"), |term, _| c("succ").apply([term]))
}

fn checking(criterion: &mut Criterion) {
    let signature = base();

    for depth in [16u32, 64] {
        let (term, ty) = lambda_chain(depth);
        criterion.bench_function(&format!("check_lambda_chain_{depth}"), |b| {
            b.iter(|| {
                check_closed(&signature, &term, &ty).expect("типизируется");
            });
        });
    }

    for depth in [4u32, 8] {
        let applied = case_tree(&signature, depth)
            .apply((0..depth).map(|bit| if bit % 2 == 0 { c("true") } else { c("false") }));
        criterion.bench_function(&format!("normalize_case_tree_{depth}"), |b| {
            b.iter(|| normalize(&applied));
        });
    }

    // Проверка `anything (plus 8 8)` против `anything 16`: конвертируемость
    // упирается в δ-разворот `plus` шестнадцать раз подряд.
    let mut with_plus = base();
    plus(&mut with_plus);
    with_plus
        .postulate(
            "P",
            Mult::Many,
            0,
            pi(Mult::Zero, "n", c("Nat"), Term::universe(0)),
        )
        .expect("P");
    with_plus
        .postulate(
            "anything",
            Mult::Many,
            0,
            pi(Mult::Zero, "n", c("Nat"), c("P").apply([Term::var(0)])),
        )
        .expect("anything");
    let witness = c("anything").apply([number(16)]);
    let stated = c("P").apply([c("plus").apply([number(8), number(8)])]);
    criterion.bench_function("check_through_delta_plus_8_8", |b| {
        b.iter(|| {
            check_closed(&with_plus, &witness, &stated).expect("8+8 конвертируемо с 16");
        });
    });
}

criterion_group!(benches, checking);
criterion_main!(benches);
