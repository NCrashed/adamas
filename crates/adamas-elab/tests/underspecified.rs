//! Недописанная ссылка - разделение параметров объемлющего (§3.5, §10 в. 139).
//!
//! Ссылка на себя или соседа по группе объявления несёт меньше аргументов,
//! чем объявляет арность: её параметры - те же параметры объемлющего,
//! разделённые, а не инстанцированные. Форма названа в §3.5, и инвариант
//! охраняется здесь: **всякая** недописанная ссылка обязана указывать на
//! себя либо на члена своей группы (`Functor#List.map` внутри
//! `Functor#List`). Дикая недописанная ссылка - дефект элаборации, а не
//! новая форма.
//!
//! Мутант мысленный: расползись форма на чужие ссылки - фильтр по объемлющему
//! имени их не пропустит, и тест назовёт места; потребителям терма
//! (специализация §6) такие места читать не по чему.

use std::collections::BTreeSet;

use adamas_core::meta::Metas;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::{Owned, Warnings};

#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанный корпус, и падать он должен громко"
)]
fn elaborated(source: &str) -> Signature {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect("исходник обязан проходить проверку");
    signature
}

/// Собирает недописанные ссылки терма: имя цели при объемлющем `at`.
fn scan(signature: &Signature, term: &Term, at: &str, found: &mut BTreeSet<(String, String)>) {
    let recur = |inner: &Term, found: &mut BTreeSet<(String, String)>| {
        scan(signature, inner, at, found);
    };
    match term {
        Term::Const(name, levels, args) => {
            if let Some(def) = signature.lookup(name) {
                if args.row_args().len() < def.row_arity as usize
                    || args.mult_args().len() < def.mult_allowed.len()
                    || levels.len() < def.level_arity as usize
                {
                    found.insert((at.to_owned(), name.to_string()));
                }
            }
        }
        Term::Lam(_, _, body) => recur(body, found),
        Term::App(callee, argument) => {
            recur(callee, found);
            recur(argument, found);
        }
        Term::Pi(_, _, domain, _, codomain) => {
            recur(domain, found);
            recur(codomain, found);
        }
        Term::Let(_, _, ty, value, body) => {
            recur(ty, found);
            recur(value, found);
            recur(body, found);
        }
        Term::Record(fields) | Term::Row(fields) => {
            for field in fields.iter() {
                recur(&field.ty, found);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                recur(value, found);
            }
        }
        Term::With(base, fields) => {
            recur(base, found);
            for (_, value) in fields.iter() {
                recur(value, found);
            }
        }
        Term::Project(record, _) => recur(record, found),
        Term::Case(case) => {
            recur(&case.scrutinee, found);
            recur(&case.motive, found);
            for branch in &case.branches {
                recur(&branch.body, found);
            }
        }
        _ => {}
    }
}

/// Своя группа: сама ссылка либо член под её квалификацией.
fn own_group(enclosing: &str, target: &str) -> bool {
    target == enclosing || target.starts_with(&format!("{enclosing}."))
}

#[test]
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанный корпус, и падать он должен громко"
)]
fn an_underspecified_reference_points_into_its_own_group() {
    for file in ["interpreter", "prelude", "functor"] {
        let path = format!(
            "{}/../../tests/golden/eval/{file}.adamas",
            env!("CARGO_MANIFEST_DIR")
        );
        let source = std::fs::read_to_string(&path).expect("файл корпуса обязан читаться");
        let signature = elaborated(&source);
        let mut found = BTreeSet::new();
        let mut names = signature.names();
        names.sort();
        for name in names {
            let Some(def) = signature.lookup(&name) else {
                continue;
            };
            scan(&signature, &def.ty, &name, &mut found);
            if let Some(body) = &def.body {
                scan(&signature, body, &name, &mut found);
            }
        }
        let wild: Vec<_> = found
            .iter()
            .filter(|(enclosing, target)| !own_group(enclosing, target))
            .collect();
        assert!(
            wild.is_empty(),
            "дикие недописанные ссылки в {file}: {wild:?}"
        );
    }
}
