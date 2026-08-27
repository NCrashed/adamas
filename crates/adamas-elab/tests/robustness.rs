//! Что элаборация обязана делать со **всяким** входом, а не с написанным от
//! руки.
//!
//! Проверяются два свойства, и оба про отказ, а не про успех: разобранная
//! программа не роняет элаборацию, а её отказ показывается человеку. Второе
//! важно не меньше первого - спан, вышедший за файл или разрезавший символ,
//! роняет уже печать, то есть компилятор падает на попытке объяснить ошибку.

use adamas_core::source::SourceFile;
use adamas_elab::{elaborate, report};
use adamas_parser::parse;
use proptest::prelude::*;

const BASE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

";

/// Выражения, собранные из фрагментов: каждое скобочно замкнуто, поэтому
/// подставляется и в тело, и в тип.
fn expression() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        Just("Zero"),
        Just("Succ"),
        Just("x"),
        Just("y"),
        Just("_"),
        Just("1"),
        Just("()"),
        Just("Type"),
        Just("Nat"),
    ]
    .prop_map(str::to_owned);
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone())
                .prop_map(|(callee, argument)| format!("({callee} {argument})")),
            (inner.clone(), inner.clone())
                .prop_map(|(domain, codomain)| format!("({domain} -> {codomain})")),
            (inner.clone(), inner.clone()).prop_map(|(left, right)| format!("({left}, {right})")),
            inner.clone().prop_map(|body| format!("(\\x -> {body})")),
            inner
                .clone()
                .prop_map(|ty| format!("((0 x : {ty}) -> Nat)")),
        ]
    })
}

/// Программа: то же выражение в теле и в типе - позиции разные, и правила в
/// них тоже.
fn program() -> impl Strategy<Value = String> {
    (expression(), expression())
        .prop_map(|(body, ty)| format!("{BASE}f : Nat -> Nat\nf x = {body}\n\ng : {ty}\n"))
}

proptest! {
    #[test]
    fn elaboration_answers_instead_of_falling(text in program()) {
        let Ok(module) = parse(&text) else { return Ok(()) };
        let Err(error) = elaborate(&module) else { return Ok(()) };
        let span = error.span();
        prop_assert!(span.end() <= text.len(), "спан за краем файла: {span:?}");
        prop_assert!(text.is_char_boundary(span.start()), "спан режет символ");
        prop_assert!(text.is_char_boundary(span.end()), "спан режет символ");
    }

    #[test]
    fn every_refusal_can_be_shown(text in program()) {
        let Ok(module) = parse(&text) else { return Ok(()) };
        let Err(error) = elaborate(&module) else { return Ok(()) };
        let file = SourceFile::new("проба.adamas", text);
        let shown = report(&file, &error);
        prop_assert!(shown.contains("проба.adamas"), "сообщение без позиции: {shown}");
        prop_assert!(shown.contains('^'), "сообщение без подчёркивания: {shown}");
    }
}
