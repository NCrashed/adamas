//! Отказ ядра, доведённый до места в исходнике (§10 вопрос 49б).
//!
//! Проверяется одно: **что подчёркнуто**. Текст сообщения - работа
//! рендеринга, а здесь важно, что маршрут ядра прошёл обратно по дереву и
//! указал на тот фрагмент, который написан неверно, а не на объявление целиком.

use adamas_elab::{ElabError, elaborate};
use adamas_parser::parse;

/// `Nat` и `Bool` - база, на которой пишется всё остальное.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

";

/// Фрагмент, который подчеркнёт диагностика. Отказ обязан прийти от ядра.
fn underlined(text: &str) -> String {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    let Err(error) = elaborate(&module) else {
        panic!("ожидался отказ")
    };
    assert!(
        matches!(error, ElabError::Core { .. }),
        "отказ обязан прийти от ядра, получено {error:?}"
    );
    let span = error.span();
    text[span.start()..span.end()].to_owned()
}

#[test]
fn a_clause_body_is_underlined_not_the_whole_definition() {
    // Единственная клауза без разбора: дерево - одна лямбда, и маршрут ведёт
    // прямо в тело.
    let text = format!("{BASE}f : Nat -> Bool\nf n = n\n");
    assert_eq!(underlined(&text), "n");
}

#[test]
fn the_route_reaches_the_body_of_the_second_clause() {
    // Дерево разбора: маршрут идёт через `Branch`, и вывести из формы, какая
    // клауза за ветвью стоит, нельзя - соответствие записывает сборка.
    let text = format!(
        "{BASE}f : Nat -> Bool
f Zero = True
f (Succ k) = k
"
    );
    assert_eq!(underlined(&text), "k");
}

#[test]
fn a_refusal_in_the_type_is_underlined_in_the_type() {
    // `Nat Nat` в домене: маршрут `MemberType`, `Domain`.
    let text = format!("{BASE}f : Nat Nat -> Bool\n");
    assert_eq!(underlined(&text), "Nat Nat");
}

#[test]
fn a_refusal_in_the_codomain_is_underlined_there() {
    let text = format!("{BASE}f : Nat -> Bool Bool\n");
    assert_eq!(underlined(&text), "Bool Bool");
}

#[test]
fn a_dependent_binder_names_its_own_domain() {
    // Группа `(0 n : Nat Nat)` разворачивается в `Pi`, и кадр `Domain` ведёт
    // в написанный тип связывания, а не в объявление.
    let text = format!("{BASE}f : (0 n : Nat Nat) -> Bool\n");
    assert_eq!(underlined(&text), "Nat Nat");
}

#[test]
fn a_refusal_in_a_constructor_names_that_constructor() {
    let text = format!(
        "{BASE}data Odd where
  One : Odd
  Two : Nat
"
    );
    assert_eq!(underlined(&text), "Nat");
}

#[test]
fn a_let_value_is_underlined_not_the_let() {
    let text = format!(
        "{BASE}two : Nat
two =
  let one : Nat = True
  Succ one
"
    );
    assert_eq!(underlined(&text), "True");
}

#[test]
fn a_type_refused_by_the_clause_compiler_is_underlined_in_the_signature() {
    // Тип проверяет сборка клауз, а написан он в сигнатуре - на две
    // декларации выше того места, где сборка споткнулась.
    let text = format!("{BASE}f : Nat Nat -> Bool\nf n = True\n");
    let module = parse(&text).expect("разбирается");
    let error = elaborate(&module).expect_err("ожидался отказ");
    assert!(
        matches!(error, ElabError::Clauses { .. }),
        "получено {error:?}"
    );
    let span = error.span();
    assert_eq!(&text[span.start()..span.end()], "Nat Nat");
}

#[test]
fn an_unreachable_clause_names_that_clause() {
    // Отказ сборки, носящий номер клаузы, показывается на ней самой.
    let text = format!(
        "{BASE}f : Nat -> Bool
f n = True
f Zero = False
"
    );
    let module = parse(&text).expect("разбирается");
    let error = elaborate(&module).expect_err("ожидался отказ");
    let span = error.span();
    assert_eq!(&text[span.start()..span.end()], "f Zero = False");
}

#[test]
fn a_refusal_without_a_route_falls_back_to_the_declaration() {
    // Занятое имя - отказ про объявление целиком, а не про подтерм: маршрут
    // пуст, и выдумывать место не из чего.
    let text = format!("{BASE}data Bool where\n  Yes : Bool\n");
    assert_eq!(underlined(&text), "data Bool where\n  Yes : Bool");
}
