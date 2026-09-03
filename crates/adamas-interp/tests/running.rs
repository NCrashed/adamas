//! Исполнение: машина считает то же, что ядро, и сверх того - эффекты.
//!
//! Два вычислителя обязаны сходиться на чистом фрагменте, иначе второй не
//! интерпретатор, а второй язык. Поэтому первым делом здесь стоит сверка с
//! `conv::evaluated`, и только потом то, чего ядро не умеет вовсе.

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;

/// `Nat`, `Bool` и `Unit` - база, без которой не пишется ни один пример.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

infixl 6 +
(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)
";

/// Элаборирует исходник, проверяя, что он принят.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отвергнутый исходник означает сломанный тест, и падать он должен громко"
)]
fn elaborated(source: &str) -> Signature {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    adamas_elab::elaborate(&module).expect("исходник обязан проходить проверку")
}

/// Тело определения с подставленными аргументами уровня и row.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отсутствие определения означает сломанный тест"
)]
fn body(signature: &Signature, name: &str) -> Term {
    let definition = signature.lookup(name).expect("определение объявлено");
    let body = definition.body.as_ref().expect("у определения есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

/// Значение по мнению машины.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: непогашенная операция означает сломанный тест"
)]
fn ran(source: &str, name: &str) -> String {
    let signature = elaborated(source);
    let body = body(&signature, name);
    adamas_interp::run(&signature, &body)
        .expect("операция обязана встретить хендлер")
        .to_string()
}

/// Значение по мнению ядра.
fn normalized(source: &str, name: &str) -> String {
    let signature = elaborated(source);
    let body = body(&signature, name);
    adamas_core::conv::evaluated(&signature, &body).to_string()
}

/// На чистом фрагменте вычислители сходятся.
///
/// Это договор между ними: машина заведена ради эффектов, а не ради другого
/// ответа на то же самое. Разойдись они здесь - и `adamas eval` перестал бы
/// говорить о той же программе, которую проверил `adamas check`.
#[test]
fn the_machine_agrees_with_the_core_on_the_pure_fragment() {
    let source = format!(
        "{BASE}
double : Nat -> Nat
double n = n + n

sum : List Nat -> Nat
sum Nil = Zero
sum (Cons x xs) = x + sum xs

nested : List Nat
nested = [double 2, sum [1, 2], 0]

applied : Nat
applied = double (double 3)

matched : Bool
matched = case Succ Zero of
  Zero -> False
  Succ k -> True
"
    );
    for name in ["nested", "applied", "matched", "double", "sum"] {
        assert_eq!(
            ran(&source, name),
            normalized(&source, name),
            "определение `{name}` посчиталось по-разному"
        );
    }
}

/// Хендлер глубокий: операция после возобновления попадает ему же.
#[test]
fn a_handler_survives_its_own_resumption() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

twice : {{Ask}} Nat
twice =
  let a : Nat = ask
  let b : Nat = ask
  a + b

main : Nat
main = handle twice with
  return v -> v
  ask -> resume 1
"
    );
    assert_eq!(ran(&source, "main"), "Succ (Succ Zero)");
}

/// Ветка, не зовущая резумпцию, обрывает вычисление.
#[test]
fn a_branch_without_resume_abandons_the_computation() {
    let source = format!(
        "{BASE}
effect Fail where
  fail : a

broken : {{Fail}} Nat
broken =
  let n : Nat = fail
  Succ (Succ n)

main : Nat
main = handle broken with
  return v -> Succ v
  fail -> Zero
"
    );
    // Ни `Succ` из `broken`, ни `Succ` из `return` не случились: ветка `fail`
    // и есть ответ хендлера.
    assert_eq!(ran(&source, "main"), "Zero");
}

/// `handleMulti` зовёт резумпцию дважды, и оба хода доходят до конца.
#[test]
fn a_multi_shot_resumption_runs_twice() {
    let source = format!(
        "{BASE}
effect Amb where
  toss : Bool

branching : {{Amb}} Nat
branching =
  let b : Bool = toss
  case b of
    True -> 1
    False -> 2

main : Nat
main = handleMulti branching with
  return v -> v
  toss -> resume True + resume False
"
    );
    assert_eq!(ran(&source, "main"), "Succ (Succ (Succ Zero))");
}

/// Чужая метка уходит наружу, а внутренний хендлер встаёт на её продолжении.
#[test]
fn a_foreign_label_passes_through_and_reinstalls_the_handler() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

effect Fail where
  fail : a

mixed : {{Ask, Fail}} Nat
mixed =
  let n : Nat = ask
  let m : Nat = ask
  n + m

inner : {{Ask}} Nat
inner = handle mixed with
  return v -> v
  fail -> Zero

main : Nat
main = handle inner with
  return v -> v
  ask -> resume 1
"
    );
    // Второй `ask` доходит до внешнего хендлера только если внутренний
    // переустановился после первого.
    assert_eq!(ran(&source, "main"), "Succ (Succ Zero)");
}

/// Значение, которое только возвращают, всё равно досчитывается.
///
/// Регрессия: разворот определения стоит у применения, разбора и проекции, а
/// `Cons answer Nil` не делает ни того, ни другого, ни третьего. Дочитывало
/// такое значение обратное чтение ядра, и хендлер под ним оставался нейтралью -
/// при том что соседний элемент списка, попавший под разбор, считался верно.
#[test]
fn a_value_that_is_only_returned_is_computed_too() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

asked : {{Ask}} Nat
asked =
  let n : Nat = ask
  n

answer : Nat
answer = handle asked with
  return v -> v
  ask -> resume 1

main : List Nat
main = Cons answer Nil
"
    );
    assert_eq!(ran(&source, "main"), "Cons{0} Nat (Succ Zero) (Nil{0} Nat)");
}
