//! Обратная печать: что она выдаёт и что после неё разбирается обратно.

use adamas_parser::ast::{Module, dump};
use adamas_parser::{parse, print};
use proptest::prelude::*;

/// Корпус: по программе на каждую форму подмножества Фазы 2. Один и тот же для
/// снапшотов, round-trip и идемпотентности - иначе свойство держалось бы на
/// одних примерах, а печать проверялась на других.
const PROGRAMS: &[(&str, &str)] = &[
    (
        "signature_and_clauses",
        "\
map : (a -> b) -> Vect n a -> Vect n b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
",
    ),
    (
        "indexed_family",
        "\
data Vect : (0 n : Nat) -> Type -> Type where
  Nil  : Vect 0 a
  Cons : a -> Vect n a -> Vect (n + 1) a
",
    ),
    (
        "family_with_parameters",
        "\
data Pair a b where
  MkPair : a -> b -> Pair a b

data Void : Type
",
    ),
    (
        "type_members",
        "\
type Twice a = Pair a a

type Endo (a : Type) = a -> a

module type BagSig where
  type Bag (a : Type)
  empty : Bag Int
",
    ),
    (
        "effect_rows",
        "\
State : Type -> Effect

step : Bool -> {State Bool} Bool

both : Bool -> {IO, State Bool | e} Bool
",
    ),
    (
        "parameter_defaults",
        "\
data Pair (a : Type) (b = a) where
  Both : a -> b -> Pair a b

type Store (a : Type) (idx = UInt32) = idx -> a

class Mul a (b = a) where
  mul : a -> b -> a
",
    ),
    (
        "classes_and_instances",
        "\
coherent class Key a when Eqv a where
  key : a -> Nat

instance Key Int where
  key n = n

instance productMonoid : Monoid Int where
  unit = 1
",
    ),
    (
        "block_of_statements",
        "\
counter =
  let n = get
  put (n + 1)
  n
",
    ),
    (
        "several_bindings_in_one_let",
        "\
sum =
  let
    a = 1
    b = 2
  add a b
",
    ),
    (
        "blocks_nested_in_blocks",
        "\
counter =
  let w = case x of
            A -> 1
  w

f x = y
  where
    g z = case z of
      A -> 1
    h = g x
",
    ),
    (
        "blocks_in_tail_position",
        "\
f = g case x of
  A -> 1

h = k \\y -> case y of
  A -> 2

m = a + case x of
  A -> 3
",
    ),
    (
        "where_after_a_tall_body",
        "\
f x =
  let y = 1
  g y
where
  g z = z
",
    ),
    (
        "resource_with_drop",
        "\
resource File where
  Open : String -> File
  drop : File -> Unit
  drop h = closeFile h
",
    ),
    (
        "unique_family",
        "\
unique data Array (0 n : Nat) a where
  MkArray : Array n a
",
    ),
    (
        "local_definitions",
        "\
f x = y
  where
    y = g x
    z : Nat
    z = h y
",
    ),
    (
        "lambdas",
        "\
f = \\x -> x
g = \\(0 a : Type) x -> x
h = \\() -> get
",
    ),
    (
        "case_and_conditional",
        "\
classify x = case x of
  Cons y ys -> y
  Nil       -> zero

choice x = if isZero x then none else some x
",
    ),
    (
        "operators_literals_and_holes",
        "\
f = a + b * c
g = h (-42) 0xff \"текст\" 3.14 _
items = [1, 2, 3]
pair = (a, b)
unit = ()
(++) : List a -> List a -> List a
",
    ),
    (
        "binders_and_type_application",
        "\
groups : (a : Type) (b : Type) -> Type
implicits : {0 a : Type} -> (1 h : File) -> a
apply = runExcept @IOError prog
",
    ),
];

/// Разбор, который обязан удаться.
fn tree(text: &str) -> Module {
    match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("исходник корпуса не разобрался: {error}"),
    }
}

#[test]
fn the_corpus_prints_as_adamas() {
    let mut printed = String::new();
    for (name, source) in PROGRAMS {
        printed.push_str("=== ");
        printed.push_str(name);
        printed.push('\n');
        printed.push_str(&print(&tree(source)));
    }
    insta::assert_snapshot!(printed);
}

#[test]
fn printing_survives_a_round_trip() {
    // Договор печати: `parse(print(m))` даёт `m` с точностью до спанов.
    // Сравниваются дампы - они спанов не показывают, и это ровно та точность.
    for (name, source) in PROGRAMS {
        let module = tree(source);
        let reparsed = match parse(&print(&module)) {
            Ok(reparsed) => reparsed,
            Err(error) => panic!(
                "{name}: печать не разобралась обратно: {error}\n{}",
                print(&module)
            ),
        };
        assert_eq!(dump(&reparsed), dump(&module), "{name}");
    }
}

#[test]
fn printing_is_idempotent() {
    // Печать канонична: второй проход ничего не меняет. Без этого «канонично»
    // означало бы только «детерминированно».
    for (name, source) in PROGRAMS {
        let once = print(&tree(source));
        let twice = print(&tree(&once));
        assert_eq!(twice, once, "{name}");
    }
}

#[test]
fn a_body_block_of_one_statement_stays_a_block() {
    // `f = e` и `f =` с телом-блоком из одного оператора - разные деревья, и
    // печать обязана их различать, иначе round-trip тихо схлопывает одно в
    // другое.
    let inline = print(&tree("f = g x\n"));
    let block = print(&tree("f =\n  g x\n"));
    assert_eq!(inline, "f = g x\n");
    assert_eq!(block, "f =\n  g x\n");
}

#[test]
fn parentheses_are_restored_where_precedence_needs_them() {
    // Скобки не хранятся в дереве, поэтому печать ставит их заново - и там,
    // где они нужны, а не там, где стояли.
    let cases = [
        ("f = g (h x)\n", "f = g (h x)\n"),
        ("f = ((g x))\n", "f = g x\n"),
        ("f : (a -> b) -> c\n", "f : (a -> b) -> c\n"),
        ("f : a -> (b -> c)\n", "f : a -> b -> c\n"),
        ("f = g (a + b)\n", "f = g (a + b)\n"),
        ("f = (\\x -> x) y\n", "f = (\\x -> x) y\n"),
        ("f = a + g x\n", "f = a + g x\n"),
    ];
    for (source, expected) in cases {
        assert_eq!(print(&tree(source)), expected, "для {source:?}");
    }
}

#[test]
fn a_conditional_breaks_when_its_then_branch_opens_a_block() {
    // Ветка «да», кончающаяся блоком, съела бы `else` внутрь этого блока.
    let source = "\
f x = if c then case x of
                  A -> 1
              else 2
";
    let printed = print(&tree(source));
    insta::assert_snapshot!(printed);
    assert_eq!(dump(&tree(&printed)), dump(&tree(source)));
}

#[test]
fn a_long_application_spine_prints_without_recursion() {
    // Аргументы разбор набирает циклом, вложенности записи на них не
    // тратится, а звено терма даёт каждый - и предел вложенности их считает
    // (§10 вопрос 62). Печать по спайну идёт циклом и на предельной длине
    // рекурсией не пользуется; проверяется ровно граница, потому что за ней
    // текста для печати уже не бывает.
    let text = format!("f = g{}\n", " x".repeat(256));
    assert_eq!(print(&tree(&text)), text);
}

/// Выражения, собранные из фрагментов, - каждое скобочно замкнуто, поэтому
/// подставляется в любую позицию и всегда разбирается.
///
/// Корпус выше проверяет формы по одной; здесь проверяются их сочетания, а
/// печать ломается именно на них: скобки ставятся по приоритету позиции, и
/// ошибка видна только тогда, когда узел попал в позицию, для которой его не
/// проверяли.
fn expression() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        Just("x".to_owned()),
        Just("y".to_owned()),
        Just("42".to_owned()),
        Just("(-1)".to_owned()),
        Just("0xff".to_owned()),
        Just("3.14".to_owned()),
        Just("\"s\"".to_owned()),
        Just("_".to_owned()),
        Just("()".to_owned()),
    ];
    leaf.prop_recursive(4, 48, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(f, x)| format!("({f} {x})")),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("({a} + {b})")),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("({a} -> {b})")),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("((0 z : {a}) -> {b})")),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("({a}, {b})")),
            (inner.clone(), inner.clone(), inner.clone())
                .prop_map(|(c, t, e)| format!("(if {c} then {t} else {e})")),
            inner.clone().prop_map(|body| format!("(\\z -> {body})")),
            inner.clone().prop_map(|item| format!("[{item}]")),
            inner.prop_map(|argument| format!("(g @({argument}))")),
        ]
    })
}

/// Объявление вокруг выражения.
///
/// Формы с блоками - `case` и тело-цепочка - живут только здесь и только в
/// хвосте: разбор пропускает такую форму лишь туда, где за ней на строке
/// ничего не стоит (§4.1), поэтому в [`expression`], где фрагмент замкнут
/// скобками и за ним всегда что-то следует, их нет.
fn declaration() -> impl Strategy<Value = String> {
    prop_oneof![
        expression().prop_map(|body| format!("f = {body}\n")),
        expression().prop_map(|ty| format!("f : {ty}\n")),
        expression().prop_map(|body| format!("f z = {body}\n")),
        (expression(), expression()).prop_map(|(a, b)| format!("f =\n  let w = {a}\n  {b}\n")),
        (expression(), expression())
            .prop_map(|(a, b)| format!("f z = case z of\n  A w -> {a}\n  _ -> {b}\n")),
        (expression(), expression())
            .prop_map(|(a, b)| format!("f z = {a}\n  where\n    w = {b}\n")),
        // `where` после трёх видов тела: выражения, блока операторов и веток
        // `case`. Блоки у них закрываются по разным правилам, и печать обязана
        // выбрать отступ `where` под каждое.
        (expression(), expression())
            .prop_map(|(a, b)| format!("f z =\n  {a}\n  where\n    w = {b}\n")),
        (expression(), expression())
            .prop_map(|(a, b)| format!("f z = case z of\n  A -> {a}\nwhere\n  w = {b}\n")),
        expression().prop_map(|ty| format!("data D : Type where\n  C : {ty}\n")),
        // Форма с блоком в хвосте: аргументом, телом лямбды-аргумента и
        // операндом цепочки. Скобок вокруг неё быть не может, и печать обязана
        // их не поставить.
        expression().prop_map(|body| format!("f = g case z of\n  A -> {body}\n")),
        expression().prop_map(|body| format!("f = g \\w -> case w of\n  A -> {body}\n")),
        expression().prop_map(|operand| format!("f = {operand} + case z of\n  A -> 1\n")),
    ]
}

proptest! {
    /// Round-trip на сочетаниях форм.
    #[test]
    fn generated_declarations_survive_printing(text in declaration()) {
        let module = match parse(&text) {
            Ok(module) => module,
            Err(error) => return Err(TestCaseError::fail(
                format!("сгенерированное не разобралось: {error}\n{text}")
            )),
        };
        let printed = print(&module);
        let reparsed = parse(&printed);
        prop_assert!(
            reparsed.is_ok(),
            "печать не разобралась обратно: {:?}\nисходник:\n{text}\nпечать:\n{printed}",
            reparsed.err()
        );
        if let Ok(reparsed) = reparsed {
            prop_assert_eq!(dump(&reparsed), dump(&module), "\nпечать:\n{}", printed);
            prop_assert_eq!(print(&reparsed), printed.clone(), "печать не идемпотентна");
        }
    }

    /// Round-trip на всём, что вообще разобралось. Текст случайный, поэтому
    /// разбирается редко - но каждый случай, который разобрался, проверяется
    /// целиком.
    #[test]
    fn anything_that_parses_survives_printing(text in "(?s).{0,300}") {
        let Ok(module) = parse(&text) else { return Ok(()) };
        let printed = print(&module);
        let reparsed = parse(&printed);
        prop_assert!(
            reparsed.is_ok(),
            "печать не разобралась обратно: {:?}\n{printed}",
            reparsed.err()
        );
        if let Ok(reparsed) = reparsed {
            prop_assert_eq!(dump(&reparsed), dump(&module));
        }
    }

    /// То же на подмножестве лексики, где разбор удаётся заметно чаще.
    #[test]
    fn plausible_input_survives_printing(text in r"[a-z0-9=()\[\],:\\ \n-]{0,120}") {
        let Ok(module) = parse(&text) else { return Ok(()) };
        let printed = print(&module);
        let reparsed = parse(&printed);
        prop_assert!(
            reparsed.is_ok(),
            "печать не разобралась обратно: {:?}\n{printed}",
            reparsed.err()
        );
        if let Ok(reparsed) = reparsed {
            prop_assert_eq!(dump(&reparsed), dump(&module));
        }
    }
}

#[test]
fn a_where_after_a_case_body_stays_printable() {
    // Ветки `case` - блок объявлений, и `where` на их колонке его не закрывает:
    // правило про `where` выпускает из блоков `=` и `let`, а этот открыт `of`.
    let source = "\
f x = case x of
  A -> 1
where
  z = 2
";
    let printed = print(&tree(source));
    assert_eq!(
        dump(&tree(&printed)),
        dump(&tree(source)),
        "печать:\n{printed}"
    );
}
