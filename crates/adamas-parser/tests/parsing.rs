//! Разбор на примерах §4 и свойства, которые обязаны держаться на любом входе.

use adamas_parser::ast::dump;
use adamas_parser::parser::{ParseError, Unsupported};
use adamas_parser::{Error, parse};
use proptest::prelude::*;

/// Дерево s-выражениями. Ошибка возвращается, а не паникует: помощник зовут и
/// из тестов, которые её ждут.
fn tree(text: &str) -> Result<String, Error> {
    Ok(dump(&parse(text)?))
}

/// `count` строк подряд, каждая по своему номеру.
fn repeat(count: usize, each: impl Fn(usize) -> String) -> String {
    let mut out = String::new();
    for index in 0..count {
        out.push_str(&each(index));
    }
    out
}

/// Ошибка разбора; всё остальное - провал теста.
fn parse_error(text: &str) -> ParseError {
    match parse(text) {
        Err(Error::Parse(error)) => error,
        other => panic!("ожидалась ошибка разбора, получено {other:?}"),
    }
}

#[test]
fn a_signature_and_its_clauses_become_one_group() {
    // §4.1 дословно, кроме `Vect n a` вместо кратностей: клаузы идут подряд и
    // собираются в одно определение.
    let text = "\
map : (a -> b) -> Vect n a -> Vect n b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn an_indexed_family_parses() {
    let text = "\
data Vect : (0 n : Nat) -> Type -> Type where
  Nil  : Vect 0 a
  Cons : a -> Vect n a -> Vect (n + 1) a
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn parameters_may_be_written_as_bare_names() {
    // §4.1: `data Pair a b where` - параметры до `where`, тип-формер не написан.
    let text = "\
data Pair a b where
  MkPair : a -> b -> Pair a b
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn a_family_without_constructors_needs_no_where() {
    // Пустой тип иначе незаписываем: layout пустых блоков не делает. Ядру он
    // нужен - разбор с нулём ветвей и есть доказательство необитаемости.
    assert_eq!(
        tree("data Void : Type\n").expect("разбор удался"),
        "(data Void\n  (kind Type))\n"
    );
}

#[test]
fn a_body_is_a_block_of_statements() {
    // §4.1: цепочка let-биндингов вместо do-нотации.
    let text = "\
counter =
  let n = get
  put (n + 1)
  n
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn a_resource_carries_its_drop() {
    let text = "\
resource File where
  drop h = closeFile h
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn where_attaches_local_definitions() {
    let text = "\
f x = y
  where
    y = g x
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn a_where_leaves_the_body_it_follows() {
    // `where` присоединяется к клаузе, а не к оператору в её теле, поэтому
    // тело закрывается на любой колонке самого `where` (§4.1 правило 2).
    let at_the_column = "\
f x =
  y
  where
    z = 1
";
    let to_the_left = "\
f x =
    y
  where
    z = 1
";
    assert_eq!(
        tree(at_the_column).expect("разбор удался"),
        "(def f\n  (clause (x) (block y)\n    (where (def z\n      (clause () 1)))))\n"
    );
    assert_eq!(
        tree(at_the_column).expect("разбор удался"),
        tree(to_the_left).expect("разбор удался"),
        "отступ самого `where` дерева не меняет"
    );
}

#[test]
fn a_lambda_takes_patterns_and_typed_binders() {
    let text = "\
f = \\x -> x
g = \\(0 a : Type) x -> x
h = \\() -> get
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn case_alternatives_are_members_of_a_block() {
    let text = "\
f x = case x of
  Cons y ys -> y
  Nil       -> zero
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}

#[test]
fn binder_groups_before_the_arrow_make_one_pi() {
    assert_eq!(
        tree("groups : (a : Type) (b : Type) -> Type\n").expect("разбор удался"),
        "(sig groups (pi ((a : Type) (b : Type)) Type))\n"
    );
}

#[test]
fn a_type_application_takes_its_argument_first() {
    // §4.1: в `runExcept @IOError prog` сначала подставляется тип, и только
    // получившееся применяется к `prog`.
    assert_eq!(
        tree("apply = runExcept @IOError prog\n").expect("разбор удался"),
        "(def apply\n  (clause () ((@ runExcept IOError) prog)))\n"
    );
}

#[test]
fn tuples_and_lists_are_nodes_of_their_own() {
    assert_eq!(
        tree("tuple = (a, b, c)\nitems = [1, 2, 3]\n").expect("разбор удался"),
        "(def tuple\n  (clause () (tuple a b c)))\n(def items\n  (clause () (list 1 2 3)))\n"
    );
}

#[test]
fn a_multiline_if_stays_one_statement() {
    // `then` и `else` на колонке `if` продолжают член, а не начинают новые
    // (§4.1 правило 2).
    let text = "\
choice x =
  if isZero x
  then none
  else some x
";
    assert_eq!(
        tree(text).expect("разбор удался"),
        "(def choice\n  (clause (x) (block (if (isZero x) none (some x)))))\n"
    );
}

#[test]
fn a_family_may_carry_both_parameters_and_a_kind() {
    let text = "\
data Pair a : Type where
  MkPair : a -> Pair a
";
    assert_eq!(
        tree(text).expect("разбор удался"),
        "(data Pair a\n  (kind Type)\n  (ctor MkPair (-> a (Pair a))))\n"
    );
}

#[test]
fn an_operator_chain_stays_flat() {
    // Фикситеты объявляются в prelude (§4.4), поэтому скобки здесь не
    // расставляются: дерево несёт цепочку как написано.
    assert_eq!(
        tree("f = a + b * c\n").expect("разбор удался"),
        "(def f\n  (clause () (chain a (+ b) (* c))))\n"
    );
}

#[test]
fn a_sign_belongs_to_the_literal_only_where_an_operand_starts() {
    // §4.3 выбирает класс преобразования по написанию: `-42` это `FromInt`.
    assert_eq!(
        tree("f = g (-42)\n").expect("разбор удался"),
        "(def f\n  (clause () (g -42)))\n"
    );
    // А между операндами тот же знак - вычитание, как в Haskell.
    assert_eq!(
        tree("f = x - 42\n").expect("разбор удался"),
        "(def f\n  (clause () (chain x (- 42))))\n"
    );
}

#[test]
fn an_operator_may_be_defined_by_name() {
    let text = "\
(++) : List a -> List a -> List a
";
    assert_eq!(
        tree(text).expect("разбор удался"),
        "(sig ++ (-> (List a) (-> (List a) (List a))))\n"
    );
}

#[test]
fn arrows_are_right_associative() {
    assert_eq!(
        tree("f : a -> b -> c\n").expect("разбор удался"),
        "(sig f (-> a (-> b c)))\n"
    );
}

#[test]
fn clauses_of_one_definition_must_not_be_split() {
    // Порядок клауз значим - побеждает первая совпавшая, - поэтому собирать
    // разнесённые куски молча нельзя.
    let error = parse_error("f 0 = a\ng = b\nf 1 = c\n");
    let ParseError::SplitClauses { name, .. } = &error else {
        panic!("ожидалась SplitClauses, получено {error:?}");
    };
    assert_eq!(&**name, "f");
}

#[test]
fn a_form_with_a_block_must_be_last() {
    // `case` тянется до строки, начатой левее, и в скобки не берётся: дерево,
    // где за ним стоит ещё что-то, не записывается ничем (§4.1).
    let cases = [
        "f = g case x of\n    A -> 1\n  y\n",
        "f = case x of\n    A -> 1\n  + b\n",
        "f : case x of\n    A -> Type\n  -> a\n",
        "f = case case x of\n         A -> 1\n     of\n  B -> 2\n",
        "f = if case x of\n         A -> 1\n     then a else b\n",
        "data D : case x of\n    A -> Type\n  where\n    C : D\n",
        "f =\n  let w : case x of\n            A -> Type\n        = 1\n  w\n",
    ];
    for text in cases {
        let error = parse_error(text);
        assert!(
            matches!(error, ParseError::BlockNotLast { .. }),
            "для {text:?} получено {error:?}"
        );
    }
    // Последней - можно, и это единственный способ передать `case` в функцию:
    // скобки для него закрыты (§10 вопрос 55).
    assert!(tree("f = g case x of\n  A -> 1\n").is_ok());
    assert!(tree("f = a + case x of\n  A -> 1\n").is_ok());
    assert!(tree("f = g \\y -> case y of\n  A -> 1\n").is_ok());
}

#[test]
fn a_multiplicity_is_zero_one_or_omega() {
    // Полукольцо §3.2 - ровно три элемента, и ошибка указывает на само число.
    let error = parse_error("f : (2 n : Nat) -> Nat\n");
    assert!(
        matches!(error, ParseError::Multiplicity { .. }),
        "получено {error:?}"
    );
    assert!(tree("f : (ω n : Nat) -> Nat\n").is_ok());
    assert!(tree("f : (0 n : Nat) -> Nat\n").is_ok());
}

#[test]
fn forms_of_later_phases_name_their_phase() {
    // Лексема зарезервирована и опечаткой быть не может, поэтому честнее
    // назвать фазу, чем перечислять, что бывает здесь вместо неё.
    let cases = [
        ("class Functor f where\n  map : a\n", Unsupported::Class),
        (
            "instance Functor Option where\n  map = f\n",
            Unsupported::Instance,
        ),
        ("effect State s where\n  get : s\n", Unsupported::Effect),
        // Effect row и запись пишутся одними скобками, а различает их регистр
        // (§4.1): метка ряда заглавная, поле записи строчное.
        ("f : {IO} a\n", Unsupported::Braces),
        ("infixl 6 +\n", Unsupported::Fixity),
    ];
    for (text, expected) in cases {
        let error = parse_error(text);
        let ParseError::Unsupported { what, .. } = error else {
            panic!("для {text:?} ожидалась Unsupported, получено {error:?}");
        };
        assert_eq!(what, expected, "для {text:?}");
    }
    // Сообщение - предложение целиком, вместе с подсказкой.
    assert_eq!(
        parse_error("f : {IO} a\n").to_string(),
        "записи (§4.2) и effect row (§3.4) появляются в одной из следующих фаз; \
         группа implicit-связываний пишется `{a : Type}`"
    );
}

#[test]
fn an_error_names_what_was_expected_and_points_at_the_token() {
    let error = parse_error("f x y\n");
    let ParseError::Expected { span, .. } = &error else {
        panic!("ожидалась Expected, получено {error:?}");
    };
    // Указывает на конец объявления, а не на начало файла.
    assert!(span.start() >= 5, "спан {span:?} указывает не туда");
    // Настоящее время, потому что род у подставляемых существительных разный:
    // «ожидалось идентификатор» не согласуется ни с чем.
    assert_eq!(error.to_string(), "ожидается `=`, а не конец блока");
    assert_eq!(
        parse_error("data 1\n").to_string(),
        "ожидается имя, а не натуральный литерал"
    );
}

#[test]
fn deep_nesting_is_an_error_not_a_crash() {
    // Спуск рекурсивен, поэтому глубина записи - это глубина стека. Урок
    // warm-up'а Фазы 0: без предела компилятор падает вместо сообщения.
    let deep = format!("f = {}x{}\n", "(".repeat(20_000), ")".repeat(20_000));
    assert!(matches!(parse_error(&deep), ParseError::TooDeep { .. }));
    // Предел не должен резать законные программы: сотня стрелок в сигнатуре
    // абсурдна, но глубже неё предел не опускается.
    let wide = format!("f : {}a\n", "a -> ".repeat(100));
    assert!(tree(&wide).is_ok());
}

/// Плоский список, разворачивающийся в цепочку узлов ядра, ограничен той же
/// мерой, что и вложенность записи (§10 вопрос 62).
///
/// Все четыре набираются циклом, поэтому разбор их переживает: рекурсивен не
/// он, а всякий, кто пойдёт по получившемуся дереву.
#[test]
fn a_flat_list_that_unfolds_into_a_chain_is_bounded_too() {
    let refused = |what: &str, text: &str| {
        let error = parse_error(text);
        assert!(
            matches!(error, ParseError::TooDeep { .. }),
            "{what}: получено {error:?}"
        );
    };

    refused("спайн", &format!("f = g{}\n", " x".repeat(257)));
    refused(
        "операторы блока",
        &format!(
            "f =\n{}  x\n",
            repeat(257, |index| format!("  let x{index} : T = y\n"))
        ),
    );
    refused(
        "связывания одного `let`",
        &format!(
            "f =\n  let\n{}  x\n",
            repeat(257, |index| format!("    x{index} : T = y\n"))
        ),
    );
    refused(
        "имена в группе",
        &format!(
            "f : (0{} : T) -> T\n",
            repeat(257, |index| format!(" a{index}"))
        ),
    );
    // Тип записи - телескоп: поле живёт под предыдущими (§4.2).
    refused(
        "поля типа записи",
        &format!(
            "type Big = {{ f0 : T{} }}\n",
            repeat(256, |index| format!(", f{} : T", index + 1))
        ),
    );
    // Предел общий, поэтому формы **складываются**: каждая порознь под ним, а
    // вместе - нет. Порознь поставленные пределы этого не ловили.
    refused(
        "скобки со спайнами",
        &format!(
            "f = {}x{}\n",
            "(g ".repeat(30),
            format!("{})", " y".repeat(20)).repeat(30)
        ),
    );
}

#[test]
fn the_limit_does_not_cut_on_its_own_boundary() {
    assert!(parse(&format!("f = g{}\n", " x".repeat(256))).is_ok());
    let block = repeat(256, |index| format!("  let x{index} : T = y\n"));
    assert!(parse(&format!("f =\n{block}  x\n")).is_ok());
    let fields = repeat(255, |index| format!(", f{} : T", index + 1));
    assert!(parse(&format!("type Big = {{ f0 : T{fields} }}\n")).is_ok());
}

/// Список, который в цепочку **не** разворачивается, пределом не режется.
///
/// Значение записи - плоский набор: зависимости в нём нет, и `{ x = a, y = b }`
/// глубины не даёт. Считать его телескопом значило бы запретить широкую
/// запись ни за что - а §4.11 (`SoA`, ECS) на широких и стоит.
#[test]
fn a_flat_list_that_stays_flat_is_not_bounded() {
    let values = repeat(4_000, |index| format!(", f{index} = y"));
    assert!(parse(&format!("v = {{ f = y{values} }}\n")).is_ok());
    let items = repeat(4_000, |index| format!(", x{index}"));
    assert!(parse(&format!("v = [y{items}]\n")).is_ok());
}

#[test]
fn an_empty_file_is_an_empty_module() {
    assert_eq!(tree("").expect("разбор удался"), "");
    assert_eq!(tree("-- только комментарий\n").expect("разбор удался"), "");
}

proptest! {
    /// Разбор не паникует ни на чём.
    #[test]
    fn parsing_never_panics(text in "(?s).{0,300}") {
        let _ = parse(&text);
    }

    /// На осмысленном подмножестве лексики разбор либо даёт дерево, либо
    /// ошибку - но не панику и не бесконечный цикл.
    #[test]
    fn parsing_terminates_on_plausible_input(
        text in r"[a-z=(){}\[\]:,\n ]{0,120}"
    ) {
        let _ = parse(&text);
    }
}

#[test]
fn a_record_type_may_name_its_tail() {
    // §4.2: сохранение полей пишется явно, `{ x : Nat | r }`. Первая запись
    // читается ещё и как группа implicit-связываний, и разводит их `|` -
    // возврат назад отсюда и начинается.
    assert_eq!(
        tree("keep : { x : Nat | r } -> { x : Nat | r }\n").expect("разбор удался"),
        "(sig keep (-> (record (x Nat) | r) (record (x Nat) | r)))\n"
    );
}

#[test]
fn a_module_and_its_signature_parse() {
    // §4.8: обе формы разбираются одной, различает их `type` сразу за
    // `module`. Член - обычное объявление, поэтому вложенный модуль
    // разбирается сам собой.
    let text = "\
module type Eqv where
  type T
  eq : T -> T -> Bool

module NatEq : Eqv where
  type T = Nat
  eq a b = True

module Outer where
  module Inner where
    flag : Bool
";
    insta::assert_snapshot!(tree(text).expect("разбор удался"));
}
