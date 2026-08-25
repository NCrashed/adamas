//! Значимые отступы на примерах §4.1 и свойства расстановки блоков.

use adamas_parser::layout::LayoutError;
use adamas_parser::token::{TokenKind, dump_inline};
use adamas_parser::{Error, tokenize};
use proptest::prelude::*;

/// Поток в одну строку: границы блоков - `{|`, `;`, `|}`.
fn shape(text: &str) -> Result<String, Error> {
    Ok(dump_inline(text, &tokenize(text)?.tokens))
}

#[test]
fn the_state_handler_from_the_design_lays_out() {
    // §4.1 дословно. `with` открывает блок веток, каждая ветка - член блока.
    let text = "\
runState : s -> ({State s} a) -> (s, a)
runState s0 prog = handle prog with
  get     resume => resume s0 s0
  put s'  resume => runState s' (resume ())
  return v       => (s0, v)
";
    insta::assert_snapshot!(shape(text).expect("разбор удался"));
}

#[test]
fn a_resource_and_its_user_lay_out() {
    let text = "\
resource File where
  drop h = closeFile h

withFile path k =
  let h = openFile path
  k h
";
    insta::assert_snapshot!(shape(text).expect("разбор удался"));
}

#[test]
fn a_class_with_defaults_lays_out() {
    // §4.1: `when` в заголовке класса, default-метод в теле.
    let text = "\
class Applicative f when Functor f where
  pure : a -> f a
  ap   : f (a -> b) -> f a -> f b
  map f x = ap (pure f) x

instance Functor Option where
  map f None     = None
  map f (Some x) = Some (f x)
";
    insta::assert_snapshot!(shape(text).expect("разбор удался"));
}

#[test]
fn a_signature_may_break_before_its_arrows() {
    // Стрелка блока не открывает, поэтому многострочная сигнатура остаётся
    // одним членом блока верхнего уровня.
    let text = "\
withFile : String
  -> (File -> {IO} a)
  -> {IO, Except IOError} a
";
    assert_eq!(
        shape(text).expect("разбор удался"),
        "{| withFile : String -> ( File -> { IO } a ) -> { IO , Except IOError } a |}"
    );
}

#[test]
fn a_multiline_conditional_stays_one_member() {
    // `then` и `else` член блока начать не могут, значит границы перед ними
    // нет - и многострочный `if` остаётся одним оператором тела (§4.1).
    let text = "\
counter =
  if positive
  then 1
  else 0
";
    assert_eq!(
        shape(text).expect("разбор удался"),
        "{| counter = {| if positive then 1 else 0 |} |}"
    );
}

#[test]
fn nested_modules_lay_out() {
    // §4.8 дословно. `where` стоит после скобочной группы, то есть уже вне
    // скобок, - блок открывается им, а не теряется вместе с выключенным
    // внутри скобок layout.
    let text = "\
module Collections where
  module OrderedMap (Key : Ord) where
    lookup = ()
  module HashMap (Key : Hashable) where
    lookup = ()
";
    insta::assert_snapshot!(shape(text).expect("разбор удался"));
}

#[test]
fn a_shallow_body_is_refused_with_both_columns() {
    let error = tokenize("f =\nx").expect_err("тело не правее блока");
    let Error::Layout(LayoutError::ShallowBlock {
        column, enclosing, ..
    }) = error
    else {
        panic!("ожидалась ShallowBlock, получено {error:?}");
    };
    assert_eq!((column, enclosing), (1, 1));
}

#[test]
fn a_token_left_of_the_file_block_is_refused_with_both_columns() {
    let error = tokenize("  f = 1\ng = 2").expect_err("лексема левее блока файла");
    let Error::Layout(LayoutError::LeftOfFile { column, file, .. }) = error else {
        panic!("ожидалась LeftOfFile, получено {error:?}");
    };
    assert_eq!((column, file), (1, 3));
}

#[test]
fn a_comment_keeps_pointing_at_its_token_after_layout() {
    // Виртуальные границы встают в том числе прямо перед токеном, к которому
    // привязан комментарий, поэтому индекс пересчитывается (§7.1, `adamas fmt`).
    let text = "f = 1\n-- шапка g\ng = 2";
    let tokens = tokenize(text).expect("разбор удался");
    let [comment] = tokens.comments[..] else {
        panic!("ожидался ровно один комментарий");
    };
    let token = tokens.tokens[comment.token as usize];
    assert_eq!(token.kind, TokenKind::Ident);
    assert_eq!(token.text(text), "g");
}

proptest! {
    /// Расстановка блоков не паникует ни на чём.
    #[test]
    fn layout_never_panics(text in "(?s).{0,300}") {
        let _ = tokenize(&text);
    }

    /// Блоки сбалансированы и вложены, и ни один настоящий токен не лежит вне
    /// блока файла. Без первого парсер, доверяющий границам, читает за край
    /// конструкции; без второго - молча теряет всё, что левее первой
    /// декларации.
    #[test]
    fn every_token_lives_inside_a_block(text in "(?s).{0,300}") {
        let Ok(tokens) = tokenize(&text) else { return Ok(()) };
        let mut depth = 0i32;
        for token in &tokens.tokens {
            match token.kind {
                TokenKind::Open => depth += 1,
                TokenKind::Close => {
                    depth -= 1;
                    prop_assert!(depth >= 0, "`Close` без открытого блока");
                }
                TokenKind::Eof => {}
                _ => prop_assert!(depth >= 1, "токен вне блока файла"),
            }
        }
        prop_assert_eq!(depth, 0, "блок остался открытым");
    }

    /// Виртуальные токены ничего не добавляют к тексту и ничего не убирают:
    /// поток без них - ровно то, что отдал лексер.
    #[test]
    fn layout_only_inserts_virtual_tokens(text in "(?s).{0,300}") {
        let Ok(lexed) = adamas_parser::lexer::lex(&text) else { return Ok(()) };
        let Ok(laid) = adamas_parser::layout::layout(&lexed.tokens) else { return Ok(()) };
        let kept: Vec<_> = laid
            .iter()
            .filter(|token| !token.kind.is_virtual())
            .copied()
            .collect();
        prop_assert_eq!(kept, lexed.tokens);
    }

    /// Комментарий указывает на настоящий токен, и притом стоящий после него.
    #[test]
    fn every_comment_points_at_the_token_after_it(text in "(?s).{0,300}") {
        let Ok(tokens) = tokenize(&text) else { return Ok(()) };
        for comment in &tokens.comments {
            let Some(token) = tokens.tokens.get(comment.token as usize) else {
                return Err(TestCaseError::fail("индекс мимо потока"));
            };
            prop_assert!(!token.kind.is_virtual(), "привязка к границе блока");
            prop_assert!(comment.span.end() <= token.span.start(), "токен раньше комментария");
        }
    }
}
