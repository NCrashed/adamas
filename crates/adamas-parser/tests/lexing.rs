//! Лексер на примерах §4.1 и свойства, которые обязаны держаться на любом
//! входе.

use adamas_parser::lexer::lex;
use adamas_parser::token::{TokenKind, dump};
use proptest::prelude::*;

/// Кусок §4.1: сигнатура с кратностями, effect row и клаузы.
const WITH_FILE: &str = "\
-- Ресурсный тип с автоматическим cleanup
resource File where
  drop h = closeFile h

openFile : String -> {IO, Except IOError} File

withFile : String -> (File -> {IO} a) -> {IO, Except IOError} a
withFile path k =
  let h = openFile path
  k h
";

/// Кусок §4.1: индексированное семейство и разбор клаузами.
const VECT: &str = "\
data Vect : (0 n : Nat) -> Type -> Type where
  Nil  : Vect 0 a
  Cons : a -> Vect n a -> Vect (n + 1) a

map : (a -> b) -> Vect n a -> Vect n b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
";

#[test]
fn a_resource_declaration_lexes() {
    let lexed = lex(WITH_FILE).expect("лексер справился");
    insta::assert_snapshot!(dump(WITH_FILE, &lexed.tokens));
}

#[test]
fn an_indexed_family_lexes() {
    let lexed = lex(VECT).expect("лексер справился");
    insta::assert_snapshot!(dump(VECT, &lexed.tokens));
}

#[test]
fn multiplicities_read_as_literals_in_binders() {
    // `(0 n : Nat)` и `(1 h : File)` - кратности пишутся литералами (§4.1).
    // Лексер их не выделяет: это работа парсера, и здесь проверяется, что
    // разделение на токены ему это позволяет.
    let lexed = lex("(0 n : Nat) -> (1 h : File)").expect("лексер справился");
    let kinds: Vec<TokenKind> = lexed.tokens.iter().map(|token| token.kind).collect();
    assert_eq!(
        kinds,
        [
            TokenKind::LParen,
            TokenKind::Nat,
            TokenKind::Ident,
            TokenKind::Colon,
            TokenKind::Ident,
            TokenKind::RParen,
            TokenKind::Arrow,
            TokenKind::LParen,
            TokenKind::Nat,
            TokenKind::Ident,
            TokenKind::Colon,
            TokenKind::Ident,
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
}

#[test]
fn an_effect_row_is_braces_a_bar_and_names() {
    // `{State s | e}` - §3.4. Вертикальная черта обязана быть отдельным
    // токеном, а не частью оператора: `|>` рядом в prelude (§4.4).
    let kinds: Vec<TokenKind> = lex("{State s | e}")
        .expect("лексер справился")
        .tokens
        .iter()
        .map(|token| token.kind)
        .collect();
    assert_eq!(
        kinds,
        [
            TokenKind::LBrace,
            TokenKind::Ident,
            TokenKind::Ident,
            TokenKind::Pipe,
            TokenKind::Ident,
            TokenKind::RBrace,
            TokenKind::Eof,
        ]
    );
}

proptest! {
    /// Лексер не паникует ни на чём. Компилятор, падающий на невалидном
    /// вводе, - серьёзный баг, и лексер здесь первая линия.
    #[test]
    fn lexing_never_panics(text in "(?s).{0,300}") {
        let _ = lex(&text);
    }

    /// Спаны токенов и комментариев идут по возрастанию, не пересекаются, а в
    /// промежутках между ними - только пробелы. Иначе диагностика показывает
    /// не тот фрагмент, а `adamas fmt` теряет кусок исходника.
    #[test]
    fn spans_partition_the_source(text in "(?s).{0,300}") {
        let Ok(lexed) = lex(&text) else { return Ok(()) };

        let mut pieces: Vec<_> = lexed
            .tokens
            .iter()
            .filter(|token| token.kind != TokenKind::Eof)
            .map(|token| token.span)
            .chain(lexed.comments.iter().map(|comment| comment.span))
            .collect();
        pieces.sort_by_key(|span| span.start());

        // BOM - единственное, что лексер пропускает, не покрывая спаном: он не
        // лексема и не пробел.
        let mut cursor = if text.starts_with('\u{feff}') { '\u{feff}'.len_utf8() } else { 0 };
        for piece in pieces {
            prop_assert!(piece.start() >= cursor, "куски пересекаются");
            prop_assert!(piece.end() <= text.len(), "кусок за границей файла");
            prop_assert!(
                text[cursor..piece.start()].chars().all(char::is_whitespace),
                "между кусками потерян не-пробельный текст"
            );
            cursor = piece.end();
        }
        prop_assert!(text[cursor..].chars().all(char::is_whitespace));
    }

    /// Комментарий указывает на существующий токен.
    #[test]
    fn every_comment_points_at_a_token(text in "(?s).{0,300}") {
        let Ok(lexed) = lex(&text) else { return Ok(()) };
        for comment in &lexed.comments {
            prop_assert!((comment.token as usize) < lexed.tokens.len());
        }
    }
}
