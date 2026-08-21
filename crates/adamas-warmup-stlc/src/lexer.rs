//! Ручной лексер.

use adamas_core::source::Span;

use crate::error::Error;

/// Разновидность токена.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Ident(String),
    Int(i64),
    Let,
    Rec,
    In,
    If,
    Then,
    Else,
    Fix,
    True,
    False,
    Lambda,
    Arrow,
    Equals,
    Colon,
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Less,
    EqEq,
    Eof,
}

impl Kind {
    /// Как токен называется в сообщении об ошибке.
    pub(crate) fn describe(&self) -> String {
        match self {
            Self::Ident(name) => format!("идентификатор `{name}`"),
            Self::Int(value) => format!("число `{value}`"),
            Self::Let => "`let`".to_owned(),
            Self::Rec => "`rec`".to_owned(),
            Self::In => "`in`".to_owned(),
            Self::If => "`if`".to_owned(),
            Self::Then => "`then`".to_owned(),
            Self::Else => "`else`".to_owned(),
            Self::Fix => "`fix`".to_owned(),
            Self::True => "`true`".to_owned(),
            Self::False => "`false`".to_owned(),
            Self::Lambda => "`\\`".to_owned(),
            Self::Arrow => "`->`".to_owned(),
            Self::Equals => "`=`".to_owned(),
            Self::Colon => "`:`".to_owned(),
            Self::LParen => "`(`".to_owned(),
            Self::RParen => "`)`".to_owned(),
            Self::Plus => "`+`".to_owned(),
            Self::Minus => "`-`".to_owned(),
            Self::Star => "`*`".to_owned(),
            Self::Less => "`<`".to_owned(),
            Self::EqEq => "`==`".to_owned(),
            Self::Eof => "конец файла".to_owned(),
        }
    }
}

/// Токен вместе с занимаемым диапазоном.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Token {
    pub(crate) kind: Kind,
    pub(crate) span: Span,
}

/// Разбивает исходник на токены. Последним всегда идёт [`Kind::Eof`], чтобы
/// парсеру не приходилось отдельно проверять конец потока.
pub(crate) fn tokenize(text: &str) -> Result<Vec<Token>, Error> {
    let mut tokens = Vec::new();
    let mut chars = text.char_indices().peekable();

    while let Some(&(offset, ch)) = chars.peek() {
        if ch.is_whitespace() {
            chars.next();
            continue;
        }
        // Комментарий до конца строки: `-- ...`. Проверяется раньше минуса.
        if ch == '-' && text[offset..].starts_with("--") {
            while let Some(&(_, c)) = chars.peek() {
                if c == '\n' {
                    break;
                }
                chars.next();
            }
            continue;
        }

        // `λ` проверяется раньше идентификаторов: греческая лямбда проходит
        // `char::is_alphabetic`, и иначе её съел бы разбор имени.
        let (kind, end) = if ch == '\\' || ch == 'λ' {
            chars.next();
            (Kind::Lambda, offset + ch.len_utf8())
        } else if ch.is_ascii_digit() {
            let (digits, end) = take_while(text, &mut chars, |c| c.is_ascii_digit());
            let value = digits.parse().map_err(|_| Error::IntTooLarge {
                span: Span::new(offset, end),
            })?;
            (Kind::Int(value), end)
        } else if is_ident_start(ch) {
            let (word, end) = take_while(text, &mut chars, is_ident_continue);
            (keyword(word), end)
        } else {
            // Всё ниже - ASCII, поэтому длина в байтах равна длине в символах.
            let (kind, len) = match ch {
                '(' => (Kind::LParen, 1),
                ')' => (Kind::RParen, 1),
                '+' => (Kind::Plus, 1),
                '*' => (Kind::Star, 1),
                '<' => (Kind::Less, 1),
                ':' => (Kind::Colon, 1),
                '-' if text[offset..].starts_with("->") => (Kind::Arrow, 2),
                '-' => (Kind::Minus, 1),
                '=' if text[offset..].starts_with("==") => (Kind::EqEq, 2),
                '=' => (Kind::Equals, 1),
                _ => {
                    return Err(Error::UnexpectedChar {
                        ch,
                        span: Span::new(offset, offset + ch.len_utf8()),
                    });
                }
            };
            for _ in 0..len {
                chars.next();
            }
            (kind, offset + len)
        };

        tokens.push(Token {
            kind,
            span: Span::new(offset, end),
        });
    }

    tokens.push(Token {
        kind: Kind::Eof,
        span: Span::at(text.len()),
    });
    Ok(tokens)
}

/// Съедает символы, пока держится предикат. Возвращает срез и смещение конца.
fn take_while<'a>(
    text: &'a str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'a>>,
    predicate: impl Fn(char) -> bool,
) -> (&'a str, usize) {
    let start = chars.peek().map_or(text.len(), |&(offset, _)| offset);
    let mut end = start;
    while let Some(&(offset, ch)) = chars.peek() {
        if !predicate(ch) {
            break;
        }
        end = offset + ch.len_utf8();
        chars.next();
    }
    (&text[start..end], end)
}

fn keyword(word: &str) -> Kind {
    match word {
        "let" => Kind::Let,
        "rec" => Kind::Rec,
        "in" => Kind::In,
        "if" => Kind::If,
        "then" => Kind::Then,
        "else" => Kind::Else,
        "fix" => Kind::Fix,
        "true" => Kind::True,
        "false" => Kind::False,
        other => Kind::Ident(other.to_owned()),
    }
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

#[cfg(test)]
mod tests {
    use super::{Kind, tokenize};

    fn kinds(text: &str) -> Vec<Kind> {
        tokenize(text)
            .unwrap()
            .into_iter()
            .map(|token| token.kind)
            .collect()
    }

    #[test]
    fn keywords_win_over_identifiers() {
        assert_eq!(
            kinds("let letter"),
            [Kind::Let, Kind::Ident("letter".to_owned()), Kind::Eof]
        );
    }

    #[test]
    fn longest_match_wins_for_operators() {
        assert_eq!(
            kinds("= == - ->"),
            [
                Kind::Equals,
                Kind::EqEq,
                Kind::Minus,
                Kind::Arrow,
                Kind::Eof
            ]
        );
    }

    #[test]
    fn comments_run_to_end_of_line() {
        assert_eq!(
            kinds("1 -- 2 3\n4"),
            [Kind::Int(1), Kind::Int(4), Kind::Eof]
        );
    }

    #[test]
    fn lambda_accepts_both_spellings() {
        assert_eq!(kinds("\\ λ"), [Kind::Lambda, Kind::Lambda, Kind::Eof]);
    }

    #[test]
    fn spans_are_byte_accurate_around_multibyte_lambda() {
        let tokens = tokenize("λx").unwrap();
        assert_eq!(tokens[0].span.end(), 2);
        assert_eq!(tokens[1].span.start(), 2);
    }

    #[test]
    fn oversized_literal_is_an_error_not_a_panic() {
        assert!(tokenize("99999999999999999999999").is_err());
    }
}
