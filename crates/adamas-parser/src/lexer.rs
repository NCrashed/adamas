//! Ручной лексер: текст -> токены и комментарии.
//!
//! Ручной, а не `logos` (§8 разрешал оба): значимые отступы требуют от каждого
//! токена строки и колонки, генератор их не считает, и досчитывать пришлось бы
//! всё равно - отдельным проходом по тем же байтам.
//!
//! # Что лексер решает сам, а что оставляет парсеру
//!
//! Решает: где кончается лексема, ключевое слово это или имя, законно ли
//! экранирование в строке. Не решает: что значит оператор (фикситеты
//! объявляются в prelude, §4.4), какое число получится из литерала, где
//! начинается блок (это [`crate::layout`]).
//!
//! Мелкие правила - `--` против оператора из минусов, штрих внутри имени,
//! отказ на табуляции в отступе - обоснованы в decision log 2026-08-25,
//! пункт 6; здесь они только реализованы.

use adamas_core::source::Span;

use crate::token::{Comment, CommentKind, Token, TokenKind, Tokens, keyword};

/// Ошибка лексического разбора.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum LexError {
    /// Знак, который в языке не значит ничего.
    #[error("неизвестный символ")]
    UnexpectedChar {
        /// Где он.
        span: Span,
    },

    /// Блочный комментарий не закрыт до конца файла.
    #[error("незакрытый комментарий `{{-`")]
    UnterminatedComment {
        /// Спан открывающего `{-`. Не весь незакрытый кусок: подчёркивать
        /// хвост файла там, где виновата одна лексема, диагностике незачем.
        open: Span,
    },

    /// Строковый литерал не закрыт до конца строки.
    #[error("незакрытый строковый литерал")]
    UnterminatedString {
        /// Спан от открывающей кавычки до конца строки, не включая перевод:
        /// каретка обязана уместиться в одну строку исходника.
        span: Span,
    },

    /// Экранирование, которого нет.
    #[error("неизвестное экранирование в строке")]
    UnknownEscape {
        /// Спан от обратной косой черты.
        span: Span,
    },

    /// Табуляция в отступе строки, на которой есть лексема.
    ///
    /// Отступ значим (§4.1), а ширина табуляции - соглашение редактора, не
    /// свойство текста. Считать её за восемь колонок значит поставить смысл
    /// программы в зависимость от настройки, которой в файле не видно.
    #[error("табуляция в отступе: отступ значим, ширина табуляции - нет")]
    TabInIndentation {
        /// Где она.
        span: Span,
    },
}

impl LexError {
    /// Где ошибка.
    #[must_use]
    pub fn span(self) -> Span {
        match self {
            Self::UnexpectedChar { span }
            | Self::UnterminatedString { span }
            | Self::UnknownEscape { span }
            | Self::TabInIndentation { span } => span,
            Self::UnterminatedComment { open } => open,
        }
    }
}

/// Знаки, из которых складываются операторы.
///
/// Набор haskell'евский за вычетом `,` `;` `(` `)` `[` `]` `{` `}`, которые
/// здесь пунктуация. `:` в наборе: `::` - это Cons (§4.4), и он обязан
/// склеиваться максимальным куском, иначе распался бы на два двоеточия.
const SYMBOLS: &str = "!#$%&*+./<=>?@\\^|-~:";

/// Складывается ли текст целиком из символьных знаков.
///
/// Нужна печати ([`crate::printer`]): имя оператора в позиции имени
/// определения пишется в скобках (`(++) : …`, §4.4), а обычное - без них, и
/// отличить их можно только по написанию. Спрашивать здесь, а не заводить
/// вторую копию набора: набор один, и разъехаться копиям было бы негде видно.
#[must_use]
pub fn is_operator(text: &str) -> bool {
    !text.is_empty() && text.chars().all(|ch| SYMBOLS.contains(ch))
}

/// Byte order mark. Знаком языка не является; редакторы Windows ставят его
/// молча, и отказ на нём выглядел бы отказом на пустом месте.
const BOM: &str = "\u{feff}";

/// Разбивает исходник на токены.
///
/// # Errors
///
/// Неизвестный знак; незакрытый комментарий или строка; неизвестное
/// экранирование; табуляция в отступе.
pub fn lex(text: &str) -> Result<Tokens, LexError> {
    let mut cursor = Cursor::new(text);
    let mut lexed = Tokens::default();

    loop {
        let indent_tab = skip_trivia(&mut cursor, &mut lexed)?;
        let start = cursor.mark();
        let Some(ch) = cursor.peek() else { break };

        // Табуляция значима там, где по ней меряется отступ, то есть только
        // если на строке дальше есть лексема. Строку без лексем layout не
        // видит вовсе, и отвергать её из-за забытого редактором знака незачем.
        if let Some(span) = indent_tab {
            return Err(LexError::TabInIndentation { span });
        }

        let kind = if is_ident_start(ch) {
            identifier(&mut cursor)
        } else if ch.is_ascii_digit() {
            number(&mut cursor)
        } else if ch == '"' {
            string(&mut cursor)?
        } else if let Some(kind) = punctuation(ch) {
            cursor.bump();
            kind
        } else if SYMBOLS.contains(ch) {
            symbol(&mut cursor)
        } else {
            cursor.bump();
            return Err(LexError::UnexpectedChar {
                span: cursor.span_from(start),
            });
        };

        lexed.tokens.push(Token {
            kind,
            span: cursor.span_from(start),
            line: start.line,
            column: start.column,
        });
    }

    lexed.tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span::at(text.len()),
        line: cursor.line,
        column: cursor.column,
    });
    Ok(lexed)
}

/// Пробелы и комментарии до следующего токена.
///
/// Возвращает спан табуляции в отступе строки, на которой курсор остановился.
/// Решает по нему не лексер, а вызывающий: пока неизвестно, есть ли на строке
/// лексема, неизвестно и то, меряется ли по этой табуляции отступ.
fn skip_trivia(cursor: &mut Cursor<'_>, lexed: &mut Tokens) -> Result<Option<Span>, LexError> {
    let mut indent_tab = None;
    loop {
        match cursor.peek() {
            Some('\n') => {
                indent_tab = None;
                cursor.bump();
            }
            Some('\t') if cursor.line_is_blank_before() => {
                let start = cursor.mark();
                cursor.bump();
                indent_tab = indent_tab.or_else(|| Some(cursor.span_from(start)));
            }
            Some(ch) if ch.is_whitespace() => {
                cursor.bump();
            }
            Some('-') if cursor.dashes_start_a_comment() => {
                let start = cursor.mark();
                while cursor.peek().is_some_and(|ch| ch != '\n') {
                    cursor.bump();
                }
                lexed.comments.push(Comment {
                    kind: CommentKind::Line,
                    span: cursor.span_from(start),
                    token: token_index(lexed),
                });
            }
            Some('{') if cursor.starts_with("{-") => {
                let start = cursor.mark();
                block_comment(cursor, start)?;
                lexed.comments.push(Comment {
                    kind: CommentKind::Block,
                    span: cursor.span_from(start),
                    token: token_index(lexed),
                });
            }
            _ => return Ok(indent_tab),
        }
    }
}

/// Индекс токена, перед которым стоит комментарий.
fn token_index(lexed: &Tokens) -> u32 {
    u32::try_from(lexed.tokens.len()).unwrap_or(u32::MAX)
}

/// Вложенный блочный комментарий. Курсор стоит на `{-`.
fn block_comment(cursor: &mut Cursor<'_>, start: Mark) -> Result<(), LexError> {
    let mut depth = 0usize;
    loop {
        if cursor.starts_with("{-") {
            depth += 1;
            cursor.bump();
            cursor.bump();
        } else if cursor.starts_with("-}") {
            depth -= 1;
            cursor.bump();
            cursor.bump();
            if depth == 0 {
                return Ok(());
            }
        } else if cursor.bump().is_none() {
            return Err(LexError::UnterminatedComment {
                open: start.span_of("{-"),
            });
        }
    }
}

/// Идентификатор или ключевое слово.
fn identifier(cursor: &mut Cursor<'_>) -> TokenKind {
    let start = cursor.mark();
    while cursor.peek().is_some_and(is_ident_continue) {
        cursor.bump();
    }
    let text = cursor.text_from(start);
    if text == "_" {
        return TokenKind::Underscore;
    }
    keyword(text).unwrap_or(TokenKind::Ident)
}

/// Числовой литерал. Знак минуса сюда не входит: `-42` - это оператор и
/// литерал, а `fromInt` из них соберёт парсер (§4.3).
///
/// Цифра и имя, написанные слитно, остаются двумя лексемами: `1foo` - это
/// `1 foo`, применение литерала к имени, как в Haskell. По той же причине
/// `0x` - начало шестнадцатеричного литерала только тогда, когда за ним идёт
/// шестнадцатеричная цифра: `0xs` - это `0 xs`, а не сломанный `0xff`.
fn number(cursor: &mut Cursor<'_>) -> TokenKind {
    if cursor.starts_with("0x") || cursor.starts_with("0X") {
        let hex = cursor
            .text_after(2)
            .starts_with(|ch: char| ch.is_ascii_hexdigit());
        if hex {
            cursor.bump();
            cursor.bump();
            while cursor
                .peek()
                .is_some_and(|ch| ch.is_ascii_hexdigit() || ch == '_')
            {
                cursor.bump();
            }
            return TokenKind::Nat;
        }
    }

    digits(cursor);
    let mut float = false;

    // Точка - десятичная, только если за ней цифра: `xs.length` - проекция, а
    // не литерал `xs.` с потерянным хвостом.
    if cursor.peek() == Some('.')
        && cursor
            .text_after(1)
            .starts_with(|ch: char| ch.is_ascii_digit())
    {
        float = true;
        cursor.bump();
        digits(cursor);
    }

    if matches!(cursor.peek(), Some('e' | 'E')) && exponent_follows(cursor) {
        float = true;
        cursor.bump();
        if matches!(cursor.peek(), Some('+' | '-')) {
            cursor.bump();
        }
        digits(cursor);
    }

    if float {
        TokenKind::Float
    } else {
        TokenKind::Nat
    }
}

/// Идёт ли за `e` показатель степени. Без проверки `2e` распался бы на
/// литерал и имя `e`, а с ней остаётся именно этим.
fn exponent_follows(cursor: &Cursor<'_>) -> bool {
    let rest = cursor.text_after(1);
    let digits = rest.strip_prefix(['+', '-']).unwrap_or(rest);
    digits.starts_with(|ch: char| ch.is_ascii_digit())
}

/// Цифры и разделяющие подчёркивания.
fn digits(cursor: &mut Cursor<'_>) {
    while cursor
        .peek()
        .is_some_and(|ch| ch.is_ascii_digit() || ch == '_')
    {
        cursor.bump();
    }
}

/// Строковый литерал вместе с кавычками.
fn string(cursor: &mut Cursor<'_>) -> Result<TokenKind, LexError> {
    let start = cursor.mark();
    cursor.bump();
    loop {
        let escape = cursor.mark();
        match cursor.peek() {
            Some('"') => {
                cursor.bump();
                return Ok(TokenKind::Str);
            }
            Some('\\') => {
                cursor.bump();
                let ok = match cursor.bump() {
                    Some('n' | 't' | 'r' | '0' | '\\' | '"' | '\'') => true,
                    Some('u') => unicode_escape(cursor),
                    _ => false,
                };
                if !ok {
                    return Err(LexError::UnknownEscape {
                        span: cursor.span_from(escape),
                    });
                }
            }
            // Многострочных литералов нет: незакрытая кавычка иначе съедает
            // остаток файла и указывает на ошибку страницей ниже. Перевод
            // строки при этом не съеден - он уже не часть литерала.
            None | Some('\n') => {
                return Err(LexError::UnterminatedString {
                    span: cursor.span_from(start),
                });
            }
            Some(_) => {
                cursor.bump();
            }
        }
    }
}

/// `\u{XXXX}` после уже съеденного `u`.
fn unicode_escape(cursor: &mut Cursor<'_>) -> bool {
    if cursor.bump() != Some('{') {
        return false;
    }
    let mut seen = 0;
    while cursor.peek().is_some_and(|ch| ch.is_ascii_hexdigit()) {
        cursor.bump();
        seen += 1;
    }
    seen > 0 && cursor.bump() == Some('}')
}

/// Символьный оператор максимальным куском.
fn symbol(cursor: &mut Cursor<'_>) -> TokenKind {
    let start = cursor.mark();
    while cursor.peek().is_some_and(|ch| SYMBOLS.contains(ch)) {
        cursor.bump();
    }
    match cursor.text_from(start) {
        "->" => TokenKind::Arrow,
        "=>" => TokenKind::FatArrow,
        "=" => TokenKind::Equals,
        ":" => TokenKind::Colon,
        ":>" => TokenKind::Seal,
        "|" => TokenKind::Pipe,
        "\\" => TokenKind::Backslash,
        "@" => TokenKind::At,
        _ => TokenKind::Operator,
    }
}

/// Односимвольная пунктуация. В набор [`SYMBOLS`] она не входит и потому не
/// склеивается: `(a,b)` - пять токенов, а не оператор `,b`.
fn punctuation(ch: char) -> Option<TokenKind> {
    let kind = match ch {
        '(' => TokenKind::LParen,
        ')' => TokenKind::RParen,
        '[' => TokenKind::LBracket,
        ']' => TokenKind::RBracket,
        '{' => TokenKind::LBrace,
        '}' => TokenKind::RBrace,
        ',' => TokenKind::Comma,
        _ => return None,
    };
    Some(kind)
}

/// Может ли знак начинать имя.
fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

/// Может ли знак продолжать имя. Штрих допускается (`put s'` из §4.1), и
/// поэтому символьных литералов в языке нет - `'` занят.
fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

/// Запомненная позиция курсора.
#[derive(Clone, Copy, Debug)]
struct Mark {
    offset: usize,
    line: u32,
    column: u32,
}

impl Mark {
    /// Спан лексемы, начинающейся здесь и состоящей ровно из `text`.
    fn span_of(self, text: &str) -> Span {
        Span::new(self.offset, self.offset + text.len())
    }
}

/// Курсор по тексту, считающий строки и колонки.
struct Cursor<'a> {
    text: &'a str,
    offset: usize,
    line: u32,
    column: u32,
}

impl<'a> Cursor<'a> {
    /// Курсор на начале текста, за BOM'ом, если он есть.
    fn new(text: &'a str) -> Self {
        Self {
            text,
            offset: if text.starts_with(BOM) { BOM.len() } else { 0 },
            line: 1,
            column: 1,
        }
    }

    fn mark(&self) -> Mark {
        Mark {
            offset: self.offset,
            line: self.line,
            column: self.column,
        }
    }

    fn rest(&self) -> &'a str {
        &self.text[self.offset..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn starts_with(&self, prefix: &str) -> bool {
        self.rest().starts_with(prefix)
    }

    /// Хвост, начиная со `skip`-го символа от курсора.
    fn text_after(&self, skip: usize) -> &'a str {
        let mut chars = self.rest().chars();
        for _ in 0..skip {
            chars.next();
        }
        chars.as_str()
    }

    fn text_from(&self, start: Mark) -> &'a str {
        &self.text[start.offset..self.offset]
    }

    fn span_from(&self, start: Mark) -> Span {
        Span::new(start.offset, self.offset)
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.offset += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    /// Стоит ли курсор в отступе - до него на строке только пробелы.
    fn line_is_blank_before(&self) -> bool {
        self.text[..self.offset]
            .rsplit('\n')
            .next()
            .is_some_and(|prefix| prefix.chars().all(char::is_whitespace))
    }

    /// Начинается ли здесь комментарий `--`: символьный кусок целиком из
    /// минусов и длиной хотя бы два.
    fn dashes_start_a_comment(&self) -> bool {
        let run = self
            .rest()
            .find(|ch: char| !SYMBOLS.contains(ch))
            .unwrap_or(self.rest().len());
        let run = &self.rest()[..run];
        run.len() >= 2 && run.bytes().all(|byte| byte == b'-')
    }
}

#[cfg(test)]
mod tests {
    use super::{LexError, lex};
    use crate::token::TokenKind;

    fn kinds(text: &str) -> Vec<TokenKind> {
        lex(text)
            .expect("лексер справился")
            .tokens
            .iter()
            .map(|token| token.kind)
            .collect()
    }

    #[test]
    fn maximal_munch_keeps_operators_whole() {
        assert_eq!(
            kinds("a |> b"),
            [
                TokenKind::Ident,
                TokenKind::Operator,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
        // `::` - Cons (§4.4), а не два двоеточия.
        assert_eq!(
            kinds("x :: xs"),
            [
                TokenKind::Ident,
                TokenKind::Operator,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn dashes_split_between_comment_and_operator() {
        assert_eq!(kinds("a -- b"), [TokenKind::Ident, TokenKind::Eof]);
        assert_eq!(
            kinds("a --> b"),
            [
                TokenKind::Ident,
                TokenKind::Operator,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn a_dot_after_digits_is_a_decimal_point_only_before_a_digit() {
        assert_eq!(kinds("1.5"), [TokenKind::Float, TokenKind::Eof]);
        assert_eq!(
            kinds("1.foo"),
            [
                TokenKind::Nat,
                TokenKind::Operator,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
        assert_eq!(
            kinds("2e"),
            [TokenKind::Nat, TokenKind::Ident, TokenKind::Eof]
        );
        assert_eq!(kinds("2e-3"), [TokenKind::Float, TokenKind::Eof]);
    }

    #[test]
    fn a_digit_glued_to_a_name_stays_two_tokens() {
        // `1foo` - применение литерала к имени, как в Haskell; `0xs` - тоже,
        // потому что `s` не шестнадцатеричная цифра.
        assert_eq!(
            kinds("1foo"),
            [TokenKind::Nat, TokenKind::Ident, TokenKind::Eof]
        );
        assert_eq!(
            kinds("0xs"),
            [TokenKind::Nat, TokenKind::Ident, TokenKind::Eof]
        );
        assert_eq!(kinds("0xff"), [TokenKind::Nat, TokenKind::Eof]);
    }

    #[test]
    fn a_prime_continues_a_name() {
        assert_eq!(kinds("s'"), [TokenKind::Ident, TokenKind::Eof]);
    }

    #[test]
    fn block_comments_nest() {
        assert_eq!(kinds("{- {- x -} -} y"), [TokenKind::Ident, TokenKind::Eof]);
        // Спан указывает на открывающие две лексемы, а не на весь хвост файла.
        let Err(LexError::UnterminatedComment { open }) = lex("{- {- x -}") else {
            panic!("ожидался незакрытый комментарий");
        };
        assert_eq!((open.start(), open.end()), (0, 2));
    }

    #[test]
    fn a_tab_is_refused_only_where_indentation_is_measured() {
        assert!(matches!(
            lex("f = 1\n\tg = 2"),
            Err(LexError::TabInIndentation { .. })
        ));
        // Внутри строки табуляция - обычный знак.
        assert!(lex("f = 1\t+ 2").is_ok());
        // На строке без лексем мерить нечего: layout её не видит.
        assert!(lex("f = 1\n\t\ng = 2").is_ok(), "пустая строка");
        assert!(
            lex("f = 1\n\t-- хвост\ng = 2").is_ok(),
            "только комментарий"
        );
        assert!(lex("f = 1\n\t").is_ok(), "хвост файла");
    }

    #[test]
    fn columns_count_characters() {
        let lexed = lex("ℓ x").expect("лексер справился");
        assert_eq!(lexed.tokens[1].column, 3, "`ℓ` - один символ, два байта");
    }

    #[test]
    fn a_bom_is_not_a_token() {
        let lexed = lex("\u{feff}f = 1").expect("лексер справился");
        assert_eq!(lexed.tokens[0].kind, TokenKind::Ident);
        assert_eq!(lexed.tokens[0].column, 1, "BOM не сдвигает колонку");
    }

    #[test]
    fn a_comment_points_at_the_token_it_precedes() {
        let lexed = lex("-- шапка\nf = 1").expect("лексер справился");
        assert_eq!(lexed.comments.len(), 1);
        assert_eq!(lexed.comments[0].token, 0);
        let trailing = lex("f\n-- хвост").expect("лексер справился");
        assert_eq!(trailing.comments[0].token, 1, "последний токен - Eof");
    }

    #[test]
    fn strings_validate_their_escapes() {
        assert!(lex(r#""a\n\u{1F600}b""#).is_ok());
        assert!(matches!(
            lex(r#""a\q""#),
            Err(LexError::UnknownEscape { .. })
        ));
        // Спан обрывается на переводе строки, а не перескакивает через него.
        let Err(LexError::UnterminatedString { span }) = lex("\"abc\ndef\"") else {
            panic!("ожидался незакрытый литерал");
        };
        assert_eq!((span.start(), span.end()), (0, 4));
    }
}
