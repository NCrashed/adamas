//! Токены поверхностного языка (§4.1).
//!
//! Токен текста не носит: у него есть спан, а сам текст берётся из исходника
//! срезом ([`Token::text`]). Поэтому `Token` - `Copy`, и парсер таскает его по
//! значению, не считая ссылок и не аллоцируя строк на каждое имя.
//!
//! Ключевые слова распознаёт лексер, сверяя текст идентификатора с таблицей
//! ([`keyword`]). Зарезервировано сразу всё, что §4 показывает синтаксической
//! формой, включая формы Фаз 3-4 (decision log 2026-08-25, пункт 6).

use std::fmt;

use adamas_core::source::Span;

/// Разновидность токена.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    /// Идентификатор: буква или `_`, дальше буквы, цифры, `_`, `'`.
    ///
    /// Буквы юникодные: §4.1 пишет `{ℓ : Level}`, и `ℓ` обязана быть именем.
    Ident,
    /// Символьный оператор - максимальный кусок из символьных знаков.
    ///
    /// Фикситеты объявляются в prelude (`infixl 6 +, -`, §4.4), поэтому лексер
    /// операторы не различает: `+`, `<>`, `::` и `|>` для него одно и то же.
    Operator,
    /// Натуральный литерал: `42`, `0xff`. Класс преобразования - `FromNat`
    /// (§4.3).
    Nat,
    /// Литерал с плавающей точкой: `3.14`, `1e9`. Класс - `FromFloat` (§4.3).
    Float,
    /// Строковый литерал вместе с кавычками. Экранирование проверено лексером,
    /// раскодировка - за парсером.
    Str,

    /// `data`
    Data,
    /// `where`
    Where,
    /// `let`
    Let,
    /// `case`
    Case,
    /// `of`
    Of,
    /// `if`
    If,
    /// `then`
    Then,
    /// `else`
    Else,
    /// `resource` (§3.3, §4.1)
    Resource,
    /// `unique` - маркер уникальности на `data` (§3.3)
    Unique,
    /// `effect` (§3.4)
    Effect,
    /// `handle` (§3.4)
    Handle,
    /// `handleMulti` (§3.4)
    HandleMulti,
    /// `with`
    With,
    /// `class` (§4.1)
    Class,
    /// `instance` (§4.1)
    Instance,
    /// `when` - суперклассы класса (§4.1)
    When,
    /// `module` (§4.8)
    Module,
    /// `type` - записи (§4.2)
    Type,
    /// `mutual` (§4.8)
    Mutual,
    /// `using` - выбор именованного инстанса (§4.1)
    Using,
    /// `import` (§4.8)
    Import,
    /// `coherent` - маркер глобальной уникальности инстансов (§3.5)
    Coherent,
    /// `infix`
    Infix,
    /// `infixl`
    Infixl,
    /// `infixr`
    Infixr,

    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    /// `=`
    Equals,
    /// `:`
    Colon,
    /// `|`
    Pipe,
    /// `\`
    Backslash,
    /// `@` - type application и атрибуты (§4.1, §4.6)
    At,
    /// `,`
    Comma,
    /// `_`
    Underscore,

    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LBrace,
    /// `}`
    RBrace,

    /// Начало блока. Ставит [`crate::layout`], в исходнике не пишется.
    Open,
    /// Граница между членами блока. Ставит [`crate::layout`].
    Sep,
    /// Конец блока. Ставит [`crate::layout`].
    Close,
    /// Конец файла. Идёт последним всегда, чтобы парсеру не проверять край
    /// потока отдельно от края конструкции.
    Eof,
}

/// Как выглядит разновидность токена.
///
/// Одна таблица на всё: и на отладочный дамп, и на сообщения об ошибках.
/// Раздельные таблицы разъезжаются - добавить ключевое слово в одну и забыть
/// про другую компилятор не мешает, а `match` здесь исчерпывающий.
enum Face {
    /// Написание единственно и совпадает с текстом в исходнике.
    Spelled(&'static str),
    /// Написаний много (имена, литералы) или нет вовсе (виртуальные границы).
    Class {
        /// Короткое имя для [`dump`].
        tag: &'static str,
        /// Как назвать в сообщении об ошибке.
        described: &'static str,
    },
}

impl TokenKind {
    fn face(self) -> Face {
        let class = |tag, described| Face::Class { tag, described };
        match self {
            Self::Ident => class("ident", "идентификатор"),
            Self::Operator => class("op", "оператор"),
            Self::Nat => class("nat", "натуральный литерал"),
            Self::Float => class("float", "литерал с плавающей точкой"),
            Self::Str => class("str", "строковый литерал"),
            Self::Open => class("open", "начало блока"),
            Self::Sep => class("sep", "граница блока"),
            Self::Close => class("close", "конец блока"),
            Self::Eof => class("eof", "конец файла"),

            Self::Data => Face::Spelled("data"),
            Self::Where => Face::Spelled("where"),
            Self::Let => Face::Spelled("let"),
            Self::Case => Face::Spelled("case"),
            Self::Of => Face::Spelled("of"),
            Self::If => Face::Spelled("if"),
            Self::Then => Face::Spelled("then"),
            Self::Else => Face::Spelled("else"),
            Self::Resource => Face::Spelled("resource"),
            Self::Unique => Face::Spelled("unique"),
            Self::Effect => Face::Spelled("effect"),
            Self::Handle => Face::Spelled("handle"),
            Self::HandleMulti => Face::Spelled("handleMulti"),
            Self::With => Face::Spelled("with"),
            Self::Class => Face::Spelled("class"),
            Self::Instance => Face::Spelled("instance"),
            Self::When => Face::Spelled("when"),
            Self::Module => Face::Spelled("module"),
            Self::Type => Face::Spelled("type"),
            Self::Mutual => Face::Spelled("mutual"),
            Self::Using => Face::Spelled("using"),
            Self::Import => Face::Spelled("import"),
            Self::Coherent => Face::Spelled("coherent"),
            Self::Infix => Face::Spelled("infix"),
            Self::Infixl => Face::Spelled("infixl"),
            Self::Infixr => Face::Spelled("infixr"),

            Self::Arrow => Face::Spelled("->"),
            Self::FatArrow => Face::Spelled("=>"),
            Self::Equals => Face::Spelled("="),
            Self::Colon => Face::Spelled(":"),
            Self::Pipe => Face::Spelled("|"),
            Self::Backslash => Face::Spelled("\\"),
            Self::At => Face::Spelled("@"),
            Self::Comma => Face::Spelled(","),
            Self::Underscore => Face::Spelled("_"),
            Self::LParen => Face::Spelled("("),
            Self::RParen => Face::Spelled(")"),
            Self::LBracket => Face::Spelled("["),
            Self::RBracket => Face::Spelled("]"),
            Self::LBrace => Face::Spelled("{"),
            Self::RBrace => Face::Spelled("}"),
        }
    }

    /// Как лексема пишется в исходнике. `None` у тех, чьё написание не одно:
    /// имён, литералов и виртуальных границ блока.
    #[must_use]
    pub fn spelling(self) -> Option<&'static str> {
        match self.face() {
            Face::Spelled(text) => Some(text),
            Face::Class { .. } => None,
        }
    }

    /// Короткое имя для отладочной печати ([`dump`]). У лексемы с единственным
    /// написанием это само написание.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self.face() {
            Face::Spelled(text) => text,
            Face::Class { tag, .. } => tag,
        }
    }

    /// Открывающая скобка? Внутри скобок layout приостановлен
    /// ([`crate::layout`]).
    #[must_use]
    pub fn opens_bracket(self) -> bool {
        matches!(self, Self::LParen | Self::LBracket | Self::LBrace)
    }

    /// Закрывающая для этой открывающей.
    #[must_use]
    pub fn closing_bracket(self) -> Option<Self> {
        match self {
            Self::LParen => Some(Self::RParen),
            Self::LBracket => Some(Self::RBracket),
            Self::LBrace => Some(Self::RBrace),
            _ => None,
        }
    }

    /// Закрывающая скобка?
    #[must_use]
    pub fn closes_bracket(self) -> bool {
        matches!(self, Self::RParen | Self::RBracket | Self::RBrace)
    }

    /// Виртуальная граница блока - то, что дописал [`crate::layout`].
    #[must_use]
    pub fn is_virtual(self) -> bool {
        matches!(self, Self::Open | Self::Sep | Self::Close)
    }
}

/// Как токен назвать в сообщении об ошибке: `` `data` `` для лексемы с
/// единственным написанием, «идентификатор» для класса лексем.
impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.face() {
            Face::Spelled(text) => write!(f, "`{text}`"),
            Face::Class { described, .. } => f.write_str(described),
        }
    }
}

/// Ключевое слово по тексту идентификатора. `None` - обычное имя.
///
/// Таблица здесь вторая - обратная к [`TokenKind::spelling`], - и это `match`
/// ради скорости: слово сверяется на каждом идентификаторе. Что обе таблицы
/// говорят об одном и том же, проверяют `debug_assert` ниже и тест
/// `keywords_spell_themselves`.
#[must_use]
pub fn keyword(text: &str) -> Option<TokenKind> {
    let kind = match text {
        "data" => TokenKind::Data,
        "where" => TokenKind::Where,
        "let" => TokenKind::Let,
        "case" => TokenKind::Case,
        "of" => TokenKind::Of,
        "if" => TokenKind::If,
        "then" => TokenKind::Then,
        "else" => TokenKind::Else,
        "resource" => TokenKind::Resource,
        "unique" => TokenKind::Unique,
        "effect" => TokenKind::Effect,
        "handle" => TokenKind::Handle,
        "handleMulti" => TokenKind::HandleMulti,
        "with" => TokenKind::With,
        "class" => TokenKind::Class,
        "instance" => TokenKind::Instance,
        "when" => TokenKind::When,
        "module" => TokenKind::Module,
        "type" => TokenKind::Type,
        "mutual" => TokenKind::Mutual,
        "using" => TokenKind::Using,
        "import" => TokenKind::Import,
        "coherent" => TokenKind::Coherent,
        "infix" => TokenKind::Infix,
        "infixl" => TokenKind::Infixl,
        "infixr" => TokenKind::Infixr,
        _ => return None,
    };
    debug_assert_eq!(kind.spelling(), Some(text), "таблицы разъехались");
    Some(kind)
}

/// Токен: что, где и в какой позиции строки.
///
/// Строка и колонка хранятся, а не считаются по спану: их отдаёт лексер даром,
/// а [`crate::layout`] спрашивает колонку у каждого токена. Пересчёт через
/// [`adamas_core::source::SourceFile::location`] дал бы двоичный поиск на
/// токен там, где достаточно счётчика.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    /// Что за токен.
    pub kind: TokenKind,
    /// Диапазон в исходнике. У виртуальных токенов пустой.
    pub span: Span,
    /// Номер строки, с единицы.
    pub line: u32,
    /// Номер колонки в Unicode scalar values, с единицы - как
    /// [`adamas_core::source::Location`].
    pub column: u32,
}

impl Token {
    /// Текст токена из исходника. У виртуальных токенов пустой.
    ///
    /// # Panics
    ///
    /// Если `text` - не тот исходник, из которого токен получен.
    #[must_use]
    pub fn text<'a>(&self, text: &'a str) -> &'a str {
        &text[self.span.start()..self.span.end()]
    }
}

/// Вид комментария.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommentKind {
    /// `-- до конца строки`
    Line,
    /// `{- ... -}`, вложенные допускаются
    Block,
}

/// Комментарий, привязанный к токену, перед которым стоит.
///
/// Комментарии живут в отдельной таблице, а не на узлах: элаборации они не
/// нужны вовсе, а `adamas fmt` (§7.1) без них съел бы их при первом же
/// проходе. Привязка к **следующему** токену, а не к предыдущему, потому что
/// комментарий в этом языке пишется над тем, что поясняет.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Comment {
    /// Вид.
    pub kind: CommentKind,
    /// Диапазон вместе с открывающими знаками.
    pub span: Span,
    /// Индекс токена, перед которым комментарий стоит, в [`Tokens::tokens`] -
    /// того же значения, что несёт этот комментарий. У комментария в конце
    /// файла это индекс [`TokenKind::Eof`].
    pub token: u32,
}

/// Токены файла вместе с комментариями.
///
/// Тип один на оба прохода: [`crate::lexer::lex`] отдаёт его без виртуальных
/// границ, [`crate::tokenize`] - с ними и с пересчитанными индексами. Инвариант
/// поэтому тоже один: [`Comment::token`] всегда индексирует соседнее поле
/// `tokens`, а не какой-то другой поток.
#[derive(Clone, Debug, Default)]
pub struct Tokens {
    /// Поток; последний - [`TokenKind::Eof`].
    pub tokens: Vec<Token>,
    /// Комментарии в порядке появления.
    pub comments: Vec<Comment>,
}

/// Ширина колонки тега в [`dump`]. Хватает самого длинного тега класса лексем
/// (`float`); написания длиннее её печатаются как есть, но текста за ними нет
/// и сталкиваться не с чем.
const TAG_WIDTH: usize = 8;

/// Отладочная печать потока: по токену на строку.
///
/// Нужна снапшотам и будущему `adamas check --dump-tokens`. Текст печатается
/// только у тех, чьё написание не единственно: у ключевого слова он совпал бы
/// с тегом, а у виртуального токена его нет вовсе.
#[must_use]
pub fn dump(text: &str, tokens: &[Token]) -> String {
    let mut out = String::new();
    for token in tokens {
        let position = format!("{}:{}", token.line, token.column);
        let body = if token.kind.spelling().is_some() {
            ""
        } else {
            token.text(text)
        };
        let line = format!(
            "{position:<8}{tag:<TAG_WIDTH$}{body}",
            tag = token.kind.tag()
        );
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

/// Отладочная печать потока в одну строку: видно, где границы блоков.
///
/// Границы печатаются `{|`, `;`, `|}`, а не фигурными скобками: скобки в языке
/// заняты записями и effect row, и в примере с записью настоящая скобка и
/// граница блока выглядели бы одинаково.
#[must_use]
pub fn dump_inline(text: &str, tokens: &[Token]) -> String {
    let mut out = String::new();
    for token in tokens {
        let piece = match token.kind {
            TokenKind::Open => "{|",
            TokenKind::Sep => ";",
            TokenKind::Close => "|}",
            TokenKind::Eof => continue,
            _ => token.text(text),
        };
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(piece);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{TokenKind, keyword};

    /// Все ключевые слова языка. Список ради проверки ниже: исчерпывающего
    /// обхода вариантов enum'а в stable Rust нет.
    const KEYWORDS: &[TokenKind] = &[
        TokenKind::Data,
        TokenKind::Where,
        TokenKind::Let,
        TokenKind::Case,
        TokenKind::Of,
        TokenKind::If,
        TokenKind::Then,
        TokenKind::Else,
        TokenKind::Resource,
        TokenKind::Unique,
        TokenKind::Effect,
        TokenKind::Handle,
        TokenKind::HandleMulti,
        TokenKind::With,
        TokenKind::Class,
        TokenKind::Instance,
        TokenKind::When,
        TokenKind::Module,
        TokenKind::Type,
        TokenKind::Mutual,
        TokenKind::Using,
        TokenKind::Import,
        TokenKind::Coherent,
        TokenKind::Infix,
        TokenKind::Infixl,
        TokenKind::Infixr,
    ];

    #[test]
    fn keywords_are_not_identifiers() {
        assert_eq!(keyword("data"), Some(TokenKind::Data));
        assert_eq!(keyword("handleMulti"), Some(TokenKind::HandleMulti));
        assert_eq!(keyword("Data"), None, "регистр значим");
        assert_eq!(keyword("dataset"), None, "префикс - не ключевое слово");
    }

    /// Прямая и обратная таблицы согласованы: как слово пишется, так оно и
    /// распознаётся.
    #[test]
    fn keywords_spell_themselves() {
        for &kind in KEYWORDS {
            let spelling = kind.spelling().expect("у ключевого слова есть написание");
            assert_eq!(keyword(spelling), Some(kind), "{spelling}");
        }
    }

    #[test]
    fn a_kind_is_named_by_its_spelling_or_by_its_class() {
        assert_eq!(TokenKind::Data.to_string(), "`data`");
        assert_eq!(TokenKind::Arrow.to_string(), "`->`");
        assert_eq!(TokenKind::Ident.to_string(), "идентификатор");
        // Дамп печатает написание без бэктиков: текст токена стоит рядом.
        assert_eq!(TokenKind::Data.tag(), "data");
        assert_eq!(TokenKind::Ident.tag(), "ident");
    }

    #[test]
    fn brackets_know_their_pairs() {
        assert_eq!(TokenKind::LBrace.closing_bracket(), Some(TokenKind::RBrace));
        assert_eq!(TokenKind::Ident.closing_bracket(), None);
    }
}
