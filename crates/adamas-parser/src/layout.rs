//! Значимые отступы: поток токенов -> поток токенов с границами блоков.
//!
//! §4.1 фиксирует, что блоки задаются **только** отступами: фигурные скобки в
//! языке заняты effect row, записями и имплиситами. Отсюда отдельный проход:
//! лексер отступы измеряет, парсер видит уже готовые [`TokenKind::Open`],
//! [`TokenKind::Sep`] и [`TokenKind::Close`] и об отступах не знает ничего.
//!
//! # Правила
//!
//! 1. **Блок открывает ключевое слово.** `where`, `with`, `of`, `mutual`,
//!    `let` открывают блок всегда; `=` - только если стоит последним на своей
//!    строке. Колонка первого токена тела и есть колонка блока, и она обязана
//!    быть строго больше колонки объемлющего.
//! 2. **Офсайд.** Первая лексема строки с колонкой меньше колонки блока
//!    закрывает его (и дальше, пока есть что закрывать); равная - даёт границу
//!    между членами; большая - продолжение текущего члена. Границы не бывает
//!    перед лексемой, которая член начать не может (`starts_a_member`).
//!    Строка, начатая `where`, вдобавок закрывает блоки от `=` и `let`
//!    (`Members::Statements`): `where` присоединяется к объявлению, а члены
//!    таких блоков - операторы и связывания, и присоединяться не к чему.
//! 3. **Файл - блок**, открытый первым же токеном и закрытый только на `Eof`.
//!    Лексема левее его колонки - отказ.
//! 4. **Внутри скобок layout выключен.** Ни `Open`, ни `Sep`, ни `Close` там
//!    не появляются, а ключевое слово, которому нужен блок, - отказ.
//!
//! Правила языковые, а не детали реализации: они записаны в §4.1, обоснование
//! в decision log 2026-08-25. Коротко о самом неочевидном: `=` открывает блок
//! потому, что тело определения - последовательность операторов, разделить
//! которые нечем, кроме перевода строки; условие «последний на строке»
//! отделяет этот случай и от продолжения строки (`f x = bar` с аргументом
//! ниже), и от `=` внутри записи (§4.2). Цена правила 4 названа там же и
//! заведена §10 вопросом 55.

use adamas_core::source::Span;

use crate::token::{Token, TokenKind};

/// Ошибка расстановки блоков.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum LayoutError {
    /// Тело блока начинается не правее объемлющего блока.
    #[error("тело блока должно быть с большим отступом, чем окружающий блок")]
    ShallowBlock {
        /// Ключевое слово, открывающее блок.
        keyword: Span,
        /// Первый токен тела.
        body: Span,
        /// Его колонка.
        column: u32,
        /// Колонка объемлющего блока.
        enclosing: u32,
    },

    /// За ключевым словом, открывающим блок, ничего нет.
    #[error("после ключевого слова нет тела блока")]
    EmptyBlock {
        /// Ключевое слово.
        keyword: Span,
    },

    /// Лексема левее колонки блока файла.
    #[error("лексема левее первой в файле: блок файла закрывается только концом файла")]
    LeftOfFile {
        /// Она самая.
        token: Span,
        /// Её колонка.
        column: u32,
        /// Колонка блока файла - колонка первого токена файла.
        file: u32,
    },

    /// Ключевое слово, которому нужен блок, стоит внутри скобок.
    ///
    /// Внутри скобок layout выключен (§4.1, правило 4), поэтому блока там не
    /// возникнет ни при каком отступе. Отказ здесь, а не молчаливый поток без
    /// границ: иначе ошибка приедет из парсера и будет про другое.
    #[error("блок внутри скобок: layout там выключен (§10 вопрос 55)")]
    BlockInBrackets {
        /// Ключевое слово.
        keyword: Span,
        /// Скобка, которая выключила layout.
        open: Span,
    },

    /// Скобка не закрыта до конца файла.
    #[error("незакрытая скобка")]
    UnclosedBracket {
        /// Открывающая скобка.
        open: Span,
    },

    /// Закрывающая скобка без открывающей.
    #[error("закрывающая скобка без открывающей")]
    UnmatchedBracket {
        /// Она самая.
        close: Span,
    },

    /// Закрывающая скобка не того вида.
    #[error("скобка закрыта не тем видом скобки")]
    MismatchedBracket {
        /// Открывающая.
        open: Span,
        /// Закрывающая.
        close: Span,
    },
}

impl LayoutError {
    /// Где ошибка.
    #[must_use]
    pub fn span(self) -> Span {
        match self {
            Self::ShallowBlock { body: span, .. }
            | Self::EmptyBlock { keyword: span }
            | Self::LeftOfFile { token: span, .. }
            | Self::BlockInBrackets { keyword: span, .. }
            | Self::UnclosedBracket { open: span }
            | Self::UnmatchedBracket { close: span }
            | Self::MismatchedBracket { close: span, .. } => span,
        }
    }
}

/// Чем открыт блок, которого ещё нет.
#[derive(Clone, Copy, Debug)]
enum Pending {
    /// Верхний уровень: блок файла, ключевого слова у него нет.
    TopLevel,
    /// Тело ключевого слова.
    Body(Token),
}

/// Что за члены у блока.
///
/// Различие нужно одному правилу - тому, которое решает судьбу `where` на
/// колонке блока (правило 2). Больше layout про содержимое блока не знает и
/// знать не должен: разбирает его парсер.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Members {
    /// Объявления и ветки: файл, `where`, `of`, `with`, `mutual`.
    Declarations,
    /// Операторы и связывания: `=` и `let`.
    Statements,
}

/// Открытый блок.
#[derive(Clone, Copy, Debug)]
struct Block {
    /// Колонка первого токена тела - она же колонка каждого члена.
    column: u32,
    /// Что за члены.
    members: Members,
}

impl Block {
    /// Блок файла: члены - объявления, колонку задаёт первый токен файла.
    fn file(column: u32) -> Self {
        Self {
            column,
            members: Members::Declarations,
        }
    }

    /// Блок, открытый ключевым словом (или `=`).
    fn opened_by(keyword: TokenKind, column: u32) -> Self {
        let members = match keyword {
            TokenKind::Equals | TokenKind::Let => Members::Statements,
            _ => Members::Declarations,
        };
        Self { column, members }
    }
}

/// Расставляет границы блоков.
///
/// На вход идёт то, что отдал [`crate::lexer::lex`], вместе с завершающим
/// [`TokenKind::Eof`].
///
/// # Errors
///
/// Тело блока не правее объемлющего; пустое тело; лексема левее блока файла;
/// блок внутри скобок; несбалансированные скобки.
///
/// # Panics
///
/// В debug-сборке - если в потоке нет завершающего `Eof`: без него блоки
/// нечем закрыть, и результат вышел бы несбалансированным.
pub fn layout(tokens: &[Token]) -> Result<Vec<Token>, LayoutError> {
    debug_assert_eq!(
        tokens.last().map(|token| token.kind),
        Some(TokenKind::Eof),
        "layout ждёт поток целиком, вместе с Eof"
    );

    let mut out = Vec::with_capacity(tokens.len() + tokens.len() / 4);
    // Открытые блоки, снаружи внутрь. Первый - блок файла.
    let mut blocks: Vec<Block> = Vec::new();
    // Открытые скобки: внутри них layout выключен.
    let mut brackets: Vec<Token> = Vec::new();
    let mut pending = Some(Pending::TopLevel);
    // Строка предыдущего токена: по ней видно, первая ли лексема на строке.
    let mut previous_line = 0;

    for (index, token) in tokens.iter().enumerate() {
        if token.kind == TokenKind::Eof {
            if let Some(open) = brackets.first() {
                return Err(LayoutError::UnclosedBracket { open: open.span });
            }
            match pending {
                // Пустой файл - пустой блок верхнего уровня. Парсеру так
                // не нужно отдельной ветки на файл без деклараций.
                Some(Pending::TopLevel) => {
                    out.push(virtual_token(TokenKind::Open, token));
                    blocks.push(Block::file(token.column));
                }
                Some(Pending::Body(keyword)) => {
                    return Err(LayoutError::EmptyBlock {
                        keyword: keyword.span,
                    });
                }
                None => {}
            }
            while blocks.pop().is_some() {
                out.push(virtual_token(TokenKind::Close, token));
            }
            out.push(*token);
            break;
        }

        if let Some(&outermost) = brackets.first() {
            if opens_block_keyword(token.kind) {
                return Err(LayoutError::BlockInBrackets {
                    keyword: token.span,
                    open: outermost.span,
                });
            }
            track_bracket(&mut brackets, token)?;
            out.push(*token);
            previous_line = token.line;
            continue;
        }

        if let Some(opener) = pending.take() {
            let block = match opener {
                Pending::TopLevel => Block::file(token.column),
                Pending::Body(keyword) => {
                    if let Some(enclosing) = blocks.last() {
                        if token.column <= enclosing.column {
                            return Err(LayoutError::ShallowBlock {
                                keyword: keyword.span,
                                body: token.span,
                                column: token.column,
                                enclosing: enclosing.column,
                            });
                        }
                    }
                    Block::opened_by(keyword.kind, token.column)
                }
            };
            out.push(virtual_token(TokenKind::Open, token));
            blocks.push(block);
        } else if token.line != previous_line {
            // Блок файла переживает любой офсайд и закрывается только на Eof:
            // иначе всё, что левее первой декларации, оказалось бы вне всякого
            // блока, а парсер дочитал бы файл до края, ничего не заметив.
            while blocks.len() > 1 && blocks.last().is_some_and(|last| token.column < last.column) {
                blocks.pop();
                out.push(virtual_token(TokenKind::Close, token));
            }
            // `where` присоединяется к объявлению; в блоке от `=` или `let`
            // присоединяться не к чему, значит он закончился - на какой бы
            // колонке `where` ни стоял. Блок файла этим не задеть: он
            // `Declarations`, и цикл останавливается на нём.
            if token.kind == TokenKind::Where {
                while blocks
                    .last()
                    .is_some_and(|last| last.members == Members::Statements)
                {
                    blocks.pop();
                    out.push(virtual_token(TokenKind::Close, token));
                }
            }
            if let Some(file) = blocks.first().map(|first| first.column) {
                if token.column < file {
                    return Err(LayoutError::LeftOfFile {
                        token: token.span,
                        column: token.column,
                        file,
                    });
                }
            }
            let member_column = blocks.last().map(|last| last.column);
            if member_column == Some(token.column) && starts_a_member(token.kind) {
                out.push(virtual_token(TokenKind::Sep, token));
            }
        }

        out.push(*token);
        track_bracket(&mut brackets, token)?;
        if opens_block(tokens, index) {
            pending = Some(Pending::Body(*token));
        }
        previous_line = token.line;
    }

    Ok(out)
}

/// Ключевое слово, которое открывает блок всегда.
fn opens_block_keyword(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Where | TokenKind::With | TokenKind::Of | TokenKind::Mutual | TokenKind::Let
    )
}

/// Открывает ли токен блок.
fn opens_block(tokens: &[Token], index: usize) -> bool {
    let token = tokens[index];
    if opens_block_keyword(token.kind) {
        return true;
    }
    // `=` - только последним на строке, см. заголовок модуля. Конец файла
    // считается концом строки: иначе `f =` без финального перевода строки и с
    // ним отвергались бы разными проходами.
    token.kind == TokenKind::Equals
        && tokens
            .get(index + 1)
            .is_some_and(|next| next.line != token.line || next.kind == TokenKind::Eof)
}

/// Может ли лексема начинать член блока.
///
/// `then`, `else`, `of`, `where`, `with` не могут: каждое продолжает уже
/// начатую конструкцию. Поэтому строка, начатая одним из них, продолжает член,
/// а не открывает новый, - без этого правила многострочный `if` разваливался бы
/// на три члена, а `where`, отбитый на колонку определения, - на два.
///
/// У `where` это верно там, где члены - объявления: тогда он продолжает
/// предыдущее. Из блока операторов он выходит наружу раньше, чем дело дойдёт
/// сюда, - см. [`Members`].
fn starts_a_member(kind: TokenKind) -> bool {
    !matches!(
        kind,
        TokenKind::Then | TokenKind::Else | TokenKind::Of | TokenKind::Where | TokenKind::With
    )
}

/// Учитывает скобку. Внутри скобок layout выключен, поэтому знать, где они
/// открылись и закрылись, обязан именно этот проход - и он же даёт по ним
/// диагностику, потому что рассинхронизация видна здесь раньше всего.
fn track_bracket(brackets: &mut Vec<Token>, token: &Token) -> Result<(), LayoutError> {
    if token.kind.opens_bracket() {
        brackets.push(*token);
        return Ok(());
    }
    if !token.kind.closes_bracket() {
        return Ok(());
    }
    let Some(open) = brackets.pop() else {
        return Err(LayoutError::UnmatchedBracket { close: token.span });
    };
    if open.kind.closing_bracket() == Some(token.kind) {
        Ok(())
    } else {
        Err(LayoutError::MismatchedBracket {
            open: open.span,
            close: token.span,
        })
    }
}

/// Виртуальный токен в позиции того, что его вызвал. Спан пустой: в исходнике
/// этой лексемы нет, но указать на место, где она подразумевается, диагностика
/// обязана уметь.
fn virtual_token(kind: TokenKind, at: &Token) -> Token {
    Token {
        kind,
        span: Span::at(at.span.start()),
        line: at.line,
        column: at.column,
    }
}

#[cfg(test)]
mod tests {
    use super::{LayoutError, layout};
    use crate::lexer::lex;
    use crate::token::{Token, dump_inline};

    fn run(text: &str) -> Result<Vec<Token>, LayoutError> {
        layout(&lex(text).expect("лексер справился").tokens)
    }

    fn shape(text: &str) -> String {
        dump_inline(text, &run(text).expect("layout справился"))
    }

    #[test]
    fn the_file_is_a_block() {
        assert_eq!(shape("f = 1\ng = 2"), "{| f = 1 ; g = 2 |}");
        assert_eq!(shape(""), "{| |}", "пустой файл - пустой блок");
        assert_eq!(shape("-- только комментарий"), "{| |}");
    }

    #[test]
    fn the_file_block_outlives_every_offside() {
        // Колонку блока файла задаёт первый токен; левее неё - отказ, а не
        // декларация вне всякого блока.
        assert_eq!(shape("  f = 1\n  g = 2"), "{| f = 1 ; g = 2 |}");
        let Err(LayoutError::LeftOfFile { column, file, .. }) = run("  f = 1\ng = 2") else {
            panic!("ожидалась лексема левее блока файла");
        };
        assert_eq!((column, file), (1, 3));
    }

    #[test]
    fn a_trailing_equals_opens_the_body() {
        // §4.1: тело counter - три оператора, разделить их нечем, кроме
        // перевода строки.
        assert_eq!(
            shape("counter =\n  let n = get\n  put n\n  n"),
            "{| counter = {| let {| n = get |} ; put n ; n |} |}"
        );
    }

    #[test]
    fn an_equals_inside_a_line_leaves_a_continuation() {
        // Аргумент, перенесённый на следующую строку, остаётся аргументом.
        assert_eq!(shape("f = bar\n  baz"), "{| f = bar baz |}");
    }

    #[test]
    fn where_always_opens() {
        assert_eq!(
            shape("data Vect : Type where\n  Nil : Vect\n  Cons : Vect"),
            "{| data Vect : Type where {| Nil : Vect ; Cons : Vect |} |}"
        );
    }

    #[test]
    fn a_dedent_closes_every_block_it_leaves() {
        // Тело `y =` отбито глубже самого `y`: колонка `y` - это колонка
        // блока `let`, и всё, что левее, его закрывает.
        assert_eq!(
            shape("f x =\n  let y =\n        g x\n  y\nh = 1"),
            "{| f x = {| let {| y = {| g x |} |} ; y |} ; h = 1 |}"
        );
    }

    #[test]
    fn a_continuation_keyword_gets_no_separator() {
        // Многострочный `if`: `then` и `else` на колонке `if` продолжают член,
        // а не открывают новые.
        assert_eq!(
            shape("f =\n  if p\n  then 1\n  else 2"),
            "{| f = {| if p then 1 else 2 |} |}"
        );
        // `where`, отбитый на колонку определения, - продолжение определения.
        assert_eq!(
            shape("f x = y\nwhere\n  y = 1"),
            "{| f x = y where {| y = 1 |} |}"
        );
        // И на колонке члена в блоке объявлений - продолжение этого члена.
        assert_eq!(
            shape("f x = y\n  where\n    g z = w\n    where\n      h = 1"),
            "{| f x = y where {| g z = w where {| h = 1 |} |} |}"
        );
        // Закрывать блоки офсайд при этом не перестаёт.
        assert_eq!(
            shape("f x =\n    case x of\n      A -> 1\n  where\n    y = 1"),
            "{| f x = {| case x of {| A -> 1 |} |} where {| y = 1 |} |}"
        );
    }

    #[test]
    fn where_leaves_the_block_of_statements() {
        // `where` присоединяется к клаузе, а не к оператору внутри её тела,
        // поэтому тело закрывается - на любой колонке самого `where`.
        assert_eq!(
            shape("f x =\n  y\n  where\n    z = 1"),
            "{| f x = {| y |} where {| z = 1 |} |}"
        );
        assert_eq!(
            shape("f x =\n  y\n    where\n      z = 1"),
            "{| f x = {| y |} where {| z = 1 |} |}"
        );
        // Блок `let` - тоже блок операторов, и выходить приходится через два.
        assert_eq!(
            shape("f x =\n  let y = 1\n  y\n  where\n    z = 1"),
            "{| f x = {| let {| y = 1 |} ; y |} where {| z = 1 |} |}"
        );
    }

    #[test]
    fn brackets_switch_layout_off() {
        // Перенос внутри скобок ничего не открывает и не закрывает.
        assert_eq!(
            shape("f = g (a,\nb)\nh = 1"),
            "{| f = g ( a , b ) ; h = 1 |}"
        );
        // `=` в записи блока не открывает - ни в строке, ни в её конце.
        assert_eq!(shape("f = { x = 1, y = 2 }"), "{| f = { x = 1 , y = 2 } |}");
        assert_eq!(
            shape("f = { x =\n        1\n    , y = 2 }"),
            "{| f = { x = 1 , y = 2 } |}"
        );
    }

    #[test]
    fn a_block_keyword_inside_brackets_is_refused() {
        // §10 вопрос 55: блок внутри скобок невыразим - и это видно сразу,
        // а не в парсере, которому достался бы поток без границ.
        assert!(matches!(
            run("f = map (\\x -> let y = f x\n  g y) xs"),
            Err(LayoutError::BlockInBrackets { .. })
        ));
        assert!(matches!(
            run("f = (case x of A -> 1)"),
            Err(LayoutError::BlockInBrackets { .. })
        ));
    }

    #[test]
    fn a_body_must_be_deeper_than_its_block() {
        assert!(matches!(
            run("f =\nx"),
            Err(LayoutError::ShallowBlock { .. })
        ));
        assert!(matches!(
            run("f = where"),
            Err(LayoutError::EmptyBlock { .. })
        ));
        // С финальным переводом строки и без него - одна и та же ошибка.
        assert!(matches!(run("f ="), Err(LayoutError::EmptyBlock { .. })));
        assert!(matches!(run("f =\n"), Err(LayoutError::EmptyBlock { .. })));
    }

    #[test]
    fn brackets_are_checked_for_balance() {
        assert!(matches!(
            run("f = (a"),
            Err(LayoutError::UnclosedBracket { .. })
        ));
        assert!(matches!(
            run("f = a)"),
            Err(LayoutError::UnmatchedBracket { .. })
        ));
        assert!(matches!(
            run("f = (a]"),
            Err(LayoutError::MismatchedBracket { .. })
        ));
    }
}
