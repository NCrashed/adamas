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
    /// Чем открыт: по нему `->` узнаёт, что стоит в ветке (§10 вопрос 61).
    opener: TokenKind,
}

impl Block {
    /// Блок файла: члены - объявления, колонку задаёт первый токен файла.
    fn file(column: u32) -> Self {
        Self {
            column,
            members: Members::Declarations,
            opener: TokenKind::Eof,
        }
    }

    /// Блок, открытый ключевым словом (или `=`, или `->`).
    fn opened_by(keyword: TokenKind, column: u32) -> Self {
        let members = match keyword {
            TokenKind::Equals | TokenKind::Let | TokenKind::Arrow => Members::Statements,
            _ => Members::Declarations,
        };
        Self {
            column,
            members,
            opener: keyword,
        }
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
    let mut brackets: Vec<(Token, usize)> = Vec::new();
    let mut pending = Some(Pending::TopLevel);
    // Строка предыдущего токена: по ней видно, первая ли лексема на строке.
    let mut previous_line = 0;

    for (index, token) in tokens.iter().enumerate() {
        if token.kind == TokenKind::Eof {
            if let Some((open, _)) = brackets.first() {
                return Err(LayoutError::UnclosedBracket { open: open.span });
            }
            match pending {
                // Пустой файл - пустой блок верхнего уровня. Парсеру так
                // не нужно отдельной ветки на файл без деклараций.
                Some(Pending::TopLevel) => {
                    out.push(virtual_token(TokenKind::Open, token));
                    blocks.push(Block::file(token.column));
                }
                // `of` без веток законен: разбор с нулём ветвей и есть
                // доказательство необитаемости, и `absurd` пишется только им
                // (§9 Фаза 1, сверка 2026-09-08). Пустых блоков layout не
                // делает, поэтому блок тут не открывается вовсе.
                //
                // Прочие ключевые слова остаются как были: `f =` без тела -
                // ошибка, и её не с чем спутать.
                Some(Pending::Body(keyword)) if keyword.kind != TokenKind::Of => {
                    return Err(LayoutError::EmptyBlock {
                        keyword: keyword.span,
                    });
                }
                Some(Pending::Body(_)) | None => {}
            }
            while blocks.pop().is_some() {
                out.push(virtual_token(TokenKind::Close, token));
            }
            out.push(*token);
            break;
        }

        // Внутри скобок layout выключен **не весь** (§10 вопрос 55). `let` и
        // `where` там работают: без них лямбда с телом-цепочкой не пишется, а
        // цепочка `let` - обычный способ писать эффектный код (§3.4). Прочие
        // открывашки остаются выключенными: `of` под скобкой требовал бы
        // разделителей, которых там нет, а `=` столкнулся бы с записью
        // `{ x = 1, y = 2 }`, где блок обязан закрыться на запятой.
        //
        // Блок, открытый под скобкой, закрывается на **парной**: она и есть его
        // граница, потому что отступ внутри скобок ничего не обещает.
        if let Some(&(outermost, _)) = brackets.first() {
            if opens_block_keyword(token.kind) && !opens_inside_brackets(token.kind) {
                return Err(LayoutError::BlockInBrackets {
                    keyword: token.span,
                    open: outermost.span,
                });
            }
            if bare_in_brackets(tokens, index, &brackets, &blocks, pending.is_some()) {
                track_bracket(&mut brackets, token, &mut blocks, &mut out)?;
                out.push(*token);
                previous_line = token.line;
                continue;
            }
        }

        if branchless(pending, token, &blocks) {
            pending = None;
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
            offside(token, &mut blocks, &mut out);
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

        // Закрывающая скобка сперва закрывает блоки, открытые под ней, и лишь
        // потом идёт в поток: иначе `Close` встанет после неё, и парсер
        // увидит скобку посреди блока.
        track_bracket(&mut brackets, token, &mut blocks, &mut out)?;
        out.push(*token);
        let inside = blocks.last().map(|it| it.opener);
        if opens_block(
            tokens,
            index,
            sequenced(tokens, index, inside),
            !brackets.is_empty(),
        ) {
            pending = Some(Pending::Body(*token));
        }
        previous_line = token.line;
    }

    Ok(out)
}

/// Открывашка, работающая и под скобкой (§10 вопрос 55).
///
/// `let` и `where` - потому что без них лямбда с телом-цепочкой не пишется.
/// `of` под скобкой требовал бы разделителей, которых там нет; `=` столкнулся
/// бы с записью `{ x = 1, y = 2 }`, где блок обязан закрыться на запятой.
fn opens_inside_brackets(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::Let | TokenKind::Where)
}

/// Ключевое слово, которое открывает блок всегда.
fn opens_block_keyword(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Where | TokenKind::With | TokenKind::Of | TokenKind::Mutual | TokenKind::Let
    )
}

/// Открывает ли токен блок.
///
/// `sequenced` - стоим ли там, где стрелка открывает блок; `bracketed` - внутри
/// скобок, где часть открывашек выключена (§10 вопрос 55).
fn opens_block(tokens: &[Token], index: usize, sequenced: bool, bracketed: bool) -> bool {
    let token = tokens[index];
    if opens_block_keyword(token.kind) {
        return !bracketed || opens_inside_brackets(token.kind);
    }
    // `=` под скобкой выключен: он столкнулся бы с записью `{ x = 1, y = 2 }`,
    // где блок обязан закрыться на запятой, а закрывать его там нечем.
    if bracketed && token.kind == TokenKind::Equals {
        return false;
    }
    // `=` - только последним на строке, см. заголовок модуля. Конец файла
    // считается концом строки: иначе `f =` без финального перевода строки и с
    // ним отвергались бы разными проходами.
    //
    // `->` - тем же правилом, но **не везде** (§10 вопрос 61). Стрелка живёт и
    // в типах, где `f : Nat ->` с переносом есть продолжение, а не блок;
    // различает их место: тело ветки `of` и тело лямбды - позиции, где
    // последовательность и пишут.
    let last_on_line = tokens
        .get(index + 1)
        .is_some_and(|next| next.line != token.line || next.kind == TokenKind::Eof);
    last_on_line
        && (token.kind == TokenKind::Equals || (sequenced && token.kind == TokenKind::Arrow))
}

/// Офсайд: первая лексема строки закрывает всё, что левее её колонки.
///
/// Блок файла переживает любой офсайд и закрывается только на `Eof`: иначе всё,
/// что левее первой декларации, оказалось бы вне всякого блока, а парсер дочитал
/// бы файл до края, ничего не заметив.
///
/// `where` вдобавок закрывает блоки от `=` и `let`: он присоединяется к
/// объявлению, а членам таких блоков присоединяться не к чему - на какой бы
/// колонке он ни стоял. Блок файла этим не задеть: он `Declarations`, и цикл
/// останавливается на нём.
fn offside(token: &Token, blocks: &mut Vec<Block>, out: &mut Vec<Token>) {
    while blocks.len() > 1 && blocks.last().is_some_and(|last| token.column < last.column) {
        blocks.pop();
        out.push(virtual_token(TokenKind::Close, token));
    }
    if token.kind == TokenKind::Where {
        while blocks
            .last()
            .is_some_and(|last| last.members == Members::Statements)
        {
            blocks.pop();
            out.push(virtual_token(TokenKind::Close, token));
        }
    }
}

/// Молчит ли layout на этом токене под скобкой.
///
/// Пока под скобкой ни одного блока не открыто, скобочное выражение отступом не
/// размечается - как и прежде. Молчит, но не глух: лексему, которая блок
/// **откроет**, проход обязан увидеть, иначе стрелка лямбды под скобкой пройдёт
/// мимо (§10 вопрос 55).
fn bare_in_brackets(
    tokens: &[Token],
    index: usize,
    brackets: &[(Token, usize)],
    blocks: &[Block],
    pending: bool,
) -> bool {
    let inside = blocks.last().map(|it| it.opener);
    brackets
        .last()
        .is_some_and(|&(_, depth)| blocks.len() <= depth)
        && !pending
        && !opens_block(tokens, index, sequenced(tokens, index, inside), true)
}

/// Стоит ли стрелка там, где за ней разрешена последовательность.
///
/// Два места, и оба узнаются на месте: тело ветки - когда ближайший блок открыт
/// `of`; тело лямбды - когда на этой же строке левее стоит `\`.
fn sequenced(tokens: &[Token], index: usize, inside: Option<TokenKind>) -> bool {
    if inside == Some(TokenKind::Of) {
        return true;
    }
    let line = tokens[index].line;
    tokens[..index]
        .iter()
        .rev()
        .take_while(|it| it.line == line)
        .any(|it| it.kind == TokenKind::Backslash)
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
fn track_bracket(
    brackets: &mut Vec<(Token, usize)>,
    token: &Token,
    blocks: &mut Vec<Block>,
    out: &mut Vec<Token>,
) -> Result<(), LayoutError> {
    if token.kind.opens_bracket() {
        brackets.push((*token, blocks.len()));
        return Ok(());
    }
    // Блоки, открытые под этой скобкой, закрываются ею: отступ внутри скобок
    // границы не задаёт, а парная её задаёт однозначно (§10 вопрос 55).
    // Условие разбито на два: `let` в цепочке `&&` требует Rust 2024, а MSRV
    // проекта 1.85 (джоба `msrv` его и ловит).
    if let Some(&(_, depth)) = brackets.last().filter(|_| token.kind.closes_bracket()) {
        while blocks.len() > depth {
            blocks.pop();
            out.push(virtual_token(TokenKind::Close, token));
        }
    }
    if !token.kind.closes_bracket() {
        return Ok(());
    }
    let Some((open, _)) = brackets.pop() else {
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

/// Кончился ли `of` не начавшись: следующая лексема левее или на колонке
/// объемлющего блока.
///
/// Мелкий отступ после `of` значит не ошибку, а **нуль ветвей**: разбор без них
/// и есть доказательство необитаемости, и `absurd` пишется только им (§9 Фаза
/// 1, сверка 2026-09-08). Блок тогда не открывается вовсе, и дальше всё идёт
/// обычным путём - тем же, каким идёт токен после закрытой формы. Закрывать
/// блоки здесь самому нельзя: виртуальные `Close` встают мимо, и парсер
/// жалуется на конец блока (проверено).
///
/// Прочие ключевые слова правила не касаются: `f =` без тела остаётся ошибкой.
fn branchless(pending: Option<Pending>, token: &Token, blocks: &[Block]) -> bool {
    let Some(Pending::Body(keyword)) = pending else {
        return false;
    };
    keyword.kind == TokenKind::Of
        && blocks
            .last()
            .is_some_and(|enclosing| token.column <= enclosing.column)
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
        // §10 вопрос 55: под скобкой работают `let` и `where`, прочие
        // открывашки выключены - и это видно сразу, а не в парсере, которому
        // достался бы поток без границ.
        //
        // `of` там требовал бы разделителей, которых внутри скобок нет.
        assert!(matches!(
            run("f = (case x of A -> 1)"),
            Err(LayoutError::BlockInBrackets { .. })
        ));
        // А лямбда с телом-цепочкой пишется: блок открывает стрелка, закрывает
        // парная скобка (§10 вопрос 61).
        assert_eq!(
            shape("f = map xs (\\x ->\n  let y = f x\n  g y)"),
            "{| f = map xs ( \\ x -> {| let {| y = f x |} ; g y |} ) |}"
        );
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
