//! Семантические токены: подсветка от настоящего разбора (§7.2).
//!
//! # Почему не грамматика
//!
//! Обычный путь к подсветке - вторая грамматика на язык: `TextMate` для VS
//! Code, tree-sitter для Neovim. Она работает без сервера и на сломанном
//! файле, но это второй разбор, и разъезжается он молча.
//!
//! Замер говорит, что покупать за это нечего. Оба обещания грамматики отдаёт
//! **лексер компилятора**, и отдаёт их на тех же данных: по всему корпусу (235
//! фикстур) взято 453 391 состояние набора, то есть каждый префикс по границе
//! знака, и [`adamas_parser::lexer::lex`] разобрал 453 386 из них - 99,999%.
//! Всех отказов пять, все они суть незакрытый `{-` в одной фикстуре, и на них
//! работает откат ниже. Разбор целиком держится на 72% тех же состояний:
//! значит слой лексики видно всегда, а слой дерева - в трёх случаях из
//! четырёх.
//!
//! Цена решения названа и не нулевая: до старта сервера подсветки нет вовсе, а
//! на неразобранном файле имена остаются без цвета - ключевые слова,
//! комментарии, строки и числа при этом на месте.
//!
//! # Два слоя
//!
//! **Лексика** ([`Slot`]) - то, что видно без дерева: ключевые слова,
//! комментарии, литералы, операторы. Разъехаться ей не с чем: [`Slot::of`] -
//! исчерпывающий `match` по [`TokenKind`], и новое ключевое слово языка не
//! соберётся, пока ему не назначен вид.
//!
//! **Дерево** ([`Names`]) - то, чего лексема о себе не знает: имя определения
//! против имени типа, конструктор против связывания, поле записи, метка
//! эффекта. Имена ищутся тем же порядком, каким их ищет элаборация
//! (`adamas-elab/src/expr.rs`, `Elab::name`): локальное связывание, сорт,
//! объявление файла, примитив.
//!
//! # Чего слой дерева не решает
//!
//! Имя, не объявленное в файле и не занятое языком, остаётся без цвета.
//! С волны 2 Фазы 9 это уже ограничение **сервера**, а не языка: `import`
//! подключает чужой файл (§4.8), но буфер сервер разбирает по одному, и того
//! файла не видит. Открытые имена поэтому красятся как ссылки, а объявлены они
//! там, куда сервер не ходит. Связать буферы - трек B той же волны.

use std::collections::HashMap;

use adamas_core::prim::{self, Prim, PrimTy};
use adamas_core::source::{SourceFile, Span};
use adamas_parser::ast::{
    Alt, Binder, Block, ClassDecl, Clause, Decl, DeclKind, EffectLabel, Expr, ExprKind,
    HandlerBranch, LamParam, LamParamKind, Module, ModuleDecl, Name, Pattern, PatternKind, Stmt,
    StmtKind, Symbol,
};
use adamas_parser::token::{TokenKind, Tokens};
use lsp_types::{SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokensLegend};

use crate::position::{self, Encoding};

/// Вид подсветки.
///
/// Перечень - те имена протокола, у которых есть смысл в этом языке. Своих
/// имён не заводится: клиент раскрашивает по легенде, а незнакомый вид тема
/// оставит без цвета.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Face {
    /// Ключевое слово.
    Keyword,
    /// Комментарий.
    Comment,
    /// Строковый литерал.
    Str,
    /// Числовой литерал.
    Number,
    /// Оператор и знаки, которые язык читает как знаки.
    Operator,
    /// Определение: сигнатура, клауза, метод, операция эффекта.
    Function,
    /// Тип: семейство, алиас, ресурс, примитив, сорт `Type`.
    Type,
    /// Конструктор семейства.
    Constructor,
    /// Метка эффекта и сорт `Effect`.
    Effect,
    /// Класс (§3.5).
    Class,
    /// Модуль (§4.8).
    Namespace,
    /// Связывание: параметр, переменная паттерна, хвост row.
    Parameter,
    /// Локальное значение `let` и именованный инстанс.
    Variable,
    /// Поле записи (§4.2).
    Property,
    /// Атрибут определения: `@total` и прочие (§4.7).
    Attribute,
}

/// Виды в порядке легенды: индекс в ответе указывает в этот список.
///
/// Список и [`Face::index`] - прямая и обратная таблицы одного соответствия,
/// как [`adamas_parser::token::keyword`] и `spelling`. Что они согласованы,
/// проверяет тест `faces_index_themselves`.
const FACES: &[Face] = &[
    Face::Keyword,
    Face::Comment,
    Face::Str,
    Face::Number,
    Face::Operator,
    Face::Function,
    Face::Type,
    Face::Constructor,
    Face::Effect,
    Face::Class,
    Face::Namespace,
    Face::Parameter,
    Face::Variable,
    Face::Property,
    Face::Attribute,
];

/// Признак «здесь имя объявлено», бит 0 в наборе признаков.
const DECLARATION: u32 = 1;

impl Face {
    /// Индекс в легенде.
    #[must_use]
    pub fn index(self) -> u32 {
        match self {
            Self::Keyword => 0,
            Self::Comment => 1,
            Self::Str => 2,
            Self::Number => 3,
            Self::Operator => 4,
            Self::Function => 5,
            Self::Type => 6,
            Self::Constructor => 7,
            Self::Effect => 8,
            Self::Class => 9,
            Self::Namespace => 10,
            Self::Parameter => 11,
            Self::Variable => 12,
            Self::Property => 13,
            Self::Attribute => 14,
        }
    }

    /// Имя вида в протоколе.
    #[must_use]
    pub fn kind(self) -> SemanticTokenType {
        match self {
            Self::Keyword => SemanticTokenType::KEYWORD,
            Self::Comment => SemanticTokenType::COMMENT,
            Self::Str => SemanticTokenType::STRING,
            Self::Number => SemanticTokenType::NUMBER,
            Self::Operator => SemanticTokenType::OPERATOR,
            Self::Function => SemanticTokenType::FUNCTION,
            Self::Type => SemanticTokenType::TYPE,
            Self::Constructor => SemanticTokenType::ENUM_MEMBER,
            Self::Effect => SemanticTokenType::INTERFACE,
            Self::Class => SemanticTokenType::CLASS,
            Self::Namespace => SemanticTokenType::NAMESPACE,
            Self::Parameter => SemanticTokenType::PARAMETER,
            Self::Variable => SemanticTokenType::VARIABLE,
            Self::Property => SemanticTokenType::PROPERTY,
            Self::Attribute => SemanticTokenType::DECORATOR,
        }
    }
}

/// Легенда: чем сервер красит и какие признаки объявляет.
#[must_use]
pub fn legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: FACES.iter().map(|face| face.kind()).collect(),
        token_modifiers: vec![SemanticTokenModifier::DECLARATION],
    }
}

/// Что лексема знает о себе сама.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Slot {
    /// Вид известен из самой лексемы.
    Face(Face),
    /// Имя: вид решает дерево, а без дерева цвета нет.
    Named,
    /// Красить нечего: пунктуация, границы блоков, конец файла.
    Bare,
}

impl Slot {
    /// Исчерпывающий `match`: новое ключевое слово языка не соберётся, пока
    /// ему не назначен вид. Это и есть то, чем подсветка удерживается от
    /// расхождения с языком - не внимательность, а тип.
    fn of(kind: TokenKind) -> Self {
        match kind {
            TokenKind::Ident => Self::Named,
            TokenKind::Nat | TokenKind::Float => Self::Face(Face::Number),
            TokenKind::Str => Self::Face(Face::Str),

            TokenKind::Data
            | TokenKind::Where
            | TokenKind::Let
            | TokenKind::Case
            | TokenKind::Of
            | TokenKind::If
            | TokenKind::Then
            | TokenKind::Else
            | TokenKind::Resource
            | TokenKind::Unique
            | TokenKind::Unsafe
            | TokenKind::Effect
            | TokenKind::Handle
            | TokenKind::HandleMulti
            | TokenKind::Mask
            | TokenKind::With
            | TokenKind::Class
            | TokenKind::Instance
            | TokenKind::When
            | TokenKind::Module
            | TokenKind::Type
            | TokenKind::Mutual
            | TokenKind::Using
            | TokenKind::Import
            | TokenKind::Extern
            | TokenKind::Export
            | TokenKind::Coherent
            | TokenKind::Infix
            | TokenKind::Infixl
            | TokenKind::Infixr => Self::Face(Face::Keyword),

            TokenKind::Operator
            | TokenKind::Arrow
            | TokenKind::FatArrow
            | TokenKind::Equals
            | TokenKind::Colon
            | TokenKind::Seal
            | TokenKind::Pipe
            | TokenKind::Backslash
            | TokenKind::At => Self::Face(Face::Operator),

            // Скобки, запятая и `_` красит сама тема редактора: цвет у них
            // общий с любым другим языком, и объявлять его здесь значило бы
            // спорить с темой.
            TokenKind::Comma
            | TokenKind::Underscore
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::LBrace
            | TokenKind::RBrace
            | TokenKind::Open
            | TokenKind::Sep
            | TokenKind::Close
            | TokenKind::Eof => Self::Bare,
        }
    }
}

/// Кусок текста со своим видом.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Piece {
    /// Где.
    span: Span,
    /// Чем красить.
    face: Face,
    /// Признаки: сегодня один - [`DECLARATION`].
    modifiers: u32,
}

/// Семантические токены файла в виде протокола.
///
/// `module` - дерево из [`adamas_elab::analyze`]; `None` значит, что файл не
/// разобрался, и тогда отдаётся один слой лексики.
#[must_use]
pub fn tokens(
    file: &SourceFile,
    module: Option<&Module>,
    encoding: Encoding,
) -> Vec<SemanticToken> {
    encode(file, &paint(file.text(), module), encoding)
}

/// Оба слоя в один упорядоченный список кусков.
fn paint(text: &str, module: Option<&Module>) -> Vec<Piece> {
    let (lexed, tail) = lexical(text);
    let named = module.map_or_else(HashMap::new, |module| {
        Names::of(text, &lexed.tokens, module)
    });
    let mut pieces: Vec<Piece> = Vec::with_capacity(lexed.tokens.len() + lexed.comments.len());
    // Имя дерева бывает длиннее лексемы: `Boxes.Wrap` - три лексемы и одно имя
    // (§4.8). Поглощённые им лексемы своих кусков не дают: перекрывающиеся
    // токены протокол запрещает.
    let mut swallowed = 0usize;
    for token in &lexed.tokens {
        if token.span.start() < swallowed {
            continue;
        }
        match Slot::of(token.kind) {
            Slot::Face(face) => pieces.push(Piece {
                span: token.span,
                face,
                modifiers: 0,
            }),
            Slot::Named => {
                if let Some(&(face, modifiers, end)) = named.get(&token.span.start()) {
                    swallowed = end.max(token.span.end());
                    pieces.push(Piece {
                        span: Span::new(token.span.start(), swallowed),
                        face,
                        modifiers,
                    });
                }
            }
            Slot::Bare => {}
        }
    }
    pieces.extend(lexed.comments.iter().map(|comment| Piece {
        span: comment.span,
        face: Face::Comment,
        modifiers: 0,
    }));
    pieces.extend(tail);
    pieces.sort_by_key(|piece| piece.span.start());
    pieces
}

/// Лексика с восстановлением плюс кусок, на котором лексер остановился.
///
/// Отказ лексики - обычное состояние набора, а не поломка: у всякой строки
/// есть момент, когда напечатана первая кавычка. Слева от места отказа текст
/// цел по построению - лексер идёт слева направо, - поэтому он лексится
/// повторно, а само незакрытое место красится тем, чем начато.
fn lexical(text: &str) -> (Tokens, Option<Piece>) {
    let error = match adamas_parser::lexer::lex(text) {
        Ok(lexed) => return (lexed, None),
        Err(error) => error,
    };
    let at = error.span().start();
    let lexed = text
        .get(..at)
        .and_then(|prefix| adamas_parser::lexer::lex(prefix).ok())
        .unwrap_or_default();
    let tail = match error {
        adamas_parser::lexer::LexError::UnterminatedComment { open } => Some(Piece {
            // Незакрытый `{-` съедает остаток файла, и это ровно то, что видит
            // лексер: пока пара не напечатана, комментарий и есть весь хвост.
            span: Span::new(open.start(), text.len()),
            face: Face::Comment,
            modifiers: 0,
        }),
        adamas_parser::lexer::LexError::UnterminatedString { span }
        | adamas_parser::lexer::LexError::UnknownEscape { span } => Some(Piece {
            span,
            face: Face::Str,
            modifiers: 0,
        }),
        adamas_parser::lexer::LexError::UnexpectedChar { .. }
        | adamas_parser::lexer::LexError::TabInIndentation { .. } => None,
    };
    (lexed, tail)
}

/// Куски в дельты протокола.
///
/// Считается всё в кодовых единицах договорённой кодировки - и колонка, и
/// длина, - а сама дельта берётся от предыдущего куска. Отсюда вторая жизнь у
/// ловушки перевода позиций: разность двух колонок, посчитанных байтами,
/// отличается от разности тех же колонок в UTF-16 ровно тогда, когда между
/// кусками стоит неASCII-текст.
fn encode(file: &SourceFile, pieces: &[Piece], encoding: Encoding) -> Vec<SemanticToken> {
    let mut out = Vec::with_capacity(pieces.len());
    let (mut line, mut start) = (0u32, 0u32);
    for piece in pieces {
        // Токен протокола не переходит на другую строку: так велит
        // спецификация, и блочный комментарий отдаётся построчно.
        for span in per_line(file.text(), piece.span) {
            let (Some(at), Some(text)) = (
                position::position(file, span.start(), encoding),
                file.text().get(span.start()..span.end()),
            ) else {
                continue;
            };
            let length = u32::try_from(encoding.units(text)).unwrap_or(u32::MAX);
            let delta_line = at.line.saturating_sub(line);
            out.push(SemanticToken {
                delta_line,
                delta_start: if delta_line == 0 {
                    at.character.saturating_sub(start)
                } else {
                    at.character
                },
                length,
                token_type: piece.face.index(),
                token_modifiers_bitset: piece.modifiers,
            });
            line = at.line;
            start = at.character;
        }
    }
    out
}

/// Спан по строкам, без переводов строки.
fn per_line(text: &str, span: Span) -> Vec<Span> {
    let Some(body) = text.get(span.start()..span.end()) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut at = span.start();
    for chunk in body.split_inclusive('\n') {
        let end = at + chunk.trim_end_matches(['\r', '\n']).len();
        if end > at {
            out.push(Span::new(at, end));
        }
        at += chunk.len();
    }
    out
}

/// Разметка имён по дереву.
///
/// Порядок поиска тот же, каким имя ищет элаборация: локальное связывание,
/// сорт, объявление файла, примитив. Второй копией знания это не является -
/// объявление говорит о себе само, а совпасть с элаборацией разметке нужно
/// только в цвете.
#[derive(Debug)]
struct Names<'a> {
    /// Исходник и его лексемы: нужны формам, чьё слово в дерево не попадает.
    source: &'a str,
    /// Лексемы в порядке появления.
    lexed: &'a [adamas_parser::token::Token],
    /// Имена, объявленные в файле, и чем они объявлены.
    globals: HashMap<Symbol, Face>,
    /// Стек связываний; ближайшее побеждает.
    locals: Vec<(Symbol, Face)>,
    /// Идёт ли обход по написанному типу.
    ///
    /// В типе свободное строчное имя - не ошибка, а **связывание**: §4.1
    /// поднимает его в имплицит-параметр, и `map : (a -> b) -> …` не пишет `a`
    /// нигде больше. В теле такое же имя есть отказ, и цвета ему не
    /// полагается.
    in_type: bool,
    /// Что вышло: смещение начала имени -> вид, признаки и конец имени.
    found: HashMap<usize, (Face, u32, usize)>,
}

impl<'a> Names<'a> {
    /// Разметка всего дерева.
    fn of(
        source: &'a str,
        lexed: &'a [adamas_parser::token::Token],
        module: &Module,
    ) -> HashMap<usize, (Face, u32, usize)> {
        let mut names = Self {
            source,
            lexed,
            globals: HashMap::new(),
            locals: Vec::new(),
            in_type: false,
            found: HashMap::new(),
        };
        names.collect(&module.decls);
        names.decls(&module.decls);
        names.found
    }

    /// Слово формы, стоящее прямо перед этим местом.
    ///
    /// Нужно тем формам, чьё слово в дерево не попадает: у члена `state s0`
    /// узла нет, а есть только начальное значение.
    fn word_before(&self, at: usize, text: &str) -> Option<Span> {
        let next = self.lexed.partition_point(|token| token.span.end() <= at);
        let token = self.lexed.get(next.checked_sub(1)?)?;
        (token.kind == TokenKind::Ident && token.text(self.source) == text).then_some(token.span)
    }

    /// Имя в этом месте выглядит так.
    fn mark(&mut self, span: Span, face: Face, modifiers: u32) {
        self.found
            .insert(span.start(), (face, modifiers, span.end()));
    }

    /// Связывание: помечает место объявления и вводит имя в область видимости.
    fn bind(&mut self, name: &Name, face: Face) {
        self.mark(name.span, face, DECLARATION);
        self.locals.push((Symbol::clone(&name.text), face));
    }

    /// Чем окажется написанное имя.
    fn lookup(&self, text: &str) -> Option<Face> {
        if let Some((_, face)) = self.locals.iter().rev().find(|(it, _)| &**it == text) {
            return Some(*face);
        }
        // Сорта заслоняются связыванием, но не объявлением - тем же правилом,
        // каким их берёт элаборация.
        if text == prim::TYPE || text == adamas_elab::GRADE || text == adamas_elab::UNIT {
            return Some(Face::Type);
        }
        if text == prim::EFFECT {
            return Some(Face::Effect);
        }
        if let Some(&face) = self.globals.get(text) {
            return Some(face);
        }
        if PrimTy::named(text).is_some() {
            return Some(Face::Type);
        }
        Prim::taken(text).then_some(Face::Function)
    }

    /// Написанное имя - не объявление.
    ///
    /// Не нашлось ничего, а имя строчное и стоит в типе - это поднятый
    /// имплицит (§4.1), то есть связывание. Заглавное в том же месте - ссылка
    /// на неизвестное, и цвета у неё нет: незнакомое имя и выглядеть должно
    /// незнакомым.
    fn used(&mut self, name: &Name) {
        let face = self.lookup(&name.text).or_else(|| {
            (self.in_type && !adamas_elab::is_reference(&name.text)).then_some(Face::Parameter)
        });
        if let Some(face) = face {
            self.mark(name.span, face, 0);
        }
    }

    /// Обход написанного типа: см. [`Names::in_type`].
    fn typed(&mut self, expr: &Expr) {
        let outer = std::mem::replace(&mut self.in_type, true);
        self.expr(expr);
        self.in_type = outer;
    }

    /// Первый проход: что в файле объявлено.
    fn collect(&mut self, decls: &[Decl]) {
        for decl in decls {
            match &decl.kind {
                DeclKind::Alias { name, .. } => self.declare(name, Face::Type),
                DeclKind::Signature { name, .. } | DeclKind::Clauses { name, .. } => {
                    self.declare(name, Face::Function);
                }
                DeclKind::Extern(declared) => self.declare(&declared.name, Face::Function),
                DeclKind::Data(data) => {
                    self.declare(&data.name, Face::Type);
                    for constructor in &data.constructors {
                        self.declare(&constructor.name, Face::Constructor);
                    }
                }
                DeclKind::Module(module) => {
                    self.declare(&module.name, Face::Namespace);
                    self.collect(&module.members);
                }
                DeclKind::Class(class) => {
                    if let (false, Some(name)) = (class.instance, head_name(&class.head)) {
                        self.declare(name, Face::Class);
                    }
                    if let Some(name) = &class.name {
                        self.declare(name, Face::Variable);
                    }
                    self.collect(&class.members);
                }
                DeclKind::Mutual(members) => self.collect(members),
                DeclKind::Resource(resource) => {
                    self.declare(&resource.name, Face::Type);
                    self.collect(&resource.members);
                }
                DeclKind::Effect(effect) => {
                    self.declare(&effect.name, Face::Effect);
                    for operation in &effect.operations {
                        self.declare(&operation.name, Face::Function);
                    }
                }
                // Открытое имя объявлено не здесь, а в подключённом файле;
                // подсветка одного буфера туда не ходит, и покрасить его
                // объявлением значило бы соврать про место. Экспорт имени не
                // объявляет вовсе: имя ему даёт определение выше.
                DeclKind::Fixity(_) | DeclKind::Import(_) | DeclKind::Export(_) => {}
            }
        }
    }

    fn declare(&mut self, name: &Name, face: Face) {
        self.globals.insert(Symbol::clone(&name.text), face);
    }

    /// Второй проход: сами объявления.
    fn decls(&mut self, decls: &[Decl]) {
        for decl in decls {
            self.decl(decl);
        }
    }

    fn decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Alias { name, params, body } => {
                self.mark(name.span, Face::Type, DECLARATION);
                let scope = self.locals.len();
                self.typed_binders(params);
                if let Some(body) = body {
                    self.typed(body);
                }
                self.locals.truncate(scope);
            }
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                for attribute in attributes {
                    self.mark(attribute.span, Face::Attribute, 0);
                }
                self.mark(name.span, Face::Function, DECLARATION);
                let scope = self.locals.len();
                self.typed(ty);
                self.locals.truncate(scope);
            }
            DeclKind::Extern(declared) => {
                for attribute in &declared.attributes {
                    self.mark(attribute.span, Face::Attribute, 0);
                }
                self.mark(declared.name.span, Face::Function, DECLARATION);
                let scope = self.locals.len();
                self.typed(&declared.ty);
                self.locals.truncate(scope);
            }
            DeclKind::Export(exported) => self.mark(exported.name.span, Face::Function, 0),
            DeclKind::Clauses { clauses, .. } => {
                for clause in clauses {
                    self.clause(clause);
                }
            }
            DeclKind::Data(data) => {
                self.mark(data.name.span, Face::Type, DECLARATION);
                let scope = self.locals.len();
                self.typed_binders(&data.params);
                if let Some(kind) = &data.kind {
                    self.typed(kind);
                }
                for constructor in &data.constructors {
                    self.mark(constructor.name.span, Face::Constructor, DECLARATION);
                    self.typed(&constructor.ty);
                }
                self.locals.truncate(scope);
            }
            DeclKind::Module(module) => self.module(module),
            DeclKind::Class(class) => self.class(class),
            DeclKind::Mutual(members) => self.decls(members),
            DeclKind::Resource(resource) => {
                self.mark(resource.name.span, Face::Type, DECLARATION);
                let scope = self.locals.len();
                self.typed_binders(&resource.params);
                self.decls(&resource.members);
                self.locals.truncate(scope);
            }
            DeclKind::Effect(effect) => {
                self.mark(effect.name.span, Face::Effect, DECLARATION);
                let scope = self.locals.len();
                self.typed_binders(&effect.params);
                for operation in &effect.operations {
                    self.mark(operation.name.span, Face::Function, DECLARATION);
                    self.typed(&operation.ty);
                }
                self.locals.truncate(scope);
            }
            DeclKind::Fixity(fixity) => {
                for operator in &fixity.operators {
                    self.mark(operator.span, Face::Operator, DECLARATION);
                }
            }
            // Путь - пространство имён, открытое имя - ссылка на чужой член:
            // объявления здесь нет ни одного.
            DeclKind::Import(import) => {
                for segment in &import.path {
                    self.mark(segment.span, Face::Namespace, 0);
                }
                if let Some(alias) = &import.alias {
                    self.mark(alias.span, Face::Namespace, DECLARATION);
                }
                for opened in &import.open {
                    self.mark(opened.span, Face::Function, 0);
                }
            }
        }
    }

    fn module(&mut self, module: &ModuleDecl) {
        self.mark(module.name.span, Face::Namespace, DECLARATION);
        let scope = self.locals.len();
        self.binders(&module.params);
        if let Some(ascription) = &module.ascription {
            self.typed(ascription);
        }
        if let Some(body) = &module.body {
            self.expr(body);
        }
        self.decls(&module.members);
        self.locals.truncate(scope);
    }

    fn class(&mut self, class: &ClassDecl) {
        let scope = self.locals.len();
        if let Some(name) = &class.name {
            self.mark(name.span, Face::Variable, DECLARATION);
        }
        if class.instance {
            // У инстанса голова написана целиком (`Ord Int`), и всё в ней -
            // обычные вхождения имён.
            self.typed(&class.head);
        } else if let Some(name) = head_name(&class.head) {
            self.mark(name.span, Face::Class, DECLARATION);
        }
        self.typed_binders(&class.params);
        for superclass in &class.superclasses {
            self.typed(superclass);
        }
        self.decls(&class.members);
        self.locals.truncate(scope);
    }

    /// Клауза: имя, паттерны, тело и локальные определения.
    fn clause(&mut self, clause: &Clause) {
        // Имя клаузы в дереве одно на всю группу, а написано оно над каждой.
        // Спан клаузы начинается ровно на нём, и по этому смещению имя
        // находится в потоке лексем - длину брать неоткуда и не нужно.
        self.found
            .insert(clause.span.start(), (Face::Function, DECLARATION, 0));
        let scope = self.locals.len();
        for pattern in &clause.patterns {
            self.pattern(pattern);
        }
        // Локальные определения видны телу: имена вводятся до обхода.
        self.collect_locals(&clause.wheres);
        self.decls(&clause.wheres);
        self.expr(&clause.body);
        self.locals.truncate(scope);
    }

    /// Имена блока `where` - локальные, а не файловые.
    fn collect_locals(&mut self, decls: &[Decl]) {
        for decl in decls {
            if let DeclKind::Signature { name, .. } | DeclKind::Clauses { name, .. } = &decl.kind {
                self.locals
                    .push((Symbol::clone(&name.text), Face::Function));
            }
        }
    }

    /// Связывания в заголовке объявления: их типы - типы (см.
    /// [`Names::in_type`]).
    fn typed_binders(&mut self, binders: &[Binder]) {
        let outer = std::mem::replace(&mut self.in_type, true);
        self.binders(binders);
        self.in_type = outer;
    }

    fn binders(&mut self, binders: &[Binder]) {
        for binder in binders {
            // Кратность красится как число: `0` и `1` - числа и есть, а `ω`
            // пишется именем, и без этого одна запись из трёх осталась бы
            // другого цвета.
            if let Some(mult) = binder.mult {
                self.mark(mult.span, Face::Number, 0);
            }
            for name in binder.names.iter().chain(&binder.factors) {
                self.bind(name, Face::Parameter);
            }
            if let Some(ty) = &binder.ty {
                self.expr(ty);
            }
            if let Some(default) = &binder.default {
                self.expr(default);
            }
        }
    }

    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            // Заглавное имя разбирает, строчное связывает (§4.1): правило то
            // же и берётся оттуда же, откуда его берёт элаборация.
            PatternKind::Name(name) => {
                if adamas_elab::is_reference(&name.text) {
                    self.mark(name.span, Face::Constructor, 0);
                } else {
                    self.bind(name, Face::Parameter);
                }
            }
            PatternKind::Wildcard | PatternKind::Lit(_) => {}
            PatternKind::App { head, fields } => {
                self.mark(head.span, Face::Constructor, 0);
                for field in fields {
                    self.pattern(field);
                }
            }
            PatternKind::Tuple(items) => {
                for item in items {
                    self.pattern(item);
                }
            }
        }
    }

    fn label(&mut self, label: &EffectLabel) {
        self.mark(label.name.span, Face::Effect, 0);
        for argument in &label.arguments {
            self.expr(argument);
        }
    }

    fn block(&mut self, block: &Block) {
        let scope = self.locals.len();
        for stmt in &block.stmts {
            self.stmt(stmt);
        }
        self.locals.truncate(scope);
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let(bindings) => {
                for binding in bindings {
                    if let Some(mult) = binding.mult {
                        self.mark(mult.span, Face::Number, 0);
                    }
                    // Имя видно своему телу: `let` рекурсивен.
                    self.bind(&binding.name, Face::Variable);
                    let scope = self.locals.len();
                    for param in &binding.params {
                        self.pattern(param);
                    }
                    if let Some(ty) = &binding.ty {
                        self.expr(ty);
                    }
                    self.expr(&binding.body);
                    self.locals.truncate(scope);
                }
            }
            StmtKind::Expr(expr) => self.expr(expr),
        }
    }

    fn alt(&mut self, alt: &Alt) {
        let scope = self.locals.len();
        self.pattern(&alt.pattern);
        self.expr(&alt.body);
        self.locals.truncate(scope);
    }

    /// Ветка хендлера. `stateful` - параметризован ли хендлер: тогда ветка
    /// видит ещё и `state` (§4.1).
    fn branch(&mut self, branch: &HandlerBranch, stateful: bool) {
        self.mark(branch.name.span, Face::Function, 0);
        let scope = self.locals.len();
        for param in &branch.params {
            self.bind(param, Face::Parameter);
        }
        // Резумпцию связывает сама форма (§3.4), в дереве её имени нет вовсе -
        // поэтому и связывается она здесь, а не разметкой написанного.
        self.locals
            .push((Symbol::from(adamas_elab::RESUME), Face::Parameter));
        if stateful {
            self.locals
                .push((Symbol::from(adamas_elab::STATE), Face::Parameter));
        }
        self.expr(&branch.body);
        self.locals.truncate(scope);
    }

    fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => self.used(name),
            ExprKind::Lit(_) | ExprKind::Hole => {}
            ExprKind::App(left, right)
            | ExprKind::TypeApp(left, right)
            | ExprKind::Arrow(left, right) => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Using { name, body } => {
                self.used(name);
                self.expr(body);
            }
            ExprKind::Lam { params, body } => {
                let scope = self.locals.len();
                for param in params {
                    self.lam_param(param);
                }
                self.expr(body);
                self.locals.truncate(scope);
            }
            ExprKind::Pi { binders, codomain } => {
                let scope = self.locals.len();
                self.binders(binders);
                self.expr(codomain);
                self.locals.truncate(scope);
            }
            ExprKind::Effectful { labels, tail, body } => {
                for label in labels {
                    self.label(label);
                }
                if let Some(tail) = tail {
                    self.mark(tail.span, Face::Parameter, 0);
                }
                self.expr(body);
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::Handle {
                label,
                computation,
                state,
                branches,
                ..
            } => self.handler(label.as_deref(), computation, state.as_deref(), branches),
            ExprKind::Mask(inner) => self.expr(inner),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr(cond);
                self.expr(then_branch);
                self.expr(else_branch);
            }
            ExprKind::Case { scrutinee, alts } => {
                self.expr(scrutinee);
                for alt in alts {
                    self.alt(alt);
                }
            }
            ExprKind::RecordType(fields, tail) => {
                for field in fields {
                    self.mark(field.name.span, Face::Property, DECLARATION);
                    self.expr(&field.ty);
                }
                if let Some(tail) = tail {
                    self.mark(tail.span, Face::Parameter, 0);
                }
            }
            ExprKind::Record(fields) => self.fields(fields),
            ExprKind::Project(inner, name) => {
                self.expr(inner);
                self.mark(name.span, Face::Property, 0);
            }
            ExprKind::Update(base, fields) => {
                self.expr(base);
                self.fields(fields);
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Chain(chain) => {
                self.expr(&chain.head);
                for (_, operand) in &chain.tail {
                    // Сам оператор уже покрашен лексером: символьная лексема
                    // без дерева читается однозначно.
                    self.expr(operand);
                }
            }
        }
    }

    /// Хендлер: метка, состояние, вычисление и ветки (§3.4).
    fn handler(
        &mut self,
        label: Option<&EffectLabel>,
        computation: &Expr,
        state: Option<&Expr>,
        branches: &[HandlerBranch],
    ) {
        if let Some(label) = label {
            self.label(label);
        }
        if let Some(state) = state {
            // Слово `state` в дереве не лежит - там только начальное значение,
            // - а ключевым словом оно при этом является: связывание `state` в
            // ветках ставит сама форма (§4.1, §10 вопрос 86).
            if let Some(span) = self.word_before(state.span.start(), adamas_elab::STATE) {
                self.mark(span, Face::Keyword, 0);
            }
            self.expr(state);
        }
        self.expr(computation);
        for branch in branches {
            self.branch(branch, state.is_some());
        }
    }

    /// Поля значения записи: имя поля и то, что в нём написано.
    fn fields(&mut self, fields: &[(Name, Expr)]) {
        for (name, value) in fields {
            self.mark(name.span, Face::Property, 0);
            self.expr(value);
        }
    }

    fn lam_param(&mut self, param: &LamParam) {
        match &param.kind {
            LamParamKind::Pattern(pattern) => self.pattern(pattern),
            LamParamKind::Binder(binder) => self.binders(std::slice::from_ref(binder)),
        }
    }
}

/// Голова применения: `Ord` в `Ord a`.
fn head_name(expr: &Expr) -> Option<&Name> {
    match &expr.kind {
        ExprKind::Name(name) => Some(name),
        ExprKind::App(callee, _) | ExprKind::TypeApp(callee, _) => head_name(callee),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{FACES, legend, tokens};
    use crate::position::Encoding;
    use adamas_core::source::SourceFile;

    /// Токены в читаемом виде: `строка:знак+длина вид признаки`.
    ///
    /// Позиции здесь **абсолютные**, а в ответе они дельты: тест, сверяющий
    /// дельты как есть, сдвинулся бы весь от одной вставленной строки, и
    /// сломанное место в нём было бы не найти.
    fn decoded(text: &str, encoding: Encoding) -> Vec<String> {
        let file = SourceFile::new("t.adamas", text);
        let names = legend().token_types;
        let (mut line, mut start) = (0u32, 0u32);
        let mut out = Vec::new();
        for token in tokens(&file, adamas_parser::parse(text).ok().as_ref(), encoding) {
            line += token.delta_line;
            start = if token.delta_line == 0 {
                start + token.delta_start
            } else {
                token.delta_start
            };
            let modifiers = if token.token_modifiers_bitset == 0 {
                String::new()
            } else {
                format!(" #{}", token.token_modifiers_bitset)
            };
            out.push(format!(
                "{line}:{start}+{} {}{modifiers}",
                token.length,
                names[token.token_type as usize].as_str()
            ));
        }
        out
    }

    /// Прямая и обратная таблицы легенды согласованы: вид стоит на своём
    /// индексе, и индексов ровно столько, сколько видов.
    #[test]
    fn faces_index_themselves() {
        for (index, &face) in FACES.iter().enumerate() {
            assert_eq!(usize::try_from(face.index()), Ok(index), "{face:?}");
        }
        assert_eq!(legend().token_types.len(), FACES.len());
    }

    /// Разные конструкции получают разные виды.
    ///
    /// Смысл теста - именно различение: ответ из одних `variable` был бы
    /// ответом, и проверка «токены пришли» его бы приняла.
    #[test]
    fn different_constructs_get_different_faces() {
        let text = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

double : Nat -> Nat
double Zero = Zero
double n = Succ n
";
        assert_eq!(
            decoded(text, Encoding::Utf16),
            [
                "0:0+4 keyword",
                "0:5+3 type #1",
                "0:9+5 keyword",
                "1:2+4 enumMember #1",
                "1:7+1 operator",
                "1:9+3 type",
                "2:2+4 enumMember #1",
                "2:7+1 operator",
                "2:9+3 type",
                "2:13+2 operator",
                "2:16+3 type",
                "4:0+6 function #1",
                "4:7+1 operator",
                "4:9+3 type",
                "4:13+2 operator",
                "4:16+3 type",
                "5:0+6 function #1",
                "5:7+4 enumMember",
                "5:12+1 operator",
                "5:14+4 enumMember",
                "6:0+6 function #1",
                "6:7+1 parameter #1",
                "6:9+1 operator",
                "6:11+4 enumMember",
                "6:16+1 parameter",
            ]
        );
    }

    /// Дельты за многобайтовым текстом.
    ///
    /// Числа записаны руками. Семантические токены считаются **разностями**
    /// колонок, поэтому неASCII-текст обязан стоять **между** двумя токенами
    /// одной строки: `{- 😀 -}` стоит, и от этого `Succ` начинается на 18-й
    /// единице UTF-16 при 26-м байте, а сам комментарий занимает 8 единиц при
    /// 10 байтах. Форма взята у фикстуры
    /// `tests/golden/errors/position-past-multibyte.adamas`.
    #[test]
    fn deltas_past_multibyte_text_are_written_out() {
        let text = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

двойка = {- 😀 -} Succ Zero Zero
";
        let tail = |encoding| {
            let all = decoded(text, encoding);
            all[all.len() - 6..].to_vec()
        };
        assert_eq!(
            tail(Encoding::Utf16),
            [
                "4:0+6 function #1",
                "4:7+1 operator",
                "4:9+8 comment",
                "4:18+4 enumMember",
                "4:23+4 enumMember",
                "4:28+4 enumMember",
            ]
        );
        assert_eq!(
            tail(Encoding::Utf8),
            [
                "4:0+12 function #1",
                "4:13+1 operator",
                "4:15+10 comment",
                "4:26+4 enumMember",
                "4:31+4 enumMember",
                "4:36+4 enumMember",
            ]
        );
        assert_eq!(
            tail(Encoding::Utf32),
            [
                "4:0+6 function #1",
                "4:7+1 operator",
                "4:9+7 comment",
                "4:17+4 enumMember",
                "4:22+4 enumMember",
                "4:27+4 enumMember",
            ]
        );
    }

    /// Неразобранный файл сохраняет слой лексики и теряет слой имён.
    #[test]
    fn a_broken_file_keeps_the_lexical_layer() {
        // `(` не закрыта: разбора нет, лексика есть.
        let text = "-- вот\nmain = (1\n";
        assert!(
            adamas_parser::parse(text).is_err(),
            "текст обязан не разбираться, иначе тест проверяет не то"
        );
        assert_eq!(
            decoded(text, Encoding::Utf16),
            ["0:0+6 comment", "1:5+1 operator", "1:8+1 number"]
        );
    }

    /// Незакрытый блочный комментарий красится до конца файла - построчно,
    /// потому что токен протокола строку не переходит.
    ///
    /// Имени `f` цвета нет: файл не разбирается вовсе, и слой дерева
    /// отсутствует целиком - ровно то состояние, ради которого держат
    /// грамматику.
    #[test]
    fn an_unterminated_comment_paints_to_the_end() {
        assert_eq!(
            decoded("f = {- ой\nещё\n", Encoding::Utf16),
            ["0:2+1 operator", "0:4+5 comment", "1:0+3 comment"]
        );
    }

    /// Закрытый блочный комментарий тоже идёт по токену на строку.
    #[test]
    fn a_block_comment_is_split_per_line() {
        assert_eq!(
            decoded("{- раз\nдва -}\nf = 1\n", Encoding::Utf16),
            [
                "0:0+6 comment",
                "1:0+6 comment",
                "2:0+1 function #1",
                "2:2+1 operator",
                "2:4+1 number",
            ]
        );
    }

    /// Заглавное имя в паттерне разбирает, строчное связывает (§4.1), и
    /// вхождение строчного видно тем же связыванием.
    #[test]
    fn a_pattern_name_binds_or_matches_by_its_case() {
        let head = "data Nat where\n  Zero : Nat\n\nshadow : Nat -> Nat\n";
        let matched = decoded(&format!("{head}shadow Zero = Zero\n"), Encoding::Utf16);
        assert_eq!(
            matched[matched.len() - 4..],
            [
                "4:0+6 function #1",
                "4:7+4 enumMember",
                "4:12+1 operator",
                "4:14+4 enumMember",
            ]
        );
        let bound = decoded(&format!("{head}shadow zero = zero\n"), Encoding::Utf16);
        assert_eq!(
            bound[bound.len() - 4..],
            [
                "4:0+6 function #1",
                "4:7+4 parameter #1",
                "4:12+1 operator",
                "4:14+4 parameter",
            ],
            "`zero` - связывание, хотя рядом объявлен `Zero`"
        );
    }

    /// Токены идут по возрастанию и не перекрываются: и то и другое требует
    /// протокол, а перекрытие редактор рисует мусором.
    #[test]
    fn tokens_are_ordered_and_disjoint() {
        let text = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/golden/eval/interpreter.adamas"
        ))
        .expect("капстоун Фазы 6 на месте");
        let file = SourceFile::new("interpreter.adamas", text.as_str());
        let module = adamas_parser::parse(&text).expect("капстоун разбирается");
        let mut line = 0u32;
        let mut previous = 0u32;
        let mut count = 0usize;
        for token in tokens(&file, Some(&module), Encoding::Utf16) {
            line += token.delta_line;
            // Дельта считается от начала предыдущего токена: меньше его длины
            // значит они наложились.
            assert!(
                token.delta_line > 0 || token.delta_start >= previous,
                "перекрытие на строке {line}: {} < {previous}",
                token.delta_start
            );
            previous = token.length;
            count += 1;
        }
        assert!(
            count > 3000,
            "токенов на 944 строки подозрительно мало: {count}"
        );
    }
}
