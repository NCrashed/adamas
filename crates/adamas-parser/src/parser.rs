//! Recursive descent по потоку с границами блоков.
//!
//! Рекурсивный спуск, а не генератор (§9 Фаза 2): сообщения об ошибках пишутся
//! в той точке, где известно, чего ждали.
//!
//! # Как читается поток
//!
//! Отступов парсер не видит - их перевёл [`crate::layout`] в
//! [`TokenKind::Open`], [`TokenKind::Sep`] и [`TokenKind::Close`]. Блок читается
//! везде одинаково: `Open` член (`Sep` член)\* `Close`. Пустым бывает только
//! блок файла - за остальными layout следит сам.
//!
//! # Что парсер не решает
//!
//! Ничего, для чего нужны сведения из других объявлений. Имя в паттерне не
//! делится на переменную и конструктор, фикситеты не расставляются, кратность
//! по умолчанию не подставляется - см. заголовок [`crate::ast`]. Отсюда же
//! ограничение: восстановления после ошибки нет, первая ошибка останавливает
//! разбор. Диагностика от этого точнее, а LSP на неполном вводе потребует
//! отдельного прохода - цена названа в decision log 2026-08-25.
//!
//! # Форма с блоком - последняя
//!
//! `case` и блок операторов тянутся до строки, начатой левее, и в скобки не
//! берутся: под скобкой layout выключен (§10 вопрос 55). Поэтому за такой
//! формой на строке ничего не стоит - ни аргумента, ни оператора, ни `of`, -
//! и разбор отвергает `g case … y` с [`ParseError::BlockNotLast`]. Правило
//! языковое (§4.1) и заведено ради печати: дерево, где форма с блоком стоит
//! не последней, не записывается ничем.
//!
//! # Подмножество Фазы 2
//!
//! Разбирается то, что §9 относит к Фазе 2: сигнатуры, клаузы, `data`,
//! `resource`, выражения и паттерны. Классы, инстансы, модули, эффекты и
//! handler'ы - формы Фаз 3-4; их лексемы зарезервированы, и парсер отвечает на
//! них [`ParseError::Unsupported`], а не «ожидалось объявление».
//!
//! Двух форм нет и внутри Фазы 2, потому что §4 их не показывает: определения
//! оператора в инфиксной позиции (`x <> y = …`; в скобках, `(<>) x y = …`,
//! разбирается) и отрицательного литерала в паттерне (`f (-1) = …`). И то и
//! другое - расширение поверхностного языка, а не пробел разбора.
//!
//! # Спаны
//!
//! Спан узла начинается на первой его лексеме и кончается на последней:
//! клауза - вместе с блоком `where`, `data` - по последний конструктор,
//! выражение в скобках - вместе со скобками. Виртуальные границы блока
//! лексемами не считаются: `Close` стоит в позиции токена, который блок
//! закрыл, то есть уже следующего объявления, и спан, кончающийся им, накрыл
//! бы чужой текст.
//!
//! Отсюда два следствия, и оба проверяются (`tests/spans.rs`): спан ребёнка
//! лежит внутри спана родителя, и ни один спан не начинается и не кончается
//! пробелом. Решение - decision log 2026-08-25.

use std::fmt;
use std::rc::Rc;

use adamas_core::source::Span;

use crate::ast::{
    Alt, Binder, Binding, Block, Chain, Clause, Constructor, Data, Decl, DeclKind, Expr, ExprKind,
    LamParam, LamParamKind, Lit, LitKind, Module, ModuleDecl, Mult, MultAnn, Name, Pattern,
    PatternKind, RecordField, Resource, Stmt, StmtKind, Symbol, Visibility, contains_block,
};
use crate::token::{Token, TokenKind};

/// Чего парсер ждал в точке отказа.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expected {
    /// Конкретная лексема.
    Token(TokenKind),
    /// Объявление верхнего уровня.
    Declaration,
    /// Выражение.
    Expression,
    /// Паттерн.
    Pattern,
    /// Имя.
    Name,
}

impl fmt::Display for Expected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Token(kind) => write!(f, "{kind}"),
            Self::Declaration => f.write_str("объявление"),
            Self::Expression => f.write_str("выражение"),
            Self::Pattern => f.write_str("паттерн"),
            Self::Name => f.write_str("имя"),
        }
    }
}

/// Форма языка, до которой Фаза 2 ещё не дошла.
///
/// Отдельный вариант ошибки, а не «ожидалось объявление»: лексема
/// зарезервирована и опечаткой быть не может, поэтому сказать про фазу честнее,
/// чем перечислять, что здесь бывает вместо неё.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unsupported {
    /// `class`, `coherent class`, `when`.
    Class,
    /// `instance`.
    Instance,
    /// `using`.
    NamedInstance,
    /// `module`.
    Module,
    /// `import`.
    Import,
    /// `mutual`.
    Mutual,
    /// `effect`.
    Effect,
    /// `handle`, `handleMulti`, `with`.
    Handler,
    /// `type` - записи.
    Record,
    /// `infix`, `infixl`, `infixr`.
    Fixity,
    /// Фигурные скобки там, где это не группа implicit-связываний.
    Braces,
}

/// Части сообщения о форме следующих фаз.
///
/// Одна таблица на всё: описание и фаза расходиться не должны. Поля именованы,
/// потому что складываются в предложение, и порядок в нём читается только у
/// названных частей.
struct Message {
    /// Что это - во множественном числе: подставляется подлежащим.
    what: &'static str,
    /// В какой фазе появится - в предложном падеже, после «появляются в».
    phase: &'static str,
    /// Что написать вместо, если лексема бывает и законной.
    hint: Option<&'static str>,
}

impl Unsupported {
    fn message(self) -> Message {
        let form = |what, phase| Message {
            what,
            phase,
            hint: None,
        };
        match self {
            Self::Class => form("классы (§4.1)", "Фазе 3"),
            Self::Instance => form("инстансы (§4.1)", "Фазе 3"),
            Self::NamedInstance => form("именованные инстансы (§4.1)", "Фазе 3"),
            Self::Module => form("модули (§4.8)", "Фазе 3"),
            Self::Import => form("импорты (§4.8)", "Фазе 3"),
            Self::Mutual => form("блоки `mutual` (§4.8)", "Фазе 3"),
            Self::Effect => form("объявления эффектов (§3.4)", "Фазе 4"),
            Self::Handler => form("handler'ы (§3.4)", "Фазе 4"),
            Self::Record => form("записи (§4.2)", "одной из следующих фаз"),
            Self::Fixity => form("объявления фикситетов (§4.4)", "фазе с prelude"),
            Self::Braces => Message {
                what: "записи (§4.2) и effect row (§3.4)",
                phase: "одной из следующих фаз",
                hint: Some("группа implicit-связываний пишется `{a : Type}`"),
            },
        }
    }
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Message { what, phase, hint } = self.message();
        write!(f, "{what} появляются в {phase}")?;
        match hint {
            Some(hint) => write!(f, "; {hint}"),
            None => Ok(()),
        }
    }
}

/// Ошибка разбора.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ParseError {
    /// `{}` - ни тип, ни значение.
    #[error("пустая запись: `{{}}` не различает тип и значение")]
    EmptyRecord {
        /// Где написано.
        span: Span,
    },

    /// В одной записи и объявления полей, и присваивания.
    #[error("запись либо объявляет поля, либо присваивает им значения")]
    MixedRecord {
        /// Поле, на котором форма сменилась.
        span: Span,
    },

    /// Не та лексема.
    ///
    /// Настоящее время, а не прошедшее: `expected` и `found` - существительные
    /// всех трёх родов («идентификатор», «граница блока», «имя»), и с
    /// «ожидалось» согласуется только среднее.
    #[error("ожидается {expected}, а не {found}")]
    Expected {
        /// Чего ждали.
        expected: Expected,
        /// Что нашли.
        found: TokenKind,
        /// Где.
        span: Span,
    },

    /// Кратность записана не 0, 1 и не ω.
    ///
    /// Полукольцо §3.2 состоит ровно из трёх элементов, поэтому это не
    /// «неизвестное число», а исчерпывающий список.
    #[error("кратность записывается `0`, `1` или `ω`")]
    Multiplicity {
        /// Что написано вместо кратности.
        span: Span,
    },

    /// Клаузы одного определения разделены другим объявлением.
    ///
    /// Порядок клауз значим - побеждает первая совпавшая (§9 Фаза 1), - поэтому
    /// собирать разнесённые по файлу куски молча нельзя.
    #[error("клаузы `{name}` разделены другим объявлением")]
    SplitClauses {
        /// Имя определения.
        name: Symbol,
        /// Где группа началась.
        first: Span,
        /// Где она продолжена.
        again: Span,
    },

    /// Форма языка из следующих фаз.
    #[error("{what}")]
    Unsupported {
        /// Какая.
        what: Unsupported,
        /// Где.
        span: Span,
    },

    /// За формой с блоком на строке ещё что-то стоит.
    ///
    /// `case` и блок операторов тянутся до строки, начатой левее: где форма
    /// кончилась, видно только по отступу ([`crate::ast::contains_block`]).
    /// Взять её в скобки нельзя - под скобкой layout выключен (§10 вопрос
    /// 55), - поэтому дерево, где за ней стоит аргумент, оператор или `of`,
    /// не записывается ничем. Отвергает его разбор, а не печать позже и молча.
    #[error(
        "после формы с блоком на строке ничего не пишется: где она кончается, видно только по отступу"
    )]
    BlockNotLast {
        /// Где форма с блоком.
        form: Span,
        /// Что стоит за ней.
        next: Span,
    },

    /// Вложенность глубже предела.
    ///
    /// Меряется дважды и с разных сторон. Спуск рекурсивен, поэтому глубина
    /// **записи** - это глубина стека, и без предела достаточно тысячи скобок,
    /// чтобы компилятор упал вместо сообщения; урок Фазы 0
    /// (`adamas-warmup-stlc`), перенесённый сюда. А глубина **терма**, который
    /// из записи получится, - глубина стека всякого, кто по нему пойдёт, и она
    /// с первой не совпадает: её меряет [`crate::depth`] отдельным проходом
    /// (§10 вопрос 62).
    #[error("вложенность глубже предела в {limit}")]
    TooDeep {
        /// Предел.
        limit: u32,
        /// Где кончилось терпение.
        span: Span,
    },
}

impl ParseError {
    /// Где ошибка.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::EmptyRecord { span }
            | Self::MixedRecord { span }
            | Self::Expected { span, .. }
            | Self::Multiplicity { span }
            | Self::SplitClauses { again: span, .. }
            | Self::Unsupported { span, .. }
            | Self::BlockNotLast { next: span, .. }
            | Self::TooDeep { span, .. } => *span,
        }
    }
}

/// Разбирает файл.
///
/// `tokens` - поток с границами блоков, то есть выход [`crate::tokenize`], а не
/// голого лексера.
///
/// # Errors
///
/// Любое несовпадение с грамматикой §4, форма из следующих фаз, разнесённые
/// клаузы.
///
/// # Panics
///
/// В debug-сборке - если поток не заканчивается `Eof`.
pub fn parse(text: &str, tokens: &[Token]) -> Result<Module, ParseError> {
    debug_assert_eq!(
        tokens.last().map(|token| token.kind),
        Some(TokenKind::Eof),
        "парсер ждёт поток целиком, вместе с Eof"
    );
    let module = Parser::new(text, tokens).module()?;
    // Вторая мера: глубина не записи, а терма, который из неё получится. См.
    // заголовок [`crate::depth`] - почему это не одно и то же и почему проход
    // отдельный.
    crate::depth::bounded(&module)?;
    Ok(module)
}

/// Предел вложенности - один на обе меры.
///
/// **Для спуска** считает не уровни исходника, а входы в [`Parser::nested`]:
/// скобка стоит двух (`atom`, затем `expr`), стрелка, лямбда, `if`, `case`,
/// блок и вложенное объявление - по одному. Через один из этих входов проходит
/// каждый цикл рекурсии, поэтому предел ограничивает стек разбора целиком.
///
/// **Для терма** считает звенья, которые встанут одно под другим:
/// [`crate::depth`]. Мера другая - `f a b c` стоит одного входа и даёт три
/// звена, `(((x)))` стоит шести входов и не даёт ни одного, - а предел общий,
/// потому что для автора обе означают одно: написано слишком глубоко.
///
/// Значение то же, что в warm-up'е Фазы 0: 256 - это больше сотни вложенных
/// скобок, чего в написанном человеком коде не бывает, и заведомо меньше
/// глубины, на которой кончается стек. Замер: в debug `check` срывается между
/// 1000 и 1300 звеньями, смотря какими; предел взят впятеро меньшим - стек на
/// кадр зависит от того, что на нём уже лежит.
///
/// Цена названа: ни спайна, ни блока, ни группы связываний длиннее 256 не
/// напишет и сгенерированный код. Если упрётся, снимать предел не нужно -
/// достаточно сделать потребителей итеративными, а их сегодня большинство
/// рекурсивные (`infer_app` и `eval` в ядре, будущий codegen, наконец `Drop` у
/// самой цепочки `Rc`).
pub(crate) const MAX_DEPTH: u32 = 256;

/// Состояние разбора: поток, позиция в нём и глубина спуска.
struct Parser<'a> {
    text: &'a str,
    tokens: &'a [Token],
    index: usize,
    depth: u32,
}

impl<'a> Parser<'a> {
    fn new(text: &'a str, tokens: &'a [Token]) -> Self {
        Self {
            text,
            tokens,
            index: 0,
            depth: 0,
        }
    }

    /// Спускается на уровень глубже.
    fn nested<T>(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        if self.depth == MAX_DEPTH {
            return Err(ParseError::TooDeep {
                limit: MAX_DEPTH,
                span: self.peek().span,
            });
        }
        self.depth += 1;
        let parsed = parse(self);
        self.depth -= 1;
        parsed
    }

    // --- поток -----------------------------------------------------------

    /// Текущая лексема.
    ///
    /// За краем потока - `Eof` из воздуха, а не паника и не последний токен:
    /// `parse` публична, договор про завершающий `Eof` держит только
    /// `debug_assert`, а цикл, который ждёт `Eof`, обязан остановиться и на
    /// потоке, договор нарушившем. Повтор последнего токена его бы не
    /// остановил - `bump` двигал бы индекс, `peek` возвращал бы то же самое.
    fn peek(&self) -> Token {
        self.tokens.get(self.index).copied().unwrap_or(Token {
            kind: TokenKind::Eof,
            span: Span::at(self.text.len()),
            line: 1,
            column: 1,
        })
    }

    fn kind(&self) -> TokenKind {
        self.peek().kind
    }

    /// Разновидность лексемы на `offset` вперёд - для просмотра, отличающего
    /// группу связываний от скобок.
    fn kind_ahead(&self, offset: usize) -> TokenKind {
        self.tokens
            .get(self.index + offset)
            .map_or(TokenKind::Eof, |token| token.kind)
    }

    fn text_ahead(&self, offset: usize) -> &'a str {
        self.tokens
            .get(self.index + offset)
            .map_or("", |token| token.text(self.text))
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.kind() == kind
    }

    fn bump(&mut self) -> Token {
        let token = self.peek();
        if token.kind != TokenKind::Eof {
            self.index += 1;
        }
        token
    }

    fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        self.at(kind).then(|| self.bump())
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        if self.at(kind) {
            Ok(self.bump())
        } else {
            Err(self.expected(Expected::Token(kind)))
        }
    }

    fn expected(&self, expected: Expected) -> ParseError {
        let found = self.peek();
        ParseError::Expected {
            expected,
            found: found.kind,
            span: found.span,
        }
    }

    /// Ошибка «за формой с блоком стоит ещё что-то» - на текущей лексеме.
    fn block_not_last(&self, form: &Expr) -> ParseError {
        ParseError::BlockNotLast {
            form: form.span,
            next: self.peek().span,
        }
    }

    /// Ошибка про форму следующих фаз, если лексема - одна из них.
    fn unsupported_here(&self) -> Option<ParseError> {
        let token = self.peek();
        let what = match token.kind {
            TokenKind::Class | TokenKind::Coherent | TokenKind::When => Unsupported::Class,
            TokenKind::Instance => Unsupported::Instance,
            TokenKind::Using => Unsupported::NamedInstance,
            TokenKind::Import => Unsupported::Import,
            TokenKind::Mutual => Unsupported::Mutual,
            TokenKind::Effect => Unsupported::Effect,
            TokenKind::Handle | TokenKind::HandleMulti | TokenKind::With => Unsupported::Handler,
            TokenKind::Infix | TokenKind::Infixl | TokenKind::Infixr => Unsupported::Fixity,
            TokenKind::LBrace => Unsupported::Braces,
            _ => return None,
        };
        Some(ParseError::Unsupported {
            what,
            span: token.span,
        })
    }

    fn symbol(&self, token: Token) -> Symbol {
        Rc::from(token.text(self.text))
    }

    fn name_of(&self, token: Token) -> Name {
        Name {
            text: self.symbol(token),
            span: token.span,
        }
    }

    // --- объявления ------------------------------------------------------

    fn module(&mut self) -> Result<Module, ParseError> {
        let open = self.expect(TokenKind::Open)?;
        let decls = self.members(TokenKind::Close, Self::decl)?;
        self.expect(TokenKind::Close)?;
        self.expect(TokenKind::Eof)?;
        // По объявлениям, а не по границам блока файла: `Close` стоит на
        // `Eof`, и спан модуля кончался бы концом файла, а не текстом.
        let end = decls.last().map_or(open.span, |last| last.span);
        Ok(Module {
            decls,
            span: open.span.merge(end),
        })
    }

    /// Члены блока до `end`, разделённые `Sep`, с объединением соседних клауз.
    ///
    /// Пустым бывает только блок файла: за остальными следит layout, поэтому
    /// отдельной проверки «блок не пуст» здесь нет.
    fn members(
        &mut self,
        end: TokenKind,
        member: fn(&mut Self) -> Result<Decl, ParseError>,
    ) -> Result<Vec<Decl>, ParseError> {
        let mut decls: Vec<Decl> = Vec::new();
        // Имена уже закрытых групп клауз: по ним видно, что группу продолжают
        // после чужого объявления.
        let mut closed: Vec<(Symbol, Span)> = Vec::new();
        if self.at(end) {
            return Ok(decls);
        }
        loop {
            let decl = member(self)?;
            merge_clauses(&mut decls, &mut closed, decl)?;
            if self.eat(TokenKind::Sep).is_none() {
                break;
            }
        }
        Ok(decls)
    }

    /// Блок объявлений: тело `where`, `resource` или локальных определений.
    fn decl_block(&mut self) -> Result<Vec<Decl>, ParseError> {
        self.expect(TokenKind::Open)?;
        let decls = self.members(TokenKind::Close, Self::decl)?;
        self.expect(TokenKind::Close)?;
        Ok(decls)
    }

    fn decl(&mut self) -> Result<Decl, ParseError> {
        self.nested(Self::decl_inner)
    }

    fn decl_inner(&mut self) -> Result<Decl, ParseError> {
        match self.kind() {
            TokenKind::Data => self.data(false),
            // `unique` стоит перед `data` и ничего больше не открывает:
            // отдельной формы объявления он не заводит, а помечает уже
            // существующую.
            TokenKind::Unique => self.unique_data(),
            TokenKind::Resource => self.resource(),
            TokenKind::Type => self.alias(),
            TokenKind::Module => self.module_decl(),
            TokenKind::Ident | TokenKind::LParen => self.signature_or_clause(),
            _ => Err(self
                .unsupported_here()
                .unwrap_or_else(|| self.expected(Expected::Declaration))),
        }
    }

    /// `name : ty` или `name pat* = body [where …]` - решает лексема после
    /// имени, поэтому возврата назад не требуется.
    fn signature_or_clause(&mut self) -> Result<Decl, ParseError> {
        let name = self.decl_name()?;
        if self.eat(TokenKind::Colon).is_some() {
            let ty = self.expr()?;
            let span = name.span.merge(ty.span);
            return Ok(Decl {
                kind: DeclKind::Signature { name, ty },
                span,
            });
        }

        let mut patterns = Vec::new();
        while starts_pattern(self.kind()) {
            patterns.push(self.atomic_pattern()?);
        }
        self.expect(TokenKind::Equals)?;
        let body = self.body()?;
        let wheres = if self.eat(TokenKind::Where).is_some() {
            self.decl_block()?
        } else {
            Vec::new()
        };
        // Локальные определения клаузе принадлежат, значит входят в её спан.
        let end = wheres.last().map_or(body.span, |last| last.span);
        let span = name.span.merge(end);
        let clause = Clause {
            patterns,
            body,
            wheres,
            span,
        };
        Ok(Decl {
            kind: DeclKind::Clauses {
                name,
                clauses: vec![clause],
            },
            span,
        })
    }

    /// Имя определения: обычное или оператор в скобках (`(++) : …`, §4.4).
    fn decl_name(&mut self) -> Result<Name, ParseError> {
        let Some(open) = self.eat(TokenKind::LParen) else {
            return self.ident();
        };
        let operator = self.expect(TokenKind::Operator)?;
        let close = self.expect(TokenKind::RParen)?;
        Ok(Name {
            text: self.symbol(operator),
            span: open.span.merge(close.span),
        })
    }

    /// Имя. Ошибка называет имя, а не идентификатор: «идентификатор» - это
    /// лексический класс, о котором пишущий на языке не думает.
    fn ident(&mut self) -> Result<Name, ParseError> {
        if !self.at(TokenKind::Ident) {
            return Err(self.expected(Expected::Name));
        }
        let token = self.bump();
        Ok(self.name_of(token))
    }

    /// `data Name param* [: kind] [where блок конструкторов]`.
    ///
    /// `where` необязателен: без него семейство остаётся без конструкторов, и
    /// иначе пустой тип был бы незаписываем - layout пустых блоков не делает, а
    /// ядру пустое семейство нужно (разбор с нулём ветвей и есть доказательство
    /// его необитаемости, §9 Фаза 1).
    /// `unique data …` - тот же разбор, что у `data`, с маркером.
    fn unique_data(&mut self) -> Result<Decl, ParseError> {
        let start = self.bump().span;
        if !self.at(TokenKind::Data) {
            return Err(self.expected(Expected::Token(TokenKind::Data)));
        }
        let decl = self.data(true)?;
        Ok(Decl {
            span: start.merge(decl.span),
            ..decl
        })
    }

    fn data(&mut self, unique: bool) -> Result<Decl, ParseError> {
        let start = self.bump().span;
        let name = self.ident()?;
        let params = self.params()?;
        let kind = if self.eat(TokenKind::Colon).is_some() {
            Some(self.expr()?)
        } else {
            None
        };

        if let Some(kind) = &kind {
            if self.at(TokenKind::Where) && contains_block(kind) {
                return Err(self.block_not_last(kind));
            }
        }

        let mut end = kind.as_ref().map_or(name.span, |kind| kind.span);
        let mut constructors = Vec::new();
        if self.eat(TokenKind::Where).is_some() {
            self.expect(TokenKind::Open)?;
            loop {
                constructors.push(self.constructor()?);
                if self.eat(TokenKind::Sep).is_none() {
                    break;
                }
            }
            self.expect(TokenKind::Close)?;
            // Последний конструктор, а не `Close`: тот стоит в позиции токена,
            // который блок закрыл, то есть уже следующего объявления.
            end = constructors.last().map_or(end, |last| last.span);
        }

        Ok(Decl {
            kind: DeclKind::Data(Data {
                unique,
                name,
                params,
                kind,
                constructors,
            }),
            span: start.merge(end),
        })
    }

    fn constructor(&mut self) -> Result<Constructor, ParseError> {
        let name = self.decl_name()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.expr()?;
        let span = name.span.merge(ty.span);
        Ok(Constructor { name, ty, span })
    }

    /// `resource Name param* where` и блок членов (§3.3).
    fn resource(&mut self) -> Result<Decl, ParseError> {
        let start = self.bump().span;
        let name = self.ident()?;
        let params = self.params()?;
        self.expect(TokenKind::Where)?;
        let members = self.decl_block()?;
        let end = members.last().map_or(name.span, |last| last.span);
        let span = start.merge(end);
        Ok(Decl {
            kind: DeclKind::Resource(Resource {
                name,
                params,
                members,
            }),
            span,
        })
    }

    /// Параметры объявления: голые имена (`data Pair a b`) вперемешку с
    /// группами в скобках (`data Vect {0 n : Nat}`).
    fn params(&mut self) -> Result<Vec<Binder>, ParseError> {
        let mut params = Vec::new();
        loop {
            if self.at(TokenKind::Ident) {
                let name = self.ident()?;
                params.push(Binder {
                    visibility: Visibility::Explicit,
                    mult: None,
                    span: name.span,
                    names: vec![name],
                    ty: None,
                });
            } else if self.at_binder() {
                params.push(self.binder()?);
            } else {
                return Ok(params);
            }
        }
    }

    // --- выражения -------------------------------------------------------

    /// Тело определения или связывания: блок, если его открыл `=`, иначе
    /// выражение в одну строку.
    fn body(&mut self) -> Result<Expr, ParseError> {
        if self.at(TokenKind::Open) {
            let block = self.block()?;
            let span = block.span;
            return Ok(Expr {
                kind: ExprKind::Block(block),
                span,
            });
        }
        self.expr()
    }

    fn block(&mut self) -> Result<Block, ParseError> {
        self.nested(Self::block_inner)
    }

    fn block_inner(&mut self) -> Result<Block, ParseError> {
        let open = self.expect(TokenKind::Open)?;
        let mut stmts = Vec::new();
        loop {
            stmts.push(self.stmt()?);
            if self.eat(TokenKind::Sep).is_none() {
                break;
            }
        }
        self.expect(TokenKind::Close)?;
        let end = stmts.last().map_or(open.span, |last| last.span);
        Ok(Block {
            stmts,
            span: open.span.merge(end),
        })
    }

    fn stmt(&mut self) -> Result<Stmt, ParseError> {
        let Some(let_token) = self.eat(TokenKind::Let) else {
            let expr = self.expr()?;
            let span = expr.span;
            return Ok(Stmt {
                kind: StmtKind::Expr(expr),
                span,
            });
        };
        self.expect(TokenKind::Open)?;
        let mut bindings = Vec::new();
        loop {
            bindings.push(self.binding()?);
            if self.eat(TokenKind::Sep).is_none() {
                break;
            }
        }
        self.expect(TokenKind::Close)?;
        let end = bindings.last().map_or(let_token.span, |last| last.span);
        Ok(Stmt {
            kind: StmtKind::Let(bindings),
            span: let_token.span.merge(end),
        })
    }

    /// `[кратность] имя паттерн* [: тип] = тело`.
    fn binding(&mut self) -> Result<Binding, ParseError> {
        let start = self.peek().span;
        let mult = self.multiplicity()?;
        let name = self.ident()?;
        let mut params = Vec::new();
        while starts_pattern(self.kind()) {
            params.push(self.atomic_pattern()?);
        }
        let ty = if self.eat(TokenKind::Colon).is_some() {
            Some(self.expr()?)
        } else {
            None
        };
        if let Some(ty) = &ty {
            if contains_block(ty) {
                return Err(self.block_not_last(ty));
            }
        }
        self.expect(TokenKind::Equals)?;
        let body = self.body()?;
        let span = start.merge(body.span);
        Ok(Binding {
            mult,
            name,
            params,
            ty,
            body,
            span,
        })
    }

    /// Выражение целиком, вместе со стрелками.
    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.nested(Self::expr_inner)
    }

    fn expr_inner(&mut self) -> Result<Expr, ParseError> {
        if self.at_binder() {
            // Единственное место, где парсер возвращается назад: `{x : Nat}`
            // читается и как группа implicit-связываний, и как тип записи
            // (§4.2). Различает их то, идёт ли следом стрелка, а этого не
            // видно ни по одному токену вперёд - группа бывает любой длины, и
            // `{x : Nat, y : Nat}` группой не является вовсе.
            //
            // Возврат назад разрешён только фигурным скобкам: у круглых
            // второго прочтения нет, и подменять их ошибку записью значило бы
            // отвечать не о том, что написано.
            let mark = self.index;
            let braces = self.at(TokenKind::LBrace);
            match self.binder_group() {
                Ok(expr) => return Ok(expr),
                Err(error) => {
                    if !braces || !self.at_record_at(mark) {
                        return Err(error);
                    }
                    self.index = mark;
                }
            }
        }

        self.arrowed()
    }

    /// Группа связываний вместе со стрелкой: `(q x y : A) {r z : B} -> C`.
    ///
    /// Отказ здесь для фигурных скобок не окончателен - см. `expr_inner`.
    fn binder_group(&mut self) -> Result<Expr, ParseError> {
        let start = self.peek().span;
        let mut binders = vec![self.binder()?];
        while self.at_binder() {
            binders.push(self.binder()?);
        }
        self.expect(TokenKind::Arrow)?;
        let codomain = self.expr()?;
        let span = start.merge(codomain.span);
        Ok(Expr {
            kind: ExprKind::Pi {
                binders,
                codomain: Box::new(codomain),
            },
            span,
        })
    }

    /// Цепочка, за которой может идти стрелка.
    fn arrowed(&mut self) -> Result<Expr, ParseError> {
        let left = self.chain()?;
        if !self.at(TokenKind::Arrow) {
            return Ok(left);
        }
        if contains_block(&left) {
            return Err(self.block_not_last(&left));
        }
        self.bump();
        // Стрелка правоассоциативна: `A -> B -> C` это `A -> (B -> C)`.
        let right = self.expr()?;
        let span = left.span.merge(right.span);
        Ok(Expr {
            kind: ExprKind::Arrow(Box::new(left), Box::new(right)),
            span,
        })
    }

    /// Цепочка операторов. Скобок не расставляет - фикситетов ещё нет.
    fn chain(&mut self) -> Result<Expr, ParseError> {
        let head = self.application()?;
        if !self.at(TokenKind::Operator) {
            return Ok(head);
        }
        if contains_block(&head) {
            return Err(self.block_not_last(&head));
        }
        let mut span = head.span;
        let mut tail = Vec::new();
        while let Some(operator) = self.eat(TokenKind::Operator) {
            let operand = self.application()?;
            if self.at(TokenKind::Operator) && contains_block(&operand) {
                return Err(self.block_not_last(&operand));
            }
            span = span.merge(operand.span);
            tail.push((self.name_of(operator), operand));
        }
        Ok(Expr {
            kind: ExprKind::Chain(Chain {
                head: Box::new(head),
                tail,
            }),
            span,
        })
    }

    fn application(&mut self) -> Result<Expr, ParseError> {
        let mut callee = self.postfix()?;
        // Флаг накапливается по частям, а не пересчитывается по всему спайну
        // на каждом шаге: иначе длинный спайн стоил бы квадрата.
        let mut blocked = contains_block(&callee);
        loop {
            let type_app = self.at(TokenKind::At);
            // Функция-проекция начинает атом, хотя её первая лексема -
            // операторный знак: `map .x` есть применение, а не цепочка.
            if !type_app && !starts_atom(self.kind()) && !self.at_projection() {
                return Ok(callee);
            }
            if blocked {
                return Err(self.block_not_last(&callee));
            }
            if type_app {
                self.bump();
            }
            let argument = self.postfix()?;
            blocked = contains_block(&argument);
            let span = callee.span.merge(argument.span);
            let kind = if type_app {
                ExprKind::TypeApp(Box::new(callee), Box::new(argument))
            } else {
                ExprKind::App(Box::new(callee), Box::new(argument))
            };
            callee = Expr { kind, span };
        }
    }

    /// Атом вместе с проекциями: `p.x.y`.
    ///
    /// Проекция связывает крепче применения - `f p.x` есть `f (p.x)`, - и её
    /// `.` в фикситетах не участвует вовсе.
    fn postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.atom()?;
        // Примыкание требуется и слева: `map .x` - это `map` и функция-
        // проекция, а не `(map).x`.
        while self.peek().span.start() == expr.span.end() {
            let Some(field) = self.projected() else {
                break;
            };
            let span = expr.span.merge(field.span);
            expr = Expr {
                kind: ExprKind::Project(Box::new(expr), field),
                span,
            };
        }
        Ok(expr)
    }

    /// `.x` в позиции атома - функция-проекция: `map .x` (§4.2).
    ///
    /// Сахар для `\p -> p.x`, и разворачивается он здесь: связывания у него
    /// своего нет, а имя параметра пользователю невидимо.
    fn projection(&mut self) -> Expr {
        let start = self.peek().span;
        let Some(field) = self.projected() else {
            unreachable!("вызвано не на проекции")
        };
        let span = start.merge(field.span);
        let param: Symbol = Rc::from("#record");
        let name = Name {
            text: Rc::clone(&param),
            span,
        };
        let body = Expr {
            kind: ExprKind::Project(
                Box::new(Expr {
                    kind: ExprKind::Name(name.clone()),
                    span,
                }),
                field,
            ),
            span,
        };
        Expr {
            kind: ExprKind::Lam {
                params: vec![LamParam {
                    kind: LamParamKind::Pattern(Pattern {
                        kind: PatternKind::Name(name),
                        span,
                    }),
                    span,
                }],
                body: Box::new(body),
            },
            span,
        }
    }

    /// Стоит ли на разделителе `|`.
    fn at_pipe(&self) -> bool {
        self.at(TokenKind::Pipe)
    }

    /// Хвост формы `{ base | x = v, y = w }` - после самого `|`.
    fn updated(&mut self, start: Span, base: Expr) -> Result<Expr, ParseError> {
        let mut fields = Vec::new();
        loop {
            let name = self.expect(TokenKind::Ident)?;
            let name = self.name_of(name);
            // Punning работает и здесь: `{ p | x }` есть `{ p | x = x }`.
            let value = if self.eat(TokenKind::Equals).is_some() {
                self.expr()?
            } else {
                Expr {
                    kind: ExprKind::Name(name.clone()),
                    span: name.span,
                }
            };
            fields.push((name, value));
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        let close = self.expect(TokenKind::RBrace)?;
        Ok(Expr {
            kind: ExprKind::Update(Box::new(base), fields),
            span: start.merge(close.span),
        })
    }

    /// Стоит ли на `.name` - функции-проекции в позиции атома.
    fn at_projection(&self) -> bool {
        let dot = self.peek();
        if dot.text(self.text) != "." {
            return false;
        }
        self.tokens
            .get(self.index + 1)
            .copied()
            .is_some_and(|field| {
                field.kind == TokenKind::Ident && dot.span.end() == field.span.start()
            })
    }

    /// Имя поля, если дальше идёт примыкающая проекция `.name`.
    ///
    /// Примыкание проверяется по спанам: `.` - обычный операторный знак, и
    /// отличить проекцию от оператора можно только тем, что между ними и
    /// вокруг них ничего не написано.
    fn projected(&mut self) -> Option<Name> {
        let dot = self.peek();
        if dot.kind != TokenKind::Operator || dot.text(self.text) != "." {
            return None;
        }
        let field = self.tokens.get(self.index + 1).copied();
        let field = field?;
        if field.kind != TokenKind::Ident || dot.span.end() != field.span.start() {
            return None;
        }
        self.bump();
        self.bump();
        Some(self.name_of(field))
    }

    fn atom(&mut self) -> Result<Expr, ParseError> {
        self.nested(Self::atom_inner)
    }

    /// `{ x : A, y : B }` - тип записи, `{ x = a, y }` - её значение (§4.2).
    ///
    /// Различает их первый разделитель после имени поля: `:` объявляет, `=`
    /// присваивает, а голое имя - punning, то есть `x = x`. Смешивать нельзя:
    /// запись либо тип, либо значение, и половина каждого была бы ни тем ни
    /// другим.
    /// `module M [: S] where …` и `module type S where …` (§4.8).
    ///
    /// Обе формы разбираются одной: различает их `type` сразу за `module`, а
    /// дальше у них общее всё - имя, необязательная аннотация и блок членов.
    /// Член - обычное объявление, поэтому вложенный модуль разбирается сам
    /// собой; законен ли он там, решает элаборация.
    fn module_decl(&mut self) -> Result<Decl, ParseError> {
        let start = self.bump().span;
        let signature = self.eat(TokenKind::Type).is_some();
        let name = self.expect(TokenKind::Ident)?;
        let name = self.name_of(name);
        // Параметры есть только у модуля: сигнатура интерфейс, а не функция от
        // него. Написанные у сигнатуры отвергает элаборация - сказать это
        // словами она умеет, а парсер их просто разбирает.
        let params = self.params()?;
        let sealed = self.at(TokenKind::Seal);
        let ascription =
            if self.eat(TokenKind::Colon).is_some() || self.eat(TokenKind::Seal).is_some() {
                let written = self.expr()?;
                if self.at(TokenKind::Where) && contains_block(&written) {
                    return Err(self.block_not_last(&written));
                }
                Some(written)
            } else {
                None
            };
        let mut end = ascription.as_ref().map_or(name.span, |it| it.span);
        // `module IntMap = OrderedMap IntOrd` - применение функтора; тела
        // блоком у него нет, и `where` за ним не идёт.
        let body = if self.eat(TokenKind::Equals).is_some() {
            let written = self.body()?;
            end = written.span;
            Some(written)
        } else {
            None
        };
        let mut members = Vec::new();
        if body.is_none() && self.eat(TokenKind::Where).is_some() {
            self.expect(TokenKind::Open)?;
            members = self.members(TokenKind::Close, Self::decl)?;
            self.expect(TokenKind::Close)?;
            end = members.last().map_or(end, |last| last.span);
        }
        Ok(Decl {
            kind: DeclKind::Module(ModuleDecl {
                signature,
                name,
                params,
                body,
                ascription,
                sealed,
                members,
            }),
            span: start.merge(end),
        })
    }

    /// Уравнение необязательно: `type T` без него объявляет абстрактный
    /// типовой член сигнатуры модуля (§4.8). Что эта форма законна только
    /// внутри `module type`, решает элаборация - парсеру про место объявления
    /// знать неоткуда.
    fn alias(&mut self) -> Result<Decl, ParseError> {
        let start = self.expect(TokenKind::Type)?.span;
        let name = self.expect(TokenKind::Ident)?;
        let name = self.name_of(name);
        let mut span = start.merge(name.span);
        let body = if self.eat(TokenKind::Equals).is_some() {
            let body = self.body()?;
            span = start.merge(body.span);
            Some(body)
        } else {
            None
        };
        Ok(Decl {
            kind: DeclKind::Alias { name, body },
            span,
        })
    }

    /// Метка effect row пишется теми же лексемами, что punning записи: `{IO}`
    /// читается и как ряд с меткой `IO`, и как `{IO = IO}`. Различает их
    /// **регистр** - то же правило §4.1, по которому заглавное имя ссылается на
    /// объявленное, а строчное связывает. Поле записи строчное, метка ряда
    /// заглавная, и разойтись им негде.
    fn at_record_at(&self, mark: usize) -> bool {
        let first = self.tokens.get(mark + 1).copied();
        first.is_some_and(|token| {
            token.kind == TokenKind::Ident
                && !token
                    .text(self.text)
                    .starts_with(|ch: char| ch.is_uppercase())
        })
    }

    fn at_record(&self) -> bool {
        self.at_record_at(self.index)
    }

    fn record(&mut self) -> Result<Expr, ParseError> {
        let open = self.expect(TokenKind::LBrace)?;
        if let Some(close) = self.eat(TokenKind::RBrace) {
            return Err(ParseError::EmptyRecord {
                span: open.span.merge(close.span),
            });
        }
        // `{ p | x = v }` - обновление. Отличается оно от списка полей только
        // тем, что после первого выражения стоит `|`, а не `:`, `=` или `,`;
        // выражение при этом бывает любым, поэтому парсер пробует и
        // возвращается. Возврат тот же, что у `{x : Nat}`, и по той же причине.
        let mark = self.index;
        // Основа читается применением, а не выражением целиком: `|` - обычный
        // операторный знак, и цепочка съела бы его вместе с полями.
        if let Ok(base) = self.application() {
            if self.at_pipe() {
                self.bump();
                return self.updated(open.span, base);
            }
        }
        self.index = mark;
        let mut fields = Vec::new();
        let mut values = Vec::new();
        loop {
            let name = self.expect(TokenKind::Ident)?;
            let name = self.name_of(name);
            if self.eat(TokenKind::Colon).is_some() {
                if !values.is_empty() {
                    return Err(ParseError::MixedRecord { span: name.span });
                }
                fields.push(RecordField {
                    name: name.clone(),
                    ty: self.expr()?,
                });
            } else {
                if !fields.is_empty() {
                    return Err(ParseError::MixedRecord { span: name.span });
                }
                // Punning: `{ x }` есть `{ x = x }`, и одноимённая переменная
                // берётся из области видимости, а не выдумывается.
                let value = if self.eat(TokenKind::Equals).is_some() {
                    self.expr()?
                } else {
                    Expr {
                        kind: ExprKind::Name(name.clone()),
                        span: name.span,
                    }
                };
                values.push((name.clone(), value));
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        // Явный хвост пишется у типа: `{ x : Nat | r }` (§4.2, §4.11). У
        // значения его нет - там `|` уже означает обновление.
        let tail = if values.is_empty() && self.at_pipe() {
            self.bump();
            let name = self.expect(TokenKind::Ident)?;
            Some(self.name_of(name))
        } else {
            None
        };
        let close = self.expect(TokenKind::RBrace)?;
        let span = open.span.merge(close.span);
        let kind = if values.is_empty() {
            ExprKind::RecordType(fields, tail)
        } else {
            ExprKind::Record(values)
        };
        Ok(Expr { kind, span })
    }

    fn atom_inner(&mut self) -> Result<Expr, ParseError> {
        let token = self.peek();
        let (kind, span) = match token.kind {
            TokenKind::Ident => {
                self.bump();
                (ExprKind::Name(self.name_of(token)), token.span)
            }
            TokenKind::Underscore => {
                self.bump();
                (ExprKind::Hole, token.span)
            }
            TokenKind::Backslash => return self.lambda(),
            TokenKind::If => return self.conditional(),
            TokenKind::Case => return self.case(),
            TokenKind::LParen => return self.parenthesised(),
            TokenKind::LBrace if self.at_record() => return self.record(),
            TokenKind::Operator if self.at_projection() => return Ok(self.projection()),
            TokenKind::LBracket => return self.list(),
            _ if self.at_literal() => {
                let lit = self.literal()?;
                let span = lit.span;
                (ExprKind::Lit(lit), span)
            }
            _ => {
                return Err(self
                    .unsupported_here()
                    .unwrap_or_else(|| self.expected(Expected::Expression)));
            }
        };
        Ok(Expr { kind, span })
    }

    /// Стоит ли на литерале - вместе со знаком, если знак здесь часть числа.
    fn at_literal(&self) -> bool {
        match self.kind() {
            TokenKind::Nat | TokenKind::Float | TokenKind::Str => true,
            // Знак перед числом - часть литерала: §4.3 выбирает класс
            // преобразования по написанию, и `-42` это `FromInt`, а не
            // применение вычитания.
            TokenKind::Operator => self.negative_literal_ahead(),
            _ => false,
        }
    }

    /// Стоит ли на знаке, за которым идёт число: `-42`, `-1e9`.
    fn negative_literal_ahead(&self) -> bool {
        self.peek().text(self.text) == "-"
            && matches!(self.kind_ahead(1), TokenKind::Nat | TokenKind::Float)
    }

    fn literal(&mut self) -> Result<Lit, ParseError> {
        let negative = self.negative_literal_ahead();
        let start = if negative { Some(self.bump()) } else { None };
        let token = self.bump();
        let kind = match (token.kind, negative) {
            (TokenKind::Nat, false) => LitKind::Nat,
            (TokenKind::Nat, true) => LitKind::Int,
            (TokenKind::Float, _) => LitKind::Float,
            (TokenKind::Str, _) => LitKind::Str,
            _ => return Err(self.expected(Expected::Expression)),
        };
        let number = token.text(self.text);
        // Текст собирается из знака и числа, а не режется по спану целиком:
        // между ними бывает пробел (`- 42`), и он попал бы в текст литерала,
        // который обязан читаться как число.
        let text: Symbol = match start {
            Some(_) => Rc::from(format!("-{number}")),
            None => Rc::from(number),
        };
        let span = start.map_or(token.span, |sign| sign.span.merge(token.span));
        Ok(Lit { kind, text, span })
    }

    fn lambda(&mut self) -> Result<Expr, ParseError> {
        let start = self.bump().span;
        let mut params = Vec::new();
        loop {
            if self.at_binder() {
                let binder = self.binder()?;
                params.push(LamParam {
                    span: binder.span,
                    kind: LamParamKind::Binder(binder),
                });
            } else if starts_pattern(self.kind()) {
                let pattern = self.atomic_pattern()?;
                params.push(LamParam {
                    span: pattern.span,
                    kind: LamParamKind::Pattern(pattern),
                });
            } else {
                break;
            }
        }
        if params.is_empty() {
            return Err(self.expected(Expected::Pattern));
        }
        self.expect(TokenKind::Arrow)?;
        let body = self.expr()?;
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::Lam {
                params,
                body: Box::new(body),
            },
            span,
        })
    }

    fn conditional(&mut self) -> Result<Expr, ParseError> {
        let start = self.bump().span;
        let cond = self.expr()?;
        if contains_block(&cond) {
            return Err(self.block_not_last(&cond));
        }
        self.expect(TokenKind::Then)?;
        let then_branch = self.expr()?;
        self.expect(TokenKind::Else)?;
        let else_branch = self.expr()?;
        let span = start.merge(else_branch.span);
        Ok(Expr {
            kind: ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            },
            span,
        })
    }

    fn case(&mut self) -> Result<Expr, ParseError> {
        let start = self.bump().span;
        let scrutinee = self.expr()?;
        if contains_block(&scrutinee) {
            return Err(self.block_not_last(&scrutinee));
        }
        self.expect(TokenKind::Of)?;
        self.expect(TokenKind::Open)?;
        let mut alts = Vec::new();
        loop {
            alts.push(self.alt()?);
            if self.eat(TokenKind::Sep).is_none() {
                break;
            }
        }
        self.expect(TokenKind::Close)?;
        let end = alts.last().map_or(start, |last| last.span);
        Ok(Expr {
            kind: ExprKind::Case {
                scrutinee: Box::new(scrutinee),
                alts,
            },
            span: start.merge(end),
        })
    }

    fn alt(&mut self) -> Result<Alt, ParseError> {
        let pattern = self.pattern()?;
        self.expect(TokenKind::Arrow)?;
        let body = self.expr()?;
        let span = pattern.span.merge(body.span);
        Ok(Alt {
            pattern,
            body,
            span,
        })
    }

    /// `()`, `(expr)` или кортеж. Группа связываний сюда не попадает - её
    /// отводит [`Self::at_binder`] раньше.
    fn parenthesised(&mut self) -> Result<Expr, ParseError> {
        let open = self.bump();
        if let Some(close) = self.eat(TokenKind::RParen) {
            return Ok(Expr {
                kind: ExprKind::Tuple(Vec::new()),
                span: open.span.merge(close.span),
            });
        }
        let first = self.expr()?;
        if let Some(close) = self.eat(TokenKind::RParen) {
            // Отдельного узла у скобок нет: печать расставит их заново по
            // приоритетам, а хранить их значило бы иметь два способа записать
            // одно дерево. Спан при этом берётся вместе со скобками - на них
            // указывает диагностика, когда указывает на это выражение.
            return Ok(Expr {
                kind: first.kind,
                span: open.span.merge(close.span),
            });
        }
        let mut items = vec![first];
        while self.eat(TokenKind::Comma).is_some() {
            items.push(self.expr()?);
        }
        let close = self.expect(TokenKind::RParen)?;
        Ok(Expr {
            kind: ExprKind::Tuple(items),
            span: open.span.merge(close.span),
        })
    }

    fn list(&mut self) -> Result<Expr, ParseError> {
        let open = self.bump();
        let mut items = Vec::new();
        if !self.at(TokenKind::RBracket) {
            loop {
                items.push(self.expr()?);
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        let close = self.expect(TokenKind::RBracket)?;
        Ok(Expr {
            kind: ExprKind::List(items),
            span: open.span.merge(close.span),
        })
    }

    // --- связывания ------------------------------------------------------

    /// Стоит ли на группе связываний: `(0 n m : Nat)`, `{ℓ : Level}`.
    ///
    /// Просмотр вперёд, а не разбор с возвратом: у `(` в этом языке три разных
    /// продолжения - группа, кортеж и просто скобки, - и различает их наличие
    /// `:` после списка имён.
    fn at_binder(&self) -> bool {
        if !matches!(self.kind(), TokenKind::LParen | TokenKind::LBrace) {
            return false;
        }
        let mut offset = 1;
        if self.at_multiplicity(offset) {
            offset += 1;
        }
        let mut names = 0;
        while matches!(
            self.kind_ahead(offset),
            TokenKind::Ident | TokenKind::Underscore
        ) {
            offset += 1;
            names += 1;
        }
        names > 0 && self.kind_ahead(offset) == TokenKind::Colon
    }

    /// Может ли лексема на `offset` быть кратностью. Число здесь любое: не то
    /// число даёт [`ParseError::Multiplicity`] с указанием на само число, а не
    /// отказ где-то дальше.
    fn at_multiplicity(&self, offset: usize) -> bool {
        match self.kind_ahead(offset) {
            TokenKind::Nat => true,
            TokenKind::Ident => self.text_ahead(offset) == "ω",
            _ => false,
        }
    }

    fn binder(&mut self) -> Result<Binder, ParseError> {
        let open = self.bump();
        let visibility = if open.kind == TokenKind::LParen {
            Visibility::Explicit
        } else {
            Visibility::Implicit
        };
        let mult = self.multiplicity()?;
        let mut names = vec![self.binder_name()?];
        while matches!(self.kind(), TokenKind::Ident | TokenKind::Underscore) {
            names.push(self.binder_name()?);
        }
        self.expect(TokenKind::Colon)?;
        let ty = self.expr()?;
        let closing = open.kind.closing_bracket().unwrap_or(TokenKind::RParen);
        let close = self.expect(closing)?;
        Ok(Binder {
            visibility,
            mult,
            names,
            ty: Some(ty),
            span: open.span.merge(close.span),
        })
    }

    /// Имя связывания. `_` допускается: `(1 _ : a)` связывает, не называя.
    fn binder_name(&mut self) -> Result<Name, ParseError> {
        match self.kind() {
            TokenKind::Ident | TokenKind::Underscore => {
                let token = self.bump();
                Ok(self.name_of(token))
            }
            _ => Err(self.expected(Expected::Name)),
        }
    }

    /// Кратность, если написана.
    fn multiplicity(&mut self) -> Result<Option<MultAnn>, ParseError> {
        let token = self.peek();
        let mult = match token.kind {
            TokenKind::Nat => match token.text(self.text) {
                "0" => Mult::Zero,
                "1" => Mult::One,
                _ => return Err(ParseError::Multiplicity { span: token.span }),
            },
            TokenKind::Ident if token.text(self.text) == "ω" => Mult::Many,
            _ => return Ok(None),
        };
        self.bump();
        Ok(Some(MultAnn {
            mult,
            span: token.span,
        }))
    }

    // --- паттерны --------------------------------------------------------

    /// Паттерн с полями без скобок: так пишется ветка `case`.
    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        if !self.at(TokenKind::Ident) {
            return self.atomic_pattern();
        }
        let head = self.ident()?;
        let mut fields = Vec::new();
        while starts_pattern(self.kind()) {
            fields.push(self.atomic_pattern()?);
        }
        if fields.is_empty() {
            return Ok(Pattern {
                span: head.span,
                kind: PatternKind::Name(head),
            });
        }
        let span = fields
            .last()
            .map_or(head.span, |last| head.span.merge(last.span));
        Ok(Pattern {
            kind: PatternKind::App { head, fields },
            span,
        })
    }

    /// Паттерн в позиции аргумента: конструктор с полями требует скобок.
    fn atomic_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.nested(Self::atomic_pattern_inner)
    }

    fn atomic_pattern_inner(&mut self) -> Result<Pattern, ParseError> {
        let token = self.peek();
        let (kind, span) = match token.kind {
            TokenKind::Ident => {
                self.bump();
                (PatternKind::Name(self.name_of(token)), token.span)
            }
            TokenKind::Underscore => {
                self.bump();
                (PatternKind::Wildcard, token.span)
            }
            // Знака здесь не бывает: отрицательный литерал в паттерне - форма
            // следующего среза, см. заголовок модуля.
            TokenKind::Nat | TokenKind::Float | TokenKind::Str => {
                let lit = self.literal()?;
                let span = lit.span;
                (PatternKind::Lit(lit), span)
            }
            TokenKind::LParen => return self.parenthesised_pattern(),
            _ => return Err(self.expected(Expected::Pattern)),
        };
        Ok(Pattern { kind, span })
    }

    fn parenthesised_pattern(&mut self) -> Result<Pattern, ParseError> {
        let open = self.bump();
        if let Some(close) = self.eat(TokenKind::RParen) {
            return Ok(Pattern {
                kind: PatternKind::Tuple(Vec::new()),
                span: open.span.merge(close.span),
            });
        }
        let first = self.pattern()?;
        if let Some(close) = self.eat(TokenKind::RParen) {
            return Ok(Pattern {
                kind: first.kind,
                span: open.span.merge(close.span),
            });
        }
        let mut items = vec![first];
        while self.eat(TokenKind::Comma).is_some() {
            items.push(self.pattern()?);
        }
        let close = self.expect(TokenKind::RParen)?;
        Ok(Pattern {
            kind: PatternKind::Tuple(items),
            span: open.span.merge(close.span),
        })
    }
}

/// Может ли лексема начинать аргумент применения.
///
/// Оператора здесь нет намеренно: `x - 42` это вычитание, а не применение `x` к
/// `-42`. Знак становится частью литерала только там, где операнд начинается, -
/// то есть внутри [`Parser::atom`], а не в цикле аргументов.
fn starts_atom(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Ident
            | TokenKind::Nat
            | TokenKind::Float
            | TokenKind::Str
            | TokenKind::Underscore
            | TokenKind::LParen
            | TokenKind::LBracket
            | TokenKind::Backslash
            | TokenKind::If
            | TokenKind::Case
            // Не аргумент, а точная ошибка: иначе про запись сообщил бы
            // объемлющий разбор и сказал бы что-то другое.
            | TokenKind::LBrace
            | TokenKind::Handle
            | TokenKind::HandleMulti
            | TokenKind::Using
    )
}

/// Может ли лексема начинать паттерн в позиции аргумента.
fn starts_pattern(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Ident
            | TokenKind::Underscore
            | TokenKind::Nat
            | TokenKind::Float
            | TokenKind::Str
            | TokenKind::LParen
    )
}

/// Приклеивает клаузы к соседней группе того же имени.
///
/// Группой владеет парсер, а не элаборация, потому что «подряд» - свойство
/// исходника: разнесённые по файлу клаузы одного имени обязаны быть отказом, а
/// не молча собранной группой, раз порядок клауз значим.
fn merge_clauses(
    decls: &mut Vec<Decl>,
    closed: &mut Vec<(Symbol, Span)>,
    mut decl: Decl,
) -> Result<(), ParseError> {
    let DeclKind::Clauses { name, clauses } = &mut decl.kind else {
        close_last(decls, closed);
        decls.push(decl);
        return Ok(());
    };

    if let Some(last) = decls.last_mut() {
        if let DeclKind::Clauses {
            name: previous,
            clauses: collected,
        } = &mut last.kind
        {
            if previous.text == name.text {
                // Перенос, а не копия: клауза несёт дерево тела целиком.
                collected.append(clauses);
                last.span = last.span.merge(decl.span);
                return Ok(());
            }
        }
    }

    if let Some((_, first)) = closed.iter().find(|(seen, _)| *seen == name.text) {
        return Err(ParseError::SplitClauses {
            name: Rc::clone(&name.text),
            first: *first,
            again: name.span,
        });
    }

    close_last(decls, closed);
    decls.push(decl);
    Ok(())
}

/// Запоминает имя группы клауз, которую только что перестали продолжать.
fn close_last(decls: &[Decl], closed: &mut Vec<(Symbol, Span)>) {
    if let Some(last) = decls.last() {
        if let DeclKind::Clauses { name, .. } = &last.kind {
            closed.push((Rc::clone(&name.text), name.span));
        }
    }
}
