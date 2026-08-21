//! Recursive descent. Грамматика, от слабого связывания к сильному:
//!
//! ```text
//! expr  := lambda | let | if | cmp
//! cmp   := add [('<' | '==') add]        -- неассоциативно
//! add   := mul (('+' | '-') mul)*
//! mul   := app ('*' app)*
//! app   := atom atom*                    -- левоассоциативно
//! atom  := int | bool | ident | 'fix' atom | '(' expr [':' type] ')'
//! type  := atype ['->' type]             -- правоассоциативно
//! atype := 'Int' | 'Bool' | '(' type ')'
//! ```

use adamas_core::source::Span;

use crate::error::Error;
use crate::lexer::{Kind as Tok, Token};
use crate::syntax::{BinOp, Kind, Term, TypeExpr};

/// Предел вложенности при разборе.
///
/// Рекурсивный спуск тратит стек пропорционально вложенности, а переполнение
/// стека - abort процесса, а не паника: перехватить его нельзя. Замер в debug
/// на потоке с 2 МБ (столько у тестовых): скобки перестают помещаться на 236
/// уровнях исходника, вложенные лямбды - на 399.
///
/// Счётчик считает не уровни исходника, а входы в [`Parser::nested`]: скобка
/// стоит двух (`atom`, затем `expr`), лямбда, `let`, `if` и стрелка типа - по
/// одному. Нижняя граница задана снизу бенчмарком `check_let_chain_64` - это
/// 128 вложенных `let`, законная программа, которую предел резать не должен.
const MAX_DEPTH: u32 = 256;

/// Разбирает поток токенов в одно выражение и требует, чтобы после него был
/// конец файла.
pub(crate) fn parse(tokens: &[Token]) -> Result<Term, Error> {
    let mut parser = Parser {
        tokens,
        pos: 0,
        depth: 0,
    };
    let term = parser.expr()?;
    parser.expect(&Tok::Eof, "конец файла")?;
    Ok(term)
}

struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    depth: u32,
}

impl Parser<'_> {
    fn peek(&self) -> &Token {
        // Последний токен всегда Eof, поэтому индекс не выходит за границы.
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn bump(&mut self) -> Token {
        let token = self.peek().clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        token
    }

    fn eat(&mut self, kind: &Tok) -> bool {
        if self.peek().kind == *kind {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &Tok, expected: &str) -> Result<Token, Error> {
        if self.peek().kind == *kind {
            Ok(self.bump())
        } else {
            Err(self.unexpected(expected))
        }
    }

    /// Спускается на уровень глубже.
    ///
    /// Обёрнуты [`Self::expr`], [`Self::atom`] и [`Self::type_expr`] - через
    /// один из трёх проходит каждый цикл рекурсии: тела `\`, `let` и `if`
    /// возвращаются в `expr` напрямую, скобки и `fix` - в `atom`, стрелка
    /// типа - в `type_expr`.
    fn nested<T>(&mut self, parse: impl FnOnce(&mut Self) -> Result<T, Error>) -> Result<T, Error> {
        if self.depth == MAX_DEPTH {
            return Err(Error::TooDeep {
                limit: MAX_DEPTH,
                span: self.peek().span,
            });
        }
        self.depth += 1;
        let result = parse(self);
        self.depth -= 1;
        result
    }

    fn unexpected(&self, expected: &str) -> Error {
        let token = self.peek();
        Error::UnexpectedToken {
            expected: expected.to_owned(),
            found: token.kind.describe(),
            span: token.span,
        }
    }

    fn ident(&mut self) -> Result<(String, Span), Error> {
        let token = self.peek().clone();
        if let Tok::Ident(name) = token.kind {
            self.bump();
            Ok((name, token.span))
        } else {
            Err(self.unexpected("идентификатор"))
        }
    }

    fn expr(&mut self) -> Result<Term, Error> {
        self.nested(Self::expr_inner)
    }

    fn expr_inner(&mut self) -> Result<Term, Error> {
        match self.peek().kind {
            Tok::Lambda => self.lambda(),
            Tok::Let => self.let_in(),
            Tok::If => self.if_then_else(),
            _ => self.cmp(),
        }
    }

    fn lambda(&mut self) -> Result<Term, Error> {
        let start = self.expect(&Tok::Lambda, "`\\`")?.span;
        // Параметр либо голый, либо в скобках с аннотацией: `\(x : Int) -> …`.
        let (param, annotation) = if self.eat(&Tok::LParen) {
            let (name, _) = self.ident()?;
            self.expect(&Tok::Colon, "`:`")?;
            let ty = self.type_expr()?;
            self.expect(&Tok::RParen, "`)`")?;
            (name, Some(ty))
        } else {
            (self.ident()?.0, None)
        };
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.expr()?;
        let span = start.merge(body.span);
        Ok(Term {
            kind: Kind::Lambda {
                param,
                annotation,
                body: Box::new(body),
            },
            span,
        })
    }

    fn let_in(&mut self) -> Result<Term, Error> {
        let start = self.expect(&Tok::Let, "`let`")?.span;
        let recursive = self.eat(&Tok::Rec);
        let (name, _) = self.ident()?;
        // Сахар: `let f x y = e` разворачивается в `let f = \x -> \y -> e`.
        let mut params = Vec::new();
        while let Tok::Ident(_) = self.peek().kind {
            params.push(self.ident()?);
        }
        self.expect(&Tok::Equals, "`=`")?;
        let mut value = self.expr()?;
        for (param, param_span) in params.into_iter().rev() {
            let span = param_span.merge(value.span);
            value = Term {
                kind: Kind::Lambda {
                    param,
                    annotation: None,
                    body: Box::new(value),
                },
                span,
            };
        }
        self.expect(&Tok::In, "`in`")?;
        let body = self.expr()?;
        let span = start.merge(body.span);
        Ok(Term {
            kind: Kind::Let {
                name,
                recursive,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        })
    }

    fn if_then_else(&mut self) -> Result<Term, Error> {
        let start = self.expect(&Tok::If, "`if`")?.span;
        let cond = self.expr()?;
        self.expect(&Tok::Then, "`then`")?;
        let then = self.expr()?;
        self.expect(&Tok::Else, "`else`")?;
        let otherwise = self.expr()?;
        let span = start.merge(otherwise.span);
        Ok(Term {
            kind: Kind::If {
                cond: Box::new(cond),
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            },
            span,
        })
    }

    /// Сравнения неассоциативны: `a < b < c` - почти наверняка опечатка, и
    /// отказ разобрать её дешевле, чем тихо принять `(a < b) < c`, которое к
    /// тому же не типизируется.
    fn cmp(&mut self) -> Result<Term, Error> {
        let left = self.add()?;
        let op = match self.peek().kind {
            Tok::Less => BinOp::Less,
            Tok::EqEq => BinOp::Equal,
            _ => return Ok(left),
        };
        self.bump();
        let right = self.add()?;
        Ok(binary(op, left, right))
    }

    fn add(&mut self) -> Result<Term, Error> {
        let mut left = self.mul()?;
        loop {
            let op = match self.peek().kind {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => return Ok(left),
            };
            self.bump();
            let right = self.mul()?;
            left = binary(op, left, right);
        }
    }

    fn mul(&mut self) -> Result<Term, Error> {
        let mut left = self.app()?;
        while self.eat(&Tok::Star) {
            let right = self.app()?;
            left = binary(BinOp::Mul, left, right);
        }
        Ok(left)
    }

    fn app(&mut self) -> Result<Term, Error> {
        let mut term = self.atom()?;
        while starts_atom(&self.peek().kind) {
            let arg = self.atom()?;
            let span = term.span.merge(arg.span);
            term = Term {
                kind: Kind::App(Box::new(term), Box::new(arg)),
                span,
            };
        }
        Ok(term)
    }

    fn atom(&mut self) -> Result<Term, Error> {
        self.nested(Self::atom_inner)
    }

    fn atom_inner(&mut self) -> Result<Term, Error> {
        let token = self.peek().clone();
        match token.kind {
            Tok::Int(value) => {
                self.bump();
                Ok(Term {
                    kind: Kind::Int(value),
                    span: token.span,
                })
            }
            Tok::True | Tok::False => {
                self.bump();
                let value = token.kind == Tok::True;
                Ok(Term {
                    kind: Kind::Bool(value),
                    span: token.span,
                })
            }
            Tok::Ident(name) => {
                self.bump();
                Ok(Term {
                    kind: Kind::Var(name),
                    span: token.span,
                })
            }
            Tok::Fix => {
                self.bump();
                let arg = self.atom()?;
                let span = token.span.merge(arg.span);
                Ok(Term {
                    kind: Kind::Fix(Box::new(arg)),
                    span,
                })
            }
            Tok::LParen => {
                self.bump();
                let inner = self.expr()?;
                let kind = if self.eat(&Tok::Colon) {
                    Kind::Annot {
                        term: Box::new(inner),
                        ty: self.type_expr()?,
                    }
                } else {
                    inner.kind
                };
                let close = self.expect(&Tok::RParen, "`)`")?;
                Ok(Term {
                    kind,
                    span: token.span.merge(close.span),
                })
            }
            _ => Err(self.unexpected("выражение")),
        }
    }

    fn type_expr(&mut self) -> Result<TypeExpr, Error> {
        self.nested(Self::type_expr_inner)
    }

    fn type_expr_inner(&mut self) -> Result<TypeExpr, Error> {
        let left = self.atom_type()?;
        if self.eat(&Tok::Arrow) {
            let right = self.type_expr()?;
            Ok(TypeExpr::Fun(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn atom_type(&mut self) -> Result<TypeExpr, Error> {
        let token = self.peek().clone();
        match &token.kind {
            Tok::Ident(name) if name == "Int" => {
                self.bump();
                Ok(TypeExpr::Int)
            }
            Tok::Ident(name) if name == "Bool" => {
                self.bump();
                Ok(TypeExpr::Bool)
            }
            Tok::LParen => {
                self.bump();
                let inner = self.type_expr()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(inner)
            }
            _ => Err(self.unexpected("тип")),
        }
    }
}

fn binary(op: BinOp, left: Term, right: Term) -> Term {
    let span = left.span.merge(right.span);
    Term {
        kind: Kind::Bin {
            op,
            left: Box::new(left),
            right: Box::new(right),
        },
        span,
    }
}

/// Может ли токен начать аргумент применения. Определяет, где кончается цепочка
/// `f a b` - без этого `f a + b` съело бы `+` как аргумент.
fn starts_atom(kind: &Tok) -> bool {
    matches!(
        kind,
        Tok::Int(_) | Tok::True | Tok::False | Tok::Ident(_) | Tok::Fix | Tok::LParen
    )
}

#[cfg(test)]
mod tests {
    use crate::lexer::tokenize;
    use crate::syntax::{Kind, Term, TypeExpr};

    fn parse(text: &str) -> Term {
        super::parse(&tokenize(text).unwrap()).unwrap()
    }

    fn fails(text: &str) -> String {
        let error = tokenize(text)
            .and_then(|tokens| super::parse(&tokens))
            .unwrap_err();
        error.to_string()
    }

    #[test]
    fn application_binds_tighter_than_arithmetic() {
        // `f a + b` - это `(f a) + b`, а не `f (a + b)`.
        let Kind::Bin { left, .. } = parse("f a + b").kind else {
            panic!("ожидалась бинарная операция на верхнем уровне");
        };
        assert!(matches!(left.kind, Kind::App(..)));
    }

    #[test]
    fn application_is_left_associative() {
        let Kind::App(head, _) = parse("f a b").kind else {
            panic!("ожидалось применение");
        };
        assert!(matches!(head.kind, Kind::App(..)));
    }

    #[test]
    fn lambda_body_extends_as_far_right_as_possible() {
        // `\x -> x + 1` - это `\x -> (x + 1)`, а не `(\x -> x) + 1`.
        let Kind::Lambda { body, .. } = parse("\\x -> x + 1").kind else {
            panic!("ожидалась лямбда");
        };
        assert!(matches!(body.kind, Kind::Bin { .. }));
    }

    #[test]
    fn let_parameters_desugar_into_lambdas() {
        let Kind::Let { value, .. } = parse("let f x y = x in f").kind else {
            panic!("ожидался let");
        };
        let Kind::Lambda { body, .. } = value.kind else {
            panic!("ожидалась внешняя лямбда");
        };
        assert!(matches!(body.kind, Kind::Lambda { .. }));
    }

    #[test]
    fn comparison_is_not_associative() {
        assert!(fails("1 < 2 < 3").contains("конец файла"));
    }

    #[test]
    fn error_names_what_was_expected() {
        assert!(fails("let x = 1").contains("`in`"));
    }

    /// Заведомо больше предела при любом раскладе счётчика по формам.
    const PAST_LIMIT: usize = super::MAX_DEPTH as usize * 2 + 10;

    #[test]
    fn ordinary_nesting_still_parses() {
        let parens = format!("{}1{}", "(".repeat(32), ")".repeat(32));
        assert!(matches!(parse(&parens).kind, Kind::Int(1)));

        let lambdas = format!("{}1", "\\x -> ".repeat(32));
        assert!(matches!(parse(&lambdas).kind, Kind::Lambda { .. }));
    }

    #[test]
    fn deep_parentheses_are_an_error_not_a_crash() {
        let text = format!("{}1{}", "(".repeat(PAST_LIMIT), ")".repeat(PAST_LIMIT));
        assert!(fails(&text).contains("вложенность"));
    }

    #[test]
    fn deep_lambdas_are_an_error_not_a_crash() {
        // Тела лямбд возвращаются в `expr` напрямую, минуя `atom`, - эта
        // форма проверяет именно ту ветку.
        let text = format!("{}1", "\\x -> ".repeat(PAST_LIMIT));
        assert!(fails(&text).contains("вложенность"));
    }

    #[test]
    fn deep_types_are_an_error_not_a_crash() {
        let text = format!("(1 : {}Int)", "Int -> ".repeat(PAST_LIMIT));
        assert!(fails(&text).contains("вложенность"));
    }

    /// Генератор типов: листья `Int`/`Bool`, узлы - стрелки.
    fn any_type() -> impl proptest::strategy::Strategy<Value = TypeExpr> {
        use proptest::prelude::*;

        let leaf = prop_oneof![Just(TypeExpr::Int), Just(TypeExpr::Bool)];
        leaf.prop_recursive(5, 32, 2, |inner| {
            (inner.clone(), inner)
                .prop_map(|(from, to)| TypeExpr::Fun(Box::new(from), Box::new(to)))
        })
    }

    proptest::proptest! {
        /// Печать и разбор типов обязаны быть обратны друг другу. Ломается -
        /// значит расставлены не те скобки, и правоассоциативность стрелки
        /// начинает молча менять смысл аннотаций.
        #[test]
        fn printing_a_type_round_trips_through_the_parser(ty in any_type()) {
            let Kind::Annot { ty: parsed, .. } = parse(&format!("(1 : {ty})")).kind else {
                panic!("ожидалась аннотация");
            };
            proptest::prop_assert_eq!(parsed, ty);
        }
    }
}
