//! Поверхностный синтаксис: имена, спаны, сахар.
//!
//! Разворачивается в [`crate::core`] после вывода типов - диагностика (§7.4)
//! работает по спанам, а у core их уже нет.

use adamas_core::source::Span;

/// Бинарные операторы. Все примитивны: пользовательских операторов нет.
///
/// `Equal` определено только на `Int` - равенство на произвольных типах
/// требует классов, а они появляются в Фазе 3.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BinOp {
    Add,
    Sub,
    Mul,
    Less,
    Equal,
}

/// Аннотация типа. Стрелка правоассоциативна.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypeExpr {
    Int,
    Bool,
    Fun(Box<TypeExpr>, Box<TypeExpr>),
}

impl std::fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => f.write_str("Int"),
            Self::Bool => f.write_str("Bool"),
            // Стрелка правоассоциативна: скобки нужны только слева.
            Self::Fun(from, to) if matches!(**from, Self::Fun(..)) => {
                write!(f, "({from}) -> {to}")
            }
            Self::Fun(from, to) => write!(f, "{from} -> {to}"),
        }
    }
}

/// Выражение вместе со спаном.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Term {
    pub(crate) kind: Kind,
    pub(crate) span: Span,
}

/// Форма выражения.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Int(i64),
    Bool(bool),
    Var(String),
    /// `\x -> e` или `\(x : T) -> e`.
    Lambda {
        param: String,
        annotation: Option<TypeExpr>,
        body: Box<Term>,
    },
    /// `f a`, левоассоциативно.
    App(Box<Term>, Box<Term>),
    /// `let x = e in body`; при `recursive` - `let rec`.
    Let {
        name: String,
        recursive: bool,
        value: Box<Term>,
        body: Box<Term>,
    },
    If {
        cond: Box<Term>,
        then: Box<Term>,
        otherwise: Box<Term>,
    },
    /// `fix e`, где `e : a -> a`. Единственный источник рекурсии;
    /// `let rec` - сахар над ним.
    Fix(Box<Term>),
    Bin {
        op: BinOp,
        left: Box<Term>,
        right: Box<Term>,
    },
    /// `(e : T)` - переключатель в режим проверки для bidirectional-вывода.
    Annot {
        term: Box<Term>,
        ty: TypeExpr,
    },
}
