//! Маршрут ядра в спан исходника (§10 вопрос 49б).
//!
//! Ядро отвергает **терм**, а показать надо место в тексте. Спанов на узлах
//! терма нет и не будет - идентичность узла не переживает нормализацию, - зато
//! есть маршрут кадрами. Здесь он проходится второй раз, по дереву
//! поверхностного языка.
//!
//! # Соответствие держится тем же кодом, что его строит
//!
//! Терм не изоморфен дереву: группа связываний `(x y : A)` разворачивается в
//! два `Pi`, лямбда с двумя параметрами - в две `Lam`, цепочка операторов - в
//! два применения. Правила разворота живут в [`crate::expr`], и здесь они
//! повторены **по одному на форму**: разъехаться они могут только вместе с
//! правилом, то есть заметно.
//!
//! # Где маршрут кончается
//!
//! Кадр, не ложащийся на узел, - не ошибка. Это область, порождённая
//! элаборацией: дерево разбора клауз, лямбды, которых автор не писал. Проход
//! останавливается и отдаёт спан того узла, до которого дошёл. Диагностика от
//! этого теряет точность, но не правдивость - указано место, внутри которого
//! отказ действительно случился.
//!
//! Тела клауз - исключение: там соответствие не выводится, а записывается
//! сборкой дерева ([`adamas_core::pattern::Compiled`]).

use adamas_core::check::{Frame, TypeError};
use adamas_core::pattern::Compiled;
use adamas_core::source::Span;
use adamas_parser::ast::{self, Binder, Binding, Chain, Expr, ExprKind, Stmt, StmtKind};

/// Что элаборация отдала ядру - то, по чему маршрут пойдёт обратно.
pub(crate) enum Declared<'a> {
    /// Тип сам по себе: маршрут начинается прямо с него, без объявления
    /// вокруг. Так его проверяет сборка клауз, которой имя ещё не нужно.
    Bare(&'a Expr),
    /// Постулат: у объявления есть только тип.
    Postulate(&'a Expr),
    /// Определение клаузами: тип, клаузы и дерево, собранное из них.
    Definition {
        /// Написанный тип.
        ty: &'a Expr,
        /// Клаузы в порядке написания.
        clauses: &'a [ast::Clause],
        /// Дерево разбора вместе с местами клауз в нём.
        compiled: &'a Compiled,
    },
    /// Индуктивное семейство: тип-формер и типы конструкторов.
    Data(&'a ast::Data),
}

/// Где в исходнике то, что отверг `check`.
///
/// `fallback` - спан объявления целиком: им отвечают, когда маршрут уводит в
/// область, порождённую элаборацией.
pub(crate) fn locate(declared: &Declared<'_>, error: &TypeError, fallback: Span) -> Span {
    let route: Vec<Frame> = error.path().collect();
    match declared {
        Declared::Bare(ty) => narrow(ty, &route),
        Declared::Postulate(ty) => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => narrow(ty, rest),
            _ => fallback,
        },
        Declared::Definition {
            ty,
            clauses,
            compiled,
        } => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => narrow(ty, rest),
            // Тело определения - дерево разбора, которого автор не писал.
            // Здесь соответствие не выводится из формы, а взято у сборки.
            Some((Frame::MemberBody(_), rest)) => compiled
                .locate(rest)
                .and_then(|(clause, inner)| {
                    clauses
                        .get(clause)
                        .map(|clause| narrow(&clause.body, inner))
                })
                .unwrap_or(fallback),
            _ => fallback,
        },
        Declared::Data(data) => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => match rest.split_first() {
                Some((Frame::Constructor(index), inner)) => data
                    .constructors
                    .get(*index as usize)
                    .map_or(fallback, |constructor| narrow(&constructor.ty, inner)),
                _ => data_kind(data, rest, fallback),
            },
            _ => fallback,
        },
    }
}

/// Тип-формер семейства. Параметров у него нет - их отвергает элаборация, -
/// поэтому маршрут идёт прямо по написанному; ненаписанный тип-формер это
/// `Type 0`, и указывать в нём не на что.
fn data_kind(data: &ast::Data, route: &[Frame], fallback: Span) -> Span {
    data.kind
        .as_ref()
        .map_or(fallback, |kind| narrow(kind, route))
}

/// Спан подтерма, названного маршрутом.
///
/// Маршрут идёт снаружи внутрь - в том порядке, в каком его отдаёт
/// [`adamas_core::check::TypeError::path`].
pub(crate) fn narrow(expr: &Expr, route: &[Frame]) -> Span {
    // Спуск по узлам с одним кадром идёт циклом, а не рекурсией: спайн
    // применения длиной в тысячи кадров - обычный вход (см. `expr` в
    // [`crate::expr`]).
    let mut expr = expr;
    let mut route = route;
    loop {
        let Some((frame, rest)) = route.split_first() else {
            return expr.span;
        };
        (expr, route) = match (&expr.kind, frame) {
            (ExprKind::App(callee, _), Frame::Callee) => (&**callee, rest),
            (ExprKind::App(_, argument), Frame::Argument) => (&**argument, rest),
            (ExprKind::Arrow(domain, _), Frame::Domain) => (&**domain, rest),
            (ExprKind::Arrow(_, codomain), Frame::Codomain) => (&**codomain, rest),
            (ExprKind::Pi { binders, codomain }, _) => {
                return pi(binders, codomain, route, expr.span);
            }
            (ExprKind::Lam { params, body }, Frame::Body) => {
                return lam(params.len(), body, route, expr.span);
            }
            (ExprKind::Block(block), _) => return statements(&block.stmts, route, expr.span),
            (ExprKind::Chain(chain), _) => return chain_at(chain, route, expr.span),
            _ => return expr.span,
        };
    }
}

/// `(q x y : A) (r z : B) -> C` - по `Pi` на каждое имя в группе.
fn pi(binders: &[Binder], codomain: &Expr, route: &[Frame], fallback: Span) -> Span {
    let mut route = route;
    for binder in binders {
        for _ in &binder.names {
            match route.split_first() {
                Some((Frame::Domain, rest)) => {
                    return binder
                        .ty
                        .as_ref()
                        .map_or(binder.span, |ty| narrow(ty, rest));
                }
                Some((Frame::Codomain, rest)) => route = rest,
                _ => return fallback,
            }
        }
    }
    narrow(codomain, route)
}

/// `\x y -> body` - по `Lam` на каждый параметр.
fn lam(params: usize, body: &Expr, route: &[Frame], fallback: Span) -> Span {
    let mut route = route;
    for _ in 0..params {
        match route.split_first() {
            Some((Frame::Body, rest)) => route = rest,
            _ => return fallback,
        }
    }
    narrow(body, route)
}

/// Блок: цепочка `let` и значение последним.
fn statements(stmts: &[Stmt], route: &[Frame], fallback: Span) -> Span {
    let Some((first, rest)) = stmts.split_first() else {
        return fallback;
    };
    match &first.kind {
        StmtKind::Expr(expr) if rest.is_empty() => narrow(expr, route),
        StmtKind::Let(bindings) => let_bindings(bindings, rest, route, fallback),
        StmtKind::Expr(_) => fallback,
    }
}

/// Связывания одного `let`: каждое даёт узел `Let`, вложенный в следующее.
fn let_bindings(bindings: &[Binding], rest: &[Stmt], route: &[Frame], fallback: Span) -> Span {
    let Some((binding, tail)) = bindings.split_first() else {
        return statements(rest, route, fallback);
    };
    match route.split_first() {
        Some((Frame::BindingType, inner)) => binding
            .ty
            .as_ref()
            .map_or(binding.span, |ty| narrow(ty, inner)),
        Some((Frame::BindingValue, inner)) => narrow(&binding.body, inner),
        Some((Frame::BindingBody, inner)) => let_bindings(tail, rest, inner, fallback),
        _ => binding.span,
    }
}

/// Цепочка из одного оператора: `op left right`, то есть два применения.
fn chain_at(chain: &Chain, route: &[Frame], fallback: Span) -> Span {
    let [(operator, operand)] = &chain.tail[..] else {
        return fallback;
    };
    match route {
        [Frame::Argument, rest @ ..] => narrow(operand, rest),
        [Frame::Callee, Frame::Argument, rest @ ..] => narrow(&chain.head, rest),
        [Frame::Callee, Frame::Callee, ..] => operator.span,
        _ => fallback,
    }
}
