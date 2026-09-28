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
use adamas_core::pattern::{ClauseSite, Compiled, located};
use adamas_core::source::Span;
use adamas_parser::ast::{self, Binder, Binding, Chain, Expr, ExprKind, Stmt, StmtKind};

/// Места ветвей разборов, написанных выражением, по спану выражения - см.
/// [`Compiled::nested`]. У типа их нет, и туда идёт пустой срез.
pub(crate) type Cases<'a> = &'a [(Span, Vec<ClauseSite>)];

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
    /// Группа определений: `mutual`. Кадр её маршрута начинается **номером
    /// члена**, и без него каретка вставала на блок целиком - на сорок строк
    /// вместо одной клаузы.
    Group(&'a [Member<'a>]),
    /// Индуктивное семейство: тип-формер и типы конструкторов.
    Data(&'a ast::Data),
    /// Эффект: типы его операций. Формер не пишется, указывать в нём не на что.
    Effect(&'a ast::EffectDecl),
}

/// Один член группы: то же, что несёт [`Declared::Definition`].
pub(crate) struct Member<'a> {
    /// Написанный тип. `None` - написанного типа нет вовсе: тип члена инстанса
    /// выводится из класса и головы, а не пишется, и указывать в нём не на что.
    pub ty: Option<&'a Expr>,
    /// Клаузы в порядке написания.
    pub clauses: &'a [ast::Clause],
    /// Дерево разбора вместе с местами клауз в нём.
    pub compiled: &'a Compiled,
}

impl Member<'_> {
    /// Тело определения - дерево разбора, которого автор не писал. Здесь
    /// соответствие не выводится из формы, а взято у сборки.
    fn body(&self, route: &[Frame], fallback: Span) -> Span {
        self.compiled
            .locate(route)
            .and_then(|(clause, inner)| {
                self.clauses
                    .get(clause)
                    .map(|clause| narrow(&self.compiled.nested, &clause.body, inner))
            })
            .unwrap_or(fallback)
    }
}

/// Где в исходнике то, что отверг `check`.
///
/// `fallback` - спан объявления целиком: им отвечают, когда маршрут уводит в
/// область, порождённую элаборацией.
pub(crate) fn locate(declared: &Declared<'_>, error: &TypeError, fallback: Span) -> Span {
    let route: Vec<Frame> = error.path().collect();
    at(declared, &route, fallback)
}

/// То же по готовому маршруту.
///
/// Маршрут приносит не только `check`: проверка совместимости с FBIP (§5.1)
/// ходит по тому же дереву и кадры складывает те же, а перевод их в спан от
/// того, кто их сложил, не зависит.
pub(crate) fn at(declared: &Declared<'_>, route: &[Frame], fallback: Span) -> Span {
    match declared {
        Declared::Bare(ty) => narrow(&[], ty, route),
        Declared::Postulate(ty) => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => narrow(&[], ty, rest),
            _ => fallback,
        },
        Declared::Definition {
            ty,
            clauses,
            compiled,
        } => {
            let member = Member {
                ty: Some(ty),
                clauses,
                compiled,
            };
            match route.split_first() {
                Some((Frame::MemberType(_), rest)) => narrow(&[], ty, rest),
                Some((Frame::MemberBody(_), rest)) => member.body(rest, fallback),
                _ => fallback,
            }
        }
        // У группы номер члена значим: он и выбирает, в чей текст спускаться.
        Declared::Group(members) => match route.split_first() {
            Some((Frame::MemberType(index), rest)) => members
                .get(*index as usize)
                .and_then(|member| member.ty)
                .map_or(fallback, |ty| narrow(&[], ty, rest)),
            Some((Frame::MemberBody(index), rest)) => members
                .get(*index as usize)
                .map_or(fallback, |member| member.body(rest, fallback)),
            _ => fallback,
        },
        Declared::Effect(effect) => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => match rest.split_first() {
                Some((Frame::Constructor(index), inner)) => effect
                    .operations
                    .get(*index as usize)
                    .map_or(fallback, |operation| narrow(&[], &operation.ty, inner)),
                _ => fallback,
            },
            _ => fallback,
        },
        Declared::Data(data) => match route.split_first() {
            Some((Frame::MemberType(_), rest)) => match rest.split_first() {
                Some((Frame::Constructor(index), inner)) => data
                    .constructors
                    .get(*index as usize)
                    .map_or(fallback, |constructor| narrow(&[], &constructor.ty, inner)),
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
        .map_or(fallback, |kind| narrow(&[], kind, route))
}

/// Спан подтерма, названного маршрутом.
///
/// Маршрут идёт снаружи внутрь - в том порядке, в каком его отдаёт
/// [`adamas_core::check::TypeError::path`].
pub(crate) fn narrow(cases: Cases<'_>, expr: &Expr, route: &[Frame]) -> Span {
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
                return pi(cases, binders, codomain, route, expr.span);
            }
            (ExprKind::Lam { params, body }, Frame::Body) => {
                return lam(cases, params.len(), body, route, expr.span);
            }
            (ExprKind::Block(block), _) => {
                return statements(cases, &block.stmts, route, expr.span);
            }
            (ExprKind::Chain(chain), _) => return chain_at(cases, chain, route, expr.span),
            (ExprKind::Case { scrutinee, alts }, _) => {
                let bodies: Vec<&Expr> = alts.iter().map(|alt| &alt.body).collect();
                return case_at(cases, expr.span, scrutinee, &bodies, route);
            }
            (
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                },
                _,
            ) => return case_at(cases, expr.span, cond, &[then_branch, else_branch], route),
            (
                ExprKind::Handle {
                    computation,
                    branches,
                    state,
                    ..
                },
                _,
            ) => {
                let mut bodies: Vec<&Expr> = vec![computation];
                bodies.extend(branches.iter().map(|branch| &branch.body));
                bodies.extend(state.as_deref());
                return sited(cases, expr.span, &bodies, route);
            }
            _ => return expr.span,
        };
    }
}

/// `(q x y : A) (r z : B) -> C` - по `Pi` на каждое имя в группе.
fn pi(
    cases: Cases<'_>,
    binders: &[Binder],
    codomain: &Expr,
    route: &[Frame],
    fallback: Span,
) -> Span {
    let mut route = route;
    for binder in binders {
        for _ in &binder.names {
            match route.split_first() {
                Some((Frame::Domain, rest)) => {
                    return binder
                        .ty
                        .as_ref()
                        .map_or(binder.span, |ty| narrow(cases, ty, rest));
                }
                Some((Frame::Codomain, rest)) => route = rest,
                _ => return fallback,
            }
        }
    }
    narrow(cases, codomain, route)
}

/// `\x y -> body` - по `Lam` на каждый параметр.
fn lam(cases: Cases<'_>, params: usize, body: &Expr, route: &[Frame], fallback: Span) -> Span {
    let mut route = route;
    for _ in 0..params {
        match route.split_first() {
            Some((Frame::Body, rest)) => route = rest,
            _ => return fallback,
        }
    }
    narrow(cases, body, route)
}

/// Блок: цепочка `let` и значение последним.
fn statements(cases: Cases<'_>, stmts: &[Stmt], route: &[Frame], fallback: Span) -> Span {
    let Some((first, rest)) = stmts.split_first() else {
        return fallback;
    };
    match &first.kind {
        StmtKind::Expr(expr) if rest.is_empty() => narrow(cases, expr, route),
        StmtKind::Let(bindings) => let_bindings(cases, bindings, rest, route, fallback),
        StmtKind::Expr(_) => fallback,
    }
}

/// Связывания одного `let`: каждое даёт узел `Let`, вложенный в следующее.
fn let_bindings(
    cases: Cases<'_>,
    bindings: &[Binding],
    rest: &[Stmt],
    route: &[Frame],
    fallback: Span,
) -> Span {
    let Some((binding, tail)) = bindings.split_first() else {
        return statements(cases, rest, route, fallback);
    };
    match route.split_first() {
        Some((Frame::BindingType, inner)) => binding
            .ty
            .as_ref()
            .map_or(binding.span, |ty| narrow(cases, ty, inner)),
        Some((Frame::BindingValue, inner)) => narrow(cases, &binding.body, inner),
        Some((Frame::BindingBody, inner)) => let_bindings(cases, tail, rest, inner, fallback),
        _ => binding.span,
    }
}

/// Цепочка из одного оператора: `op left right`, то есть два применения.
fn chain_at(cases: Cases<'_>, chain: &Chain, route: &[Frame], fallback: Span) -> Span {
    let [(operator, operand)] = &chain.tail[..] else {
        return fallback;
    };
    match route {
        [Frame::Argument, rest @ ..] => narrow(cases, operand, rest),
        [Frame::Callee, Frame::Argument, rest @ ..] => narrow(cases, &chain.head, rest),
        [Frame::Callee, Frame::Callee, ..] => operator.span,
        _ => fallback,
    }
}

/// Разбор выражением: `case e of …` и `if c then … else …` (§10 вопрос 217).
///
/// Разбираемое не переменная - и элаборация связывает его `let`, дерево
/// разбора стоит телом; переменная - и дерево стоит само. Внутри дерева
/// ветвь находится по записанным местам альтернатив: номер ветви в ядре -
/// номер конструктора, а не альтернативы, и без мест его не перевести.
/// `if` - те же две альтернативы, `then` первой.
fn case_at(
    cases: Cases<'_>,
    span: Span,
    scrutinee: &Expr,
    bodies: &[&Expr],
    route: &[Frame],
) -> Span {
    let tree = match route.split_first() {
        Some((Frame::BindingValue, rest)) => return narrow(cases, scrutinee, rest),
        Some((Frame::BindingBody, rest)) => rest,
        _ => route,
    };
    sited(cases, span, bodies, tree)
}

/// Написанное, до которого маршрут доходит по записанным местам: альтернатива
/// разбора, ветка хендлера, его вычисление или начальное состояние. Мест
/// нет или маршрут в них не лёг - спан самой формы.
fn sited(cases: Cases<'_>, span: Span, bodies: &[&Expr], route: &[Frame]) -> Span {
    // Проход элаборации бывает пробным, и одна форма записывается дважды:
    // последняя запись - та, что ушла в терм.
    cases
        .iter()
        .rev()
        .find(|(at, _)| *at == span)
        .and_then(|(_, sites)| located(sites, route))
        .and_then(|(alt, inner)| bodies.get(alt).map(|body| narrow(cases, body, inner)))
        .unwrap_or(span)
}
