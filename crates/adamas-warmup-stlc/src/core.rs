//! Core-язык: то, что остаётся после элаборации.
//!
//! Три отличия от [`crate::syntax`]: имён нет (индексы де Брёйна), спанов нет
//! (вся диагностика выдана раньше), сахара нет - `let` развёрнут в применение
//! лямбды, `let rec` в применение к `fix`, аннотации стёрты.

use std::rc::Rc;

use crate::syntax::{BinOp, Kind, Term};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Expr {
    Int(i64),
    Bool(bool),
    /// Индекс де Брёйна: сколько связываний отсчитать наружу.
    Var(usize),
    Lam(Rc<Expr>),
    App(Rc<Expr>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Fix(Rc<Expr>),
    Bin(BinOp, Rc<Expr>, Rc<Expr>),
}

/// Опускает поверхностный терм в core.
///
/// # Panics
///
/// На несвязанной переменной. [`crate::infer`] отвергает такие программы
/// раньше, поэтому дойти сюда они могут только при поломке компилятора.
pub(crate) fn lower(term: &Term) -> Expr {
    (*lower_in(term, &mut Vec::new())).clone()
}

fn lower_in(term: &Term, scope: &mut Vec<String>) -> Rc<Expr> {
    match &term.kind {
        Kind::Int(value) => Rc::new(Expr::Int(*value)),
        Kind::Bool(value) => Rc::new(Expr::Bool(*value)),

        Kind::Var(name) => {
            let position = scope
                .iter()
                .rposition(|bound| bound == name)
                .unwrap_or_else(|| {
                    unreachable!("несвязанная переменная `{name}` дошла до элаборации")
                });
            Rc::new(Expr::Var(scope.len() - 1 - position))
        }

        Kind::Lambda { param, body, .. } => {
            Rc::new(Expr::Lam(bind(scope, param, |scope| lower_in(body, scope))))
        }

        Kind::App(callee, argument) => Rc::new(Expr::App(
            lower_in(callee, scope),
            lower_in(argument, scope),
        )),

        // `let x = v in b`  ==>  `(\x -> b) v`
        // `let rec x = v in b`  ==>  `(\x -> b) (fix (\x -> v))`
        Kind::Let {
            name,
            recursive,
            value,
            body,
        } => {
            let bound = if *recursive {
                Rc::new(Expr::Fix(Rc::new(Expr::Lam(bind(scope, name, |scope| {
                    lower_in(value, scope)
                })))))
            } else {
                lower_in(value, scope)
            };
            let abstraction = Rc::new(Expr::Lam(bind(scope, name, |scope| lower_in(body, scope))));
            Rc::new(Expr::App(abstraction, bound))
        }

        Kind::If {
            cond,
            then,
            otherwise,
        } => Rc::new(Expr::If(
            lower_in(cond, scope),
            lower_in(then, scope),
            lower_in(otherwise, scope),
        )),

        Kind::Fix(inner) => Rc::new(Expr::Fix(lower_in(inner, scope))),

        Kind::Bin { op, left, right } => Rc::new(Expr::Bin(
            *op,
            lower_in(left, scope),
            lower_in(right, scope),
        )),

        // Аннотации стираются вместе с типами: core не типизирован.
        Kind::Annot { term: inner, .. } => lower_in(inner, scope),
    }
}

fn bind<T>(scope: &mut Vec<String>, name: &str, action: impl FnOnce(&mut Vec<String>) -> T) -> T {
    scope.push(name.to_owned());
    let result = action(scope);
    scope.pop();
    result
}

#[cfg(test)]
mod tests {
    use adamas_core::source::SourceFile;

    use super::{Expr, lower};
    use crate::{lexer, parser};

    fn compile(text: &str) -> Expr {
        let file = SourceFile::new("test.stlc", text);
        let tokens = lexer::tokenize(file.text()).unwrap();
        lower(&parser::parse(&tokens).unwrap())
    }

    #[test]
    fn shadowing_disappears_into_indices() {
        // Внешний и внутренний `x` различаются только индексом.
        let Expr::Lam(outer) = compile("\\x -> \\x -> x") else {
            panic!("ожидалась лямбда");
        };
        assert_eq!(*outer, Expr::Lam(std::rc::Rc::new(Expr::Var(0))));
    }

    #[test]
    fn let_becomes_an_application() {
        assert!(matches!(compile("let x = 1 in x"), Expr::App(..)));
    }

    #[test]
    fn let_rec_introduces_fix() {
        let Expr::App(_, bound) = compile("let rec f = \\x -> f x in f") else {
            panic!("ожидалось применение");
        };
        assert!(matches!(*bound, Expr::Fix(_)));
    }

    #[test]
    fn annotations_are_erased() {
        assert_eq!(compile("(1 : Int)"), Expr::Int(1));
    }
}
