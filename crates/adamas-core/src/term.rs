//! Термы core-языка (§3.2).
//!
//! Переменные - индексы де Брёйна: `Index(0)` указывает на ближайшее
//! связывание. Значения (`crate::value`) используют уровни, считающие с
//! другого конца; пара "индексы в термах, уровни в значениях" - обычная для
//! `NbE`, потому что делает подстановку в замыканиях бесплатной.
//!
//! Имена хранятся только для печати. Единственный источник истины о том, на
//! что ссылается переменная, - индекс.

use std::fmt;
use std::rc::Rc;

use crate::level::Level;
use crate::mult::Mult;

/// Индекс де Брёйна: сколько связываний отсчитать наружу.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Index(pub u32);

/// Имя для печати. На семантику не влияет.
pub type Name = Rc<str>;

/// Терм core-языка.
///
/// Зависимых пар (`(q x : A) ** B` из §3.2) здесь пока нет - они добавляются
/// вместе с индуктивными типами, механика та же, что у `Pi`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// Переменная.
    Var(Index),
    /// `\(q x : _) -> body`. Тип параметра в терме не хранится: его знает
    /// проверяющий из ожидаемого `Pi`.
    Lam(Mult, Name, Rc<Term>),
    /// Применение.
    App(Rc<Term>, Rc<Term>),
    /// Зависимая функция `(q x : domain) -> codomain`.
    Pi(Mult, Name, Rc<Term>, Rc<Term>),
    /// `Type level`.
    Universe(Level),
    /// `let x : ty = value in body`.
    Let(Name, Rc<Term>, Rc<Term>, Rc<Term>),
}

impl Term {
    /// Переменная по индексу.
    #[must_use]
    pub fn var(index: u32) -> Self {
        Self::Var(Index(index))
    }

    /// `Type n`.
    #[must_use]
    pub fn universe(level: u32) -> Self {
        Self::Universe(Level::number(level))
    }

    /// Применение к нескольким аргументам, левоассоциативно.
    #[must_use]
    pub fn apply(self, arguments: impl IntoIterator<Item = Self>) -> Self {
        arguments.into_iter().fold(self, |callee, argument| {
            Self::App(Rc::new(callee), Rc::new(argument))
        })
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Имя не печатается: одно и то же имя может быть у разных
            // связываний, а индекс однозначен.
            Self::Var(Index(index)) => write!(f, "#{index}"),
            Self::Universe(level) => write!(f, "Type {level}"),
            Self::Lam(mult, name, body) => write!(f, "\\({mult} {name}) -> {body}"),
            Self::App(callee, argument) => {
                write!(f, "{} {}", Callee(callee), Atom(argument))
            }
            Self::Pi(mult, name, domain, codomain) => {
                write!(f, "({mult} {name} : {domain}) -> {codomain}")
            }
            Self::Let(name, ty, value, body) => {
                write!(f, "let {name} : {ty} = {value} in {body}")
            }
        }
    }
}

/// Позиция функции: применение слева от применения скобок не требует.
struct Callee<'a>(&'a Term);

impl fmt::Display for Callee<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_) | Term::Universe(_) | Term::App(..) => write!(f, "{}", self.0),
            other => write!(f, "({other})"),
        }
    }
}

/// Позиция аргумента: всё составное берётся в скобки.
struct Atom<'a>(&'a Term);

impl fmt::Display for Atom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_) | Term::Universe(_) => write!(f, "{}", self.0),
            other => write!(f, "({other})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::Term;
    use crate::mult::Mult;

    #[test]
    fn application_prints_left_associatively() {
        let term = Term::var(0).apply([Term::var(1), Term::var(2)]);
        assert_eq!(term.to_string(), "#0 #1 #2");
    }

    #[test]
    fn arguments_are_parenthesised() {
        let identity = Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)));
        let term = Term::var(0).apply([identity]);
        assert_eq!(term.to_string(), "#0 (\\(ω x) -> #0)");
    }

    #[test]
    fn pi_shows_its_multiplicity() {
        let pi = Term::Pi(
            Mult::Zero,
            "a".into(),
            Rc::new(Term::universe(0)),
            Rc::new(Term::var(0)),
        );
        assert_eq!(pi.to_string(), "(0 a : Type 0) -> #0");
    }
}
