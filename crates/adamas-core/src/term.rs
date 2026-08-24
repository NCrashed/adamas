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

impl Index {
    /// Уровень, на который указывает индекс в контексте размера `size`.
    ///
    /// Обратна [`crate::value::Lvl::to_index`]. `None`, если индекс за
    /// пределами контекста, - в отличие от обратной операции, здесь это
    /// нормальный исход: индекс приходит из терма, а терм может быть
    /// незамкнутым, и отвечать на это должен проверяющий, а не паника.
    #[must_use]
    pub fn to_level(self, size: u32) -> Option<crate::value::Lvl> {
        size.checked_sub(self.0)
            .and_then(|distance| distance.checked_sub(1))
            .map(crate::value::Lvl)
    }
}

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
    /// `let q x : ty = value in body`.
    ///
    /// Кратность здесь по той же причине, что и на `Pi`: связывание тратит
    /// значение, и без неё `let 1 h = openFile … in …` нечем выразить.
    Let(Mult, Name, Rc<Term>, Rc<Term>, Rc<Term>),
    /// Ссылка на определение из [`crate::sig::Signature`] с явными
    /// аргументами уровня.
    ///
    /// Universe polymorphism пока явная: аргументы пишутся руками. Вывод их
    /// через level-метапеременные - следующий срез; представление от этого не
    /// изменится, поменяется только то, кто заполняет список.
    Const(Name, Rc<[Level]>),
    /// Разбор значения индуктивного типа по конструктору.
    Case(Rc<Case>),
}

/// Разбор значения индуктивного типа по конструктору (§9 Фаза 1).
///
/// **Собственных связываний узел не вводит.** И мотив, и ветви - обычные термы
/// функционального типа: мотив ждёт индексы и само разбираемое значение и
/// выдаёт тип результата, ветвь ждёт поля своего конструктора. Из-за этого
/// `case` не участвует в сдвигах индексов вовсе, а η-правило и проверка
/// кратностей достаются ему от правила лямбды даром - ветвь проверяется
/// ровно как функция от полей.
///
/// Мотив обязателен: без него `case` не может быть зависимым, а тип результата
/// брался бы из режима проверки, и тогда `case` перестал бы синтезировать
/// собственный тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Case {
    /// Индуктивный тип, по которому идёт разбор.
    pub data: Name,
    /// Аргументы уровня этого типа.
    pub levels: Rc<[Level]>,
    /// Сколько первых аргументов конструктора - параметры.
    ///
    /// Ветвь их не получает: они определены типом разбираемого значения, а не
    /// выбором конструктора. Число дублирует сигнатуру затем, чтобы
    /// [`crate::eval`] обходился без неё; проверка типов сверяет.
    pub params: u32,
    /// Что разбирается.
    pub scrutinee: Rc<Term>,
    /// Мотив: `(0 i⃗ : I) -> (0 x : D levels params i⃗) -> Type ℓ`.
    pub motive: Rc<Term>,
    /// Ветви в порядке объявления конструкторов.
    pub branches: Vec<Branch>,
}

/// Ветвь разбора - функция от полей конструктора.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branch {
    /// Конструктор, который она разбирает.
    pub constructor: Name,
    /// Тело: функция от полей, идущих после параметров.
    pub body: Rc<Term>,
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

    /// Ссылка на определение без параметров уровня.
    #[must_use]
    pub fn constant(name: &str) -> Self {
        Self::Const(name.into(), Rc::from([]))
    }

    /// Подставляет аргументы вместо параметров уровня по всему терму.
    ///
    /// Так тип определения инстанцируется в месте использования.
    #[must_use]
    pub fn substitute_levels(&self, arguments: &[Level]) -> Self {
        let recur = |term: &Rc<Self>| Rc::new(term.substitute_levels(arguments));
        match self {
            Self::Var(_) => self.clone(),
            Self::Universe(level) => Self::Universe(level.substitute(arguments)),
            Self::Lam(mult, name, body) => Self::Lam(*mult, Rc::clone(name), recur(body)),
            Self::App(callee, argument) => Self::App(recur(callee), recur(argument)),
            Self::Pi(mult, name, domain, codomain) => {
                Self::Pi(*mult, Rc::clone(name), recur(domain), recur(codomain))
            }
            Self::Let(mult, name, ty, value, body) => {
                Self::Let(*mult, Rc::clone(name), recur(ty), recur(value), recur(body))
            }
            Self::Const(name, levels) => Self::Const(
                Rc::clone(name),
                levels
                    .iter()
                    .map(|level| level.substitute(arguments))
                    .collect(),
            ),
            Self::Case(case) => Self::Case(Rc::new(Case {
                data: Rc::clone(&case.data),
                levels: case
                    .levels
                    .iter()
                    .map(|level| level.substitute(arguments))
                    .collect(),
                params: case.params,
                scrutinee: recur(&case.scrutinee),
                motive: recur(&case.motive),
                branches: case
                    .branches
                    .iter()
                    .map(|branch| Branch {
                        constructor: Rc::clone(&branch.constructor),
                        body: recur(&branch.body),
                    })
                    .collect(),
            })),
        }
    }

    /// Наибольший индекс параметра уровня, встречающийся в терме.
    #[must_use]
    pub fn max_level_var(&self) -> Option<u32> {
        let join = |a: Option<u32>, b: Option<u32>| match (a, b) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (found, None) | (None, found) => found,
        };
        match self {
            Self::Var(_) => None,
            Self::Universe(level) => level.max_var(),
            Self::Lam(_, _, body) => body.max_level_var(),
            Self::App(callee, argument) => join(callee.max_level_var(), argument.max_level_var()),
            Self::Pi(_, _, domain, codomain) => {
                join(domain.max_level_var(), codomain.max_level_var())
            }
            Self::Let(_, _, ty, value, body) => join(
                ty.max_level_var(),
                join(value.max_level_var(), body.max_level_var()),
            ),
            Self::Const(_, levels) => levels
                .iter()
                .fold(None, |found, level| join(found, level.max_var())),
            Self::Case(case) => {
                let levels = case
                    .levels
                    .iter()
                    .fold(None, |found, level| join(found, level.max_var()));
                let branches = case.branches.iter().fold(None, |found, branch| {
                    join(found, branch.body.max_level_var())
                });
                join(
                    join(levels, branches),
                    join(case.scrutinee.max_level_var(), case.motive.max_level_var()),
                )
            }
        }
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
            Self::Let(mult, name, ty, value, body) => {
                write!(f, "let {mult} {name} : {ty} = {value} in {body}")
            }
            Self::Const(name, levels) if levels.is_empty() => write!(f, "{name}"),
            Self::Const(name, levels) => {
                let printed: Vec<String> = levels.iter().map(ToString::to_string).collect();
                write!(f, "{name}{{{}}}", printed.join(", "))
            }
            // Имя типа не печатается: оно восстанавливается по конструкторам
            // ветвей, а сообщения об ошибках и без него длинные.
            Self::Case(case) => {
                let branches: Vec<String> = case
                    .branches
                    .iter()
                    .map(|branch| format!("{} => {}", branch.constructor, branch.body))
                    .collect();
                write!(
                    f,
                    "case {} return {} of {{{}}}",
                    Atom(&case.scrutinee),
                    Atom(&case.motive),
                    branches.join("; ")
                )
            }
        }
    }
}

/// Позиция функции: применение слева от применения скобок не требует.
struct Callee<'a>(&'a Term);

impl fmt::Display for Callee<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_) | Term::Universe(_) | Term::Const(..) | Term::App(..) => {
                write!(f, "{}", self.0)
            }
            other => write!(f, "({other})"),
        }
    }
}

/// Позиция аргумента: всё составное берётся в скобки.
struct Atom<'a>(&'a Term);

impl fmt::Display for Atom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_) | Term::Universe(_) | Term::Const(..) => write!(f, "{}", self.0),
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
