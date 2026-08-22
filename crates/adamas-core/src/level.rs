//! Уровни универсумов (§3.2): отдельный сорт с `zero`, `suc`, `max`, `imax`.
//!
//! Уровни - алгебраические выражения, а не числа: `Type (max u (suc v))`
//! возникает сразу, как только сигнатура полиморфна по уровню.
//!
//! `imax u v` - уровень `Pi`-типа: он равен `0`, когда кодомен живёт в `Type 0`
//! (иначе предложения не были бы замкнуты относительно импликации), и `max u v`
//! в остальных случаях. Пока `v` неизвестна, выражение остаётся символьным.
//!
//! # Равенство
//!
//! Производный `Eq` - структурный, он нужен только чтобы класть уровни в
//! `BTreeMap`. Семантическое равенство - [`Level::equiv`]: оно **корректно**
//! (равными признаёт только те уровни, что совпадают при любой подстановке) и
//! **неполно** на `imax`. Известный незакрытый случай: `max u (imax w v)` при
//! `u >= w` равно `max u v`, но это правило контекстное - оно зависит от
//! соседей по `max`, а применение его к промежуточным группировкам ломает
//! ассоциативность нормальной формы. Неполнота отвергает корректную программу,
//! неверность приняла бы некорректную, поэтому граница проведена здесь
//! (§10 вопрос 2).

use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

/// Переменная уровня - параметр universe polymorphism.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelVar(pub u32);

/// Выражение уровня.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    /// `Type 0` - самый нижний универсум.
    Zero,
    /// На единицу выше.
    Succ(Rc<Level>),
    /// Верхняя грань.
    Max(Rc<Level>, Rc<Level>),
    /// `imax u v`: `0`, если `v` равно `0`, иначе `max u v`.
    IMax(Rc<Level>, Rc<Level>),
    /// Параметр, по которому определение полиморфно.
    Var(LevelVar),
}

impl Level {
    /// Уровень из числа: `Level::number(2)` - это `suc (suc zero)`.
    #[must_use]
    pub fn number(n: u32) -> Self {
        (0..n).fold(Self::Zero, |level, _| Self::Succ(Rc::new(level)))
    }

    /// `suc self`.
    #[must_use]
    pub fn succ(self) -> Self {
        Self::Succ(Rc::new(self))
    }

    /// `max self other`.
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        Self::Max(Rc::new(self), Rc::new(other))
    }

    /// `imax self other` - уровень зависимой функции из `self` в `other`.
    #[must_use]
    pub fn imax(self, other: Self) -> Self {
        Self::IMax(Rc::new(self), Rc::new(other))
    }

    /// Семантическое равенство: оба уровня приводятся к нормальной форме.
    #[must_use]
    pub fn equiv(&self, other: &Self) -> bool {
        Parts::of(self) == Parts::of(other)
    }

    /// Нормальная форма - канонический представитель класса эквивалентности.
    #[must_use]
    pub fn normalize(&self) -> Self {
        Parts::of(self).rebuild()
    }

    /// Значение уровня при конкретных значениях переменных.
    ///
    /// Переменная, которой нет в `assignment`, считается нулём. Это
    /// определение уровня по смыслу, без всякой нормализации: `equiv` обязана
    /// совпадать с ним на любой подстановке, и property-тесты проверяют это в
    /// обе стороны.
    #[must_use]
    pub fn evaluate(&self, assignment: &dyn Fn(LevelVar) -> u32) -> u32 {
        match self {
            Self::Zero => 0,
            Self::Succ(inner) => inner.evaluate(assignment) + 1,
            Self::Var(var) => assignment(*var),
            Self::Max(left, right) => left.evaluate(assignment).max(right.evaluate(assignment)),
            Self::IMax(left, right) => match right.evaluate(assignment) {
                0 => 0,
                value => left.evaluate(assignment).max(value),
            },
        }
    }
}

/// Уровень как `max` набора атомов со смещениями плюс числовая константа.
///
/// `max (suc u) (suc (suc 0))` становится `{константа: 2, u: 1}`. Такая форма
/// делает коммутативность, ассоциативность и идемпотентность `max`
/// синтаксическим равенством, а не отдельными правилами.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Parts {
    constant: u32,
    /// Атом - то, что не раскладывается дальше: переменная либо застрявший
    /// `imax`. Значение - наибольшее смещение, с которым атом встречается.
    atoms: BTreeMap<Level, u32>,
}

impl Parts {
    fn of(level: &Level) -> Self {
        match level {
            Level::Zero => Self {
                constant: 0,
                atoms: BTreeMap::new(),
            },
            Level::Succ(inner) => Self::of(inner).shift(),
            Level::Max(left, right) => Self::of(left).join(Self::of(right)),
            Level::Var(_) => Self::atom(level.clone()),
            Level::IMax(left, right) => {
                let right_parts = Self::of(right);
                if right_parts.is_zero() {
                    // imax u 0 = 0 - Pi в Type 0 остаётся в Type 0.
                    return Self {
                        constant: 0,
                        atoms: BTreeMap::new(),
                    };
                }
                if right_parts.constant > 0 {
                    // Правая часть заведомо не ноль, значит imax = max.
                    return Self::of(left).join(right_parts);
                }

                // Дальше правая часть символьная: ноль она или нет, станет
                // известно только после подстановки. Но часть тождеств от её
                // значения не зависит.
                let left_parts = Self::of(left);

                // imax u v = v, если u <= max 1 v при любой подстановке.
                //
                // При v = 0 обе стороны нули независимо от u. При v >= 1
                // выражение равно max u v, а max 1 v = v, так что условие
                // сводится к u <= v - ровно тому, при котором max u v = v.
                //
                // Через это одно неравенство проходят все ходовые случаи:
                // u = 0 (уровень Pi, чей домен живёт в Type 0), u = 1 и
                // u = v.
                let bumped = Self::of(&right_parts.rebuild().max(Level::number(1)));
                if left_parts.clone().join(bumped.clone()) == bumped {
                    return right_parts;
                }
                // imax u (imax v w) = imax (max u v) w: при w = 0 обе стороны
                // 0, иначе внутренний imax ненулевой и оба сводятся к
                // max u (max v w). Правый аргумент убывает, рекурсия конечна.
                if let Some(Level::IMax(inner_left, inner_right)) = right_parts.single_atom() {
                    return Self::of(&Level::IMax(
                        Rc::new(left_parts.rebuild().max((**inner_left).clone())),
                        Rc::clone(inner_right),
                    ));
                }

                Self::atom(Level::IMax(
                    Rc::new(left_parts.rebuild()),
                    Rc::new(right_parts.rebuild()),
                ))
            }
        }
    }

    fn atom(level: Level) -> Self {
        Self {
            constant: 0,
            atoms: BTreeMap::from([(level, 0)]),
        }
    }

    fn is_zero(&self) -> bool {
        self.constant == 0 && self.atoms.is_empty()
    }

    /// Единственный атом с нулевым смещением и без константы, если он такой
    /// один. Именно в этой форме застревает `imax`.
    fn single_atom(&self) -> Option<&Level> {
        if self.constant > 0 || self.atoms.len() != 1 {
            return None;
        }
        self.atoms
            .iter()
            .next()
            .and_then(|(atom, offset)| (*offset == 0).then_some(atom))
    }

    fn shift(mut self) -> Self {
        self.constant += 1;
        for offset in self.atoms.values_mut() {
            *offset += 1;
        }
        self
    }

    fn join(mut self, other: Self) -> Self {
        self.constant = self.constant.max(other.constant);
        for (atom, offset) in other.atoms {
            self.atoms
                .entry(atom)
                .and_modify(|current| *current = (*current).max(offset))
                .or_insert(offset);
        }
        self
    }

    /// Собирает уровень обратно. Порядок задан `BTreeMap`, поэтому результат
    /// зависит только от класса эквивалентности, а не от того, как выражение
    /// было записано.
    fn rebuild(&self) -> Level {
        let mut result =
            (self.constant > 0 || self.atoms.is_empty()).then(|| Level::number(self.constant));

        for (atom, offset) in &self.atoms {
            let shifted = (0..*offset).fold(atom.clone(), |level, _| level.succ());
            result = Some(match result {
                Some(accumulated) => accumulated.max(shifted),
                None => shifted,
            });
        }
        result.unwrap_or(Level::Zero)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("0"),
            Self::Var(LevelVar(index)) => write!(f, "u{index}"),
            Self::Succ(_) => {
                // Цепочка `suc` печатается числом либо как `u+n`.
                let (base, offset) = peel(self);
                match base {
                    Self::Zero => write!(f, "{offset}"),
                    other => write!(f, "{other}+{offset}"),
                }
            }
            Self::Max(left, right) => write!(f, "max {} {}", Paren(left), Paren(right)),
            Self::IMax(left, right) => write!(f, "imax {} {}", Paren(left), Paren(right)),
        }
    }
}

/// Снимает цепочку `suc`, возвращая основание и её длину.
fn peel(level: &Level) -> (&Level, u32) {
    let mut current = level;
    let mut offset = 0;
    while let Level::Succ(inner) = current {
        current = inner;
        offset += 1;
    }
    (current, offset)
}

/// Скобки вокруг составного уровня; атомарные печатаются как есть.
struct Paren<'a>(&'a Level);

impl fmt::Display for Paren<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Level::Max(..) | Level::IMax(..) => write!(f, "({})", self.0),
            other => write!(f, "{other}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Level, LevelVar};

    fn u() -> Level {
        Level::Var(LevelVar(0))
    }

    fn v() -> Level {
        Level::Var(LevelVar(1))
    }

    #[test]
    fn max_is_commutative_associative_and_idempotent() {
        assert!(u().max(v()).equiv(&v().max(u())));
        assert!(u().max(u()).equiv(&u()));
        assert!(
            u().max(v())
                .max(Level::number(3))
                .equiv(&u().max(v().max(Level::number(3)))),
            "ассоциативность"
        );
    }

    #[test]
    fn zero_is_neutral_for_max() {
        assert!(u().max(Level::Zero).equiv(&u()));
    }

    #[test]
    fn numerals_collapse() {
        assert!(
            Level::number(2)
                .max(Level::number(5))
                .equiv(&Level::number(5))
        );
        assert!(Level::Zero.succ().succ().equiv(&Level::number(2)));
    }

    #[test]
    fn succ_distributes_over_max() {
        assert!(u().max(v()).succ().equiv(&u().succ().max(v().succ())));
    }

    #[test]
    fn imax_collapses_when_the_codomain_level_is_known() {
        // Pi в Type 0 остаётся в Type 0 - иначе предложения не были бы
        // замкнуты относительно импликации.
        assert!(u().imax(Level::Zero).equiv(&Level::Zero));
        // Правая часть заведомо ненулевая, значит imax вырождается в max.
        assert!(u().imax(Level::number(1)).equiv(&u().max(Level::number(1))));
    }

    #[test]
    fn imax_stays_symbolic_while_the_codomain_level_is_a_variable() {
        let stuck = u().imax(v());
        assert!(
            !stuck.equiv(&u().max(v())),
            "схлопывать рано: v может быть 0"
        );
        assert!(stuck.equiv(&u().imax(v())), "но сам себе он равен");
    }

    #[test]
    fn distinct_variables_do_not_collapse() {
        assert!(!u().equiv(&v()));
        assert!(!u().equiv(&u().succ()));
    }

    #[test]
    fn normal_form_is_canonical_across_spellings() {
        let left = v().max(u()).max(Level::Zero);
        let right = u().max(v());
        assert_eq!(left.normalize(), right.normalize());
    }

    #[test]
    fn display_reads_naturally() {
        assert_eq!(Level::number(3).to_string(), "3");
        assert_eq!(u().succ().to_string(), "u0+1");
        assert_eq!(u().max(v()).to_string(), "max u0 u1");
        assert_eq!(u().imax(v().max(u())).to_string(), "imax u0 (max u1 u0)");
    }
}
