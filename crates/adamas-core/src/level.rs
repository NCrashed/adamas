//! Уровни универсумов (§3.2): отдельный сорт с `zero`, `suc`, `max`.
//!
//! Уровни - алгебраические выражения, а не числа: `Type (max u (suc v))`
//! возникает сразу, как только сигнатура полиморфна по уровню.
//!
//! # Почему нет `imax`
//!
//! `imax u v` (правило Lean: `0` при `v = 0`, иначе `max u v`) отличается от
//! `max` ровно в одном случае - и этот случай есть определение
//! импредикативности нижнего универсума. С ним `(x : Type 0) -> Bool` попадает
//! в `Type 0`, квантифицируя по коллекции, элементом которой сам является. У
//! Lean это безопасно, потому что `Sort 0` - это `Prop` с иррелевантностью
//! доказательств и урезанной элиминацией; §3.2 предикативен и такого сорта не
//! вводит. Правило `Pi` использует `max` (см. [`crate::check`]).
//!
//! # Равенство
//!
//! Производный `Eq` - структурный, он нужен только чтобы класть уровни в
//! `BTreeMap`. Семантическое равенство - [`Level::equiv`]: оно **корректно и
//! полно** - равными признаёт ровно те уровни, что совпадают при любой
//! подстановке. Полнота получена вместе с отказом от `imax`: незакрываемый
//! случай был именно в нём (§10 вопрос 2 закрыт).

use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

/// Переменная уровня - параметр universe polymorphism.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelVar(pub u32);

/// Метапеременная уровня - дырка, которую заполняет вывод.
///
/// Живёт в [`crate::meta::Metas`] и только на время одной проверки. В том, что
/// сохраняется надолго - в типах и телах определений, - не встречается:
/// проверка определения отвергает остаточные дырки.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelMeta(pub u32);

/// Выражение уровня.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    /// `Type 0` - самый нижний универсум.
    Zero,
    /// На единицу выше.
    Succ(Rc<Level>),
    /// Верхняя грань.
    Max(Rc<Level>, Rc<Level>),
    /// Параметр, по которому определение полиморфно.
    Var(LevelVar),
    /// Нерешённая метапеременная. Для нормализации и сравнения ведёт себя как
    /// переменная: пока решения нет, про неё известно ровно столько же.
    Meta(LevelMeta),
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

    /// Подставляет аргументы вместо параметров уровня.
    ///
    /// Переменная с индексом за пределами `arguments` остаётся как есть: это
    /// не ошибка подстановки, а незакрытый параметр, и ловить его должен
    /// [`Level::max_var`] при добавлении определения.
    #[must_use]
    pub fn substitute(&self, arguments: &[Self]) -> Self {
        match self {
            Self::Zero => Self::Zero,
            Self::Succ(inner) => inner.substitute(arguments).succ(),
            Self::Max(left, right) => left.substitute(arguments).max(right.substitute(arguments)),
            // Переменная вне списка остаётся собой: это обычная частичная
            // подстановка, а не промах. Внутри определения такого не бывает -
            // арность проверена (`check_level_scope`), - но операция сама по
            // себе тотальна, и подменять это паникой было бы враньём про её
            // область определения.
            Self::Var(LevelVar(index)) => arguments
                .get(*index as usize)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            // Метапеременную инстанциация определения не затрагивает: её
            // заполняет вывод, а не подстановка параметров.
            Self::Meta(_) => self.clone(),
        }
    }

    /// Наибольший индекс переменной уровня, встречающейся в выражении.
    ///
    /// `None` - переменных нет. Нужна, чтобы проверить, что определение не
    /// ссылается на параметр уровня, которого у него нет.
    #[must_use]
    pub fn max_var(&self) -> Option<u32> {
        match self {
            // Метапеременная параметром не является: она дырка, а не аргумент,
            // и к объявленной арности отношения не имеет.
            Self::Zero | Self::Meta(_) => None,
            Self::Succ(inner) => inner.max_var(),
            Self::Max(left, right) => match (left.max_var(), right.max_var()) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (found, None) | (None, found) => found,
            },
            Self::Var(LevelVar(index)) => Some(*index),
        }
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

    /// Верно ли `self <= other` **при любой** подстановке параметров.
    ///
    /// Нужно индуктивным типам (`crate::sig`): поле конструктора обязано жить
    /// не выше самого типа, иначе `data Bad : Type 0 where mk : (0 a : Type 0)
    /// -> Bad` протащил бы импредикативность мимо правила `Pi`, а с ней и
    /// парадокс, от которого §3.2 отгораживается.
    ///
    /// Корректно и полно на этой алгебре уровней: `max` монотонен, `suc`
    /// инъективен, а нормальная форма - полный инвариант.
    #[must_use]
    pub fn leq(&self, other: &Self) -> bool {
        Parts::of(self).leq(&Parts::of(other))
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
            // Оракул работает на уровнях без дырок: значение нерешённой
            // метапеременной не определено ничем.
            Self::Meta(meta) => unreachable!("evaluate на нерешённой {meta:?}"),
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
    /// Атом - то, что не раскладывается дальше, то есть переменная уровня.
    /// Значение - наибольшее смещение, с которым атом встречается.
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
            // Нерешённая метапеременная - такой же атом, как переменная:
            // про неё известно ровно столько же.
            Level::Var(_) | Level::Meta(_) => Self::atom(level.clone()),
        }
    }

    fn atom(level: Level) -> Self {
        Self {
            constant: 0,
            atoms: BTreeMap::from([(level, 0)]),
        }
    }

    /// Значение при нулевых атомах - минимум уровня по всем подстановкам.
    fn at_zero(&self) -> u32 {
        self.constant
            .max(self.atoms.values().copied().max().unwrap_or(0))
    }

    /// Покомпонентное сравнение: каждая составляющая слева обязана
    /// перекрываться справа при любой подстановке.
    ///
    /// Константа сравнивается с минимумом правой части. Атом со смещением `k`
    /// требует того же атома справа со смещением не меньше `k`: устремив его
    /// к бесконечности, всё остальное справа перестаёт иметь значение.
    fn leq(&self, other: &Self) -> bool {
        self.constant <= other.at_zero()
            && self
                .atoms
                .iter()
                .all(|(atom, offset)| other.atoms.get(atom).is_some_and(|theirs| theirs >= offset))
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
    ///
    /// Константа выписывается, только если её не перекрывает смещение атома:
    /// `atom + k >= k` при любом значении атома, поэтому `max 1 (u+1)` - это
    /// просто `u+1`. Разница не косметическая: [`crate::meta`] снимает общие
    /// `suc` с обеих сторон, и лишний `max` прятал бы от него решаемое
    /// ограничение.
    fn rebuild(&self) -> Level {
        let covered = self.atoms.values().copied().max().unwrap_or(0);
        let keep_constant = self.atoms.is_empty() || self.constant > covered;
        let mut result = keep_constant.then(|| Level::number(self.constant));

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
            Self::Meta(LevelMeta(index)) => write!(f, "?{index}"),
        }
    }
}

/// Снимает цепочку `suc`, возвращая основание и её длину.
///
/// Живёт здесь, а не у пользователей: печать и снятие общего префикса при
/// унификации ([`crate::meta`]) обязаны понимать «основание» одинаково.
pub(crate) fn peel(level: &Level) -> (&Level, u32) {
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
            Level::Max(..) => write!(f, "({})", self.0),
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

    /// Уровень `Pi` никогда не опускается ниже уровня домена.
    ///
    /// Это и есть предикативность, выраженная арифметикой: `max u v >= u` при
    /// любых `u` и `v`. Правило Lean `imax` нарушало бы её ровно при `v = 0` -
    /// см. заголовок модуля.
    ///
    /// Значения переменных обязаны быть **разными**, и `v = 0` при `u > 0`
    /// обязан входить в перебор: при `u = v` неравенство выполняется и для
    /// `imax`, то есть такой тест прошёл бы, ничего не проверив.
    #[test]
    fn max_never_drops_below_either_argument() {
        for left in 0..4 {
            for right in 0..4 {
                let assignment = |LevelVar(index)| if index == 0 { left } else { right };
                let level = u().max(v()).evaluate(&assignment);
                assert!(level >= left, "max {left} {right} = {level}");
                assert!(level >= right, "max {left} {right} = {level}");
            }
        }
        // Именно тот случай, в котором imax отличается: квантификация по
        // Type 0 поднимает результат, а не оставляет его в нуле.
        assert_eq!(
            u().max(Level::Zero).evaluate(&|_| 1),
            1,
            "imax дал бы здесь 0"
        );
    }

    /// Нормальная форма не выписывает константу, перекрытую смещением атома.
    ///
    /// `max 1 (u+1)` - это `u+1` при любом `u`, потому что уровни неотрицательны.
    /// Лишний `max` не только шумит в сообщениях, но и прячет от унификатора
    /// решаемое ограничение: снятие общих `suc` работает по структуре.
    #[test]
    fn a_constant_covered_by_an_atom_is_dropped() {
        assert_eq!(u().succ().normalize(), u().succ());
        assert_eq!(u().succ().succ().normalize(), u().succ().succ());
        // А не перекрытую - выписывает: при `u = 0` слева 2, справа 1.
        assert_eq!(
            u().succ().max(Level::number(2)).normalize(),
            Level::number(2).max(u().succ())
        );
    }

    #[test]
    fn ordering_holds_under_every_substitution() {
        // Тривиальные границы.
        assert!(Level::Zero.leq(&u()));
        assert!(u().leq(&u()));
        assert!(u().leq(&u().succ()));
        assert!(!u().succ().leq(&u()));

        // `max` только растёт.
        assert!(u().leq(&u().max(v())));
        assert!(!u().max(v()).leq(&u()), "при большом v не выполняется");

        // Константа сравнивается с минимумом правой части, а он достигается
        // на нулевых атомах.
        assert!(!Level::number(5).leq(&u()), "при u = 0 слева больше");
        assert!(Level::number(5).leq(&u().max(Level::number(5))));
        assert!(Level::number(1).leq(&u().succ()), "u+1 >= 1 всегда");

        // Разные переменные несравнимы ни в одну сторону.
        assert!(!u().leq(&v()));
        assert!(!v().leq(&u()));
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
        assert_eq!(u().max(v().max(u())).to_string(), "max u0 (max u1 u0)");
    }
}
