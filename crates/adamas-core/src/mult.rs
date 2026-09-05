//! Кратности QTT (§3.2): полукольцо `{0, 1, ω}`.
//!
//! Сложение считает, сколько раз переменная использована суммарно; умножение -
//! что происходит с использованиями под связыванием кратности `q`.
//!
//! Кроме трёх значений полукольца здесь живут две неконкретные формы -
//! параметр определения и дырка вывода (§10 вопрос 41). Арифметика их не
//! считает и считать не может: полиморфное тело проверяется **подстановкой**,
//! а место использования - инстанцированием. Обе формы дошли до сложения или
//! сравнения означают, что подстановку забыли, и ответ тогда даётся самый
//! строгий из возможных: он ведёт к отказу, но не к пропуску.

use std::fmt;

/// Параметр кратности определения (§10 вопрос 41).
///
/// Третья компонента арности рядом с [`crate::level::LevelVar`] и
/// [`crate::row::RowVar`]: внутри типа и тела он виден переменной, а место
/// использования подставляет вместо него значение полукольца.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MultVar(pub u16);

/// Дырка кратности: что подставить, решает проверка конвертируемости.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MultMeta(pub u16);

/// Кратность.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mult {
    /// Стирается: значение не существует в рантайме (§3.3).
    Zero,
    /// Не более одного использования: аффинная, не строго линейная (§3.3).
    /// "Ровно одно" даёт `resource` - surface-конструкция поверх ядра.
    One,
    /// Без ограничений.
    Many,
    /// Параметр определения: конкретное значение придёт подстановкой.
    Var(MultVar),
    /// Дырка вывода: конкретное значение придёт решением.
    Meta(MultMeta),
}

/// Суммарное использование при двух независимых использованиях.
///
/// Неконкретное слагаемое даёт `ω`: больше полукольцо предложить не может,
/// и завышенное использование ведёт к отказу, а не к пропуску.
impl std::ops::Add for Mult {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, q) | (q, Self::Zero) => q,
            _ => Self::Many,
        }
    }
}

/// Использование под связыванием кратности `self`.
///
/// Ключевое свойство - `0 · q = 0`: внутри стёртого контекста любое
/// использование само стирается. На этом держится "доказательства ничего не
/// стоят в рантайме" (§3.3).
///
/// Неконкретный множитель даёт `ω` по той же причине, что и в сложении:
/// завышенное использование отвергается, заниженное - пропускается.
impl std::ops::Mul for Mult {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, q) | (q, Self::One) => q,
            _ => Self::Many,
        }
    }
}

impl Mult {
    /// Значение полукольца; `None` у параметра и у дырки.
    #[must_use]
    pub const fn fixed(self) -> Option<Self> {
        match self {
            Self::Zero | Self::One | Self::Many => Some(self),
            Self::Var(_) | Self::Meta(_) => None,
        }
    }

    /// Конкретна ли кратность - есть ли что считать.
    #[must_use]
    pub const fn is_fixed(self) -> bool {
        self.fixed().is_some()
    }

    /// Наибольшая из двух кратностей в порядке `0 < 1 < ω`.
    ///
    /// Не то же, что сложение, и разница принципиальна: `1 ∨ 1 = 1`, тогда как
    /// `1 + 1 = ω`. Сложение отвечает на "оба использования происходят",
    /// объединение - на "происходит ровно одно из двух". Так соединяются ветви
    /// `case`: выполняется одна, поэтому фактическое использование не
    /// превосходит максимума по ветвям.
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::One, Self::One | Self::Zero) | (Self::Zero, Self::One) => Self::One,
            (Self::Zero, Self::Zero) => Self::Zero,
            _ => Self::Many,
        }
    }

    /// Допустимо ли фактическое использование `usage` при объявленной `self`.
    ///
    /// `One` допускает и ноль использований - следствие аффинности.
    ///
    /// Неконкретная сторона допуска не даёт: объявленная кратность, которую
    /// нечем сравнить, отвергает всё, а неизвестное использование не проходит
    /// ни при `0`, ни при `1`. Исключение одно - `ω` допускает и его, потому
    /// что допускает любое конкретное значение, каким бы оно ни оказалось.
    #[must_use]
    pub fn admits(self, usage: Self) -> bool {
        match self {
            Self::Zero => usage == Self::Zero,
            Self::One => usage == Self::Zero || usage == Self::One,
            Self::Many => true,
            Self::Var(_) | Self::Meta(_) => false,
        }
    }
}

impl fmt::Display for Mult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("0"),
            Self::One => f.write_str("1"),
            Self::Many => f.write_str("ω"),
            Self::Var(MultVar(index)) => write!(f, "q{index}"),
            Self::Meta(MultMeta(index)) => write!(f, "?q{index}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Mult, MultMeta, MultVar};

    const ALL: [Mult; 3] = [Mult::Zero, Mult::One, Mult::Many];

    /// Полукольцо целиком проверяется перебором: элементов три, случаев 27.
    #[test]
    fn semiring_laws_hold() {
        for a in ALL {
            assert_eq!(a + Mult::Zero, a, "0 - нейтраль сложения");
            assert_eq!(a * Mult::One, a, "1 - нейтраль умножения");
            assert_eq!(a * Mult::Zero, Mult::Zero, "0 поглощает");

            for b in ALL {
                assert_eq!(a + b, b + a, "сложение коммутативно");
                assert_eq!(a * b, b * a, "умножение коммутативно");

                for c in ALL {
                    assert_eq!((a + b) + c, a + (b + c), "сложение ассоциативно");
                    assert_eq!((a * b) * c, a * (b * c), "умножение ассоциативно");
                    assert_eq!(a * (b + c), (a * b) + (a * c), "умножение дистрибутивно");
                }
            }
        }
    }

    #[test]
    fn one_plus_one_saturates() {
        assert_eq!(Mult::One + Mult::One, Mult::Many);
    }

    /// Ветви `case` соединяются объединением, и именно поэтому линейная
    /// переменная, использованная в каждой из двух ветвей, остаётся линейной.
    #[test]
    fn joining_is_not_adding() {
        assert_eq!(Mult::One.join(Mult::One), Mult::One);
        assert_eq!(Mult::One + Mult::One, Mult::Many, "а сложение - наоборот");
    }

    #[test]
    fn join_is_a_least_upper_bound() {
        for a in ALL {
            assert_eq!(a.join(a), a, "идемпотентно");
            assert_eq!(a.join(Mult::Zero), a, "0 - нейтраль");
            assert_eq!(a.join(Mult::Many), Mult::Many, "ω поглощает");
            for b in ALL {
                assert_eq!(a.join(b), b.join(a), "коммутативно");
                assert!(a.join(b).admits(a), "не меньше каждой из сторон");
                for c in ALL {
                    assert_eq!(a.join(b).join(c), a.join(b.join(c)), "ассоциативно");
                }
            }
        }
    }

    #[test]
    fn linear_binding_is_affine() {
        assert!(Mult::One.admits(Mult::Zero), "не использовать - можно");
        assert!(Mult::One.admits(Mult::One));
        assert!(!Mult::One.admits(Mult::Many));
    }

    #[test]
    fn erased_binding_admits_nothing_but_erasure() {
        assert!(Mult::Zero.admits(Mult::Zero));
        assert!(!Mult::Zero.admits(Mult::One));
    }

    /// Неконкретная кратность до арифметики доходить не должна - тело
    /// проверяется подстановкой (§10 вопрос 41). Дошедшая обязана вести к
    /// отказу, а не к пропуску: сложение и умножение завышают использование,
    /// допуск отказывает.
    #[test]
    fn a_symbolic_multiplicity_is_answered_strictly() {
        let symbolic = [Mult::Var(MultVar(0)), Mult::Meta(MultMeta(0))];
        for opaque in symbolic {
            assert!(!opaque.is_fixed());
            assert_eq!(opaque.fixed(), None);
            for a in ALL {
                assert!(
                    !opaque.admits(a) || opaque == Mult::Many,
                    "объявленная неизвестной не допускает ничего"
                );
                assert!(
                    a.admits(opaque) == (a == Mult::Many),
                    "неизвестное использование проходит только при ω"
                );
                assert_eq!(
                    a + opaque,
                    if a == Mult::Zero { opaque } else { Mult::Many }
                );
                assert_eq!(
                    a * opaque,
                    match a {
                        Mult::Zero => Mult::Zero,
                        Mult::One => opaque,
                        _ => Mult::Many,
                    }
                );
                assert_eq!(a.join(opaque), Mult::Many, "объединение завышает");
            }
        }
    }
}
