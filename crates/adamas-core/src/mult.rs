//! Кратности QTT (§3.2): полукольцо `{0, 1, ω}`.
//!
//! Сложение считает, сколько раз переменная использована суммарно; умножение -
//! что происходит с использованиями под связыванием кратности `q`.

use std::fmt;

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
}

/// Суммарное использование при двух независимых использованиях.
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
impl std::ops::Mul for Mult {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, q) | (q, Self::One) => q,
            (Self::Many, Self::Many) => Self::Many,
        }
    }
}

impl Mult {
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
            (Self::Many, _) | (_, Self::Many) => Self::Many,
            (Self::One, _) | (_, Self::One) => Self::One,
            (Self::Zero, Self::Zero) => Self::Zero,
        }
    }

    /// Допустимо ли фактическое использование `usage` при объявленной `self`.
    ///
    /// `One` допускает и ноль использований - следствие аффинности.
    #[must_use]
    pub fn admits(self, usage: Self) -> bool {
        match self {
            Self::Zero => usage == Self::Zero,
            Self::One => usage != Self::Many,
            Self::Many => true,
        }
    }
}

impl fmt::Display for Mult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::Many => "ω",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Mult;

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
}
