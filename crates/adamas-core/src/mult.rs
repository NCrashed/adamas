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

/// Произведение параметров кратности (§10 вопрос 41).
///
/// Умножение в `{0, 1, ω}` идемпотентно - `q · q = q` при всех трёх, - поэтому
/// произведение определяется **множеством** сомножителей, а не их
/// последовательностью и не их числом. Множество и хранится: битовая маска по
/// номерам параметров, один `u16`. Узел кратности остаётся `Copy` и мелким, а
/// равенство произведений - структурным.
///
/// Значений полукольца в произведении нет намеренно: `0 · q` и `ω · q`
/// считаются, а не пишутся, и пускать их сюда значило бы завести вторую
/// нормальную форму у того же выражения.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MultProduct(u16);

impl MultProduct {
    /// Сколько параметров кратности умещается в произведении.
    pub const LIMIT: u32 = u16::BITS;

    /// Произведение перечисленных параметров; `None`, если номер не влезает.
    ///
    /// Один сомножитель произведением не становится: `q · 1 = q`, и вторая
    /// форма у того же выражения сломала бы структурное равенство. Ноль
    /// сомножителей - пустое произведение, то есть `1`.
    #[must_use]
    pub fn of(factors: impl IntoIterator<Item = MultVar>) -> Option<Mult> {
        let mut mask = 0u16;
        for MultVar(index) in factors {
            mask |= 1u16.checked_shl(u32::from(index))?;
        }
        Some(match mask.count_ones() {
            0 => Mult::One,
            1 => Mult::Var(MultVar(mask.trailing_zeros().try_into().ok()?)),
            _ => Mult::Prod(Self(mask)),
        })
    }

    /// Сомножители по возрастанию номера.
    pub fn factors(self) -> impl Iterator<Item = MultVar> {
        parts(self.0)
    }
}

/// Сумма параметров кратности (§10 вопрос 41).
///
/// Сложение, в отличие от умножения, **не идемпотентно**: `1 + 1 = ω`, тогда
/// как `1 · 1 = 1`. Множеством поэтому выражается не всякая сумма, а только
/// сумма различных параметров - `q + q` пришлось бы хранить кратностью
/// слагаемого, а она нужна лишь одна («один раз» против «дважды и больше»), и
/// заводить ради неё вторую компоненту не за что: повтор в сумме отвергается.
///
/// Хранение - как у произведения: битовая маска по номерам параметров, один
/// `u16`, узел кратности остаётся `Copy` и мелким.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MultSum(u16);

impl MultSum {
    /// Сумма перечисленных параметров; `None` при повторе или номере за маской.
    ///
    /// Одно слагаемое суммой не становится - `q + 0 = q`, - а ноль слагаемых
    /// есть пустая сумма, то есть `0`.
    #[must_use]
    pub fn of(summands: impl IntoIterator<Item = MultVar>) -> Option<Mult> {
        let mut mask = 0u16;
        for MultVar(index) in summands {
            let bit = 1u16.checked_shl(u32::from(index))?;
            if mask & bit != 0 {
                return None;
            }
            mask |= bit;
        }
        Some(match mask.count_ones() {
            0 => Mult::Zero,
            1 => Mult::Var(MultVar(mask.trailing_zeros().try_into().ok()?)),
            _ => Mult::Sum(Self(mask)),
        })
    }

    /// Слагаемые по возрастанию номера.
    pub fn summands(self) -> impl Iterator<Item = MultVar> {
        parts(self.0)
    }
}

/// Номера, отмеченные в маске, по возрастанию.
fn parts(mask: u16) -> impl Iterator<Item = MultVar> {
    (0..u16::BITS)
        .filter(move |index| mask & (1 << index) != 0)
        .filter_map(|index| index.try_into().ok().map(MultVar))
}

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
    /// Параметр **поля записи** (§10 вопрос 115).
    ///
    /// Пространство индексов у него своё, и это не украшение. Сегодня у сорта
    /// ровно один связыватель - определение, - поэтому `MultVar(0)` работает
    /// именем: ни один обход его не сдвигает. Второй связыватель в общем
    /// пространстве потребовал бы сдвига во всех обходах сразу, а цена промаха
    /// там - молча неверный тип. В раздельном промах невозможен: подстановка
    /// определения на параметр поля просто не попадает.
    ///
    /// Инстанцирует его проекция, а на границе с определением - объявление
    /// метода и члена инстанса: там `Field(i)` переходит в `Var(i)`.
    Field(MultVar),
    /// Произведение параметров: `q * r` (§10 вопрос 41).
    ///
    /// Пишется там, где кратность связывания зависит сразу от двух параметров:
    /// у композиции домен собственного аргумента равен `q · r`, и никакое одно
    /// из двух имён на его месте не годится.
    Prod(MultProduct),
    /// Сумма параметров: `q + r` (§10 вопрос 41).
    ///
    /// Пишется там, где связывание расходуется двумя независимыми способами:
    /// у `both f g z = MkPair (f z) (g z)` домен равен `q + r`.
    Sum(MultSum),
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
            Self::Var(_) | Self::Field(_) | Self::Prod(_) | Self::Sum(_) | Self::Meta(_) => None,
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
            Self::Var(_) | Self::Field(_) | Self::Prod(_) | Self::Sum(_) | Self::Meta(_) => false,
        }
    }
}

/// Параметры через разделитель - так печатаются произведение и сумма.
fn joined(
    f: &mut fmt::Formatter<'_>,
    parts: impl Iterator<Item = MultVar>,
    between: &str,
) -> fmt::Result {
    let mut first = true;
    for MultVar(index) in parts {
        if !std::mem::take(&mut first) {
            f.write_str(between)?;
        }
        write!(f, "q{index}")?;
    }
    Ok(())
}

impl fmt::Display for Mult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("0"),
            Self::One => f.write_str("1"),
            Self::Many => f.write_str("ω"),
            Self::Var(MultVar(index)) => write!(f, "q{index}"),
            Self::Field(MultVar(index)) => write!(f, "f.q{index}"),
            Self::Prod(product) => joined(f, product.factors(), " * "),
            Self::Sum(sum) => joined(f, sum.summands(), " + "),
            Self::Meta(MultMeta(index)) => write!(f, "?q{index}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Mult, MultMeta, MultProduct, MultSum, MultVar};

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

    /// Произведение - множество, а не последовательность: умножение в
    /// `{0, 1, ω}` идемпотентно, поэтому `q · q = q` и порядок ничего не
    /// значит. Форма у выражения обязана быть одна, иначе структурное
    /// равенство перестаёт отвечать на вопрос про семантическое.
    #[test]
    fn a_product_is_a_set_of_factors() {
        let q = MultVar(0);
        let r = MultVar(1);
        let product = MultProduct::of([q, r]);
        assert_eq!(product, MultProduct::of([r, q]), "порядок не значим");
        assert_eq!(product, MultProduct::of([q, r, q]), "повтор не значим");
        assert_eq!(MultProduct::of([q, q]), Some(Mult::Var(q)), "`q · q = q`");
        assert_eq!(
            MultProduct::of([q]),
            Some(Mult::Var(q)),
            "один - не произведение"
        );
        assert_eq!(MultProduct::of([]), Some(Mult::One), "пустое - единица");
        assert_eq!(
            MultProduct::of([MultVar(u16::MAX)]),
            None,
            "номер за пределом маски"
        );
    }

    /// Сумма - множество, но, в отличие от произведения, **различных**
    /// параметров: сложение не идемпотентно, и `q + q` через множество не
    /// выражается вовсе.
    #[test]
    fn a_sum_is_a_set_of_distinct_summands() {
        let q = MultVar(0);
        let r = MultVar(1);
        let sum = MultSum::of([q, r]);
        assert_eq!(sum, MultSum::of([r, q]), "порядок не значим");
        assert_eq!(MultSum::of([q, q]), None, "`q + q` не равно `q`");
        assert_eq!(MultSum::of([q]), Some(Mult::Var(q)), "одно - не сумма");
        assert_eq!(MultSum::of([]), Some(Mult::Zero), "пустая - ноль");
        assert_ne!(
            sum,
            MultProduct::of([q, r]),
            "сумма не то же, что произведение"
        );
    }

    /// Произведение считается подстановкой, а до неё отвечает как всякая
    /// неконкретная кратность - самым строгим из возможных.
    #[test]
    fn a_product_is_answered_strictly() {
        let product = MultProduct::of([MultVar(0), MultVar(1)]).expect("два номера в маске");
        assert!(!product.is_fixed());
        for a in ALL {
            assert!(!product.admits(a), "объявленное произведение не допускает");
            assert_eq!(
                a * product,
                match a {
                    Mult::Zero => Mult::Zero,
                    Mult::One => product,
                    _ => Mult::Many,
                }
            );
        }
    }
}
