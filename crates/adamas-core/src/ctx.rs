//! Контекст проверки типов и вектор использований.
//!
//! Контекст держит две вещи параллельно: окружение для вычисления
//! ([`crate::value::Env`]) и объявленные типы с кратностями. Оба растут вместе,
//! поэтому `size` у них общий.
//!
//! Связывание бывает двух видов. [`Ctx::bind`] вводит переменную, о значении
//! которой ничего не известно, - в окружение попадает свежая нейтраль.
//! [`Ctx::define`] вводит переменную с известным значением (`let`), и тогда в
//! окружение попадает само значение: иначе тип тела мог бы сослаться на
//! связывание, которого снаружи уже нет.

use std::rc::Rc;

use crate::eval::{eval, quote};
use crate::mult::Mult;
use crate::sig::Signature;
use crate::term::{Index, Name, Term};
use crate::value::{Env, Lvl, Value};

/// Запись контекста.
#[derive(Clone, Debug)]
pub struct Binding {
    /// Имя для сообщений об ошибках.
    pub name: Name,
    /// Кратность, с которой переменная объявлена.
    pub mult: Mult,
    /// Тип переменной.
    pub ty: Rc<Value>,
}

/// Контекст проверки.
///
/// Держит ссылку на сигнатуру, а не владеет ею: контекст пересоздаётся на
/// каждом связывании, а сигнатура на время проверки одного терма неизменна.
#[derive(Clone, Debug)]
pub struct Ctx<'a> {
    signature: &'a Signature,
    env: Env,
    bindings: Option<Rc<Cell>>,
}

#[derive(Debug)]
struct Cell {
    binding: Binding,
    rest: Option<Rc<Cell>>,
}

impl<'a> Ctx<'a> {
    /// Пустой контекст над сигнатурой.
    #[must_use]
    pub fn new(signature: &'a Signature) -> Self {
        Self {
            signature,
            env: Env::default(),
            bindings: None,
        }
    }

    /// Сигнатура, в которой проверяется терм.
    #[must_use]
    pub fn signature(&self) -> &'a Signature {
        self.signature
    }

    /// Число связываний. Оно же - уровень следующей свежей переменной.
    #[must_use]
    pub fn size(&self) -> u32 {
        self.env.len()
    }

    /// Окружение для вычисления.
    #[must_use]
    pub fn env(&self) -> &Env {
        &self.env
    }

    /// Запись по индексу де Брёйна.
    #[must_use]
    pub fn lookup(&self, Index(index): Index) -> Option<&Binding> {
        let mut cell = self.bindings.as_ref()?;
        for _ in 0..index {
            cell = cell.rest.as_ref()?;
        }
        Some(&cell.binding)
    }

    /// Вводит переменную без известного значения.
    #[must_use]
    pub fn bind(&self, name: Name, mult: Mult, ty: Rc<Value>) -> Self {
        self.push(Binding { name, mult, ty }, self.fresh())
    }

    /// Вводит переменную с известным значением.
    #[must_use]
    pub fn define(&self, name: Name, mult: Mult, ty: Rc<Value>, value: Rc<Value>) -> Self {
        self.push(Binding { name, mult, ty }, value)
    }

    fn push(&self, binding: Binding, value: Rc<Value>) -> Self {
        Self {
            signature: self.signature,
            env: self.env.extend(value),
            bindings: Some(Rc::new(Cell {
                binding,
                rest: self.bindings.clone(),
            })),
        }
    }

    /// Свежая переменная, соответствующая следующему связыванию.
    #[must_use]
    pub fn fresh(&self) -> Rc<Value> {
        Value::var(Lvl(self.size()))
    }

    /// Вычисляет терм в этом контексте.
    #[must_use]
    pub fn eval(&self, term: &Term) -> Rc<Value> {
        eval(&self.env, term)
    }

    /// Читает значение обратно в терм - для сообщений об ошибках.
    #[must_use]
    pub fn quote(&self, value: &Rc<Value>) -> Term {
        quote(self.size(), value)
    }
}

/// Сколько раз каждая переменная контекста использована.
///
/// Индекс вектора - уровень де Брёйна, то есть нулевой элемент отвечает самому
/// внешнему связыванию. Уровни, а не индексы, потому что вектор переживает
/// вход под связывание: элементы не сдвигаются, только дописывается новый.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Usage(Vec<Mult>);

impl Usage {
    /// Никто не использован.
    #[must_use]
    pub fn zero(size: u32) -> Self {
        Self(vec![Mult::Zero; size as usize])
    }

    /// Использована ровно одна переменная, с кратностью `mult`.
    ///
    /// # Panics
    ///
    /// Если уровень не адресуем при таком `size`. Это internal invariant -
    /// уровень приходит из [`crate::term::Index::to_level`], который выход за
    /// контекст уже отсеял, вернув `None`. Тихо проигнорировать промах было бы
    /// хуже по той же причине, что и в [`Usage::pop`]: использование
    /// потерялось бы, и линейная переменная прошла бы проверку.
    #[must_use]
    pub fn single(size: u32, Lvl(level): Lvl, mult: Mult) -> Self {
        let mut usage = Self::zero(size);
        let slot = usage
            .0
            .get_mut(level as usize)
            .unwrap_or_else(|| unreachable!("уровень {level} вне контекста размера {size}"));
        *slot = mult;
        usage
    }

    /// Кратность использования переменной.
    ///
    /// # Panics
    ///
    /// Если уровень вне контекста - см. [`Usage::single`].
    #[must_use]
    pub fn get(&self, Lvl(level): Lvl) -> Mult {
        self.0.get(level as usize).copied().unwrap_or_else(|| {
            unreachable!("уровень {level} вне контекста размера {}", self.0.len())
        })
    }

    /// Снимает использование самого внутреннего связывания - при выходе
    /// из-под него.
    ///
    /// # Panics
    ///
    /// Паникует на пустом векторе. Internal invariant: снимать нечего только
    /// если выход из-под связывания произошёл без входа, а это поломка
    /// проверяющего. Отдавать здесь `Mult::Zero` было бы хуже - использование
    /// потерялось бы молча, и линейная переменная прошла бы проверку.
    #[expect(clippy::expect_used, reason = "internal invariant, см. описание")]
    #[must_use]
    pub fn pop(mut self) -> (Mult, Self) {
        let innermost = self
            .0
            .pop()
            .expect("выход из-под несуществующего связывания");
        (innermost, self)
    }

    /// Длина вектора - размер контекста, к которому он относится.
    ///
    /// # Panics
    ///
    /// Если контекст не помещается в `u32`. Насыщение здесь дало бы вектор,
    /// который считает себя короче, чем есть, - то есть снова тихую потерю
    /// использований.
    #[must_use]
    pub fn len(&self) -> u32 {
        u32::try_from(self.0.len()).unwrap_or_else(|_| unreachable!("контекст не помещается в u32"))
    }

    /// Пуст ли контекст, к которому относится вектор.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Использование в двух независимых позициях - поточечная сумма.
///
/// Оператор, а не именованный метод: сложение здесь то же самое, что в
/// полукольце кратностей, только покомпонентное.
///
/// # Panics
///
/// Паникует при разной длине векторов: складывать использования из разных
/// контекстов бессмысленно, и это internal invariant.
impl std::ops::Add<&Usage> for Usage {
    type Output = Self;

    fn add(self, other: &Self) -> Self {
        assert_eq!(self.0.len(), other.0.len(), "векторы из разных контекстов");
        Self(
            self.0
                .into_iter()
                .zip(&other.0)
                .map(|(a, b)| a + *b)
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{Ctx, Usage};
    use crate::mult::Mult;
    use crate::term::{Index, Term};
    use crate::value::{Lvl, Value};

    fn universe() -> Rc<Value> {
        Rc::new(Value::Universe(crate::level::Level::Zero))
    }

    #[test]
    fn lookup_reads_indices_from_the_innermost_binding() {
        let signature = crate::sig::Signature::default();
        let ctx = Ctx::new(&signature)
            .bind("outer".into(), Mult::Many, universe())
            .bind("inner".into(), Mult::One, universe());

        assert_eq!(&*ctx.lookup(Index(0)).unwrap().name, "inner");
        assert_eq!(&*ctx.lookup(Index(1)).unwrap().name, "outer");
        assert!(ctx.lookup(Index(2)).is_none());
    }

    #[test]
    fn bind_introduces_a_neutral_but_define_introduces_a_value() {
        let signature = crate::sig::Signature::default();
        let bound = Ctx::new(&signature).bind("x".into(), Mult::Many, universe());
        assert!(matches!(*bound.eval(&Term::var(0)), Value::Neutral(..)));

        let defined = Ctx::new(&signature).define("x".into(), Mult::Many, universe(), universe());
        assert!(matches!(*defined.eval(&Term::var(0)), Value::Universe(_)));
    }

    #[test]
    fn usage_adds_pointwise_and_saturates() {
        let one = Usage::single(2, Lvl(0), Mult::One);
        let doubled = one.clone() + &one;
        assert_eq!(
            doubled.get(Lvl(0)),
            Mult::Many,
            "два линейных использования"
        );
        assert_eq!(doubled.get(Lvl(1)), Mult::Zero);
    }

    #[test]
    fn pop_returns_the_innermost_usage() {
        let usage = Usage::single(3, Lvl(2), Mult::One);
        let (innermost, rest) = usage.pop();
        assert_eq!(innermost, Mult::One);
        assert_eq!(rest.len(), 2);
    }

    #[test]
    #[should_panic(expected = "вне контекста")]
    fn single_outside_the_context_is_a_bug_not_a_silent_zero() {
        // Проверяющий сюда не приходит: `Index::to_level` выход за контекст
        // отсекает раньше. Но если придёт, потеря использования означала бы
        // пропущенное нарушение линейности.
        let _ = Usage::single(1, Lvl(5), Mult::One);
    }
}
