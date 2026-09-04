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

use crate::carrier::Carriers;
use crate::eval::{eval, quote};
use crate::mult::Mult;
use crate::row::Row;
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
    /// Копилка кратностей носителей ([`crate::carrier`]), если проверка идёт
    /// ради них. `None` - обычная проверка, и тогда запись стоит ноль.
    carriers: Option<&'a Carriers>,
    /// Окружающая row - вторая компонента суждения `Γ ⊢ e ⇐ A ! ε` (§3.4).
    ///
    /// Живёт здесь, а не параметром рядом с `σ`, хотя §3.4 ставит их рядом.
    /// Причина в том, чем они друг от друга отличаются: `σ` **умножается** на
    /// каждом шаге и читается вектором использований, а `ε` меняется только на
    /// связывании - это «где мы находимся», то есть ровно контекст. Параметром
    /// она стоила бы восьмидесяти двух мест вызова, не давая взамен ничего.
    row: Row<Rc<Value>>,
    /// Идёт ли проверка **спекулятивно** - ради ответа «сошлось или нет», а не
    /// ради диагностики (§10 вопрос 52).
    ///
    /// Отказ на таком пути выбрасывается вызывающим, и собирать под него
    /// телескоп незачем: сбор стоит обхода всего локального контекста с
    /// обратным чтением каждого связывания. Форма ошибки рассчитана на
    /// редкость отказа, а спекулятивный проход делает его обычным делом.
    ///
    /// Признак живёт здесь, а не параметром: спекулятивность наследуется всем,
    /// что проверка запустит под собой, - то есть ровно контекст, как и
    /// окружающая row.
    speculative: bool,
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
            carriers: None,
            row: Row::empty(),
            speculative: false,
        }
    }

    /// Тот же контекст, но проверка под ним **спекулятивна**.
    ///
    /// Ставится вызывающим, который отказ выбросит: шаг спайна, пробующий обе
    /// кратности суждения, проверка решения дырки, вывод типа «если выйдет».
    /// Диагностику под таким контекстом не собирают - см. `speculative`.
    #[must_use]
    pub fn speculating(&self) -> Self {
        Self {
            speculative: true,
            ..self.clone()
        }
    }

    /// Спекулятивна ли проверка: собирать ли диагностику при отказе.
    #[must_use]
    pub fn is_speculative(&self) -> bool {
        self.speculative
    }

    /// Тот же контекст, копящий кратности носителей.
    #[must_use]
    pub fn recording(self, carriers: &'a Carriers) -> Self {
        Self {
            carriers: Some(carriers),
            ..self
        }
    }

    /// Тот же контекст с другой окружающей row.
    ///
    /// Меняется она на связывании: тело лямбды работает в row той стрелки,
    /// которой лямбда является.
    #[must_use]
    pub fn within(&self, row: Row<Rc<Value>>) -> Self {
        Self {
            row,
            ..self.clone()
        }
    }

    /// Окружающая row - в ней терму разрешено работать.
    #[must_use]
    pub fn row(&self) -> &Row<Rc<Value>> {
        &self.row
    }

    /// Копилка носителей, если она есть.
    #[must_use]
    pub fn carriers(&self) -> Option<&'a Carriers> {
        self.carriers
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
            row: self.row.clone(),
            env: self.env.extend(value),
            bindings: Some(Rc::new(Cell {
                binding,
                rest: self.bindings.clone(),
            })),
            carriers: self.carriers,
            speculative: self.speculative,
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
///
/// # Представление плотное, и это измерено
///
/// Вектор длиной в контекст заводится заново на каждом узле проверки, что
/// выглядит квадратичным по глубине. Замер (`benches/check.rs`,
/// `check_lambda_chain`) говорит иначе: 16 связываний - 4.7 µs, 64 - 32.3 µs,
/// 256 - 136.3 µs, то есть от 64 к 256 рост в 4.22 раза на четырёхкратной
/// глубине. Квадратичное слагаемое есть, но линейная работа на узел его
/// перекрывает на любой правдоподобной глубине.
///
/// Поэтому разреженного представления здесь нет: оно тронуло бы инвариант
/// "векторы из одного контекста", на котором стоят `Add`, [`Usage::join`] и
/// [`Usage::pop`], без выигрыша, который кто-нибудь заметил бы. Если замер
/// изменится - менять есть что.
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

    /// Использования, помноженные на кратность связывания, под которое терм
    /// подставляется.
    ///
    /// Это второй множитель правила Аткея `Γ + q · Δ`. Масштабируется
    /// **вектор**, а не кратность суждения: `σ` обязана оставаться в `{0, 1}`,
    /// иначе `q · σ` при `q = ω` даёт `ω`, а `ω` разрешает любое использование
    /// - и проверка линейности внутри терма выключается целиком.
    #[must_use]
    pub fn scale(self, mult: Mult) -> Self {
        Self(self.0.into_iter().map(|usage| usage * mult).collect())
    }

    /// Использование в альтернативных ветвях - поточечное объединение.
    ///
    /// Ветви `case` не складываются: выполняется ровно одна, поэтому
    /// фактическое использование не превосходит максимума по ветвям. Сложение
    /// здесь превратило бы линейную переменную, разобранную в двух ветвях, в
    /// `ω` и отвергло бы корректную программу.
    ///
    /// # Panics
    ///
    /// При разной длине векторов - как и сложение, см. [`std::ops::Add`].
    #[must_use]
    pub fn join(self, other: &Self) -> Self {
        assert_eq!(self.0.len(), other.0.len(), "векторы из разных контекстов");
        Self(
            self.0
                .into_iter()
                .zip(&other.0)
                .map(|(a, b)| a.join(*b))
                .collect(),
        )
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
