//! Семантические значения для `NbE`.
//!
//! Значения используют уровни де Брёйна, а термы - индексы. Разница в том,
//! откуда ведётся счёт: индекс отсчитывается от места использования, уровень -
//! от начала контекста. Уровень не меняется при входе под новое связывание,
//! поэтому значение, попавшее в замыкание, не нужно сдвигать - на этом `NbE` и
//! экономит по сравнению с подстановкой.

use std::fmt;
use std::rc::Rc;

use crate::level::Level;
use crate::mult::Mult;
use crate::row::{Row, RowVar};
use crate::term::{Binder, Field, Fields, Index, Name, Term, TermMeta};

/// Уровень де Брёйна: сколько связываний отсчитать от начала контекста.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lvl(pub u32);

impl Lvl {
    /// Индекс, которым этот уровень адресуется из контекста размера `size`.
    ///
    /// # Panics
    ///
    /// Если уровень не адресуем при таком `size`, то есть `self.0 >= size`.
    /// Это internal invariant: значение читается обратно в том же контексте,
    /// в котором построено. Проверка явная, потому что без неё вычитание в
    /// release молча заворачивается и наружу уходит индекс вроде `#4294967295`
    /// вместо отказа.
    #[must_use]
    pub fn to_index(self, size: u32) -> Index {
        Index(
            size.checked_sub(self.0)
                .and_then(|distance| distance.checked_sub(1))
                .unwrap_or_else(|| unreachable!("уровень {} вне контекста размера {size}", self.0)),
        )
    }
}

/// Окружение вычисления - список значений, голова которого соответствует
/// [`Index(0)`](Index).
///
/// Односвязный список на `Rc`, а не вектор: замыкание захватывает окружение
/// целиком, и копирование вектора на каждом связывании давало бы
/// квадратичность.
#[derive(Clone, Debug, Default)]
pub struct Env {
    head: Option<Rc<Cell>>,
    len: u32,
    /// Аргументы-row определения, которое сейчас вычисляется (§10 вопрос 73).
    ///
    /// Живут здесь, а не подставляются в терм заранее, и причина не в удобстве.
    /// Уровень **замкнут**, поэтому подставляется до вычисления; row - нет: её
    /// метка несёт термы, и `{State s}` при локальном `s` открыта. Положить
    /// такую row в замкнутое тело нечем, а окружение для того и заведено -
    /// оно уже носит открытые значения.
    rows: Rc<[Row<Rc<Value>>]>,
}

#[derive(Debug)]
struct Cell {
    value: Rc<Value>,
    rest: Option<Rc<Cell>>,
}

impl Env {
    /// Сколько значений в окружении.
    #[must_use]
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Пусто ли окружение.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Окружение с аргументами-row: так вычисляется тело определения при δ.
    #[must_use]
    pub fn rowed(rows: Rc<[Row<Rc<Value>>]>) -> Self {
        // Поля выписаны поимённо: у `Env` теперь свой `Drop`, а через него
        // синтаксис обновления структуры не проходит.
        Self {
            head: None,
            len: 0,
            rows,
        }
    }

    /// Аргумент-row по номеру параметра. `None` - параметра столько нет, и
    /// хвост остаётся собой: подставлять нечего.
    #[must_use]
    pub fn row(&self, RowVar(index): RowVar) -> Option<&Row<Rc<Value>>> {
        self.rows.get(index as usize)
    }

    /// Окружение с добавленным значением. Исходное не меняется.
    #[must_use]
    pub fn extend(&self, value: Rc<Value>) -> Self {
        Self {
            head: Some(Rc::new(Cell {
                value,
                rest: self.head.clone(),
            })),
            len: self.len + 1,
            rows: Rc::clone(&self.rows),
        }
    }

    /// Значение по индексу. `None` - индекс за пределами окружения, что
    /// означает незамкнутый терм.
    #[must_use]
    pub fn lookup(&self, Index(index): Index) -> Option<Rc<Value>> {
        let mut cell = self.head.as_ref()?;
        for _ in 0..index {
            cell = cell.rest.as_ref()?;
        }
        Some(Rc::clone(&cell.value))
    }
}

/// Замыкание: тело, ждущее ещё одного значения, вместе с захваченным
/// окружением.
#[derive(Clone, Debug)]
pub struct Closure {
    pub(crate) env: Env,
    pub(crate) body: Rc<Term>,
}

/// Голова застрявшего вычисления.
///
/// Локальная переменная застревает всегда - её значение неизвестно по
/// построению. Определение застревает, только пока его не развернули: у
/// определения с телом разворот возможен (δ-редукция, [`crate::conv`]), у
/// постулата - нет.
///
/// Равенство структурное, и для аргументов уровня это работает только потому,
/// что [`Value::constant`] приводит их к нормальной форме. Нормальная форма
/// уровня - полный инвариант (см. [`crate::level`]), так что структурное
/// равенство нормализованных уровней и есть семантическое.
/// Равенство голов не выводится: аргументы-row несут значения, а у значений
/// равенство есть конвертируемость, и живёт она в [`crate::conv`]. Сравнивать
/// головы структурно значило бы завести второе, более грубое.
#[derive(Clone, Debug)]
pub enum Head {
    /// Переменная контекста.
    Local(Lvl),
    /// Определение с нормализованными аргументами уровня и аргументами row.
    ///
    /// Списка два, потому что и параметров у определения два набора (§10
    /// вопрос 73). Row здесь несут значения: аргументы метки - обычные термы,
    /// и на стороне значения они уже вычислены.
    Global(Name, Rc<[Level]>, Rc<[Row<Rc<Value>>]>),
    /// Нерешённая метапеременная терма.
    ///
    /// Застревает так же, как переменная контекста, и по той же причине:
    /// вычислять нечего, пока не известно, чем она окажется. Решённая головой
    /// не остаётся - её разворачивает `force` до того, как спайн понадобится.
    Meta(TermMeta),
}

/// Элиминатор в спайне застрявшего вычисления.
///
/// Спайн - не просто список аргументов: разбор по конструктору тоже застревает
/// на неизвестном значении и тоже может быть продолжен применением
/// (`(case x of …) y`). Одно перечисление на оба вида снимает вопрос "в каком
/// порядке они шли" - порядок и есть порядок спайна.
#[derive(Clone, Debug)]
pub enum Elim {
    /// Применение к аргументу.
    App(Rc<Value>),
    /// Разбор по конструктору.
    Case(Rc<StuckCase>),
    /// Проекция поля записи.
    Project(Name),
    /// Переопределение полей записи: `{ p | x = v }`.
    ///
    /// Стоит в спайне, а не отдельным значением: проекция сквозь него
    /// считается (`{ p | x = v }.x` есть `v`, а `.y` - `p.y`), то есть ведёт
    /// себя ровно как элиминатор, застрявший на неизвестной базе.
    With(Rc<[(Name, Rc<Value>)]>),
}

/// Разбор, застрявший на неизвестном значении.
///
/// Мотив и ветви уже вычислены: [`crate::term::Case`] собственных связываний не
/// вводит, поэтому хранить замыкания незачем - это обычные значения
/// функционального типа.
#[derive(Clone, Debug)]
pub struct StuckCase {
    /// Индуктивный тип, по которому шёл разбор.
    pub data: Name,
    /// Аргументы уровня этого типа, уже нормализованные.
    pub levels: Rc<[Level]>,
    /// Сколько первых аргументов конструктора - параметры.
    pub params: u32,
    /// Кратность потребления разбираемого - см. [`crate::term::Case::consumed`].
    pub consumed: Mult,
    /// Мотив как значение.
    pub motive: Rc<Value>,
    /// Ветви в порядке объявления конструкторов.
    pub branches: Vec<StuckBranch>,
}

/// Ветвь застрявшего разбора.
#[derive(Clone, Debug)]
pub struct StuckBranch {
    /// Конструктор, который она разбирает.
    pub constructor: Name,
    /// Тело как значение - функция от полей конструктора.
    pub body: Rc<Value>,
}

/// Значение - терм, вычисленный до слабой головной нормальной формы.
#[derive(Clone, Debug)]
pub enum Value {
    /// Застрявшее вычисление: голова, к которой применены элиминаторы.
    ///
    /// Спайн хранится в порядке применения, то есть `x a b` - это голова `x`
    /// и спайн `[a, b]`.
    Neutral(Head, Vec<Elim>),
    /// Функция.
    Lam(Mult, Name, Closure),
    /// Тип функции вместе с row того, что происходит при применении (§3.4).
    Pi(Binder, Name, Rc<Value>, Row<Rc<Value>>, Closure),
    /// Тип записи - телескоп полей вместе с окружением.
    ///
    /// Хранится термами, а не значениями: тип поля живёт под предыдущими
    /// полями, поэтому вычислить его можно только тогда, когда их значения
    /// известны. Ровно тот же приём, что у [`Closure`], только связываний в нём
    /// не одно.
    Record(Telescope),
    /// Значение записи. Зависимости здесь уже нет - поля вычислены.
    Object(Rc<[(Name, Rc<Value>)]>),
    /// Сорт рядов `Row ℓ`.
    RowKind(Level),
    /// Сорт `Effect` - то, чем оканчивается тип формера метки (§3.4).
    EffectKind,
    /// Ряд - тот же телескоп, но сортом он не тип, а ряд.
    Row(Telescope),
    /// Универсум.
    Universe(Level),
}

/// Телескоп полей записи: термы вместе с окружением, в котором их вычислять.
#[derive(Clone, Debug)]
pub struct Telescope {
    pub(crate) env: Env,
    pub(crate) fields: Fields,
}

impl Telescope {
    /// Поля как они написаны - имена и кратности видны без вычисления.
    #[must_use]
    pub fn fields(&self) -> &[Field] {
        &self.fields.fields
    }

    /// Открыт ли ряд хвостом.
    #[must_use]
    pub fn is_open(&self) -> bool {
        self.fields.is_open()
    }

    /// Хвост-row как значение, если запись открыта.
    ///
    /// Вычисляется в окружении телескопа и **не** под полями: открытая запись
    /// зависимостей не имеет (§4.2, решение 2026-08-29), поэтому хвост от
    /// полей не зависит.
    #[must_use]
    pub fn tail(&self) -> Option<Rc<Value>> {
        self.fields
            .tail
            .as_ref()
            .map(|tail| crate::eval::eval(&self.env, tail))
    }

    /// Тип поля `index` при уже известных значениях предыдущих полей.
    ///
    /// # Panics
    ///
    /// Если значений меньше, чем полей до `index`: телескоп вычисляется по
    /// одному полю, и пропуск - баг вызывающего.
    #[must_use]
    pub fn at(&self, index: usize, earlier: &[Rc<Value>]) -> Rc<Value> {
        assert!(earlier.len() >= index, "телескоп вычисляется по порядку");
        let env = earlier[..index]
            .iter()
            .fold(self.env.clone(), |env, value| env.extend(Rc::clone(value)));
        crate::eval::eval(&env, &self.fields[index].ty)
    }
}

impl Value {
    /// Свободная переменная - нейтральное значение с пустым спайном.
    #[must_use]
    pub fn var(level: Lvl) -> Rc<Self> {
        Rc::new(Self::Neutral(Head::Local(level), Vec::new()))
    }

    /// Определение, ещё не развёрнутое.
    ///
    /// Аргументы уровня нормализуются здесь, и только здесь. Без этого
    /// `Box{max 0 1}` и `Box{1}` - разные головы, то есть один и тот же тип,
    /// записанный двумя способами, оказывается неконвертируемым сам с собой.
    /// У определения с телом это спасал бы δ-разворот, у постулата
    /// разворачивать нечего.
    #[must_use]
    pub fn constant(name: Name, levels: &[Level], rows: Rc<[Row<Rc<Self>>]>) -> Rc<Self> {
        let normalized: Rc<[Level]> = levels.iter().map(Level::normalize).collect();
        Rc::new(Self::Neutral(
            Head::Global(name, normalized, rows),
            Vec::new(),
        ))
    }
}

impl fmt::Display for Value {
    /// Печатает только форму значения: содержательный вывод получается
    /// обратным переводом в терм через [`crate::eval::quote`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Neutral(Head::Local(Lvl(level)), spine) => {
                write!(f, "@{level}·{}", spine.len())
            }
            Self::Neutral(Head::Global(name, ..), spine) => {
                write!(f, "{name}·{}", spine.len())
            }
            Self::Neutral(Head::Meta(TermMeta(name)), spine) => {
                write!(f, "?{name}·{}", spine.len())
            }
            Self::Lam(mult, name, _) => write!(f, "\\({mult} {name}) -> …"),
            Self::Pi(binder, name, _, row, _) => {
                let (open, close) = binder.visibility.brackets();
                write!(f, "{open}{} {name} : …{close} -> {row}…", binder.mult)
            }
            Self::Record(telescope) => write!(f, "{{…{}}}", telescope.fields().len()),
            Self::RowKind(level) => write!(f, "Row {level}"),
            Self::EffectKind => f.write_str("Effect"),
            Self::Row(telescope) => write!(f, "{{|{}}}", telescope.fields().len()),
            Self::Object(fields) => write!(f, "{{={}}}", fields.len()),
            Self::Universe(level) => write!(f, "Type {level}"),
        }
    }
}

/// Освобождение окружения идёт **циклом**, а не рекурсией.
///
/// Окружение - односвязный список ячеек, и его длина растёт с числом
/// связываний, а не с текстом программы: замыкание, снявшее окружение глубокой
/// раскрутки, носит его целиком. Рекурсивный `drop` кладёт стек там же, где и
/// на значении (§10 вопрос 92).
///
/// Разбор ячейки здесь свободен - [`Cell`] своего `Drop` не имеет, - поэтому
/// заглушка, нужная терму, тут не нужна.
impl Drop for Env {
    fn drop(&mut self) {
        let mut current = self.head.take();
        while let Some(cell) = current {
            // `None` - хвост делят с кем-то ещё, и дальше он не наш.
            let Some(cell) = Rc::into_inner(cell) else {
                break;
            };
            current = cell.rest;
        }
    }
}

/// Освобождение значения идёт **циклом**, а не рекурсией.
///
/// Цепочка конструкторов бывает какой угодно длины - список в сорок тысяч
/// звеньев есть `Cons x (Cons y …)` той же глубины, - и рекурсивный `drop`
/// кладёт на ней стек. Наблюдалось это как `SIGABRT` на программе, которая
/// глубокое значение **только строит и не обходит** (§10 вопрос 92): исполнение
/// к тому времени рекурсию уже не держало, а освобождение держало.
///
/// Снимаются только дети из спайна нейтрали: глубина берётся оттуда. Прочие
/// поля - окружение замыкания, телескоп записи - рвутся по-прежнему рекурсивно,
/// и предел у них остаётся; глубоким бывает и то и другое реже, а
/// единообразного способа отобрать `Rc<[T]>` по частям нет.
impl Drop for Value {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        detach(self, &mut pending);
        while let Some(value) = pending.pop() {
            // `None` - значение делят с кем-то ещё, и рвать его не наше дело.
            if let Some(mut owned) = Rc::into_inner(value) {
                detach(&mut owned, &mut pending);
            }
        }
    }
}

/// Отбирает у значения детей, которых предстоит освободить, не входя в них.
///
/// После этого собственный `drop` значения глубины не имеет: спайн пуст.
fn detach(value: &mut Value, into: &mut Vec<Rc<Value>>) {
    let Value::Neutral(_, spine) = value else {
        return;
    };
    for elim in spine.drain(..) {
        if let Elim::App(argument) = elim {
            into.push(argument);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{Elim, Env, Head, Lvl, Value};
    use crate::term::{Index, Term};

    /// Глубина, на которой рекурсивное освобождение кладёт стек теста
    /// заведомо: у тестового потока его два мегабайта.
    const DEEP: usize = 200_000;

    #[test]
    fn a_deep_constructor_chain_is_freed_without_the_rust_stack() {
        let mut value = Value::var(Lvl(0));
        for _ in 0..DEEP {
            value = Rc::new(Value::Neutral(Head::Local(Lvl(0)), vec![Elim::App(value)]));
        }
        drop(value);
    }

    #[test]
    fn a_deep_application_spine_is_freed_without_the_rust_stack() {
        let mut term = Rc::new(Term::Var(Index(0)));
        for _ in 0..DEEP {
            term = Rc::new(Term::App(Rc::new(Term::Var(Index(0))), term));
        }
        drop(term);
    }

    #[test]
    fn a_long_environment_is_freed_without_the_rust_stack() {
        let mut env = Env::default();
        for _ in 0..DEEP {
            env = env.extend(Value::var(Lvl(0)));
        }
        drop(env);
    }

    #[test]
    fn lookup_walks_outwards_from_the_innermost_binding() {
        let env = Env::default()
            .extend(Value::var(Lvl(0)))
            .extend(Value::var(Lvl(1)));

        // Index(0) - ближайшее связывание, то есть добавленное последним.
        assert!(matches!(
            *env.lookup(Index(0)).unwrap(),
            Value::Neutral(Head::Local(Lvl(1)), _)
        ));
        assert!(matches!(
            *env.lookup(Index(1)).unwrap(),
            Value::Neutral(Head::Local(Lvl(0)), _)
        ));
        assert!(env.lookup(Index(2)).is_none(), "за пределами окружения");
    }

    #[test]
    fn extending_does_not_disturb_the_original() {
        let outer = Env::default().extend(Value::var(Lvl(0)));
        let inner = outer.extend(Value::var(Lvl(1)));
        assert_eq!(outer.len(), 1);
        assert_eq!(inner.len(), 2);
    }

    #[test]
    fn levels_and_indices_are_mirror_images() {
        // В контексте размера 3 самое внешнее связывание - уровень 0 и
        // индекс 2; самое внутреннее - уровень 2 и индекс 0.
        assert_eq!(Lvl(0).to_index(3), Index(2));
        assert_eq!(Lvl(2).to_index(3), Index(0));
    }
}
