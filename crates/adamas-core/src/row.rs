//! Row эффектов - поле `Pi` (§3.2, §3.4).
//!
//! Зависимая функция ядра есть `(q x : A) -> ε ▷ B`: кратность, тип аргумента,
//! **row** и кодомен. Row описывает, что происходит при применении, поэтому
//! стоит там же, где кратность, и по той же причине - принимающая сторона
//! обязана знать контракт до вызова. Отдельного конструктора «тип вычисления»
//! в ядре нет.
//!
//! # Почему поле заводится сейчас
//!
//! Довод не эстетический, а про асимметрию цены, и он тот же, что был назван
//! логом 2026-08-21 для кратностей: **добавить поле в `Pi` задним числом
//! означает тронуть все места конструирования** - их около восьмидесяти, - а
//! добавить правило задним числом означает тронуть один модуль. Поэтому
//! представление идёт здесь, а погашение, хендлеры и объявление эффектов -
//! Фазой 4.
//!
//! # Чего здесь нет и почему
//!
//! **Суждение окружающей row не несёт.** По той же причине: правило «ограничение
//! вводит применение» (§3.4) появляется вместе с погашением, а компонента,
//! которая всегда пуста и которую никто не читает, - тот же механизм без
//! потребителя, только протянутый через весь модуль.
//!
//! # Что здесь есть
//!
//! Каноническая форма и сравнение. Метки группируются по имени, порядок внутри
//! группы **значим** и сохраняется (внутренний хендлер перехватывает раньше
//! внешнего, §4.1), группы между собой упорядочены по имени. Отсюда `A -> {IO}
//! B` и `A -> B` - разные типы, ровно как `(1 x : A) -> B` и `(ω x : A) -> B`.
//!
//! **Хвост.** Row оканчивается либо ничем - тогда она закрыта, - либо
//! параметром определения ([`RowVar`]), либо дыркой ([`RowMeta`]). Устроено это
//! по образцу `Level` (§3.2): row не тип, связывания под неё не заводится, а
//! обобщение на границе определения превращает дырку в параметр. Отличие от
//! уровня одно и названо §3.2: атом уровня есть переменная, атом row есть
//! метка, несущая термы, поэтому нормальная форма row полна с точностью до
//! конвертируемости аргументов меток.

use std::fmt;
use std::rc::Rc;

use crate::term::Name;

/// Параметр-row определения: `f : A -> {IO | e} B` несёт один такой.
///
/// По образцу [`crate::level::LevelVar`]: номер параметра в списке, а не имя.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RowVar(pub u32);

/// Метапеременная row - то, что обобщение превращает в [`RowVar`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RowMeta(pub u32);

/// Чем row продолжается сверх написанных меток.
///
/// Отсутствие хвоста - закрытая row: `{IO}` означает «ровно `IO` и ничего
/// больше». Хвост делает её открытой: `{IO | e}` означает «`IO` и что угодно
/// ещё».
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tail {
    /// Параметр определения.
    Var(RowVar),
    /// Дырка, которую решит унификация либо обобщит объявление.
    Meta(RowMeta),
}

impl fmt::Display for Tail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(RowVar(index)) => write!(f, "e{index}"),
            Self::Meta(RowMeta(name)) => write!(f, "?{name}"),
        }
    }
}

/// Метка эффекта: конструктор и его аргументы.
///
/// Аргументы - обычные термы (или значения на стороне [`crate::value`]):
/// `State Int` есть метка `State`, применённая к типу.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label<T> {
    /// Имя конструктора метки.
    pub name: Name,
    /// Аргументы, к которым он применён.
    pub arguments: Vec<T>,
}

/// Row: набор меток в канонической форме.
///
/// Обобщена по нагрузке, потому что в терме аргументы метки - термы, а в
/// значении - значения, и другой разницы между двумя формами нет.
/// Метки за одним указателем.
///
/// Тонкий указатель, а не `Rc<[Label<T>]>`: тот вдвое шире, и разница ложится
/// на `Term` - узел `Pi` стоит в каждом типе функции в программе. Row при этом
/// холодная: её читают сравнение и печать, поэтому лишняя косвенность не стоит
/// ничего, а восемь байт на каждом терме стоят.
#[derive(Debug, PartialEq, Eq)]
struct Labels<T> {
    labels: Vec<Label<T>>,
    /// Чем row продолжается. `None` - закрыта.
    tail: Option<Tail>,
}

/// Пустая row - `None`, а не пустой срез: у подавляющего большинства стрелок
/// эффектов нет вовсе, и аллокация под заголовок `Rc` была бы платой за
/// хранение ничего.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row<T>(Option<Rc<Labels<T>>>);

impl<T> Row<T> {
    /// Пустая row - «применение ничего не делает».
    #[must_use]
    pub const fn empty() -> Self {
        Self(None)
    }

    /// Собирает row, приводя метки к канонической форме.
    ///
    /// Сортировка **устойчивая**: порядок внутри группы одноимённых меток
    /// значим и сохраняется, а группы между собой выстраиваются по имени.
    #[must_use]
    pub fn new(labels: impl IntoIterator<Item = Label<T>>) -> Self {
        Self::closing(labels, None)
    }

    /// То же с хвостом: `{IO | e}`.
    ///
    /// Row из одного хвоста законна и не схлопывается в «пусто»: `{| e}`
    /// означает «что угодно», а пустая - «ничего».
    #[must_use]
    pub fn closing(labels: impl IntoIterator<Item = Label<T>>, tail: Option<Tail>) -> Self {
        let mut labels: Vec<Label<T>> = labels.into_iter().collect();
        if labels.is_empty() && tail.is_none() {
            return Self::empty();
        }
        labels.sort_by(|left, right| left.name.cmp(&right.name));
        Self(Some(Rc::new(Labels { labels, tail })))
    }

    /// Метки в каноническом порядке.
    #[must_use]
    pub fn labels(&self) -> &[Label<T>] {
        self.0.as_ref().map_or(&[], |it| &it.labels)
    }

    /// Чем row продолжается. `None` - закрыта.
    #[must_use]
    pub fn tail(&self) -> Option<Tail> {
        self.0.as_ref().and_then(|it| it.tail)
    }

    /// Ничего не происходит при применении: ни меток, ни хвоста.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Переносит row на другую нагрузку - `eval` и `quote` ходят этим путём.
    ///
    /// Порядок сохраняется, а не пересобирается: он уже канонический, и
    /// отображение нагрузки имён не трогает.
    pub fn map<U>(&self, mut carry: impl FnMut(&T) -> U) -> Row<U> {
        let Some(labels) = &self.0 else {
            return Row::empty();
        };
        Row(Some(Rc::new(Labels {
            labels: labels
                .labels
                .iter()
                .map(|label| Label {
                    name: Name::clone(&label.name),
                    arguments: label.arguments.iter().map(&mut carry).collect(),
                })
                .collect(),
            tail: labels.tail,
        })))
    }

    /// Совпадают ли формы двух row - имена и число аргументов.
    ///
    /// Сами аргументы сравнивает вызывающий: в значениях это
    /// конвертируемость, а она живёт в [`crate::conv`] и знает про сигнатуру.
    #[must_use]
    pub fn same_shape<U>(&self, other: &Row<U>) -> bool {
        // Хвосты сравниваются как метки - синтаксически: параметр равен себе,
        // дырка равна себе, а решать их - работа унификации, не сравнения.
        self.tail() == other.tail()
            && self.labels().len() == other.labels().len()
            && self
                .labels()
                .iter()
                .zip(other.labels())
                .all(|(left, right)| {
                    left.name == right.name && left.arguments.len() == right.arguments.len()
                })
    }

    /// Аргументы обеих row попарно, в каноническом порядке.
    pub fn zip<'a, U>(&'a self, other: &'a Row<U>) -> impl Iterator<Item = (&'a T, &'a U)> {
        self.labels()
            .iter()
            .zip(other.labels())
            .flat_map(|(left, right)| left.arguments.iter().zip(&right.arguments))
    }
}

impl<T> Default for Row<T> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T: fmt::Display> fmt::Display for Row<T> {
    /// `{State Int, IO}`. Пустая row не печатается вовсе - её отсутствие и
    /// означает чистую стрелку.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return Ok(());
        }
        f.write_str("{")?;
        for (position, label) in self.labels().iter().enumerate() {
            if position > 0 {
                f.write_str(", ")?;
            }
            f.write_str(&label.name)?;
            for argument in &label.arguments {
                write!(f, " {argument}")?;
            }
        }
        if let Some(tail) = self.tail() {
            if self.labels().is_empty() {
                write!(f, "| {tail}")?;
            } else {
                write!(f, " | {tail}")?;
            }
        }
        f.write_str("} ")
    }
}
