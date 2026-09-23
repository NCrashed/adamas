//! Что компилятор знает о теле, но в тексте не написано (§7.2).
//!
//! Два наблюдения, и оба собираются **в точке, где решение принято**: жизнь
//! ресурсного связывания (где взят, где закроется) и погашение эффекта (какую
//! метку снимает `handle`, кто её использует).
//!
//! # Записывается решение, а не его повторение
//!
//! §7.2 просит показывать «точки, где resource acquired и где cleanup будет
//! вставлен». Обе точки компилятор знает - он сам их и выбирает, - но знает
//! **мимоходом**: правило живёт в трёх местах [`crate::expr`], и каждое решает
//! свой род связывания (аннотированный `let`, `let` без аннотации, переменная
//! паттерна).
//!
//! Записывать их поэтому надо **там же, где решение принято**. Второй проход,
//! повторяющий правило по дереву, был бы второй записью того же правила, а
//! проект платил за такие пары четырежды за две волны: они расходятся молча, и
//! подсказка начинает врать ровно тогда, когда правило меняют.
//!
//! Из этого следует и направление отказа. Путь вставки, который забыли сюда
//! записать, даёт **отсутствующую** подсказку, а не ложную: показать нечего, и
//! читатель ничего не узнаёт. Обратное - повторение правила снаружи - даёт
//! ложную.
//!
//! # Что значит «закроется здесь»
//!
//! Не всякое ресурсное связывание закрывается на месте: расходованное дальше
//! закрывает тот, кто его взял. [`Lifecycle::released`] это и различает, и
//! различение здесь несущее - §7.2 просит эту запись ровно затем, чтобы
//! «понимать exceptional-exit cleanup поведение» (§3.3 × §3.4).

use adamas_core::source::Span;
use adamas_parser::ast::Symbol;

use crate::own::Ownership;

/// Жизнь одного связывания владеемого типа.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lifecycle {
    /// Имя связывания, как оно написано.
    pub name: Symbol,
    /// Чем объявлен его тип: `resource` либо `unique data` (§3.3).
    pub owned: Ownership,
    /// Где ресурс взят - само связывание.
    pub acquired: Span,
    /// Деструктор и место, где компилятор вставит его вызов.
    ///
    /// `None` - вставки нет. Причин две, и обе законны: связывание расходуется
    /// дальше (закрывает взявший) либо тип объявлен `unique data`, у которого
    /// деструктора нет вовсе.
    pub released: Option<Released>,
}

/// Куда встанет вызов деструктора.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Released {
    /// Имя деструктора.
    pub drop: Symbol,
    /// Конец области видимости связывания - место вставки.
    pub at: Span,
}

/// Собранное за прогон, в порядке появления.
#[derive(Clone, Debug, Default)]
pub struct Lifecycles {
    found: Vec<Lifecycle>,
}

impl Lifecycles {
    /// Пусто.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Запоминает связывание.
    ///
    /// Первая запись побеждает: элаборация одного и того же места случается
    /// дважды - спекулятивный проход откатывается, - и вторая запись отличалась
    /// бы от первой только тем, что пришла позже.
    pub(crate) fn seen(&mut self, found: Lifecycle) {
        if self.found.iter().any(|it| it.acquired == found.acquired) {
            return;
        }
        self.found.push(found);
    }

    /// Связывания в порядке появления.
    pub fn iter(&self) -> impl Iterator<Item = &Lifecycle> {
        self.found.iter()
    }

    /// Сколько их.
    #[must_use]
    pub fn len(&self) -> usize {
        self.found.len()
    }

    /// Пусто ли.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.found.is_empty()
    }
}

/// Погашение метки: какой эффект снимает этот `handle`.
///
/// Метка в тексте чаще **не написана**: `handle` берёт её из первой ветки, и
/// на корпусе так написаны 151 хендлер из 175 - `handle counter with …` не
/// называет `State` нигде. Знает её компилятор
/// ([`crate::expr::Elaborator::handled_effect`]), и показать её - значит
/// показать посчитанное, а не пересказать текст.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Handler {
    /// Имя эффекта, как его объявили (квалифицированное).
    pub effect: Symbol,
    /// Определение, в теле которого стоит `handle`.
    ///
    /// Им хендлер и называется читателю: номер строки говорит «где», а имя -
    /// «что это». В файле `eval/state.adamas` четыре хендлера одной метки, и
    /// различает их именно оно.
    pub owner: Symbol,
    /// Где стоит `handle`.
    pub at: Span,
}

/// Использование операции: где написано и какой метке принадлежит.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Performed {
    /// Имя операции, как оно написано.
    pub name: Symbol,
    /// Эффект, которому операция принадлежит.
    pub effect: Symbol,
    /// Где написано.
    pub at: Span,
}

/// Хендлеры файла и использования операций - в порядке появления.
#[derive(Clone, Debug, Default)]
pub struct Handlers {
    sites: Vec<Handler>,
    used: Vec<Performed>,
}

impl Handlers {
    /// Пусто.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Запоминает погашение. Первая запись побеждает - по тому же доводу, что
    /// у [`Lifecycles::seen`].
    pub(crate) fn discharges(&mut self, found: Handler) {
        if self.sites.iter().any(|it| it.at == found.at) {
            return;
        }
        self.sites.push(found);
    }

    /// Запоминает использование операции.
    pub(crate) fn performs(&mut self, found: Performed) {
        if self.used.iter().any(|it| it.at == found.at) {
            return;
        }
        self.used.push(found);
    }

    /// Погашения в порядке появления.
    pub fn sites(&self) -> impl Iterator<Item = &Handler> {
        self.sites.iter()
    }

    /// Использования операций в порядке появления.
    pub fn used(&self) -> impl Iterator<Item = &Performed> {
        self.used.iter()
    }

    /// Места, где эта метка гасится **в этом файле**, в порядке появления.
    ///
    /// Пусто - в этом файле не гасится: метка уходит в ряд, и снимет её тот,
    /// кто позовёт. Это не пробел анализа, а свойство языка: `handle` берёт
    /// **названное** вычисление (§3.4), поэтому операция и её хендлер стоят в
    /// разных телах почти всегда.
    pub fn discharging<'a>(&'a self, effect: &'a str) -> impl Iterator<Item = &'a Handler> {
        self.sites.iter().filter(move |it| &*it.effect == effect)
    }
}

/// Оба наблюдения одного прохода.
#[derive(Clone, Debug, Default)]
pub struct Observed {
    /// Жизнь ресурсных связываний.
    pub lifecycles: Lifecycles,
    /// Погашения меток и использования операций.
    pub handlers: Handlers,
}

impl Observed {
    /// Пусто.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}
