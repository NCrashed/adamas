//! Сообщения компилятора на языке пользователя (§7.6).
//!
//! Тексты лежат каталогами Fluent, по файлу на часть компилятора и на язык, и
//! вшиты в бинарь. Код называет сообщение идентификатором и аргументами по
//! имени ([`tr!`]); порядок слов, падежи и множественное число - дело
//! каталога. Языков два: русский и английский; всё, что не русский, -
//! английский, и недостающее в русском каталоге берётся оттуда же.
//!
//! Язык один на процесс. Драйвер берёт его из окружения ([`current`]), сервер
//! LSP - из `initialize.locale` клиента ([`set`]).

use std::borrow::Cow;
use std::fmt;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU8, Ordering};

use fluent_bundle::concurrent::FluentBundle;
use fluent_bundle::{FluentArgs, FluentResource, FluentValue};

/// Язык сообщений.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lang {
    /// Русский.
    Ru,
    /// Английский - он же запасной.
    En,
}

impl Lang {
    /// Язык по тегу локали: `ru`, `ru_RU.UTF-8`, `ru-RU`. Не русский -
    /// английский, включая `C` и `POSIX`.
    #[must_use]
    pub fn from_tag(tag: &str) -> Self {
        let language = tag.split(['_', '-', '.', '@']).next().unwrap_or("");
        if language.eq_ignore_ascii_case("ru") {
            Self::Ru
        } else {
            Self::En
        }
    }

    fn code(self) -> u8 {
        match self {
            Self::Ru => 1,
            Self::En => 2,
        }
    }

    fn of(code: u8) -> Option<Self> {
        match code {
            1 => Some(Self::Ru),
            2 => Some(Self::En),
            _ => None,
        }
    }
}

/// Переменные окружения, по которым выбирается язык, в порядке старшинства.
///
/// `ADAMAS_LANG` - своя и старше всех: ею тесты фиксируют язык снимков, не
/// трогая локаль процесса. Дальше - порядок POSIX: `LC_ALL` перекрывает
/// `LC_MESSAGES`, тот - `LANG`.
pub const VARIABLES: [&str; 4] = ["ADAMAS_LANG", "LC_ALL", "LC_MESSAGES", "LANG"];

/// Язык по окружению: первая непустая переменная из [`VARIABLES`].
#[must_use]
pub fn detect(lookup: impl Fn(&str) -> Option<String>) -> Lang {
    VARIABLES
        .iter()
        .find_map(|name| lookup(name).filter(|value| !value.is_empty()))
        .map_or(Lang::En, |tag| Lang::from_tag(&tag))
}

static CURRENT: AtomicU8 = AtomicU8::new(0);

/// Язык процесса: заданный [`set`], иначе взятый из окружения при первом
/// вопросе.
#[must_use]
pub fn current() -> Lang {
    if let Some(lang) = Lang::of(CURRENT.load(Ordering::Relaxed)) {
        return lang;
    }
    let lang = detect(|name| std::env::var(name).ok());
    CURRENT.store(lang.code(), Ordering::Relaxed);
    lang
}

/// Задаёт язык процесса - так его выбирает клиент LSP.
pub fn set(lang: Lang) {
    CURRENT.store(lang.code(), Ordering::Relaxed);
}

/// Каталог по имени файла: тексты на обоих языках.
macro_rules! catalog {
    ($file:literal) => {
        (
            $file,
            include_str!(concat!("../locales/ru/", $file)),
            include_str!(concat!("../locales/en/", $file)),
        )
    };
}

/// Каталоги: имя файла и тексты на обоих языках. Порядок не значим.
pub const CATALOGS: &[(&str, &str, &str)] = &[
    catalog!("common.ftl"),
    catalog!("parser.ftl"),
    catalog!("core.ftl"),
    catalog!("elab.ftl"),
    catalog!("codegen.ftl"),
    catalog!("interp.ftl"),
    catalog!("pkg.ftl"),
];

fn bundle(lang: Lang) -> &'static FluentBundle<FluentResource> {
    static RU: OnceLock<FluentBundle<FluentResource>> = OnceLock::new();
    static EN: OnceLock<FluentBundle<FluentResource>> = OnceLock::new();
    let (cell, tag) = match lang {
        Lang::Ru => (&RU, "ru"),
        Lang::En => (&EN, "en"),
    };
    cell.get_or_init(|| built(lang, tag))
}

#[allow(
    clippy::expect_used,
    reason = "каталоги вшиты в бинарь; разбор и полноту сверяет `tests/catalogs.rs`"
)]
fn built(lang: Lang, tag: &str) -> FluentBundle<FluentResource> {
    let mut bundle = FluentBundle::new_concurrent(vec![tag.parse().expect("тег языка")]);
    // Без этого Fluent обнимает каждую подстановку знаками изоляции
    // направления (U+2068, U+2069): в терминале они невидимы, а в снимках и
    // сравнениях строк - нет.
    bundle.set_use_isolating(false);
    for (_, ru, en) in CATALOGS {
        let text = match lang {
            Lang::Ru => ru,
            Lang::En => en,
        };
        let resource = FluentResource::try_new((*text).to_owned()).expect("каталог разбирается");
        bundle
            .add_resource(resource)
            .expect("идентификаторы не повторяются");
    }
    bundle
}

/// Аргумент сообщения.
#[derive(Debug)]
pub enum Arg {
    /// Текст: имя, тип, путь - всё, что вставляется как есть.
    Text(String),
    /// Число, по которому каталог выбирает форму слова.
    Count(i64),
}

/// Число, по которому каталог выбирает форму слова: аргумент `count(len)`.
#[must_use]
pub fn count(n: impl TryInto<i64>) -> Arg {
    Arg::Count(n.try_into().unwrap_or(i64::MAX))
}

/// Что можно подставить в сообщение.
pub trait ToArg {
    /// Аргумент из значения.
    fn to_arg(&self) -> Arg;
}

impl<T: fmt::Display + ?Sized> ToArg for T {
    fn to_arg(&self) -> Arg {
        Arg::Text(self.to_string())
    }
}

impl ToArg for Arg {
    fn to_arg(&self) -> Arg {
        match self {
            Self::Text(text) => Self::Text(text.clone()),
            Self::Count(n) => Self::Count(*n),
        }
    }
}

/// Текст сообщения `id` на языке процесса.
///
/// Нет его в каталоге языка - берётся английский; нет и там - печатается сам
/// идентификатор. Второго не бывает при зелёном `tests/catalogs.rs`.
#[must_use]
pub fn message(id: &str, args: &[(&str, Arg)]) -> String {
    message_in(current(), id, args)
}

/// То же на заданном языке.
#[must_use]
pub fn message_in(lang: Lang, id: &str, args: &[(&str, Arg)]) -> String {
    let found = |lang| {
        let bundle = bundle(lang);
        Some((bundle, bundle.get_message(id)?.value()?))
    };
    let Some((bundle, pattern)) = found(lang).or_else(|| found(Lang::En)) else {
        return id.to_owned();
    };
    let mut fluent = FluentArgs::new();
    for (name, arg) in args {
        let value = match arg {
            Arg::Text(text) => FluentValue::String(Cow::Borrowed(text.as_str())),
            Arg::Count(n) => FluentValue::from(*n),
        };
        fluent.set(*name, value);
    }
    let mut errors = Vec::new();
    bundle
        .format_pattern(pattern, Some(&fluent), &mut errors)
        .into_owned()
}

/// Текст без аргументов там, где ждут `&'static str`: причины отказов и
/// названия мест, которые хранятся в ошибках полями.
///
/// Переводится однажды на пару «язык, идентификатор» и запоминается навсегда:
/// пар не больше, чем сообщений в каталогах, поэтому память ограничена.
#[must_use]
pub fn text(id: &'static str) -> &'static str {
    use std::collections::HashMap;
    use std::sync::Mutex;
    static MEMO: OnceLock<Mutex<HashMap<(u8, &'static str), &'static str>>> = OnceLock::new();
    let lang = current();
    let memo = MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    let mut memo = memo
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    memo.entry((lang.code(), id))
        .or_insert_with(|| Box::leak(message_in(lang, id, &[]).into_boxed_str()))
}

/// [`text`] с идентификатором-литералом: `text!(…)`.
#[macro_export]
macro_rules! text {
    ($id:literal) => {
        $crate::text($id)
    };
}

/// Сообщение по идентификатору и аргументам: `tr!("parse-expected", expected
/// = e, found = f)`.
#[macro_export]
macro_rules! tr {
    ($id:literal $(, $name:ident = $value:expr)* $(,)?) => {
        $crate::message(
            $id,
            &[$((::core::stringify!($name), $crate::ToArg::to_arg(&$value))),*],
        )
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_first_set_variable_wins() {
        let env = |pairs: &'static [(&'static str, &'static str)]| {
            move |name: &str| {
                pairs
                    .iter()
                    .find(|(key, _)| *key == name)
                    .map(|(_, value)| (*value).to_owned())
            }
        };
        assert_eq!(detect(env(&[("LANG", "ru_RU.UTF-8")])), Lang::Ru);
        assert_eq!(
            detect(env(&[("LANG", "ru_RU.UTF-8"), ("LC_ALL", "C")])),
            Lang::En
        );
        assert_eq!(
            detect(env(&[("LC_ALL", ""), ("LANG", "ru_RU.UTF-8")])),
            Lang::Ru,
            "пустая переменная не считается"
        );
        assert_eq!(
            detect(env(&[("ADAMAS_LANG", "ru"), ("LC_ALL", "en_US.UTF-8")])),
            Lang::Ru
        );
        assert_eq!(detect(env(&[])), Lang::En);
        assert_eq!(Lang::from_tag("ru-RU"), Lang::Ru);
        assert_eq!(Lang::from_tag("de_DE"), Lang::En);
    }
}
