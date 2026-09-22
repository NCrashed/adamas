//! Трамплины колбэка: чужая сторона зовёт наш код (§5.3, уровни 1, 2 и 3).
//!
//! Понижение отдаёт чужой стороне адрес порождённой функции, и стоит это ноль.
//! У машины порождённой функции нет вовсе - есть терм и вычислитель, - поэтому
//! отдаётся адрес **статического** трамплина. Договор корпуса требует согласия
//! трёх вычислителей (§10 вопрос 182, вариант (а)), и без этого модуля машина
//! отстала бы ровно на той волне, ради которой договор и заводился.
//!
//! # Таблица, а не одна запись
//!
//! Трамплинов у каждой формы **[`SLOTS`] штук**, и запись о том, кого они
//! зовут, лежит в таблице того же размера. Так требует §5.3 у уровня 3, и цена
//! там же названа прямо: число одновременно живых колбэков ограничено, и
//! ограничение это обязано быть **видно в API обёртки**, а не всплывать в
//! рантайме. Видно оно ответом `adamas_callback_register`: полная таблица
//! отдаёт ноль, и
//! обёртка обязана этот ноль разобрать.
//!
//! Прежняя редакция держала одну запись на уровень, и оттого уровень 3 не
//! выражался вовсе: регистрация снималась возвратом из того чужого вызова, в
//! котором сделана, а `CURLOPT_WRITEFUNCTION` ставится одним вызовом и зовётся
//! другим.
//!
//! # Что лежит в таблице, а что едет `userdata`
//!
//! Уровень 1: `dlsym`-адрес есть `extern "C" fn`, среды у такого указателя нет
//! по построению, и кого зовёт трамплин, помнит слот таблицы.
//!
//! Уровень 2: среда есть, и едет она **последним словом** - ровно как у
//! понижения. В слоте остаётся только то, чему у чужой стороны соответствия нет
//! вовсе: сигнатура и список библиотек. Иначе договор трёх вычислителей про
//! `userdata` не говорил бы ничего - обе стороны считали бы через один и тот же
//! обход.
//!
//! Уровень 3: слот занимается `adamas_callback_register` и освобождается
//! [`release`], то есть живёт **дольше вызова**. Обёртка держит его полем `resource`, и
//! деструктор снимает регистрацию (§5.3, §3.3).
//!
//! Машина однопоточна ([`std::rc::Rc`] в значениях), поэтому таблицы в
//! переменной потока довольно.
//!
//! # Три формы, и у каждой свидетель
//!
//! Поддержаны `(UInt64, UInt64) -> Int32` и он же с `userdata` третьим словом
//! (компараторы `qsort` и `qsort_r`), а также
//! `(UInt64, UInt64, UInt64, UInt64) -> UInt64` - write-колбэк libcurl. Граница
//! та же и по той же арифметике, что у таблицы сигнатур [`crate::foreign`]: у
//! арности `k` над плоскими типами §4.11 форм `10^(k+1)`, и настоящий ответ на
//! это - libffi, а не порождение. Вторая форма добавляется десятком строк и
//! обязана приходить со своим свидетелем.
//!
//! # Чего машина не умеет, и это названо
//!
//! Колбэк идёт **отдельным прогоном** ([`crate::run_linked`]), и стек
//! хендлеров места регистрации тому прогону не виден: операция внутри колбэка
//! остаётся без площадки, хотя площадка стоит снаружи чужого вызова.
//! Понижения ту же программу считают - вектор evidence едет им в `userdata`
//! (§5.3), а у машины вектора нет вовсе. Расхождение объявлено отказом с
//! названной причиной и закреплено свидетелем
//! (`adamas-codegen/tests/userdata.rs`).
//!
//! # Вложенность
//!
//! Слоты выдаются по одному, и занятый слот освобождается дропом своей
//! [`Registration`]. Нужно это не ради двух колбэков в одном вызове, а ради
//! **пересечения внутри колбэка**: наш компаратор вправе позвать `memcmp`, и
//! пересечение это идёт тем же путём.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::{Cross, Crossing, Signature};
use adamas_core::term::{Args, Name, Term};

use crate::RunError;
use crate::foreign::Linkage;

/// Слотов в таблице трамплинов (§5.3, уровень 3).
///
/// Число фиксировано, и в этом весь смысл: трамплин у машины есть
/// **порождённая на этапе сборки** функция, а породить их по числу колбэков
/// программы нечем. Четыре - не замер, а выбор: меньше не даёт наблюдать
/// переполнение на паре колбэков, больше ничего не покупает. Обёртка узнаёт
/// предел ответом `adamas_callback_register`, а не падением.
pub(crate) const SLOTS: usize = 4;

/// Кого зовёт трамплин, пока управление у чужой стороны.
///
/// Сигнатура - указателем, а не ссылкой: таблица живёт в статике потока, а
/// `'static` у сигнатуры машины нет. Держит её живой прогон: таблица чистится
/// на выходе из **внешнего** прогона ([`Scope`]), то есть раньше, чем кончится
/// заимствование.
///
/// Связывание - копией: слот уровня 3 переживает вызов, а список библиотек у
/// вложенного прогона свой, и указателем на него слот указывал бы в мёртвое.
struct Registered {
    signature: *const Signature,
    linkage: Linkage,
    code: Code,
}

/// Кого зовёт трамплин: имя экспорта либо замыкание, приехавшее `userdata`.
enum Code {
    /// Уровень 1: имя определения, видимого C.
    Named(Name),
    /// Уровень 2: терм замыкания. Держит его сама регистрация - иначе адрес,
    /// розданный чужой стороне, указывал бы в освобождённое.
    Closed(Rc<Term>),
}

thread_local! {
    /// Таблица регистраций: слот занят либо свободен.
    ///
    /// `None` в слоте, чей трамплин позвали, - отказ, а не догадка.
    static TABLE: RefCell<[Option<Registered>; SLOTS]> =
        const { RefCell::new([const { None }; SLOTS]) };
    /// Глубина прогонов машины: таблица чистится на выходе из внешнего.
    static DEPTH: Cell<usize> = const { Cell::new(0) };
    /// Отказ, случившийся **внутри** колбэка.
    ///
    /// Отдельно, потому что отдать его чужой стороне нечем: она ждёт `int`.
    /// Раскрутка через сишный кадр запрещена §5.3 ровно тем же правилом,
    /// которое проверяет экспорт, и паника здесь была бы его нарушением с
    /// нашей же стороны. Забирает отказ [`taken`] - сразу после вызова.
    static FAILED: RefCell<Option<RunError>> = const { RefCell::new(None) };
}

/// Прогон машины: на выходе из внешнего таблица чистится.
///
/// Слот уровня 3 вправе пережить чужой вызов, но пережить **прогон** он не
/// вправе: сигнатура в нём - указатель, а дальше прогона о её жизни не знает
/// никто. Течь слота поэтому наблюдаема, как наблюдаема течь блока: слот,
/// не освобождённый обёрткой, подметается здесь.
pub(crate) struct Scope;

impl Scope {
    /// Входит в прогон.
    pub(crate) fn entered() -> Self {
        DEPTH.with(|it| it.set(it.get() + 1));
        Self
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        let left = DEPTH.with(|it| {
            let left = it.get().saturating_sub(1);
            it.set(left);
            left
        });
        if left == 0 {
            TABLE.with(|it| *it.borrow_mut() = [const { None }; SLOTS]);
        }
    }
}

/// Форма трамплина: что чужая сторона передаёт нашему коду и чем он отвечает.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// `int (*)(const void *, const void *)` - компаратор `qsort`.
    Compare,
    /// `int (*)(const void *, const void *, void *)` - компаратор `qsort_r`,
    /// `userdata` последним словом (уровень 2).
    CompareEnv,
    /// `size_t (*)(char *, size_t, size_t, void *)` - write-колбэк libcurl.
    Write,
}

/// Трамплины одной формы, по одному на слот.
///
/// Слот у трамплина - **его собственный номер**, вписанный при порождении:
/// чужая сторона передаёт только то, что написано в сигнатуре колбэка, и места
/// под номер слота там нет. Оттого функций и нужно [`SLOTS`] штук на форму, а
/// не одна с аргументом.
macro_rules! comparing {
    ($($slot:literal),+) => {
        [$({
            extern "C" fn tramp(left: u64, right: u64) -> i32 {
                narrow(guarded($slot, &[left, right], None))
            }
            tramp
        }),+]
    };
}

macro_rules! comparing_env {
    ($($slot:literal),+) => {
        [$({
            extern "C" fn tramp(left: u64, right: u64, env: u64) -> i32 {
                narrow(guarded($slot, &[left, right], Some(env)))
            }
            tramp
        }),+]
    };
}

macro_rules! writing {
    ($($slot:literal),+) => {
        [$({
            extern "C" fn tramp(a: u64, b: u64, c: u64, d: u64) -> u64 {
                wide(guarded($slot, &[a, b, c, d], None))
            }
            tramp
        }),+]
    };
}

/// Трамплины формы [`Shape::Compare`]: по одному на слот.
static COMPARE: [extern "C" fn(u64, u64) -> i32; SLOTS] = comparing!(0, 1, 2, 3);

/// Трамплины формы [`Shape::CompareEnv`]: последнее слово - `userdata`.
static COMPARE_ENV: [extern "C" fn(u64, u64, u64) -> i32; SLOTS] = comparing_env!(0, 1, 2, 3);

/// Трамплины формы [`Shape::Write`]: четыре слова, ответ словом.
///
/// Последнее слово - `userdata` **чужой стороны** (`CURLOPT_WRITEDATA`), а не
/// наша среда: уровень 3 идёт экспортом, у которого среды нет вовсе. Оттого
/// оно и едет колбэку обычным аргументом.
static WRITE: [extern "C" fn(u64, u64, u64, u64) -> u64; SLOTS] = writing!(0, 1, 2, 3);

/// Адрес трамплина формы в слоте.
fn address_of(shape: Shape, slot: usize) -> u64 {
    match shape {
        Shape::Compare => COMPARE[slot] as usize as u64,
        Shape::CompareEnv => COMPARE_ENV[slot] as usize as u64,
        Shape::Write => WRITE[slot] as usize as u64,
    }
}

/// Слот по адресу трамплина: `None` - адрес не наш.
fn slot_of(address: u64) -> Option<usize> {
    (0..SLOTS).find(|slot| {
        address_of(Shape::Compare, *slot) == address
            || address_of(Shape::CompareEnv, *slot) == address
            || address_of(Shape::Write, *slot) == address
    })
}

/// Живая регистрация: слот освобождается дропом.
///
/// Уровень 3 дроп **отменяет** ([`Registration::kept`]): там слот живёт до
/// [`release`], то есть до деструктора обёртки.
pub(crate) struct Registration {
    slot: usize,
}

impl Registration {
    /// Оставляет слот занятым: регистрация переживает вызов (уровень 3).
    pub(crate) fn kept(self) {
        std::mem::forget(self);
    }
}

impl Drop for Registration {
    fn drop(&mut self) {
        let slot = self.slot;
        TABLE.with(|it| it.borrow_mut()[slot] = None);
    }
}

/// Свободен ли хоть один слот таблицы.
pub(crate) fn vacant() -> bool {
    TABLE.with(|it| it.borrow().iter().any(Option::is_none))
}

/// Занимает свободный слот записью.
fn claim(entry: Registered, symbol: &str) -> Result<Registration, RunError> {
    TABLE.with(|it| {
        let mut table = it.borrow_mut();
        let Some(slot) = table.iter().position(Option::is_none) else {
            return Err(RunError::Callback {
                symbol: symbol.to_owned(),
                why: format!(
                    "таблица трамплинов машины полна: слотов {SLOTS}, и все заняты \
                     (§5.3, уровень 3)"
                ),
            });
        };
        table[slot] = Some(entry);
        Ok(Registration { slot })
    })
}

/// Освобождает слот по адресу трамплина.
///
/// `false` - адрес не принадлежит таблице либо слот уже свободен. Ответ этот
/// едет наружу числом, а не отказом: снять незанятую регистрацию - ошибка
/// обёртки, и разбирает её обёртка.
pub(crate) fn release(address: u64) -> bool {
    let Some(slot) = slot_of(address) else {
        return false;
    };
    TABLE.with(|it| it.borrow_mut()[slot].take().is_some())
}

/// Регистрирует определение под трамплином и отдаёт адрес трамплина словом.
///
/// Форма проверяется здесь: отдать чужой стороне адрес трамплина, чья
/// сигнатура не та, значило бы позвать наш код по чужому ABI.
///
/// # Errors
///
/// [`RunError::Callback`] - формы экспорта нет среди трамплинов либо таблица
/// полна.
pub(crate) fn registered(
    signature: &Signature,
    linkage: &Linkage,
    name: &Name,
    shape: &Crossing,
) -> Result<(Registration, u64), RunError> {
    let words: Vec<PrimTy> = shape
        .params
        .iter()
        .filter_map(|it| match it {
            Cross::Word(ty) => Some(*ty),
            _ => None,
        })
        .collect();
    if words.len() != shape.params.len() {
        return Err(unsupported(&shape.symbol));
    }
    let form = match (words.as_slice(), shape.result) {
        ([PrimTy::UInt64, PrimTy::UInt64], Some(PrimTy::Int32)) => Shape::Compare,
        (
            [
                PrimTy::UInt64,
                PrimTy::UInt64,
                PrimTy::UInt64,
                PrimTy::UInt64,
            ],
            Some(PrimTy::UInt64),
        ) => Shape::Write,
        _ => return Err(unsupported(&shape.symbol)),
    };
    let entry = Registered {
        signature: std::ptr::from_ref(signature),
        linkage: linkage.clone(),
        code: Code::Named(Rc::clone(name)),
    };
    let registration = claim(entry, &shape.symbol)?;
    let address = address_of(form, registration.slot);
    Ok((registration, address))
}

/// Регистрирует **замыкание** и отдаёт пару «адрес трамплина, `userdata`»
/// (§5.3, уровень 2).
///
/// Отличие от [`registered`] одно и оно несущее: среда едет **последним
/// словом**, а не остаётся в таблице. Таблица держит то, чему у чужой стороны
/// соответствия нет вовсе - сигнатуру и список библиотек; сам же колбэк
/// трамплин берёт из `userdata`, ровно как его берёт понижение. Иначе договор
/// трёх вычислителей про `userdata` не говорил бы ничего.
///
/// # Errors
///
/// [`RunError::Callback`] - формы колбэка нет среди трамплинов машины либо
/// таблица полна.
pub(crate) fn enclosed(
    signature: &Signature,
    linkage: &Linkage,
    closure: &Rc<Term>,
    form: &adamas_core::sig::Callback,
    symbol: &str,
) -> Result<(Registration, u64, u64), RunError> {
    if form.params != [PrimTy::UInt64, PrimTy::UInt64] || form.result != PrimTy::Int32 {
        return Err(unsupported(symbol));
    }
    let held = Rc::clone(closure);
    // Адрес терма и есть `userdata`: живым его держит регистрация, а снимается
    // она раньше, чем кончится чужой вызов.
    let data = Rc::as_ptr(&held) as usize as u64;
    let entry = Registered {
        signature: std::ptr::from_ref(signature),
        linkage: linkage.clone(),
        code: Code::Closed(held),
    };
    let registration = claim(entry, symbol)?;
    let address = address_of(Shape::CompareEnv, registration.slot);
    Ok((registration, address, data))
}

/// Форма колбэка вне таблицы трамплинов - отказ с названным списком.
fn unsupported(symbol: &str) -> RunError {
    RunError::Callback {
        symbol: symbol.to_owned(),
        why: "формы нет среди трамплинов машины: поддержаны `(UInt64, UInt64) -> Int32` \
              (компаратор `qsort`, он же со средой - `qsort_r`) и \
              `(UInt64, UInt64, UInt64, UInt64) -> UInt64` (write-колбэк libcurl)"
            .to_owned(),
    }
}

/// Отказ, случившийся внутри колбэка, - если он был.
pub(crate) fn taken() -> Option<RunError> {
    FAILED.with(|it| it.borrow_mut().take())
}

/// Считает колбэк слота, не пуская панику наружу.
///
/// # Паника внутрь не пускается
///
/// [`std::panic::catch_unwind`] стоит здесь не для порядка. Паника из
/// `extern "C"`-функции есть **abort процесса** - раскрутка через чужой кадр
/// запрещена и рантаймом Rust, и §5.3, - и наблюдалось это не в теории:
/// снятая проверка формы трамплина (мутант) роняла прогон `SIGABRT`'ом вместо
/// отказа. Внутренний инвариант компилятора, сломавшийся под чужим кадром,
/// обязан доехать до автора названным отказом, а не сигналом.
fn guarded(slot: usize, args: &[u64], env: Option<u64>) -> Result<u64, RunError> {
    std::panic::catch_unwind(|| answered(slot, args, env)).unwrap_or_else(|_| {
        Err(RunError::Callback {
            symbol: "?".to_owned(),
            why: "внутри колбэка сломался инвариант машины: раскрутить панику через \
                  чужой кадр нечем (§5.3), и она переведена в отказ"
                .to_owned(),
        })
    })
}

/// Ответ трамплина чужой стороне сишным `int`: число либо ноль при отказе.
fn narrow(answer: Result<u64, RunError>) -> i32 {
    match answer {
        Ok(word) => {
            i32::from_ne_bytes(u32::try_from(word & 0xffff_ffff).unwrap_or(0).to_ne_bytes())
        }
        Err(error) => {
            failed(error);
            0
        }
    }
}

/// Ответ трамплина чужой стороне полным словом: число либо ноль при отказе.
///
/// Ноль здесь не нейтрален: write-колбэк, ответивший не тем числом байт, какое
/// ему дали, libcurl считает отказом записи. Это и к лучшему - отказ машины
/// наблюдаем кодом возврата, а не тишиной.
fn wide(answer: Result<u64, RunError>) -> u64 {
    match answer {
        Ok(word) => word,
        Err(error) => {
            failed(error);
            0
        }
    }
}

/// Запоминает первый отказ: следом чужая сторона позовёт нас ещё много раз, и
/// перезаписать причину значило бы показать последнюю.
fn failed(error: RunError) {
    FAILED.with(|it| {
        let mut slot = it.borrow_mut();
        if slot.is_none() {
            *slot = Some(error);
        }
    });
}

/// Считает зарегистрированный колбэк на пришедших словах.
///
/// `env` - слово `userdata`, если чужая сторона его передала (уровень 2).
fn answered(slot: usize, args: &[u64], env: Option<u64>) -> Result<u64, RunError> {
    let (signature, linkage, code, closed) = TABLE.with(|it| {
        let table = it.borrow();
        let found = table[slot].as_ref().ok_or_else(|| RunError::Callback {
            symbol: "?".to_owned(),
            why: "чужая сторона позвала трамплин вне регистрации: слот таблицы свободен, \
                  то есть обёртка уже сняла регистрацию (§5.3, уровень 3)"
                .to_owned(),
        })?;
        let (code, closed) = match &found.code {
            Code::Named(name) => (Either::Named(Rc::clone(name)), None),
            Code::Closed(term) => (
                Either::Closed(Rc::clone(term)),
                Some(Rc::as_ptr(term) as usize as u64),
            ),
        };
        Ok::<_, RunError>((found.signature, found.linkage.clone(), code, closed))
    })?;
    // Слово `userdata` сверяется с тем, что зарегистрировано. Чужая сторона
    // вправе передать своё - и тогда это не наш колбэк.
    if let (Some(given), Some(held)) = (env, closed) {
        if given != held {
            return Err(RunError::Callback {
                symbol: "?".to_owned(),
                why: "`userdata` трамплина не тот, что зарегистрирован: чужая сторона \
                      передала чужое слово, и считать по нему нечего (§5.3, уровень 2)"
                    .to_owned(),
            });
        }
    }
    // SAFETY: указатель поставлен [`registered`] либо [`enclosed`] из живого
    // заимствования машины, а таблица чистится [`Scope`] на выходе из внешнего
    // прогона - то есть раньше, чем кончится заимствование. Слот уровня 3
    // переживает чужой вызов, но не прогон.
    #[allow(
        unsafe_code,
        reason = "таблица вместо среды: у указателя на функцию среды нет (§5.3)"
    )]
    let signature = unsafe { &*signature };
    let (mut term, shown) = match &code {
        Either::Named(name) => (reference(signature, name)?, name.to_string()),
        Either::Closed(closure) => ((**closure).clone(), "замыкание".to_owned()),
    };
    for word in args {
        term = Term::App(
            Rc::new(term),
            Rc::new(Term::Prim(Prim::Lit(PrimTy::UInt64, *word))),
        );
    }
    // Операция, оставшаяся без хендлера **внутри** колбэка, - не то же, что
    // операция без хендлера вообще, и говорить об этом надо прямо. Площадка у
    // неё есть: она стоит в месте регистрации. Не видит её машина, потому что
    // считает колбэк отдельным прогоном - стек хендлеров в `run_linked` не
    // передаётся. Понижения ту же программу считают: вектор evidence едет им
    // в `userdata` (§5.3), а у машины вектора нет вовсе.
    let answer = crate::run_linked(signature, &term, linkage).map_err(|error| match error {
        RunError::Unhandled { operation, effect } => RunError::Callback {
            symbol: shown.clone(),
            why: format!(
                "операция `{operation}` метки `{effect}` внутри колбэка осталась без \
                 хендлера: машина считает колбэк отдельным прогоном, и площадка места \
                 регистрации ему не видна. Понижения эту программу считают - вектор \
                 evidence едет им в `userdata` (§5.3, уровень 2)"
            ),
        },
        other => other,
    })?;
    match answer {
        Term::Prim(Prim::Lit(_, word)) => Ok(word),
        other => Err(RunError::Callback {
            symbol: shown,
            why: format!("ответ колбэка не литерал: {other}"),
        }),
    }
}

/// Кого зовём, вынутое из-под заимствования таблицы.
enum Either {
    Named(Name),
    Closed(Rc<Term>),
}

/// Ссылка на определение с **заземлёнными** аргументами обобщения.
///
/// Уровни - нулевые, row - пустые, кратности - первая дозволенная. Это и есть
/// та самая инстанцированная row, которой экспорт проверялся на элаборации:
/// у чужой стороны окружающих эффектов нет.
fn reference(signature: &Signature, name: &Name) -> Result<Term, RunError> {
    let definition = signature.lookup(name).ok_or_else(|| RunError::Callback {
        symbol: name.to_string(),
        why: "определения с таким именем в сигнатуре нет".to_owned(),
    })?;
    let levels: Rc<[Level]> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    let mults: Vec<Mult> = definition
        .mult_allowed
        .iter()
        .map(|allowed| allowed.first().copied().unwrap_or(Mult::Many))
        .collect();
    Ok(Term::Const(Rc::clone(name), levels, Args::new(rows, mults)))
}
