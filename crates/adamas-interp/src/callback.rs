//! Трамплины колбэка: чужая сторона зовёт наш код (§5.3, уровни 1 и 2).
//!
//! Понижение отдаёт чужой стороне адрес порождённой функции, и стоит это ноль.
//! У машины порождённой функции нет вовсе - есть терм и вычислитель, - поэтому
//! отдаётся адрес **статического** трамплина. Договор корпуса требует согласия
//! трёх вычислителей (§10 вопрос 182, вариант (а)), и без этого модуля машина
//! отстала бы ровно на той волне, ради которой договор и заводился.
//!
//! # Что лежит в переменной потока, а что едет `userdata`
//!
//! Уровень 1: `dlsym`-адрес есть `extern "C" fn`, среды у такого указателя нет
//! по построению, и кого зовёт трамплин, помнит переменная потока.
//!
//! Уровень 2: среда есть, и едет она **вторым словом** - ровно как у
//! понижения. В переменной потока остаётся только то, чему у чужой стороны
//! соответствия нет вовсе: сигнатура и список библиотек. Иначе договор трёх
//! вычислителей про `userdata` не говорил бы ничего - обе стороны считали бы
//! через один и тот же обход.
//!
//! Машина однопоточна ([`std::rc::Rc`] в значениях), поэтому переменной потока
//! довольно.
//!
//! # Одна форма, и у неё свидетель
//!
//! Поддержан один трамплин на уровень - `(UInt64, UInt64) -> Int32` и он же с
//! `userdata` третьим словом, то есть компараторы `qsort` и `qsort_r`. Граница
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
//! Регистрация складывается стопкой: [`Registration`] на дропе возвращает
//! прежнюю. Нужно это не ради двух колбэков в одном вызове - их уровень 1 не
//! обещает, - а ради **пересечения внутри колбэка**: наш компаратор вправе
//! позвать `memcmp`, и пересечение это идёт тем же путём.

use std::cell::RefCell;
use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::{Cross, Crossing, Signature};
use adamas_core::term::{Args, Name, Term};

use crate::RunError;
use crate::foreign::Linkage;

/// Кого зовёт трамплин, пока управление у чужой стороны.
///
/// Указателями, а не ссылками: тип живёт в статике потока, а `'static` у
/// сигнатуры машины нет. Держит их живыми [`Registration`] - она снимает
/// запись раньше, чем кончится заимствование.
struct Registered {
    signature: *const Signature,
    linkage: *const Linkage,
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
    /// Текущая регистрация. `None` - чужая сторона зовёт нас без неё, и это
    /// отказ, а не догадка.
    static CURRENT: RefCell<Option<Registered>> = const { RefCell::new(None) };
    /// Отказ, случившийся **внутри** колбэка.
    ///
    /// Отдельно, потому что отдать его чужой стороне нечем: она ждёт `int`.
    /// Раскрутка через сишный кадр запрещена §5.3 ровно тем же правилом,
    /// которое проверяет экспорт, и паника здесь была бы его нарушением с
    /// нашей же стороны. Забирает отказ [`taken`] - сразу после вызова.
    static FAILED: RefCell<Option<RunError>> = const { RefCell::new(None) };
}

/// Живая регистрация: снимается дропом.
pub(crate) struct Registration {
    previous: Option<Registered>,
}

impl Drop for Registration {
    fn drop(&mut self) {
        let previous = self.previous.take();
        CURRENT.with(|it| *it.borrow_mut() = previous);
    }
}

/// Регистрирует определение под трамплином и отдаёт адрес трамплина словом.
///
/// Форма проверяется здесь: отдать чужой стороне адрес трамплина, чья
/// сигнатура не та, значило бы позвать наш код по чужому ABI.
///
/// # Errors
///
/// [`RunError::Callback`] - формы экспорта нет среди трамплинов.
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
    let matched = words.len() == shape.params.len()
        && words == [PrimTy::UInt64, PrimTy::UInt64]
        && shape.result == Some(PrimTy::Int32);
    if !matched {
        return Err(RunError::Callback {
            symbol: shape.symbol.to_string(),
            why: "формы нет среди трамплинов машины: поддержан `(UInt64, UInt64) -> Int32`, \
                  то есть компаратор `qsort`"
                .to_owned(),
        });
    }
    let previous = CURRENT.with(|it| {
        it.borrow_mut().replace(Registered {
            signature: std::ptr::from_ref(signature),
            linkage: std::ptr::from_ref(linkage),
            code: Code::Named(Rc::clone(name)),
        })
    });
    // Через тип указателя, а не прямым приведением: приведение элемента
    // функции к целому clippy разбирает отдельно, и оно вправе взять адрес не
    // той вещи.
    let trampoline: extern "C" fn(u64, u64) -> i32 = comparing;
    let address = trampoline as usize as u64;
    Ok((Registration { previous }, address))
}

/// Регистрирует **замыкание** и отдаёт пару «адрес трамплина, `userdata`»
/// (§5.3, уровень 2).
///
/// Отличие от [`registered`] одно и оно несущее: среда едет **вторым словом**,
/// а не остаётся в переменной потока. Переменная потока держит то, чему у
/// чужой стороны соответствия нет вовсе - сигнатуру и список библиотек; сам же
/// колбэк трамплин берёт из `userdata`, ровно как его берёт понижение. Иначе
/// договор трёх вычислителей про `userdata` не говорил бы ничего.
///
/// # Errors
///
/// [`RunError::Callback`] - формы колбэка нет среди трамплинов машины.
pub(crate) fn enclosed(
    signature: &Signature,
    linkage: &Linkage,
    closure: &Rc<Term>,
    form: &adamas_core::sig::Callback,
    symbol: &str,
) -> Result<(Registration, u64, u64), RunError> {
    if form.params != [PrimTy::UInt64, PrimTy::UInt64] || form.result != PrimTy::Int32 {
        return Err(RunError::Callback {
            symbol: symbol.to_owned(),
            why: "формы нет среди трамплинов машины: поддержан `(UInt64, UInt64) -> Int32`, \
                  то есть компаратор `qsort_r`"
                .to_owned(),
        });
    }
    let held = Rc::clone(closure);
    // Адрес терма и есть `userdata`: живым его держит регистрация, а снимается
    // она раньше, чем кончится чужой вызов.
    let data = Rc::as_ptr(&held) as usize as u64;
    let previous = CURRENT.with(|it| {
        it.borrow_mut().replace(Registered {
            signature: std::ptr::from_ref(signature),
            linkage: std::ptr::from_ref(linkage),
            code: Code::Closed(held),
        })
    });
    let trampoline: extern "C" fn(u64, u64, u64) -> i32 = comparing_env;
    let address = trampoline as usize as u64;
    Ok((Registration { previous }, address, data))
}

/// Отказ, случившийся внутри колбэка, - если он был.
pub(crate) fn taken() -> Option<RunError> {
    FAILED.with(|it| it.borrow_mut().take())
}

/// Трамплин формы `int (*)(const void *, const void *)`.
///
/// Ключей два, и оба - машинные слова: `tsearch`-подобный API отдаёт компаратору
/// сами ключи, `qsort` - адреса ячеек. Различать их трамплину нечем и незачем:
/// через границу уровня 1 едет слово.
///
/// # Паника внутрь не пускается
///
/// [`std::panic::catch_unwind`] стоит здесь не для порядка. Паника из
/// `extern "C"`-функции есть **abort процесса** - раскрутка через чужой кадр
/// запрещена и рантаймом Rust, и §5.3, - и наблюдалось это не в теории:
/// снятая проверка формы трамплина (мутант) роняла прогон `SIGABRT`'ом вместо
/// отказа. Внутренний инвариант компилятора, сломавшийся под чужим кадром,
/// обязан доехать до автора названным отказом, а не сигналом.
extern "C" fn comparing(left: u64, right: u64) -> i32 {
    let answer = std::panic::catch_unwind(|| answered(&[left, right], None)).unwrap_or_else(|_| {
        Err(RunError::Callback {
            symbol: "?".to_owned(),
            why: "внутри колбэка сломался инвариант машины: раскрутить панику через \
                  чужой кадр нечем (§5.3), и она переведена в отказ"
                .to_owned(),
        })
    });
    landed(answer)
}

/// Трамплин формы `int (*)(const void *, const void *, void *)` - уровень 2.
///
/// Третьим словом приезжает `userdata`, и в нём лежит **адрес замыкания**: не
/// сигнатура, не имя, а сам колбэк. Сверяется он с тем, что держит
/// регистрация, и расхождение - отказ: чужая сторона вправе позвать трамплин с
/// чужим словом, и считать по нему было бы чтением по произвольному адресу.
extern "C" fn comparing_env(left: u64, right: u64, env: u64) -> i32 {
    let answer =
        std::panic::catch_unwind(|| answered(&[left, right], Some(env))).unwrap_or_else(|_| {
            Err(RunError::Callback {
                symbol: "?".to_owned(),
                why: "внутри колбэка сломался инвариант машины: раскрутить панику через \
                      чужой кадр нечем (§5.3), и она переведена в отказ"
                    .to_owned(),
            })
        });
    landed(answer)
}

/// Ответ трамплина чужой стороне: число либо ноль при отказе.
fn landed(answer: Result<u64, RunError>) -> i32 {
    match answer {
        Ok(word) => {
            i32::from_ne_bytes(u32::try_from(word & 0xffff_ffff).unwrap_or(0).to_ne_bytes())
        }
        Err(error) => {
            // Первый отказ и побеждает: следом чужая сторона позовёт нас ещё
            // много раз, и перезаписать причину значило бы показать последнюю.
            FAILED.with(|it| {
                let mut slot = it.borrow_mut();
                if slot.is_none() {
                    *slot = Some(error);
                }
            });
            0
        }
    }
}

/// Считает зарегистрированный колбэк на пришедших словах.
///
/// `env` - слово `userdata`, если чужая сторона его передала (уровень 2).
fn answered(args: &[u64], env: Option<u64>) -> Result<u64, RunError> {
    let (signature, linkage, code, closed) = CURRENT.with(|it| {
        let slot = it.borrow();
        let found = slot.as_ref().ok_or_else(|| RunError::Callback {
            symbol: "?".to_owned(),
            why: "чужая сторона позвала трамплин вне регистрации: звать колбэк после \
                  возврата из чужого вызова уровень 1 не обещает - это уровень 3"
                .to_owned(),
        })?;
        let (code, closed) = match &found.code {
            Code::Named(name) => (Either::Named(Rc::clone(name)), None),
            Code::Closed(term) => (
                Either::Closed(Rc::clone(term)),
                Some(Rc::as_ptr(term) as usize as u64),
            ),
        };
        Ok::<_, RunError>((found.signature, found.linkage, code, closed))
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
    // SAFETY: оба указателя поставлены [`registered`] либо [`enclosed`] из
    // живых заимствований машины, а снимает запись [`Registration`] - дропом,
    // до того как заимствования кончатся. Чужая сторона зовёт трамплин
    // **внутри** того самого вызова, на время которого регистрация и стоит.
    #[allow(
        unsafe_code,
        reason = "переменная потока вместо среды: у указателя на функцию среды нет (§5.3)"
    )]
    let (signature, linkage) = unsafe { (&*signature, &*linkage) };
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
    let answer =
        crate::run_linked(signature, &term, linkage.clone()).map_err(|error| match error {
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

/// Кого зовём, вынутое из-под заимствования переменной потока.
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
