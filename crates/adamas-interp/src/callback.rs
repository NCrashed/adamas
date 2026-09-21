//! Трамплин колбэка уровня 1: чужая сторона зовёт наше определение (§5.3).
//!
//! Понижение отдаёт чужой стороне адрес порождённой функции, и стоит это ноль.
//! У машины порождённой функции нет вовсе - есть терм и вычислитель, - поэтому
//! отдаётся адрес **статического** трамплина, а кого он зовёт, лежит рядом, в
//! переменной потока. Договор корпуса требует согласия трёх вычислителей
//! (§10 вопрос 182, вариант (а)), и без этого модуля машина отстала бы ровно на
//! той волне, ради которой договор и заводился.
//!
//! # Почему переменная потока, а не замыкание
//!
//! `dlsym`-адрес есть `extern "C" fn`, и среды у такого указателя нет по
//! построению - это ровно то, что §5.3 называет уровнем 1. Замыкание сюда не
//! кладётся не по лени: положить его значило бы завести `userdata`, а это
//! уровень 2 и трамплин совсем другого устройства. Машина однопоточна
//! ([`std::rc::Rc`] в значениях), поэтому переменной потока довольно.
//!
//! # Одна форма, и у неё свидетель
//!
//! Поддержан один трамплин - `(UInt64, UInt64) -> Int32`, то есть компаратор
//! `qsort`. Граница та же и по той же арифметике, что у таблицы сигнатур
//! [`crate::foreign`]: у арности `k` над плоскими типами §4.11 форм `10^(k+1)`,
//! и настоящий ответ на это - libffi, а не порождение. Вторая форма
//! добавляется десятком строк и обязана приходить со своим свидетелем.
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
    name: Name,
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
            name: Rc::clone(name),
        })
    });
    // Через тип указателя, а не прямым приведением: приведение элемента
    // функции к целому clippy разбирает отдельно, и оно вправе взять адрес не
    // той вещи.
    let trampoline: extern "C" fn(u64, u64) -> i32 = comparing;
    let address = trampoline as usize as u64;
    Ok((Registration { previous }, address))
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
extern "C" fn comparing(left: u64, right: u64) -> i32 {
    match answered(&[left, right]) {
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

/// Считает зарегистрированное определение на пришедших словах.
fn answered(args: &[u64]) -> Result<u64, RunError> {
    let (signature, linkage, name) = CURRENT.with(|it| {
        let slot = it.borrow();
        let found = slot.as_ref().ok_or_else(|| RunError::Callback {
            symbol: "?".to_owned(),
            why: "чужая сторона позвала трамплин вне регистрации: звать колбэк после \
                  возврата из чужого вызова уровень 1 не обещает - это уровень 3"
                .to_owned(),
        })?;
        Ok::<_, RunError>((found.signature, found.linkage, Rc::clone(&found.name)))
    })?;
    // SAFETY: оба указателя поставлены [`registered`] из живых заимствований
    // машины, а снимает запись [`Registration`] - дропом, до того как
    // заимствования кончатся. Чужая сторона зовёт трамплин **внутри** того
    // самого вызова, на время которого регистрация и стоит.
    #[allow(
        unsafe_code,
        reason = "переменная потока вместо среды: у указателя на функцию среды нет (§5.3)"
    )]
    let (signature, linkage) = unsafe { (&*signature, &*linkage) };
    let mut term = reference(signature, &name)?;
    for word in args {
        term = Term::App(
            Rc::new(term),
            Rc::new(Term::Prim(Prim::Lit(PrimTy::UInt64, *word))),
        );
    }
    let answer = crate::run_linked(signature, &term, linkage.clone())?;
    match answer {
        Term::Prim(Prim::Lit(_, word)) => Ok(word),
        other => Err(RunError::Callback {
            symbol: name.to_string(),
            why: format!("ответ колбэка не литерал: {other}"),
        }),
    }
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
