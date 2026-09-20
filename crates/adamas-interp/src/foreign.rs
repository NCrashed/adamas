//! Машина наружу: чужой символ настоящей разделяемой библиотеки (§5.3).
//!
//! Пробная правка трека C волны 1 Фазы 8 под вариант (а) вопроса 182: договор
//! корпуса требует согласия трёх вычислителей, а `adamas eval` сишную функцию
//! позвать не может ничем. Здесь она её зовёт.
//!
//! # Что здесь есть и чего нет
//!
//! Есть **путь**: имя библиотеки и символа, `dlopen`, `dlsym`, вызов по
//! сигнатуре из плоских типов (§4.11) и ответ литералом ядра. Ходит наружу
//! только машина: узла IR под внешний вызов сегодня нет вовсе, и заводит его
//! трек B. Слова `extern` в языке тоже нет - объявление приходит машине
//! [`Machine::declare_foreign`](crate::Machine::declare_foreign), минуя
//! поверхность.
//!
//! Нет **таблицы сигнатур**. Поддержаны ровно три формы, и у каждой есть
//! свидетель (`tests/outward.rs`); всё прочее - отказ с названной причиной, а
//! не догадка. Причина, по которой таблица не полна, - арифметика, а не лень:
//! `dlsym` отдаёт нетипизированный указатель, звать по нему можно только
//! **точной** сигнатурой, и у арности `k` над десятью плоскими типами (§4.11)
//! таких сигнатур `10^(k+1)`. Для `k <= 2` это 1110 ветвей по три строки
//! каждая. Настоящий ответ на это - libffi, то есть ещё одна зависимость с
//! собственным C-кодом; цена названа в `docs/phase8-trackC-notes.md`, а выбор
//! принимает не этот трек.
//!
//! # Библиотека не выгружается никогда
//!
//! Загруженное живёт до конца процесса намеренно. `dlclose` отпускает
//! отображение, а адреса символов, уже розданные наружу, после этого указывают
//! в ничто - это use-after-free, который ничем не ловится. Цена - память
//! отображения; она названа и принята.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use adamas_core::prim::PrimTy;

use crate::RunError;

/// Адрес чужого символа: указатель на код, о типе которого не известно ничего.
///
/// Именно это и есть главная цена варианта (а): `dlsym` типа не несёт, и
/// сверить объявленную сигнатуру с настоящей нечем ни на каком этапе.
type Address = unsafe extern "C" fn();

/// Класс регистра, которым значение переходит границу C.
///
/// Два, а не десять: `SysV` x86-64 делит скаляры на целые и плавающие, и внутри
/// класса разнятся они только шириной. Этого деления довольно, **пока** ширина
/// ровно слово; узкий тип пришлось бы звать своей точной сигнатурой, потому что
/// старшие биты регистра у него не определены.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Class {
    /// Целый регистр шириной в слово.
    Word,
    /// Регистр SSE, двойная точность.
    Double,
}

/// Класс плоского типа; `None` - тип, которым звать нечем.
fn classify(ty: PrimTy) -> Option<Class> {
    match ty {
        PrimTy::Int64 | PrimTy::UInt64 => Some(Class::Word),
        PrimTy::Float64 => Some(Class::Double),
        PrimTy::Int8
        | PrimTy::Int16
        | PrimTy::Int32
        | PrimTy::UInt8
        | PrimTy::UInt16
        | PrimTy::UInt32
        | PrimTy::Float32 => None,
    }
}

/// Чужая функция: где лежит, как зовётся, что принимает и что отдаёт.
///
/// Типы - плоские (§4.11), потому что через границу ходит слово, и ширина слова
/// есть ширина значения (трек A). Чужой указатель сюда входит как `UInt64` и
/// отдельного типа не требует - это и есть решение трека A.
#[derive(Clone, Debug)]
pub struct Foreign {
    /// Имя разделяемой библиотеки, как его понимает `dlopen`.
    pub library: String,
    /// Имя символа.
    pub symbol: String,
    /// Типы аргументов по порядку.
    pub params: Vec<PrimTy>,
    /// Тип ответа.
    pub result: PrimTy,
}

impl Foreign {
    /// Объявление чужой функции.
    #[must_use]
    pub fn new(library: &str, symbol: &str, params: &[PrimTy], result: PrimTy) -> Self {
        Self {
            library: library.to_owned(),
            symbol: symbol.to_owned(),
            params: params.to_vec(),
            result,
        }
    }

    /// Сигнатура словами - для текста отказа.
    fn written(&self) -> String {
        let params: Vec<&str> = self.params.iter().map(|it| it.name()).collect();
        format!("({}) -> {}", params.join(", "), self.result.name())
    }

    /// Загружает библиотеку и разрешает символ, ничего не вызывая.
    ///
    /// Отдельно от [`Foreign::call`] по двум поводам. Стенд
    /// (`benches/outward.rs`) мерит загрузку и вызов порознь - смешав их, он
    /// назвал бы микросекунды `dlopen` ценой вызова. И свидетели отсутствующей
    /// библиотеки с отсутствующим символом спрашивают ровно об этом шаге.
    ///
    /// # Errors
    ///
    /// [`RunError::NoLibrary`] либо [`RunError::NoSymbol`].
    pub fn resolve(&self) -> Result<(), RunError> {
        address(self).map(drop)
    }

    /// Зовёт чужую функцию по объявленной сигнатуре.
    ///
    /// Биты аргументов - те же, что у литерала ядра
    /// ([`adamas_core::prim::Prim::Lit`]): у плавающего это [`f64::to_bits`], у
    /// целого - значение, обрезанное по ширине.
    ///
    /// # Errors
    ///
    /// [`RunError::NoLibrary`], [`RunError::NoSymbol`] - до вызова дело не
    /// дошло. [`RunError::ForeignShape`] - сигнатура вне таблицы.
    pub fn call(&self, args: &[u64]) -> Result<u64, RunError> {
        let shape: Option<Vec<Class>> = self.params.iter().copied().map(classify).collect();
        let (Some(shape), Some(result)) = (shape, classify(self.result)) else {
            return Err(self.outside());
        };
        let address = address(self)?;
        // SAFETY: приписывание сигнатуры нетипизированному адресу. Верна она
        // или нет, не знает никто: `dlsym` типа не несёт, заголовка мы не
        // читали, и сверить объявленное с настоящим нечем. Разойдись они -
        // вызов пойдёт по чужому ABI, и ни отказа, ни падения из этого не
        // следует (свидетель `an_over_declared_arity_is_diagnosed_by_nothing`).
        // Это и есть названная цена варианта (а), а не упущение заготовки.
        #[allow(
            unsafe_code,
            reason = "вызов по нетипизированному адресу: содержание уровня 1 FFI (§5.3)"
        )]
        let answer = unsafe { invoke(address, &shape, result, args) };
        answer.ok_or_else(|| self.outside())
    }

    /// Отказ «формы нет в таблице».
    fn outside(&self) -> RunError {
        RunError::ForeignShape {
            symbol: self.symbol.clone(),
            signature: self.written(),
        }
    }
}

/// Загруженные библиотеки по имени.
///
/// Общая на процесс, а не на машину: `dlopen` и сам считает ссылки, а свидетели
/// крейта идут потоками одного процесса. Отсюда и `Mutex` - машина
/// однопоточна ([`std::rc::Rc`] в значениях), а таблица нет.
static LIBRARIES: OnceLock<Mutex<HashMap<String, &'static libloading::Library>>> = OnceLock::new();

/// Разрешённые символы: пара «библиотека, символ» в адрес.
static SYMBOLS: OnceLock<Mutex<HashMap<(String, String), Address>>> = OnceLock::new();

/// Библиотека по имени, загруженная однажды на весь процесс.
///
/// # Errors
///
/// [`RunError::NoLibrary`] - `dlopen` отказал. Отказ, а не паника: имя
/// библиотеки приходит из пользовательского текста, и отсутствующая библиотека
/// - обычная ошибка автора, а не сломанный инвариант.
fn library(name: &str) -> Result<&'static libloading::Library, RunError> {
    let table = LIBRARIES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut table = table
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(found) = table.get(name) {
        return Ok(found);
    }
    // SAFETY: инициализаторы чужой библиотеки бегут при загрузке, и что они
    // делают, Adamas не знает. Это и есть содержание §5.3: за границей стоит
    // чужой код, а не проверяемый.
    #[allow(
        unsafe_code,
        reason = "загрузка чужой библиотеки - ровно тот случай, ради которого `unsafe_code` объявлен `deny`, а не `forbid`"
    )]
    let loaded =
        unsafe { libloading::Library::new(name) }.map_err(|error| RunError::NoLibrary {
            library: name.to_owned(),
            why: error.to_string(),
        })?;
    // Отпускать нечем и незачем: см. шапку модуля.
    let leaked: &'static libloading::Library = Box::leak(Box::new(loaded));
    table.insert(name.to_owned(), leaked);
    Ok(leaked)
}

/// Адрес символа, разрешённый однажды на весь процесс.
///
/// # Errors
///
/// [`RunError::NoLibrary`] либо [`RunError::NoSymbol`].
fn address(it: &Foreign) -> Result<Address, RunError> {
    let key = (it.library.clone(), it.symbol.clone());
    let table = SYMBOLS.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let table = table
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(found) = table.get(&key) {
            return Ok(*found);
        }
    }
    let library = library(&it.library)?;
    // SAFETY: `dlsym` читает таблицу символов загруженной библиотеки; типа
    // возвращаемому адресу он не даёт, и здесь он не даётся тоже - `Address`
    // есть указатель на код без сигнатуры. Сигнатуру приписывает [`invoke`], и
    // это место названо опасностью в шапке модуля.
    #[allow(
        unsafe_code,
        reason = "разрешение чужого символа: нетипизированный указатель - свойство `dlsym`, а не выбор"
    )]
    let found = unsafe { library.get::<Address>(it.symbol.as_bytes()) }.map_err(|error| {
        RunError::NoSymbol {
            library: it.library.clone(),
            symbol: it.symbol.clone(),
            why: error.to_string(),
        }
    })?;
    let found = *found;
    let mut table = table
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    table.insert(key, found);
    Ok(found)
}

/// Вызов по классам регистров; `None` - формы нет в таблице.
///
/// Три формы, и у каждой свидетель. Четвёртая добавляется тремя строками и
/// обязана приходить со своим свидетелем - молча растущая таблица здесь
/// означала бы непроверенный ABI.
///
/// # Safety
///
/// `address` обязан указывать на функцию, чья настоящая сигнатура совпадает с
/// парой (`shape`, `result`). Проверить это нечем - см. шапку модуля.
#[allow(
    unsafe_code,
    reason = "приписывание сигнатуры чужому адресу: содержание уровня 1 FFI (§5.3)"
)]
unsafe fn invoke(address: Address, shape: &[Class], result: Class, args: &[u64]) -> Option<u64> {
    // Перекладка битов в аргумент и обратно - тот же уклад, каким литерал
    // живёт в ядре: `Float64` битами, целое значением.
    let double = |at: usize| f64::from_bits(args[at]);
    match (shape, result) {
        // `double -> double`: `cbrt`, `sqrt`, `log` - вся скалярная половина
        // libm.
        ([Class::Double], Class::Double) => {
            let call: extern "C" fn(f64) -> f64 = unsafe { std::mem::transmute(address) };
            Some(call(double(0)).to_bits())
        }
        // `long -> long`: `labs` и спутники libc.
        ([Class::Word], Class::Word) => {
            let call: extern "C" fn(u64) -> u64 = unsafe { std::mem::transmute(address) };
            Some(call(args[0]))
        }
        // `(double, double) -> double`: `pow`, `hypot`, `fmod`.
        ([Class::Double, Class::Double], Class::Double) => {
            let call: extern "C" fn(f64, f64) -> f64 = unsafe { std::mem::transmute(address) };
            Some(call(double(0), double(1)).to_bits())
        }
        _ => None,
    }
}
