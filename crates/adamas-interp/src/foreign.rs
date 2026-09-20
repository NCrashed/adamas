//! Машина наружу: чужой символ настоящей разделяемой библиотеки (§5.3).
//!
//! Вариант (а) вопроса 182: договор корпуса требует согласия трёх
//! вычислителей, а `adamas eval` сишную функцию позвать не может ничем. Здесь
//! она её зовёт.
//!
//! # Что здесь есть и чего нет
//!
//! Есть **путь**: имя библиотеки и символа, `dlopen`, `dlsym`, вызов по
//! сигнатуре из плоских типов (§4.11) и ответ литералом ядра.
//!
//! # Откуда берётся библиотека
//!
//! `extern "C" fn cbrt : Float64 -> Float64` называет **символ**, а не файл, -
//! ровно как объявление в C. С чем программу связывать, решает сборка, а не
//! исходник: `[link]` манифеста (§7.1) плюс то, что сишный компилятор
//! подключает сам. Машина читает тот же список ([`Linkage`]) и ищет символ по
//! нему слева направо, как это делает компоновщик.
//!
//! Неявная часть списка - [`C_LIBRARY`]: стандартная библиотека C, которую
//! `cc` подключает без единого ключа. У glibc она **разложена по двум файлам**,
//! и `libm.so.6` подключается `-lm`; то, что деление это есть свойство
//! упаковки, а не языка, и позволяет машине держать обе как одну неявную
//! библиотеку. Отказ открыть неявную - не ошибка автора: он её не писал, и
//! поиск идёт дальше. Отказ открыть **написанную** - ошибка, и она названа.
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
use adamas_core::sig::Crossing;

use crate::RunError;

/// Стандартная библиотека C: то, что сишный компилятор подключает сам.
///
/// Два файла, а не один, - свойство упаковки glibc: `libm.so.6` отделён от
/// `libc.so.6`, и `cc` требует за него `-lm`. Для языка это одна библиотека, и
/// делить её надвое в манифесте значило бы заставить автора знать, в каком из
/// двух файлов у его libc лежит `cbrt`.
///
/// Названная граница: имена платформенные. §8 backend targets сегодня все
/// 64-битные и все Linux/glibc; на другой платформе список другой, и это
/// обязательство, а не умолчание.
pub const C_LIBRARY: [&str; 2] = ["libc.so.6", "libm.so.6"];

/// С чем связана программа: секция `[link]` манифеста плюс [`C_LIBRARY`].
///
/// Порядок тот же, каким идёт компоновщик: написанное слева, неявное справа.
/// Библиотека проекта поэтому вправе заслонить символ стандартной - ровно как
/// `cc program.o -lmine -lm` заслоняет им же.
///
/// Имена - в написании `-l`, и это выбрано ради машины: `-lname` компоновщик
/// разрешает в файл `libname.so`, и он же открывается `dlopen`'ом. То есть
/// `adamas eval` и `adamas build` требуют от системы **одного и того же файла**:
/// собралось - значит и посчитается. Каталоги `-L` `dlopen` не читает, поэтому
/// внутри каждой библиотеки кандидаты перебираются руками: сперва
/// `<путь>/libname.so` по написанным каталогам, затем голое `libname.so` для
/// системного поиска.
#[derive(Clone, Debug, Default)]
pub struct Linkage {
    libraries: Vec<String>,
    paths: Vec<std::path::PathBuf>,
}

impl Linkage {
    /// Связывание с написанными библиотеками и каталогами их поиска.
    #[must_use]
    pub fn new(libraries: &[String], paths: &[std::path::PathBuf]) -> Self {
        Self {
            libraries: libraries.to_vec(),
            paths: paths.to_vec(),
        }
    }

    /// Файлы, которыми может оказаться `-l<library>`.
    fn candidates(&self, library: &str) -> Vec<String> {
        let file = format!("lib{library}.so");
        let mut found: Vec<String> = self
            .paths
            .iter()
            .map(|path| path.join(&file).display().to_string())
            .collect();
        found.push(file);
        found
    }

    /// Где искали - для текста отказа.
    fn written(&self) -> String {
        let mut names: Vec<String> = self
            .libraries
            .iter()
            .flat_map(|it| self.candidates(it))
            .collect();
        names.extend(C_LIBRARY.iter().map(|it| (*it).to_owned()));
        names.join(", ")
    }
}

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
    /// Регистра нет вовсе: `void`. В позиции аргумента не встречается -
    /// единицу в домене вызывающий отсеивает до сюда.
    Void,
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
///
/// `None` в [`Self::params`] и в [`Self::result`] есть **единица**: связывание
/// без аргумента в домене (сишное `(void)`) и отсутствие ответа в кодомене
/// (`void`). То же соглашение, что у [`Crossing`] и у понижения.
#[derive(Clone, Debug)]
pub struct Foreign {
    /// Имя разделяемой библиотеки, как его понимает `dlopen`. `None` - искать
    /// среди связанных ([`Linkage`]), как это делает компоновщик.
    pub library: Option<String>,
    /// Имя символа.
    pub symbol: String,
    /// Связывания по порядку.
    pub params: Vec<Option<PrimTy>>,
    /// Тип ответа.
    pub result: Option<PrimTy>,
}

impl Foreign {
    /// Объявление чужой функции в названной библиотеке.
    #[must_use]
    pub fn new(library: &str, symbol: &str, params: &[PrimTy], result: PrimTy) -> Self {
        Self {
            library: Some(library.to_owned()),
            symbol: symbol.to_owned(),
            params: params.iter().copied().map(Some).collect(),
            result: Some(result),
        }
    }

    /// Объявление, пришедшее из `extern "C"`: библиотека не написана.
    #[must_use]
    pub fn crossing(it: &Crossing) -> Self {
        Self {
            library: None,
            symbol: it.symbol.to_string(),
            params: it.params.clone(),
            result: it.result,
        }
    }

    /// Сигнатура словами - для текста отказа.
    fn written(&self) -> String {
        let name = |it: Option<PrimTy>| it.map_or("Unit", PrimTy::name);
        let params: Vec<&str> = self.params.iter().copied().map(name).collect();
        format!("({}) -> {}", params.join(", "), name(self.result))
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
    pub fn resolve(&self, linkage: &Linkage) -> Result<(), RunError> {
        address(self, linkage).map(drop)
    }

    /// Зовёт чужую функцию по объявленной сигнатуре. `None` - ответа нет
    /// (`void`).
    ///
    /// Биты аргументов - те же, что у литерала ядра
    /// ([`adamas_core::prim::Prim::Lit`]): у плавающего это [`f64::to_bits`], у
    /// целого - значение, обрезанное по ширине. Аргументы-единицы сюда не
    /// приходят вовсе: их отсеивает вызывающий, потому что чужая сторона о них
    /// не знает.
    ///
    /// # Errors
    ///
    /// [`RunError::NoLibrary`], [`RunError::NoSymbol`] - до вызова дело не
    /// дошло. [`RunError::ForeignShape`] - сигнатура вне таблицы.
    pub fn call(&self, linkage: &Linkage, args: &[u64]) -> Result<Option<u64>, RunError> {
        let shape: Option<Vec<Class>> = self
            .params
            .iter()
            .copied()
            .flatten()
            .map(classify)
            .collect();
        let (Some(shape), Some(result)) = (shape, self.result.map_or(Some(Class::Void), classify))
        else {
            return Err(self.outside());
        };
        let address = address(self, linkage)?;
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

    /// Литерал не того типа, каким объявлен аргумент.
    pub(crate) fn mismatched(&self, at: usize, want: PrimTy, got: PrimTy) -> RunError {
        RunError::ForeignArgument {
            symbol: self.symbol.clone(),
            at,
            want: want.name(),
            got: got.name(),
        }
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
/// Библиотека **написана** - ищем в ней и только в ней. Не написана - идём по
/// [`Linkage`] слева направо, как компоновщик: первая, где символ есть, и
/// побеждает.
///
/// # Errors
///
/// [`RunError::NoLibrary`] либо [`RunError::NoSymbol`].
fn address(it: &Foreign, linkage: &Linkage) -> Result<Address, RunError> {
    if let Some(named) = &it.library {
        return within(named, &it.symbol);
    }
    let mut anywhere = false;
    for library in &linkage.libraries {
        let mut missing = None;
        let mut opened = false;
        for candidate in linkage.candidates(library) {
            match within(&candidate, &it.symbol) {
                Ok(found) => return Ok(found),
                Err(error @ RunError::NoLibrary { .. }) => missing = Some(error),
                Err(_) => opened = true,
            }
        }
        anywhere |= opened;
        // **Написанной** библиотеки нет ни под одним из кандидатов - это ошибка
        // автора, и она приезжает немедленно: искать дальше значило бы ответить
        // «нет символа» там, где нет файла.
        if !opened {
            return Err(missing.unwrap_or_else(|| RunError::NoLibrary {
                library: format!("lib{library}.so"),
                why: "кандидатов не нашлось".to_owned(),
            }));
        }
    }
    for name in C_LIBRARY {
        match within(name, &it.symbol) {
            Ok(found) => return Ok(found),
            Err(RunError::NoLibrary { .. }) => {}
            Err(_) => anywhere = true,
        }
    }
    // Названы **все** места, где искали: одно из них в тексте отказа не
    // сказало бы автору, что список библиотек у программы короче, чем он думал.
    Err(RunError::NoSymbol {
        library: linkage.written(),
        symbol: it.symbol.clone(),
        why: if anywhere {
            "`dlsym` не нашёл его ни в одной".to_owned()
        } else {
            "ни одна связанная библиотека не открылась".to_owned()
        },
    })
}

/// Адрес символа в названной библиотеке.
fn within(name: &str, symbol: &str) -> Result<Address, RunError> {
    let key = (name.to_owned(), symbol.to_owned());
    let table = SYMBOLS.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let table = table
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(found) = table.get(&key) {
            return Ok(*found);
        }
    }
    let library = library(name)?;
    // SAFETY: `dlsym` читает таблицу символов загруженной библиотеки; типа
    // возвращаемому адресу он не даёт, и здесь он не даётся тоже - `Address`
    // есть указатель на код без сигнатуры. Сигнатуру приписывает [`invoke`], и
    // это место названо опасностью в шапке модуля.
    #[allow(
        unsafe_code,
        reason = "разрешение чужого символа: нетипизированный указатель - свойство `dlsym`, а не выбор"
    )]
    let found = unsafe { library.get::<Address>(symbol.as_bytes()) }.map_err(|error| {
        RunError::NoSymbol {
            library: name.to_owned(),
            symbol: symbol.to_owned(),
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

/// Вызов по классам регистров; внешний `None` - формы нет в таблице, внутренний
/// - ответа нет (`void`).
///
/// Шесть форм, и у каждой свидетель: три первых - `tests/outward.rs`, три
/// добавленных треком D - корпус (`eval/extern-c` даёт `() -> long`,
/// `eval/foreign-resource` даёт `long -> void`, `adamas-cli/tests/linking.rs`
/// даёт `(long, long) -> long`). Седьмая добавляется тремя строками и обязана
/// приходить со своим свидетелем - молча растущая таблица здесь означала бы
/// непроверенный ABI.
///
/// # Safety
///
/// `address` обязан указывать на функцию, чья настоящая сигнатура совпадает с
/// парой (`shape`, `result`). Проверить это нечем - см. шапку модуля.
#[allow(
    unsafe_code,
    reason = "приписывание сигнатуры чужому адресу: содержание уровня 1 FFI (§5.3)"
)]
unsafe fn invoke(
    address: Address,
    shape: &[Class],
    result: Class,
    args: &[u64],
) -> Option<Option<u64>> {
    // Перекладка битов в аргумент и обратно - тот же уклад, каким литерал
    // живёт в ядре: `Float64` битами, целое значением.
    let double = |at: usize| f64::from_bits(args[at]);
    match (shape, result) {
        // `double -> double`: `cbrt`, `sqrt`, `log` - вся скалярная половина
        // libm.
        ([Class::Double], Class::Double) => {
            let call: extern "C" fn(f64) -> f64 = unsafe { std::mem::transmute(address) };
            Some(Some(call(double(0)).to_bits()))
        }
        // `long -> long`: `labs`, `malloc` и спутники libc.
        ([Class::Word], Class::Word) => {
            let call: extern "C" fn(u64) -> u64 = unsafe { std::mem::transmute(address) };
            Some(Some(call(args[0])))
        }
        // `(double, double) -> double`: `pow`, `hypot`, `fmod`.
        ([Class::Double, Class::Double], Class::Double) => {
            let call: extern "C" fn(f64, f64) -> f64 = unsafe { std::mem::transmute(address) };
            Some(Some(call(double(0), double(1)).to_bits()))
        }
        // `(long, long) -> long`: двухсловная половина libc и всякая чужая
        // библиотека, берущая указатель со счётом.
        ([Class::Word, Class::Word], Class::Word) => {
            let call: extern "C" fn(u64, u64) -> u64 = unsafe { std::mem::transmute(address) };
            Some(Some(call(args[0], args[1])))
        }
        // `long -> void`: `free` и всё, что отдаёт объект обратно. Без этой
        // формы `resource` над чужим объектом (§5.3) машине не считается:
        // деструктор его есть ровно `void`-символ.
        ([Class::Word], Class::Void) => {
            let call: extern "C" fn(u64) = unsafe { std::mem::transmute(address) };
            call(args[0]);
            Some(None)
        }
        // `void -> long`: `clock` и спутники. В Adamas это функция от единицы
        // (§3.4), и единица до сюда не доезжает.
        ([], Class::Word) => {
            let call: extern "C" fn() -> u64 = unsafe { std::mem::transmute(address) };
            Some(Some(call()))
        }
        _ => None,
    }
}
