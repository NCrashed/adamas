//! Эмиттер C: [`ir`](crate::ir) в переносимый C.
//!
//! **Ядра этот модуль не читает.** Он не знает ни узлов ядра, ни сигнатуры, ни
//! кратностей иначе как полем [`Fact`](crate::ir::Fact) - и это проверяемая
//! форма шва, а не пожелание: `tests/seam.rs` читает исходник этого файла и
//! требует, чтобы ядра в нём не упоминалось. LLVM-эмиттер Фазы 7 встанет рядом
//! и получит те же факты из того же места.
//!
//! # Что эмиттер с фактами делает
//!
//! Теряет - и это его работа. Кратность решает одно: эмитить связывание или
//! нет, потому что стёртого в рантайме нет вовсе (§3.3). Уникальность и регион
//! он не читает: в C сверх `restrict` выразить `noalias` нечем, а ставить его
//! наугад - хуже, чем не ставить. Существенно, что факты **есть** и потеряны
//! последним шагом.
//!
//! # Что получается на выходе
//!
//! Одна единица трансляции: таблица конструкторов, печать, объявления, функции,
//! точка входа. Всё `static`, кроме `main`, - LTO и whole-program эмиссия
//! обещаны §13 и Фазой 7, и одним файлом они даются даром.
//!
//! # Две формы понижения (§13, обе записи 2026-09-08)
//!
//! Форму приносит IR ([`Form`]), эмиттер её не угадывает. **Первая** - обычная
//! C-функция, кадр на C-стеке, скрытых аргументов нет вовсе; написанное и есть
//! вся её сигнатура. **Вторая** несёт два скрытых аргумента перед написанным -
//! вектор evidence, затем ручку стека, - и порядок этот записан в одном месте
//! ([`HIDDEN`], [`FORWARD`]), потому что печатают его четверо: объявление,
//! определение, прямой вызов и трамплин.
//!
//! Дальше скрытые аргументы идут ровно туда, где их ждут: второй форме -
//! свои, первой - никаких. На границе **замыкания** они есть всегда, потому
//! что граница динамическая: какая из форм за указателем, место вызова не
//! знает. Первая форма, применяя значение, кладёт там `NULL` - взять ей их
//! неоткуда, - и рантайм принимает `NULL` всюду, где их читает.
//!
//! # Что эмиттер знает о владении
//!
//! `dup`, `drop` и переиспользование ячейки приходят **узлами IR** - их ставит
//! [`perceus`](crate::perceus), и эмиттер их только печатает. Своего решения о
//! владении у него ровно одно, и оно про C-ABI, а не про программу: трамплин
//! замыкания достаёт среду из слотов, которыми владеет само замыкание, а функция
//! берёт аргументы владением - значит на каждый слот идёт `adamas_dup`. В IR
//! трамплина нет вовсе, поэтому и поставить это некому больше.
//!
//! Дроп детей порождается здесь же одной функцией на программу (`release.c`):
//! `adamas.h` требует, чтобы release приходил от понижения, а какие у объекта
//! дети - отвечает таблица по тегу, та же, по которой печатается ответ.
//!
//! # Плоское значение (§4.11)
//!
//! Представление приходит фактом ([`Repr`]), и эмиттер решает по нему три
//! вещи: C-тип связывания (`int64_t` против `adamas_value`), запись поля
//! (биты в слот по значению против `adamas_set_field` с владением) и сорт
//! слота в таблице, по которой дроп с печатью узнают число от ссылки. Ничего
//! из этого он не выдумывает - объявление читается в понижении, а здесь только
//! печатается. Механика плоского слота живёт в `flat.c` вместе с доводами.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use adamas_core::prim::{PrimCmp, PrimOp, PrimTy};

use crate::ir::{
    Arm, Binding, Callback, CallbackId, Constructor, CtorId, Elems, Export, ExportId, Expr,
    FiberOp, Foreign, ForeignId, ForeignResult, Form, FuncId, Function, HandlerId, LabelId,
    LocalId, PackId, Packing, Program, Repr, Salvage, Stride, Verdict,
};
use crate::split::Suspension;

/// Как уложены элементы массива с таким шагом.
const fn elems(stride: Option<Stride>) -> Elems {
    match stride {
        Some(_) => Elems::Flat,
        None => Elems::Boxed,
    }
}

/// Плоское значение: биты слота, арифметика, печать.
pub(crate) const FLAT: &str = include_str!("flat.c");

/// Печать значения по таблице конструкторов.
pub(crate) const PRINTER: &str = include_str!("print.c");

/// Дроп детей по той же таблице.
pub(crate) const RELEASE: &str = include_str!("release.c");

/// Промоушен детей по ней же (§5.2). Печатается только программе с питомником.
pub(crate) const PROMOTE: &str = include_str!("promote.c");

/// Точка входа: печать ответа и счётчики блоков.
pub(crate) const ENTRY: &str = include_str!("main.c");

/// Почему эмиссия отказала.
#[derive(Debug, thiserror::Error)]
pub enum EmitError {
    /// Первая форма зовёт вторую прямым вызовом.
    ///
    /// Скрытых аргументов у первой нет вовсе, и передать второй нечего.
    /// Взяться такая пара не должна: прямой вызов насыщен, а применение
    /// функции с непустой row требует непустой окружающей (§3.4, погашение
    /// расширением справа), то есть второй формы у вызывающего. Поставить на
    /// её месте `NULL` значило бы досочинить - вызываемый нашёл бы пустой
    /// вектор там, где обязан найти хендлер.
    #[error("`{caller}` первой формы зовёт `{callee}`: скрытых аргументов у неё нет")]
    Hidden {
        /// Чья первая форма.
        caller: String,
        /// Кого она зовёт.
        callee: String,
    },

    /// Операция в функции, чей ответ плоский.
    ///
    /// Вердикт `SUPPRESSED` требует вернуть ответ `adamas_kont_abort`
    /// немедленно (`adamas.h`), а ответ этот - значение: у функции с плоским
    /// ответом вернуть его нечем. Граница та же, что у прочего плоского на
    /// границах (§4.11), и снимет её боксирование.
    #[error("`{function}`: операция в функции с плоским ответом - обрыв вернуть нечем (§4.11)")]
    Aborting {
        /// Чья функция.
        function: String,
    },

    /// Связывание, переживающее точку приостановки, но не влезающее в слот.
    ///
    /// Слот кадра - слово, и плоское значение примитивного типа лежит в нём
    /// битами наравне со слотом объекта (§4.11). Плотный агрегат шире слова, а
    /// плоский элемент неизвестного типа живёт внутри одного кадра по
    /// построению; и то и другое через границу кадра не проходит. Граница та
    /// же, что у прочего плоского на границах, и снимет её боксирование (§5.1).
    #[error(
        "`{function}`: {shape} переживает точку приостановки - слот кадра шире не бывает (§4.11)"
    )]
    Parked {
        /// Чья функция.
        function: String,
        /// Что именно не влезло.
        shape: String,
    },

    /// Подорожечной эта операция не бывает (§4.9).
    ///
    /// Приехать сюда она не может: `SimdOp::arith` отдаёт только три
    /// арифметические, и [`PrimOp::lanewise`] говорит то же. Отказ стоит
    /// **вместо** молчаливой печати `a / b` по дорожкам: у сдвига и деления
    /// свои ограждения (насыщение счётчика, нулевой делитель), подорожечной
    /// формы у них нет, и напечатанный без них вектор считал бы не то.
    #[error("`{function}`: `{op}` подорожечной не бывает - ограждений у неё нет (§4.9)")]
    Lanewise {
        /// Чья функция.
        function: String,
        /// Какая операция.
        op: PrimOp,
    },
}

/// Собирает единицу трансляции.
///
/// # Errors
///
/// [`EmitError`] - формы вызывающего и вызываемого не сходятся.
pub fn emit(program: &Program) -> Result<String, EmitError> {
    let suspending = crate::split::suspending(program);
    forms_agree(program, &suspending)?;
    let mut out = String::new();
    preamble(&mut out);
    out.push_str(FLAT);
    out.push('\n');
    packings(&mut out, program);
    vectors(&mut out, program);
    prototypes(&mut out, program);
    exports(&mut out, program);
    table(&mut out, program);
    out.push_str(RELEASE);
    out.push('\n');
    if nursed(program) {
        out.push_str(PROMOTE);
        out.push('\n');
    }
    if scoped(program) {
        out.push_str(
            "/* Дроп среды кадра scope: деструктор замыканием в слоте 0 (§3.3). */\n\
             static void release_closing(adamas_frame *h, adamas_kont *kont) {\n\
             \x20   (void)kont;\n\
             \x20   adamas_value *env = adamas_frame_env(h);\n\
             \x20   adamas_drop_value(env[0]);\n\
             }\n\n",
        );
    }
    out.push_str(PRINTER);
    out.push('\n');

    let boxed = wrapped(program);
    let taken = moving(program);
    let built = builders(program);

    // Тела собираются первыми: дробление заводит куски по дороге, а объявления
    // их обязаны стоять выше - кусок ссылается на кусок с бо́льшим номером.
    let mut bodies = String::new();
    let mut forward = Vec::new();
    for constructor in &program.constructors {
        if built.contains(&constructor.tag) {
            builder(&mut bodies, constructor);
        }
    }
    for function in &program.functions {
        if let Some(failure) = body(&mut bodies, program, function, &suspending, &mut forward) {
            return Err(failure);
        }
        if boxed.contains(&function.id) {
            wrapper(&mut bodies, function);
        }
        if taken.contains(&function.id) {
            taker(&mut bodies, function);
        }
    }

    out.push_str("/* Объявления: рекурсия и взаимная рекурсия видят друг друга. */\n");
    for function in &program.functions {
        let _ = writeln!(out, "{};", signature(function));
    }
    for tag in &built {
        let _ = writeln!(out, "{};", trampoline(&format!("make_{}", tag.0)));
    }
    for id in &boxed {
        let _ = writeln!(out, "{};", trampoline(&format!("box_{}", id.0)));
    }
    for id in &taken {
        let _ = writeln!(out, "{};", trampoline(&format!("take_{}", id.0)));
    }
    // Трамплины колбэка объявляются здесь по тому же доводу, что и обёртки
    // экспорта: адрес трамплина берёт тело функции, стоящей выше него.
    for (at, described) in program.callbacks.iter().enumerate() {
        let _ = writeln!(
            out,
            "{};",
            trampoline_signature(CallbackId(at), described, true)
        );
    }
    for (at, described) in program.handlers.iter().enumerate() {
        let _ = writeln!(out, "{};", branches_signature(at));
        if described.captured.iter().any(|it| it.fact.present) {
            let _ = writeln!(out, "{};", release_signature(at));
        }
    }
    for declaration in &forward {
        let _ = writeln!(out, "{declaration}");
    }
    out.push('\n');

    out.push_str(&bodies);
    for at in 0..program.handlers.len() {
        branches(&mut out, program, at);
    }
    exported_bodies(&mut out, program);
    callbacks(&mut out, program, true);

    answer(&mut out, program);
    out.push_str(ENTRY);
    Ok(out)
}

/// Скрытые аргументы стоят там, где их есть чем взять.
///
/// Проверка, а не предположение: расхождение здесь молчаливо - `NULL` вместо
/// вектора собирается и падает в рантайме. Утверждений два.
///
/// *Прямой вызов второй формы* идёт из места, где вектор и ручка есть. У первой
/// формы их нет в сигнатуре, но **под `handle` они появляются**: хендлер в
/// чистой функции заводит корень своего стека (см. [`Emitter::handling`]), и
/// вычисление под ним второй формы зовёт законно. Замыкания это не касается
/// вовсе: положить вторую форму значением законно откуда угодно, скрытые
/// аргументы там приходят от трамплина.
///
/// *Операция* стоит только там, где обрыв можно вернуть: `SUPPRESSED` требует
/// вернуть ответ `adamas_kont_abort` немедленно (`adamas.h`), а ответ этот -
/// значение. Функция с плоским ответом вернуть его не может, и отказ здесь
/// лучше, чем порождённый C, который не соберётся.
fn forms_agree(program: &Program, suspending: &Suspension) -> Result<(), EmitError> {
    for function in &program.functions {
        let hidden = function.form == Form::Detached;
        if let Some(callee) = stranded(program, &function.body, hidden) {
            return Err(EmitError::Hidden {
                caller: function.name.clone(),
                callee,
            });
        }
        // Спрашивается C-тип, а не `Repr::pointer`: массив и блок региона -
        // такое же слово с заголовком, и ответ ими вернуть можно.
        if suspending.functions.contains(&function.id) && scalar(function.result) != "adamas_value"
        {
            return Err(EmitError::Aborting {
                function: function.name.clone(),
            });
        }
    }
    Ok(())
}

/// Есть ли в программе круг: тогда нужен обход промоушена (§5.2).
///
/// Печатать его всегда нельзя - без питомника он остаётся неиспользованным, и
/// `-Wunused-function` называет это по имени.
pub(crate) fn nursed(program: &Program) -> bool {
    program.functions.iter().any(|function| {
        let mut found = false;
        walk(&function.body, &mut |expr| {
            found |= matches!(expr, Expr::Nursery { .. });
        });
        found
    })
}

/// Есть ли в программе выход из scope кадром: тогда нужен его дроп среды.
fn scoped(program: &Program) -> bool {
    program.functions.iter().any(|function| {
        let mut found = false;
        walk(&function.body, &mut |expr| {
            found |= matches!(expr, Expr::Closing { .. });
        });
        found
    })
}

/// Первый прямой вызов второй формы, которому скрытые аргументы взять неоткуда.
fn stranded(program: &Program, expr: &Expr, hidden: bool) -> Option<String> {
    match expr {
        Expr::Call { function, .. } if !hidden => {
            let called = &program.functions[function.0];
            if called.form == Form::Detached {
                return Some(called.name.clone());
            }
            None
        }
        // Под хендлером вектор и ручка есть всегда: их заводит сам `handle`.
        Expr::Handle {
            captured,
            computation,
            ..
        } => captured
            .iter()
            .find_map(|capture| stranded(program, capture, hidden))
            .or_else(|| stranded(program, computation, true)),
        // Под питомником - тоже: круг в чистой функции заводит свой корень
        // (`Emitter::nursing`), и тело считается уже под ним.
        Expr::Nursery { body } => stranded(program, body, true),
        _ => expr
            .children()
            .into_iter()
            .find_map(|child| stranded(program, child, hidden)),
    }
}

/// Чем точка входа отвечает.
///
/// Печатью и дропом ответа занимается `main.c`; отсюда приходит только то, чего
/// он знать не может: имя функции и представление её ответа (§4.11). Плоский
/// ответ дропать нечем - счётчика у него нет, - и `main.c` разводит эти две
/// формы препроцессором.
fn answer(out: &mut String, program: &Program) {
    let entry = &program.functions[program.entry.0];
    let _ = writeln!(out, "#define ADAMAS_ENTRY fn_{}", program.entry.0);
    if let Some(ty) = entry.result.primitive() {
        let _ = writeln!(out, "#define ADAMAS_ANSWER_FLAT adamas_word_{}", ty.name());
        let _ = writeln!(out, "#define ADAMAS_ANSWER_TYPE {}", c_type(entry.result));
        let _ = writeln!(out, "#define ADAMAS_ANSWER_KIND {}u", kind(ty));
    }
    out.push('\n');
}

/// Номер сорта плоского значения: он же индекс в `flat.c`.
///
/// Порядок - §4.11 и [`PrimTy::ALL`], ноль занят указательным слотом. Совпадение
/// с `flat.c` проверяется тестом, а не соглашением.
pub(crate) fn kind(ty: PrimTy) -> u8 {
    let at = PrimTy::ALL.iter().position(|it| *it == ty).unwrap_or(0);
    u8::try_from(at + 1).unwrap_or(0)
}

/// Сорт слота: ноль у указательного.
fn slot_kind(repr: Repr) -> u8 {
    repr.primitive().map_or(0, kind)
}

/// Влезает ли значение в слот кадра целиком.
///
/// Слот - слово, и годится в него всё, что словом и живёт: объект кучи любого
/// сорта и плоское значение примитивного типа битами. Не годятся плотный
/// агрегат (шире слова) и плоский элемент неизвестного типа (он буфер на
/// кадре, §4.11).
fn worded(repr: Repr) -> bool {
    repr.primitive().is_some() || scalar(repr) == "adamas_value"
}

/// Значение словом: плоское примитивное - битами, прочее - собой.
///
/// Граница куска дроблёного тела носит слово, и других форм у неё нет:
/// `adamas_frame_code` берёт `adamas_value` и им же отвечает. Половин у границы
/// три - слот среды кадра, пришедшее в кусок и ответ куска трамплину, - и мера
/// у всех трёх одна. Ячейки кучи это не стоит: биты примитива ложатся в слово
/// целиком. Счётчика у такого слова нет, поэтому дропу оно не показывается -
/// какие позиции указательные, кусок знает по типам (§4.11, §5.1).
fn into_word(repr: Repr, value: &str) -> String {
    match repr.primitive() {
        Some(ty) => format!("adamas_slot_of(adamas_word_{}({value}))", ty.name()),
        None => value.to_owned(),
    }
}

/// Обратно: слово границы в значение объявленного представления.
fn from_word(repr: Repr, value: &str) -> String {
    match repr.primitive() {
        Some(ty) => format!("adamas_bits_{}(adamas_slot_word({value}))", ty.name()),
        None => value.to_owned(),
    }
}

/// C-тип связывания.
fn c_type(repr: Repr) -> String {
    match repr {
        // Плоский агрегат - свой тип на укладку: байты по значению, и передаётся
        // он как всякая структура C (§4.11).
        Repr::Packed(pack) => format!("adamas_pack_{}", pack.0),
        // Вектор - свой тип на пару «ширина, дорожка»: у C он расширение
        // `vector_size`, то есть тоже значение, передаваемое по значению.
        Repr::Simd { lanes, lane } => vector_type(lanes, lane),
        other => scalar(other).to_owned(),
    }
}

/// C-тип всего, кроме плоского агрегата: имя у него постоянное.
pub(crate) fn scalar(repr: Repr) -> &'static str {
    match repr {
        // Массив и запись - объекты кучи, и в C они такое же слово, как всякий
        // объект: различие плоского и указательного живёт **внутри** них.
        // Блок региона - такой же объект кучи, как массив: слово с заголовком,
        // а байты нагрузки лежат внутри (§3.6). Резумпция - ручка сегмента, и
        // в C она то же слово: различие её живёт в дропе, а не в типе.
        Repr::Boxed | Repr::Array(_) | Repr::Region | Repr::Record(_) | Repr::Resumption => {
            "adamas_value"
        }
        Repr::Layout => "adamas_layout",
        // Плоский элемент неизвестного типа - байты, чья ширина известна
        // только в рантайме. Буфер стоит на кадре и наружу не выходит.
        Repr::Opaque => "char *",
        Repr::Flat(PrimTy::Int8) => "int8_t",
        Repr::Flat(PrimTy::Int16) => "int16_t",
        Repr::Flat(PrimTy::Int32) => "int32_t",
        Repr::Flat(PrimTy::Int64) => "int64_t",
        Repr::Flat(PrimTy::UInt8) => "uint8_t",
        Repr::Flat(PrimTy::UInt16) => "uint16_t",
        Repr::Flat(PrimTy::UInt32) => "uint32_t",
        Repr::Flat(PrimTy::UInt64) => "uint64_t",
        Repr::Flat(PrimTy::Float32) => "float",
        Repr::Flat(PrimTy::Float64) => "double",
        // Имя зависит от номера укладки, и постоянным быть не может.
        Repr::Packed(_) => "adamas_pack",
        // Имя зависит от ширины и дорожки - см. [`vector_type`].
        Repr::Simd { .. } => "adamas_simd",
    }
}

/// Годится ли ответ такого представления под приставку `musttail` (§6).
///
/// Годится всё, что уходит **регистром**: слово объекта и плоский скаляр.
/// Не годится то, что C возвращает как значение составного типа, - плотный
/// агрегат, вектор и дескриптор укладки. Отказ у gcc в обоих случаях
/// **сборочный**, а не молчаливый («callee returns a structure» у агрегата,
/// «other reasons» у вектора), и поймал его корпус на `packets`, а не чтение:
/// сборка не шла вовсе.
///
/// Граница та же, что у LLVM-эмиттера, и по той же причине: у агрегата шире
/// регистров ответ едет скрытым указателем вызывающего, а хвостовой вызов в
/// чужой `sret` писать не вправе. Там она названа порогом ABI хоста, здесь -
/// именем типа; условие у обоих одно, и цена его одна - у такой функции
/// гарантия §6 остаётся тем, чем была, свёрткой соседнего вызова при `-O2`.
///
/// [`Repr::Opaque`] исключён вместе с ними: ответом он не бывает вовсе
/// (понижение его там отвергает), и разрешать его здесь значило бы утверждать
/// о непроверяемом.
const fn returnable(repr: Repr) -> bool {
    matches!(
        repr,
        Repr::Boxed
            | Repr::Array(_)
            | Repr::Region
            | Repr::Record(_)
            | Repr::Resumption
            | Repr::Flat(_)
    )
}

/// Имя C-типа вектора (§4.9): `adamas_simd_8_Float32`.
fn vector_type(lanes: u32, lane: PrimTy) -> String {
    format!("adamas_simd_{lanes}_{}", lane.name())
}

/// Имя **невыровненного** близнеца того же вектора: `adamas_loose_8_Float32`.
///
/// Нужен он ровно одному месту - обращению к окну колонки (§4.9,
/// `simdLoad`/`simdStore`), - и не украшением, а условием верности. `gcc`
/// выравнивает `vector_size(32)` по шестнадцати (замерено: `_Alignof` даёт 16
/// на baseline x86-64), а ячейка колонки стоит по **шагу массива**: у
/// `Float32` это четыре байта. Разыменуй окно выровненным типом - и компилятор
/// вправе поставить `movaps`, то есть обрыв по невыровненному адресу на первой
/// же колонке, чьё начало не кратно шестнадцати.
///
/// Граница у близнеца - ширина дорожки, то есть ровно та, которую массив
/// обещает (§4.11: `n × size(a)` байт подряд). Обещать больше нечем: §4.9
/// заводит под это `AlignedBuffer`, а его здесь нет - см. `SimdOp::Load`.
fn vector_loose_type(lanes: u32, lane: PrimTy) -> String {
    format!("adamas_loose_{lanes}_{}", lane.name())
}

/// Имя беззнакового спутника того же вектора - в нём считается целочисленная
/// арифметика.
///
/// Заворачивание §4.3 держится ровно тем же ходом, каким его держит скаляр
/// (`flat.c`, `ADAMAS_FLAT_INTEGER`): операция идёт в беззнаковом типе, где
/// переполнение определено, и результат приводится обратно. У плавающего
/// спутника нет - там заворачивать нечего.
fn vector_word_type(lanes: u32, lane: PrimTy) -> String {
    format!("adamas_usimd_{lanes}_{}", lane.name())
}

/// Беззнаковый тип той же ширины, что дорожка.
const fn lane_word(lane: PrimTy) -> &'static str {
    match lane {
        PrimTy::Int8 | PrimTy::UInt8 => "uint8_t",
        PrimTy::Int16 | PrimTy::UInt16 => "uint16_t",
        PrimTy::Int32 | PrimTy::UInt32 | PrimTy::Float32 => "uint32_t",
        PrimTy::Int64 | PrimTy::UInt64 | PrimTy::Float64 => "uint64_t",
    }
}

/// Заголовок единицы трансляции.
fn preamble(out: &mut String) {
    out.push_str(concat!(
        "/* Порождено понижением Adamas. Править нечего: правится тот, кто породил.\n",
        " *\n",
        " * Договор с рантаймом - `adamas.h`; форма значения, владение и кадры\n",
        " * описаны там. Здесь только код программы.\n",
        " */\n",
        "\n",
        "#include \"adamas.h\"\n",
        "\n",
        "#include <stdio.h>\n",
        "\n",
        "/* Стёртая позиция (§3.3): значения в рантайме нет. Макрос стоит там, где\n",
        " * стёртое связывание всё-таки упомянули бы, и печатается заметно. */\n",
        "#define ADAMAS_ERASED adamas_con0(0xFFFCu)\n",
        "\n",
        "/* Самохвостовой вызов: гарантия §6, а не оптимизация.\n",
        " *\n",
        " * Приставка стоит ровно там, где вызываемый есть сама функция, - тогда\n",
        " * прототипы совпадают дословно, и требование обоих компиляторов выполнено\n",
        " * по построению. Она снимает два условия, от которых иначе зависит\n",
        " * гарантия: уровень оптимизации (свёртку соседнего вызова gcc включает с\n",
        " * `-O2`, а порождённое собирается `-O1`) и отсутствие локали, чей адрес\n",
        " * ушёл наружу (`adamas_kont` у применения замыкания - ровно такая).\n",
        " *\n",
        " * Где приставки нет, макрос пуст, и гарантия возвращается к тому, чем\n",
        " * была: свёртке соседнего вызова при `-O2`. Это ослабление, а не отказ\n",
        " * сборки, и названо оно тем же порядком, каким §9 называет границы\n",
        " * `musttail`: clang с 13, gcc с 15.1. */\n",
        "#if defined(__has_attribute)\n",
        "#  if __has_attribute(musttail)\n",
        "#    define ADAMAS_MUSTTAIL __attribute__((musttail))\n",
        "#  endif\n",
        "#endif\n",
        "#ifndef ADAMAS_MUSTTAIL\n",
        "#  define ADAMAS_MUSTTAIL\n",
        "#endif\n",
        "\n",
    ));
}

/// Прототипы чужих символов (§5.3, уровень 1).
///
/// Печатаются **своим** объявлением, а не через заголовок библиотеки: заголовка
/// у нас нет, а сигнатура написана автором в `extern "C"`, и в ней вся правда,
/// какая у компилятора есть. Расхождение с настоящей библиотекой поэтому ловит
/// линкер и ABI, а не мы, - это и есть названная цена уровня 1 (§5.3, «полный
/// контроль над сигнатурами»).
///
/// `(void)` у бессловесной функции пишется дословно: пустые скобки в C
/// объявляют функцию с **неизвестным** списком аргументов, а не без них, и под
/// `-Wstrict-prototypes` это предупреждение, под C23 - другое значение.
///
/// # Имя своё, символ чужой
///
/// Объявляется **не** `malloc`, а `adamas_foreign_malloc` с ассемблерной
/// меткой. Без метки первая же идиома §5.3 не собирается вовсе: порождённая
/// единица включает `adamas.h`, тот - `<stdlib.h>`, и `extern uint64_t
/// malloc(uint64_t)` рядом с `void *malloc(size_t)` есть «conflicting types».
/// Случай этот не редкий край, а **всякая** чужая функция с указателем:
/// указатель на уровне 1 есть `CPtr`, то есть `uint64_t` (трек A), и сойтись с
/// написанием заголовка он не может по построению.
///
/// Рассмотрено и отвергнуто: обёртка в отдельной единице трансляции, куда
/// системные заголовки не включены. Работает, но стоит единицы трансляции на
/// программу и вызова на пересечение, а метка не стоит ничего. То же решение и
/// по той же причине принимают `#[link_name]` в Rust и `@extern` в Zig.
///
/// Названная цена: `__asm__`-метка - расширение GNU (его несут gcc и clang) и
/// пишет символ **дословно**, без платформенного префикса. На ELF это верно; на
/// цели, где C-символы получают подчёркивание, метку пришлось бы строить
/// иначе, и это обязательство, а не умолчание.
fn prototypes(out: &mut String, program: &Program) {
    if program.foreigns.is_empty() {
        return;
    }
    out.push_str("/* Чужие символы (§5.3): объявлены по написанным сигнатурам. */\n");
    for foreign in &program.foreigns {
        let result = match foreign.result {
            ForeignResult::Flat(ty) => scalar(Repr::Flat(ty)),
            ForeignResult::Unit(_) => "void",
        };
        let parameters = variadic_list(foreign);
        let _ = writeln!(
            out,
            "extern {result} {}({parameters}) __asm__(\"{}\");",
            local(&foreign.symbol),
            foreign.symbol
        );
    }
    out.push('\n');
}

/// Список параметров прототипа: типы поимённой части, `...` за ними (§5.3).
///
/// Три написания, и различаются они не косметикой.
///
/// * `(void)` - аргументов нет. Пустые скобки объявили бы функцию с
///   **неизвестным** списком, а не без него.
/// * `(uint64_t, uint64_t)` - обычный прототип.
/// * `(uint64_t, uint64_t, ...)` - вариадический. Печатаются только поимённые
///   типы: что стоит за `...`, прототипу не известно по построению, а вызов
///   пишет фактические аргументы сам.
///
/// Вариадический прототип - не украшение. `SysV` AMD64 требует, чтобы
/// вызывающий положил в `al` число использованных векторных регистров, и делает
/// это компилятор **по прототипу**: напечатай мы обычный - `al` не выставится,
/// и `va_arg` у чужой стороны прочтёт незаполненную область сохранения
/// регистров. Обратное так же: вызов невариадической функции через
/// вариадический прототип портит ABI с другого конца.
fn variadic_list(foreign: &Foreign) -> String {
    let named: Vec<String> = foreign
        .parameters
        .iter()
        .take(foreign.variadic.unwrap_or(foreign.parameters.len()))
        .map(|it| scalar(Repr::Flat(*it)).to_owned())
        .collect();
    match (named.is_empty(), foreign.variadic.is_some()) {
        (true, false) => "void".to_owned(),
        // Поимённых параметров у вариадической функции C требует хотя бы один
        // (`va_start` называет последний), и элаборация это уже отвергла:
        // ветвь стоит затем, что таблица `match` исчерпывающа, а не затем, что
        // такой прототип печатается.
        (true, true) => "...".to_owned(),
        (false, false) => named.join(", "),
        (false, true) => format!("{}, ...", named.join(", ")),
    }
}

/// Имя чужого символа **внутри** порождённой единицы.
///
/// Своё, потому что настоящее имя вправе быть занято системным заголовком; у
/// линкера символ остаётся тем, что написал автор - за это отвечает метка в
/// [`prototypes`].
fn local(symbol: &str) -> String {
    format!("adamas_foreign_{symbol}")
}

/// Имя обёртки экспорта **внутри** порождённой единицы.
///
/// По тому же доводу, что и [`local`], и цена та же: символ у линкера пишет
/// `__asm__`-метка, а внутри единицы стоит имя, которое системный заголовок
/// занять не может.
fn outward(symbol: &str) -> String {
    format!("adamas_export_{symbol}")
}

/// Объявления своих символов, видимых C (§5.3, колбэк уровня 1).
///
/// Метка стоит при **объявлении**, а не при определении: GNU-метка читается на
/// первом вхождении имени, и объявление здесь идёт раньше всего, потому что
/// адрес обёртки вправе понадобиться телу функции, стоящей выше неё.
fn exports(out: &mut String, program: &Program) {
    if program.exports.is_empty() {
        return;
    }
    out.push_str("/* Свои символы, видимые C (§5.3): обёртка на символ. */\n");
    for export in &program.exports {
        let _ = writeln!(
            out,
            "{} __asm__(\"{}\");",
            exported_signature(export),
            export.symbol
        );
    }
    out.push('\n');
}

/// Заголовок обёртки экспорта - один на объявление и на определение.
fn exported_signature(export: &Export) -> String {
    let taken: Vec<String> = export
        .parameters
        .iter()
        .enumerate()
        .map(|(at, ty)| format!("{} a{at}", scalar(Repr::Flat(*ty))))
        .collect();
    format!(
        "{} {}({})",
        scalar(Repr::Flat(export.result)),
        outward(&export.symbol),
        taken.join(", ")
    )
}

/// Тела обёрток: внешняя функция сишного соглашения, зовущая внутреннюю.
///
/// Обёртка, а не переименование самой `fn_N`, - см. [`crate::ir::Export`].
/// Ставится **после** определений функций: к этому месту `fn_N` уже написана,
/// и прямой вызов её компилятор вправе встроить целиком.
fn exported_bodies(out: &mut String, program: &Program) {
    for export in &program.exports {
        let given: Vec<String> = (0..export.parameters.len())
            .map(|at| format!("a{at}"))
            .collect();
        let _ = writeln!(
            out,
            "{} {{\n    return fn_{}({});\n}}\n",
            exported_signature(export),
            export.function.0,
            given.join(", ")
        );
    }
}

/// Имя трамплина колбэка уровня 2 (§5.3).
///
/// Ключ - номер формы, а не имя определения: два колбэка одной формы
/// различаются только средой, а среда едет вторым словом.
pub(crate) fn trampoline_symbol(id: CallbackId) -> String {
    format!("adamas_callback_{}", id.0)
}

/// Заголовок трамплина: сишное соглашение, последним аргументом - `userdata`.
///
/// Позиция `userdata` **последняя**, и это названная граница, а не умолчание:
/// так её кладут GNU `qsort_r`, `GLib` и `CURLOPT_WRITEFUNCTION`, а API,
/// кладущий `void *` первым (BSD `qsort_r`), уровнем 2 не покрыт.
fn trampoline_signature(id: CallbackId, described: &Callback, statics: bool) -> String {
    let taken: Vec<String> = described
        .parameters
        .iter()
        .enumerate()
        .map(|(at, (ty, _))| format!("{} a{at}", scalar(Repr::Flat(*ty))))
        .collect();
    format!(
        "{}{} {}({}, void *userdata)",
        if statics { "static " } else { "" },
        scalar(Repr::Flat(described.result.0)),
        trampoline_symbol(id),
        taken.join(", ")
    )
}

/// Тела трамплинов колбэка уровня 2 (§5.3).
///
/// Печатается это **текстом**, а не понижением, и довод записан у
/// [`crate::ir::Callback`]: трамплин вносит вектор evidence снаружи, из
/// `userdata`, а ни одна форма понижения такого не выражает - у первой вектора
/// нет вовсе, вторая берёт его скрытым аргументом от своего вызывающего.
///
/// Тот же текст берут оба бэкенда: у C он `static` в той же единице, у LLVM -
/// внешний в спутнике (`emit_llvm::support`), где лежат те же `flat.c` и
/// `release.c`. Названная цена: на пути `.ll` трамплин собран сишным
/// компилятором, а не `llc`; наблюдаемо это ничем, кроме имени в дизассемблере,
/// потому что соглашение вызова у обоих одно - сишное.
///
/// Владение расписано построчно, потому что ошибка здесь - течь либо
/// use-after-free, а не неверный ответ:
///
/// * замыкание в слоте 0 **одолжено** - `adamas_apply` его заимствует
///   (`adamas.h`), и дропает его дроп самой среды после чужого вызова;
/// * промежуточное частичное применение приходит **владением** (копия
///   замыкания) и дропается тут же;
/// * аргументы уходят владением, ровно как их ждёт `adamas_apply`;
/// * ответ приходит владением, и биты из него читаются до дропа.
pub(crate) fn callbacks(out: &mut String, program: &Program, statics: bool) {
    for (at, described) in program.callbacks.iter().enumerate() {
        let id = CallbackId(at);
        let _ = writeln!(
            out,
            "/* Трамплин колбэка уровня 2 (§5.3): `userdata` несёт замыкание и вектор evidence. */"
        );
        let _ = writeln!(out, "{} {{", trampoline_signature(id, described, statics));
        out.push_str(
            "    adamas_value pack = (adamas_value)userdata;\n\
             \x20   const adamas_evidence *ev = (const adamas_evidence *)adamas_field(pack, 1);\n\
             \x20   adamas_kont kont;\n\
             \x20   adamas_kont_init(&kont);\n\
             \x20   adamas_value held = adamas_field(pack, 0);\n",
        );
        for (position, (ty, wrapper)) in described.parameters.iter().enumerate() {
            let _ = writeln!(
                out,
                "    adamas_value w{position} = adamas_alloc({}u, 1u);",
                wrapper.0
            );
            let _ = writeln!(
                out,
                "    adamas_slot_write(w{position}, 0, adamas_word_{}(a{position}));",
                ty.name()
            );
            let callee = if position == 0 {
                "held".to_owned()
            } else {
                format!("t{}", position - 1)
            };
            let _ = writeln!(
                out,
                "    adamas_value t{position} = adamas_apply({callee}, ev, &kont, w{position});"
            );
            if position > 0 {
                let _ = writeln!(out, "    adamas_drop_value({callee});");
            }
        }
        let last = described.parameters.len().saturating_sub(1);
        let _ = writeln!(
            out,
            "    adamas_value answer = adamas_kont_run(&kont, t{last});"
        );
        let _ = writeln!(
            out,
            "    {} bits = adamas_bits_{}(adamas_slot_bits(answer, 0));",
            scalar(Repr::Flat(described.result.0)),
            described.result.0.name()
        );
        out.push_str("    adamas_drop_value(answer);\n    return bits;\n}\n\n");
    }
}

/// Типы векторов (§4.9): `vector_size`, а не массив и не структура.
///
/// **Расширение взято намеренно, и это то самое, ради чего §4.9 писался.**
/// Структура из `n` полей либо массив на `n` ячеек дали бы тот же ответ и
/// компилировались бы везде - и ровно поэтому не годятся: свидетель обязан
/// различать вектор и поэлементный цикл, а они не различаются. Расширение
/// `vector_size` принимают gcc и clang; §4.9 разрешает «эквивалентные intrinsics либо
/// scalar fallback» для non-LLVM бэкендов, и это первое из двух. Компилятор без
/// расширения порождённый код не соберёт - названным отказом сборки, а не
/// тихим скаляром.
///
/// Беззнаковый спутник заводится только у целых дорожек: в нём считается
/// арифметика, чтобы заворачивание §4.3 держалось тем же ходом, каким его
/// держит скаляр.
fn vectors(out: &mut String, program: &Program) {
    let mut shapes: Vec<(u32, PrimTy)> = Vec::new();
    // Невыровненный близнец заводится только тем формам, которые ходят в
    // память: он нужен обращению к окну колонки и больше ничему, а лишний
    // typedef в тексте программы - лишняя вещь, которую читателю надо понять.
    let mut loose: Vec<(u32, PrimTy)> = Vec::new();
    for function in &program.functions {
        let mut note = |repr: Repr| {
            if let Some(shape) = repr.vector() {
                if !shapes.contains(&shape) {
                    shapes.push(shape);
                }
            }
        };
        note(function.result);
        for binding in function.parameters.iter().chain(&function.captured) {
            note(binding.fact.repr);
        }
        walk(&function.body, &mut |expr: &Expr| {
            if let Expr::Bind { binding, .. } = expr {
                note(binding.fact.repr);
            }
            if let Expr::Match { arms, .. } = expr {
                for arm in arms {
                    for field in &arm.fields {
                        note(field.fact.repr);
                    }
                }
            }
        });
        walk(&function.body, &mut |expr: &Expr| match expr {
            Expr::SimdSplat { lanes, lane, .. }
            | Expr::SimdSet { lanes, lane, .. }
            | Expr::SimdLane { lanes, lane, .. }
            | Expr::SimdArith { lanes, lane, .. } => note(Repr::Simd {
                lanes: *lanes,
                lane: *lane,
            }),
            Expr::SimdLoad { lanes, lane, .. } | Expr::SimdStore { lanes, lane, .. } => {
                note(Repr::Simd {
                    lanes: *lanes,
                    lane: *lane,
                });
                if !loose.contains(&(*lanes, *lane)) {
                    loose.push((*lanes, *lane));
                }
            }
            _ => {}
        });
    }
    if shapes.is_empty() {
        return;
    }
    loose.sort_by_key(|(lanes, lane)| (*lanes, lane.name()));
    // Порядок - по ширине, потом по имени дорожки: `PrimTy` сравнимого порядка
    // не имеет, а текст единицы трансляции обязан быть воспроизводимым.
    shapes.sort_by_key(|(lanes, lane)| (*lanes, lane.name()));
    out.push_str(concat!(
        "/* Векторы (§4.9): дорожки лежат подряд и обрабатываются одной\n",
        " * инструкцией. `vector_size` - расширение gcc и clang; структура из\n",
        " * полей дала бы тот же ответ и потому свидетелем не является. */\n"
    ));
    for (lanes, lane) in shapes {
        let name = vector_type(lanes, lane);
        let bytes = lanes * lane.size();
        let _ = writeln!(
            out,
            "typedef {} {name} __attribute__((vector_size({bytes})));",
            scalar(Repr::Flat(lane))
        );
        let _ = writeln!(
            out,
            "_Static_assert(sizeof({name}) == {bytes}u, \"ширина вектора разошлась с §4.9\");"
        );
        if !lane.floating() {
            let _ = writeln!(
                out,
                "typedef {} {} __attribute__((vector_size({bytes})));",
                lane_word(lane),
                vector_word_type(lanes, lane)
            );
        }
    }
    if !loose.is_empty() {
        out.push_str(concat!(
            "/* Невыровненные близнецы (§4.9): ими читается и пишется окно\n",
            " * колонки. Граница у них - ширина дорожки, то есть ровно та,\n",
            " * которую обещает плоская укладка §4.11; выровненный тип дал бы\n",
            " * компилятору право на `movaps` и обрыв на первой же колонке,\n",
            " * чьё начало не кратно ширине регистра. */\n"
        ));
        for (lanes, lane) in loose {
            let name = vector_loose_type(lanes, lane);
            let bytes = lanes * lane.size();
            let align = lane.size();
            let _ = writeln!(
                out,
                "typedef {} {name} __attribute__((vector_size({bytes}), aligned({align})));",
                scalar(Repr::Flat(lane))
            );
            let _ = writeln!(
                out,
                "_Static_assert(_Alignof({name}) == {align}u, \
                 \"граница окна разошлась с шагом колонки (§4.11)\");"
            );
        }
    }
    out.push('\n');
}

/// Типы плоских агрегатов (§4.11): байты своей длины и своей границы.
///
/// Байтовый массив, а не структура из полей: укладку считает понижение по
/// правилу §4.11, и структура C добавила бы к ней **своё** правило выравнивания.
/// Совпади они сегодня - разошлись бы на первом же типе, где ABI платформы
/// думает иначе, и разошлись бы молча. `_Alignas` при этом обязателен: без него
/// массив байт стоял бы по единице, и `Float32` внутри массива читался бы
/// невыровненным.
fn packings(out: &mut String, program: &Program) {
    if program.packings.is_empty() {
        return;
    }
    out.push_str(concat!(
        "/* Плоские агрегаты (§4.11): поля лежат подряд, поле адресуется\n",
        " * смещением. Размер и граница посчитаны понижением, а не C. */\n"
    ));
    for (at, packing) in program.packings.iter().enumerate() {
        let variants: Vec<String> = packing
            .variants
            .iter()
            .map(|variant| {
                let fields: Vec<String> = variant
                    .labels
                    .iter()
                    .zip(&variant.slots)
                    .map(|(label, slot)| {
                        let ty = match slot.ty {
                            crate::ir::SlotTy::Prim(prim) => prim.name().to_owned(),
                            crate::ir::SlotTy::Pack(sub) => format!("pack#{}", sub.0),
                        };
                        format!("{}@{} {ty}", escaped(label), slot.offset)
                    })
                    .collect();
                match variant.ctor {
                    Some(tag) => format!("#{} {}", tag.0, fields.join(", ")),
                    None => fields.join(", "),
                }
            })
            .collect();
        let described = if packing.tag == 0 {
            variants.join(" ")
        } else {
            format!("тег {} байт; {}", packing.tag, variants.join(" | "))
        };
        let _ = writeln!(out, "/* {described} */");
        let _ = writeln!(
            out,
            "typedef struct adamas_pack_{at} {{ _Alignas({}) unsigned char bytes[{}]; }} \
             adamas_pack_{at};",
            packing.align, packing.size
        );
        let _ = writeln!(
            out,
            "_Static_assert(sizeof(adamas_pack_{at}) == {}u, \"размер агрегата разошёлся с §4.11\");",
            packing.size
        );
        let _ = writeln!(
            out,
            "_Static_assert(_Alignof(adamas_pack_{at}) == {}u, \"граница агрегата разошлась с §4.11\");",
            packing.align
        );
    }
    out.push('\n');
}

/// Таблица конструкторов: имя и число полей по тегу.
///
/// Видна LLVM-эмиттеру ([`crate::emit_llvm`]) намеренно: печать и дроп детей у
/// двух бэкендов **одни** - те же `print.c` и `release.c`, - а читают они эту
/// таблицу. Вторая её сборка разъехалась бы с первой молча, и первым бы это
/// увидел не прогон, а пользователь с перепутанным именем конструктора.
pub(crate) fn table(out: &mut String, program: &Program) {
    out.push_str(concat!(
        "/* Конструкторы программы по тегу. Хвостовой элемент - чтобы массив не\n",
        " * оказался пустым у программы без единого конструктора. */\n",
    ));
    let _ = writeln!(
        out,
        "#define ADAMAS_CONSTRUCTORS {}u",
        program.constructors.len()
    );
    out.push_str("static const char *const adamas_con_name[] = {\n");
    for constructor in &program.constructors {
        let _ = writeln!(
            out,
            "    \"{}\", /* {} */",
            escaped(&constructor.name),
            escaped(&constructor.data)
        );
    }
    out.push_str("    \"\"\n};\n\nstatic const uint16_t adamas_con_slots[] = {\n");
    for constructor in &program.constructors {
        let _ = writeln!(out, "    {}u,", constructor.slots());
    }
    out.push_str("    0u\n};\n\n");

    // Сорта слотов лежат подряд, у каждого конструктора своё начало: плоский
    // слот дроп с печатью обязаны отличить от указательного (§4.11), а рваная
    // таблица стоила бы максимума арности на каждый конструктор.
    out.push_str(concat!(
        "/* Сорт каждого слота: `ADAMAS_FLAT_BOXED` - ссылка, иначе примитив.\n",
        " * Слоты конструкторов идут подряд, начало каждого - в `adamas_con_slot0`. */\n",
        "static const uint16_t adamas_con_slot0[] = {\n"
    ));
    let mut first = 0usize;
    for constructor in &program.constructors {
        let _ = writeln!(out, "    {first}u,");
        first += constructor.slots();
    }
    let _ = writeln!(out, "    {first}u\n}};\n");
    out.push_str("static const uint8_t adamas_slot_kind[] = {\n");
    for constructor in &program.constructors {
        for repr in constructor.slot_reprs() {
            let _ = writeln!(
                out,
                "    {}u, /* {} */",
                slot_kind(repr),
                escaped(&constructor.name)
            );
        }
    }
    out.push_str("    ADAMAS_FLAT_BOXED\n};\n\n");

    // Метки записи (§4.2). Печать по ним отличается от печати конструктора и
    // формой, и счётом глубины, поэтому таблица её и включает: `NULL` -
    // конструктор семейства, иначе - имена полей в порядке слотов.
    out.push_str(concat!(
        "/* Метки полей записи по слотам; `NULL` у конструктора семейства.\n",
        " * Слоты идут подряд, начало каждого - в `adamas_con_slot0`. */\n",
        "static const char *const adamas_slot_label[] = {\n"
    ));
    for constructor in &program.constructors {
        for slot in 0..constructor.slots() {
            match label(constructor, slot) {
                Some(name) => {
                    let _ = writeln!(out, "    \"{}\",", escaped(name));
                }
                None => out.push_str("    NULL,\n"),
            }
        }
    }
    out.push_str("    NULL\n};\n\n");

    // Сколько полей у записи **написано**: печать обязана назвать все, а слот
    // достаётся не всякому - типовой член живёт только в типах (§4.8). Ноль -
    // конструктор семейства либо пустая запись, у которой печать и так совпадает.
    out.push_str(concat!(
        "/* Сколько полей у записи написано; ноль - конструктор семейства.\n",
        " * Больше числа слотов - печатать её нечем: часть полей стёрта. */\n",
        "static const uint16_t adamas_con_labels[] = {\n"
    ));
    for constructor in &program.constructors {
        let _ = writeln!(
            out,
            "    {}u,",
            constructor.labels.as_ref().map_or(0, Vec::len)
        );
    }
    out.push_str("    0u\n};\n\n");
}

/// Метка живого слота: стёртое поле слота не занимает.
fn label(constructor: &Constructor, slot: usize) -> Option<&str> {
    let labels = constructor.labels.as_ref()?;
    let at = constructor
        .binders
        .iter()
        .enumerate()
        .filter(|(_, fact)| fact.present)
        .nth(slot)
        .map(|(position, _)| position)?;
    labels.get(at).map(String::as_str)
}

/// Номера функций, которым нужен трамплин: они где-то стоят значением.
fn wrapped(program: &Program) -> BTreeSet<FuncId> {
    let mut found = BTreeSet::new();
    for function in &program.functions {
        walk(&function.body, &mut |expr| {
            if let Expr::Closure { function, .. } = expr {
                found.insert(*function);
            }
        });
    }
    found
}

/// Деструкторы кадров `CLOSING`: им нужен забирающий трамплин [`taker`].
fn moving(program: &Program) -> BTreeSet<FuncId> {
    let mut found = BTreeSet::new();
    for function in &program.functions {
        walk(&function.body, &mut |expr| {
            if let Expr::Closing { closer, .. } = expr {
                found.insert(*closer);
            }
        });
    }
    found
}

/// Теги конструкторов, которые где-то стоят значением.
fn builders(program: &Program) -> BTreeSet<CtorId> {
    let mut found = BTreeSet::new();
    for function in &program.functions {
        walk(&function.body, &mut |expr| {
            if let Expr::ConstructClosure { constructor } = expr {
                found.insert(*constructor);
            }
        });
    }
    found
}

/// Обход дерева выражения сверху вниз.
fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    for child in expr.children() {
        walk(child, visit);
    }
}

/// Скрытые аргументы второй формы, в порядке `adamas_lowered_second`.
///
/// Порядок здесь **один на всё понижение**: объявление, определение, прямой
/// вызов и трамплин печатаются отсюда же, и разъехаться им негде. Он же
/// несимметричен по типам (`const adamas_evidence *` против `adamas_kont *`),
/// поэтому перестановка молча не сокращается: порождённый C с ней не
/// собирается вовсе (`-Werror=incompatible-pointer-types` в прогонах).
const HIDDEN: &str = "const adamas_evidence *ev, adamas_kont *kont";

/// Они же на месте вызова.
const FORWARD: &str = "ev, kont";

/// Сигнатура функции: скрытые аргументы формы и живые связывания.
///
/// У первой формы скрытых нет **вовсе** (`adamas_lowered_first`): написанное и
/// есть всё. У второй их два, и стоят они перед написанным - вектор evidence,
/// затем ручка стека, как в `adamas_lowered_second`. Захваченная среда сюда
/// приходит обычными параметрами - трамплин достаёт её из слотов замыкания и
/// передаёт явно.
fn signature(function: &Function) -> String {
    let mut live: Vec<String> = match function.form {
        Form::Stack => Vec::new(),
        Form::Detached => vec![HIDDEN.to_owned()],
    };
    live.extend(
        function
            .live_captured()
            .chain(function.live_parameters())
            .map(|binding| format!("{} v{}", c_type(binding.fact.repr), binding.local.0)),
    );
    let taken = if live.is_empty() {
        "void".to_owned()
    } else {
        live.join(", ")
    };
    format!(
        "static {} fn_{}({taken})",
        c_type(function.result),
        function.id.0
    )
}

/// Прототип функции без имён: им сверяются вызывающий и вызываемый под `musttail`.
///
/// Первая строка - тип ответа, дальше типы аргументов в порядке печати
/// ([`signature`]), причём скрытые аргументы второй формы входят в перечень
/// наравне с написанными: у формы они и есть часть прототипа.
///
/// Сверка нужна потому, что `musttail` требует совпадения прототипов, и
/// требуют его **оба** компилятора, которыми собирается порождённое. Мера
/// «совпали дословно» выбрана не из осторожности, а замером: gcc принимает
/// вызывающего без параметров, зовущего функцию четырёх, а clang такую пару
/// отвергает **сборкой**, - то есть правило шире дословного совпадения
/// принадлежало бы компилятору хоста, а не языку. Дословное совпадение берут
/// оба, на всех трёх уровнях оптимизации (проба `mt.c`, 2026-09-22).
fn prototype(function: &Function) -> Vec<String> {
    let mut shape = vec![c_type(function.result)];
    if function.form == Form::Detached {
        shape.push(HIDDEN.to_owned());
    }
    shape.extend(
        function
            .live_captured()
            .chain(function.live_parameters())
            .map(|binding| c_type(binding.fact.repr)),
    );
    shape
}

/// Сигнатура трамплина: каноническая форма кода замыкания из `adamas.h`.
///
/// Скрытые аргументы у неё оба, потому что граница замыкания **динамическая**:
/// какая из двух форм за указателем, место вызова не знает. Тело первой формы
/// их не смотрит, и обещание «первая форма не платит ничего» держится там, где
/// вызываемый известен статически, - на прямом вызове.
fn trampoline(name: &str) -> String {
    format!(
        "static adamas_value {name}(adamas_value self, const adamas_evidence *ev, \
         adamas_kont *kont, adamas_value arg)"
    )
}

/// Тело функции: чистым отрезком либо цепочкой кусков.
///
/// Дробится тело второй формы, внутри которой есть точка приостановки
/// ([`crate::split`]). Прочие идут как шли: первая форма - обычной C-функцией,
/// вторая без приостановок - ею же со скрытыми аргументами. Дроблёная
/// возвращает не свой ответ, а значение вершине стека, и `return` в ней стоит
/// на каждом пути - отсюда и разница в печати.
fn body(
    out: &mut String,
    program: &Program,
    function: &Function,
    suspending: &Suspension,
    forward: &mut Vec<String>,
) -> Option<EmitError> {
    let split = suspending.functions.contains(&function.id);
    let mut emitter = Emitter {
        program,
        suspending,
        out: String::new(),
        temps: 0,
        reprs: shapes(function),
        hidden: function.form == Form::Detached,
        id: function.id,
        proto: prototype(function),
        chunks: Vec::new(),
        forward: Vec::new(),
        epilogue: Vec::new(),
        failure: None,
    };
    let answer = if split {
        emitter.tail(&function.body, 1);
        None
    } else if emitter.tail_jumping(&function.body) {
        // Функция с хвостовым вызовом под приставку печатается возвратом на
        // каждом пути: только там вызов стоит под `return`, а `musttail`
        // требует именно этого (§6). Прочие печатаются как печатались.
        emitter.returning(&function.body, 1);
        None
    } else {
        Some(emitter.value(&function.body, 1))
    };
    for chunk in &emitter.chunks {
        out.push_str(chunk);
    }
    let _ = writeln!(out, "/* {} */", escaped(&function.name));
    let _ = writeln!(out, "{} {{", signature(function));
    for binding in function.live_captured().chain(function.live_parameters()) {
        let _ = writeln!(
            out,
            "    /* v{} - {} */",
            binding.local.0,
            escaped(&binding.name)
        );
    }
    out.push_str(&emitter.out);
    match answer {
        Some(answer) => {
            let _ = writeln!(out, "    return {answer};\n}}\n");
        }
        None => {
            let _ = writeln!(out, "}}\n");
        }
    }
    forward.append(&mut emitter.forward);
    emitter.failure
}

/// Трамплин: замыкание отдаёт слоты позиционно, функция берёт их аргументами.
///
/// Слоты принадлежат замыканию, а функция берёт аргументы **владением**, отсюда
/// `adamas_dup` на каждый: своё замыкание дропает применение
/// ([`perceus`](crate::perceus)), и без дублирования оно унесло бы слоты с
/// собой. Последний аргумент приходит владением уже от `adamas_apply`.
///
/// Скрытые аргументы у самого трамплина есть всегда - граница замыкания
/// динамическая, - а дальше он передаёт их ровно второй форме. Первой они не
/// передаются вовсе: у неё их нет в сигнатуре, и это ровно то, чем «первая
/// форма не платит ничего» отличается от «платит и не смотрит».
fn wrapper(out: &mut String, function: &Function) {
    let env = function.live_captured().count();
    let arity = function.parameters.len();
    let _ = writeln!(
        out,
        "/* `{}` значением: слоты - среда, затем накопленные аргументы. */",
        escaped(&function.name)
    );
    let _ = writeln!(out, "{} {{", trampoline(&format!("box_{}", function.id.0)));
    if arity == 0 {
        out.push_str("    adamas_fail(\"замыкание без параметров\");\n}\n\n");
        return;
    }
    // Слотов ровно столько, сколько связываний у ядра, - стёртые в том числе
    // (см. правило позиционного применения в `lower`). Стёртый слот в вызов не
    // идёт, и отдавать его не приходится: понижение кладёт туда `ADAMAS_ERASED`,
    // значение непосредственное, ячейки за ним нет.
    let mut taken: Vec<String> = match function.form {
        Form::Stack => Vec::new(),
        Form::Detached => vec![FORWARD.to_owned()],
    };
    taken.extend((0..env).map(|slot| format!("adamas_dup(adamas_closure_get(self, {slot}))")));
    for (position, parameter) in function.parameters.iter().enumerate() {
        if !parameter.fact.present {
            continue;
        }
        taken.push(if position + 1 == arity {
            "arg".to_owned()
        } else {
            format!("adamas_dup(adamas_closure_get(self, {}))", env + position)
        });
    }
    let _ = writeln!(
        out,
        "    return fn_{}({});\n}}\n",
        function.id.0,
        taken.join(", ")
    );
}

/// Трамплин деструктора scope'а: слоты **забираются**, а не дублируются.
///
/// Зовут такое замыкание ровно раз и тут же дропают - кадр `CLOSING` его
/// единственный владелец (`adamas.h`). Дублируй слоты, как общий трамплин, - и
/// ресурс достался бы деструктору **разделённым**: FBIP внутри него не
/// сработал бы никогда, а порядок деструкторов перестал бы быть наблюдаемым
/// ценой. Слот после взятия зануляется единицей, поэтому дроп замыкания следом
/// отдаёт уже ничего.
fn taker(out: &mut String, function: &Function) {
    let env = function.live_captured().count();
    let _ = writeln!(
        out,
        "/* `{}` кадром scope: слоты уходят владением. */",
        escaped(&function.name)
    );
    let _ = writeln!(out, "{} {{", trampoline(&format!("take_{}", function.id.0)));
    for slot in 0..env {
        let _ = writeln!(
            out,
            "    adamas_value s{slot} = adamas_closure_get(self, {slot});"
        );
        let _ = writeln!(out, "    adamas_closure_set(self, {slot}, adamas_unit());");
    }
    let mut taken: Vec<String> = match function.form {
        Form::Stack => Vec::new(),
        Form::Detached => vec![FORWARD.to_owned()],
    };
    taken.extend((0..env).map(|slot| format!("s{slot}")));
    taken.push("arg".to_owned());
    let _ = writeln!(
        out,
        "    return fn_{}({});\n}}\n",
        function.id.0,
        taken.join(", ")
    );
}

/// Сигнатура веток площадки: каноническая форма `adamas_handler_code`.
fn branches_signature(at: usize) -> String {
    format!(
        "static adamas_value handler_{at}(adamas_frame *h, adamas_kont *kont, \
         uint32_t op, adamas_value *args, size_t count)"
    )
}

/// Сигнатура дропа среды кадра хендлера.
fn release_signature(at: usize) -> String {
    frame_release_signature(&format!("release_{at}"))
}

/// Сигнатура куска дроблёного тела: каноническая форма `adamas_frame_code`.
fn chunk_signature(name: &str) -> String {
    format!("static adamas_value {name}(adamas_frame *h, adamas_kont *kont, adamas_value incoming)")
}

/// Сигнатура дропа среды кадра: каноническая форма `adamas_frame_release`.
fn frame_release_signature(name: &str) -> String {
    format!("static void {name}(adamas_frame *h, adamas_kont *kont)")
}

/// Одна ветвь `switch`'а веток: всё, чем ветки различаются между собой.
struct Dispatch<'a> {
    /// Метка `case`: номер операции либо `ADAMAS_HANDLER_RETURN`.
    case: &'a str,
    /// Имя операции - им подписан порождённый C.
    title: &'a str,
    /// Слотов в среде кадра.
    env: usize,
    /// Функция тела ветки.
    function: FuncId,
    /// Сколько аргументов операции она связывает.
    written: usize,
    /// Её вердикт (§3.4).
    verdict: Verdict,
    /// Мультишотна ли площадка.
    multi: bool,
}

/// Ветки одной площадки `handle` одной функцией: их выбирает номер операции.
///
/// Одной, а не по функции на ветку, потому что выбирает их **рантайм**:
/// операция приходит с кадром на руках и статически не знает, чьи это ветки
/// (`adamas.h`, `adamas_handler_code`). Тела же веток - обычные функции
/// понижения, и здесь только раздача аргументов.
///
/// Среда кадра принадлежит кадру, а функция берёт аргументы владением - отсюда
/// `adamas_dup` на каждый слот, тот же довод, что у трамплина замыкания.
/// Аргументы операции приходят владением и передаются как есть; лишние -
/// синтезированный триггер приостановленного вычисления - дропаются здесь:
/// сколько ветка связывает, знает эта площадка, а место операции не знает.
/// Одна ветвь раздачи: аргументы ветке, а у абортивной - ещё и снятие сегмента.
///
/// Вердиктов три, и различает их то, что случается с сегментом.
///
/// **Хвостово-резумптивная** его не трогает: ответ ветки есть значение
/// операции, и трамплин отдаёт его кадру продолжения самой операции.
///
/// **Абортивная** режет сегмент и кладёт его раскрутку кадром **до** ветки.
/// Порядок тот же, каким его держит машина (`adamas-interp/src/effect.rs`,
/// `performed` и `buried`): сперва разрез - кадр хендлера в нём, - потом бежит
/// ветка, и только потом деструкторы, потому что кадр раскрутки лежит ниже
/// всего, что ветка положит. Ответ ветки приходит раскрутке проточным
/// значением и выходит из неё же - кадру продолжения `handle`, который после
/// разреза стал вершиной. Перестань резать до ветки - и операция ветки нашла
/// бы собственный хендлер живым.
///
/// **Общая** режет сегмент в **значение** и отдаёт его ветке лишним
/// аргументом. Дальше решает владение: возобновит ветка - звенья встанут
/// обратно, дропнет - раскрутка пойдёт от дропа. Кадра решения о смерти
/// резумпции здесь нет и не нужно (§10 вопрос 129): у машины его требовал
/// признак «резумпцию не позвали», считаемый на возврате ветки, а владение
/// отвечает на тот же вопрос точнее и без точки.
/// **Мультишотная** режет так же, но помечает ручку: возобновление будет
/// ставить копию сегмента, пока на ручку есть лишние ссылки
/// (`adamas_segment_multi`, §3.4 «Стоимость multi-shot»). Вердикт у всех её
/// веток общий - сколько раз позовут ω-резумпцию, телу ветки не видно.
fn dispatch(out: &mut String, arm: &Dispatch<'_>) {
    let &Dispatch {
        case,
        title,
        env,
        function,
        written,
        verdict,
        multi,
    } = arm;
    let _ = writeln!(out, "    case {case}: {{ /* {title} */");
    let _ = writeln!(
        out,
        "        if (count < {written}u) {{ adamas_fail(\"ветке `{title}` не хватило аргументов\"); }}"
    );
    let _ = writeln!(
        out,
        "        for (size_t extra = {written}u; extra < count; extra += 1) {{ \
         adamas_drop_value(args[extra]); }}"
    );
    if verdict == Verdict::Abortive {
        let _ = writeln!(
            out,
            "        adamas_segment_unwind(kont, adamas_kont_cut(kont, h));"
        );
    }
    let mut given: Vec<String> = vec![FORWARD.to_owned()];
    given.extend((0..env).map(|slot| format!("adamas_dup(env[{slot}])")));
    given.extend((0..written).map(|slot| format!("args[{slot}]")));
    if verdict == Verdict::General {
        let seized = "adamas_segment_value(adamas_kont_cut(kont, h))";
        let seized = if multi {
            format!("adamas_segment_multi({seized})")
        } else {
            seized.to_owned()
        };
        let _ = writeln!(out, "        adamas_value seized = {seized};");
        given.push("seized".to_owned());
    }
    let _ = writeln!(
        out,
        "        return fn_{}({});",
        function.0,
        given.join(", ")
    );
    let _ = writeln!(out, "    }}");
}

fn branches(out: &mut String, program: &Program, at: usize) {
    let described = &program.handlers[at];
    let label = &program.labels[described.label.0 as usize];
    let env = described
        .captured
        .iter()
        .filter(|it| it.fact.present)
        .count();
    let _ = writeln!(out, "/* ветки `{}` */", escaped(&label.name));
    let _ = writeln!(out, "{} {{", branches_signature(at));
    let _ = writeln!(
        out,
        "    const adamas_evidence *ev = adamas_frame_evidence(h);"
    );
    if env > 0 {
        let _ = writeln!(out, "    adamas_value *env = adamas_frame_env(h);");
    }
    let _ = writeln!(out, "    switch (op) {{");
    for (slot, branch) in described.branches.iter().enumerate() {
        let title = label
            .operations
            .get(slot)
            .map_or_else(|| format!("#{slot}"), |name| escaped(name));
        dispatch(
            out,
            &Dispatch {
                case: &format!("{slot}u"),
                title: &title,
                env,
                function: branch.function,
                written: branch.written,
                verdict: branch.verdict,
                multi: described.multi,
            },
        );
    }
    dispatch(
        out,
        &Dispatch {
            case: "ADAMAS_HANDLER_RETURN",
            title: "return",
            env,
            function: described.returned,
            written: 1,
            // Резумпции у неё нет вовсе: вычисление договорило, снимать нечего.
            verdict: Verdict::Tail,
            multi: false,
        },
    );
    let _ = writeln!(out, "    default: break;");
    let _ = writeln!(out, "    }}");
    let _ = writeln!(
        out,
        "    adamas_fail(\"у хендлера `{}` нет такой ветки\");",
        escaped(&label.name)
    );
    let _ = writeln!(out, "}}\n");

    if env == 0 {
        return;
    }
    let _ = writeln!(out, "/* среда веток `{}` */", escaped(&label.name));
    let _ = writeln!(out, "{} {{", release_signature(at));
    let _ = writeln!(out, "    (void)kont;");
    let _ = writeln!(out, "    adamas_value *env = adamas_frame_env(h);");
    for slot in 0..env {
        let _ = writeln!(out, "    adamas_drop_value(env[{slot}]);");
    }
    let _ = writeln!(out, "}}\n");
}

/// Сборщик конструктора: замыкание копит аргументы, последний собирает объект.
///
/// `adamas_set_field` владение забирает, а слоты принадлежат замыканию, отсюда
/// `adamas_dup` - тот же довод, что у [`wrapper`].
fn builder(out: &mut String, constructor: &Constructor) {
    let slots = constructor.slots();
    let arity = constructor.binders.len();
    let _ = writeln!(out, "/* `{}` значением. */", escaped(&constructor.name));
    let _ = writeln!(
        out,
        "{} {{",
        trampoline(&format!("make_{}", constructor.tag.0))
    );
    if arity == 0 {
        out.push_str("    adamas_fail(\"конструктор без полей значением\");\n}\n\n");
        return;
    }
    let _ = writeln!(
        out,
        "    adamas_value value = adamas_alloc({}u, {slots}u);",
        constructor.tag.0
    );
    // Аргументов накоплено по связыванию ядра - стёртые в том числе, - а слот
    // объекта достался живым. Стёртый в объект не идёт и отдачи не требует:
    // понижение кладёт туда `ADAMAS_ERASED`, ячейки за ним нет.
    let mut slot = 0usize;
    for (position, fact) in constructor.binders.iter().enumerate() {
        if !fact.present {
            continue;
        }
        let taken = if position + 1 == arity {
            "arg".to_owned()
        } else {
            format!("adamas_dup(adamas_closure_get(self, {position}))")
        };
        let _ = writeln!(out, "    adamas_set_field(value, {slot}, {taken});");
        slot += 1;
    }
    out.push_str("    return value;\n}\n\n");
}

/// Представления всех связываний функции.
///
/// Собираются разом и заранее: C-тип временного имени зависит от того, что в
/// нём лежит, а узнаётся это по связываниям, до которых обход ещё не дошёл.
fn shapes(function: &Function) -> HashMap<LocalId, Repr> {
    let mut found = HashMap::new();
    for binding in function.captured.iter().chain(&function.parameters) {
        found.insert(binding.local, binding.fact.repr);
    }
    walk(&function.body, &mut |expr| match expr {
        Expr::Bind { binding, .. } => {
            found.insert(binding.local, binding.fact.repr);
        }
        Expr::Match { arms, .. } => {
            for arm in arms {
                for field in &arm.fields {
                    found.insert(field.local, field.fact.repr);
                }
            }
        }
        Expr::Reclaim { token, .. } => {
            // Придержанный блок - сырая ячейка, представление у неё одно.
            found.insert(*token, Repr::Boxed);
        }
        _ => {}
    });
    found
}

/// Состояние эмиссии одного тела.
struct Emitter<'a> {
    program: &'a Program,
    /// Функции, чей вызов есть точка приостановки (§3.4, решение 3 волны 4).
    suspending: &'a Suspension,
    out: String,
    temps: u32,
    /// Что в каком связывании лежит: от этого C-тип временного имени.
    reprs: HashMap<LocalId, Repr>,
    /// Есть ли у эмитируемого тела скрытые аргументы - то есть вторая ли форма.
    ///
    /// От этого зависит, чем идут вектор и ручка на месте вызова: своими у
    /// второй формы и `NULL` плюс свой корень у первой, которой их взять негде.
    hidden: bool,
    /// Чьё тело эмитируется: номер идёт в имена кусков.
    id: FuncId,
    /// Прототип эмитируемого тела: с ним сверяется хвостовой вызов ([`prototype`]).
    proto: Vec<String>,
    /// Готовые куски дроблёного тела: каждый - своя C-функция.
    chunks: Vec<String>,
    /// Их объявления: кусок ссылается на кусок с бо́льшим номером.
    forward: Vec<String>,
    /// Что обязан отдать всякий возврат из этого куска.
    ///
    /// Живёт здесь один жанр - расширенный вектор evidence места `handle`:
    /// вычисление под ним идёт хвостом того же куска, а дроп поставить после
    /// `return` нечем. Кадры, положенные вычислением, свою ссылку берут сами.
    epilogue: Vec<String>,
    /// Названная граница, встреченная по дороге. Отдаётся отказом.
    ///
    /// Полем, а не ответом обхода: обход печатает, и `Result` пришлось бы
    /// протащить сквозь каждый узел ради одного места, где отказ возможен.
    failure: Option<EmitError>,
}

impl Emitter<'_> {
    /// Свежее временное имя.
    fn temp(&mut self) -> String {
        let name = format!("t{}", self.temps);
        self.temps += 1;
        name
    }

    /// Представление значения выражения.
    fn shape(&self, expr: &Expr) -> Repr {
        match expr {
            Expr::Local(local) => self.reprs.get(local).copied().unwrap_or(Repr::Boxed),
            Expr::Literal { ty, .. } | Expr::Primitive { ty, .. } => Repr::Flat(*ty),
            Expr::Call { function, .. } => self.program.functions[function.0].result,
            // Чужой вызов (§5.3): ответ его берётся из таблицы символов.
            Expr::Foreign { function, .. } => self.program.foreigns[function.0].result.repr(),
            // Ответ scope'а есть ответ его тела: деструктор отвечает мимо.
            Expr::Bind { body, .. }
            | Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. }
            | Expr::Discard { body, .. }
            | Expr::Closing { body, .. } => self.shape(body),
            Expr::Match { arms, .. } => arms
                .first()
                .map_or(Repr::Boxed, |arm| self.shape(&arm.body)),
            Expr::Layout { .. } => Repr::Layout,
            Expr::LayoutField { .. } => Repr::Flat(PrimTy::UInt32),
            Expr::Pack { packing, .. } => Repr::Packed(*packing),
            Expr::Unpack {
                packing,
                variant,
                field,
                ..
            } => self.program.packings[packing.0 as usize].variants[*variant as usize].slots
                [*field as usize]
                .ty
                .repr(),
            Expr::ArrayNew { stride, .. } | Expr::ArraySet { stride, .. } => {
                Repr::Array(elems(*stride))
            }
            Expr::ArrayIndex { stride, .. } => stride.map_or(Repr::Boxed, Stride::element),
            // Вектор (§4.9): четыре узла отдают его, чтение дорожки - дорожку,
            // а запись окна - саму колонку.
            Expr::SimdSplat { lanes, lane, .. }
            | Expr::SimdSet { lanes, lane, .. }
            | Expr::SimdArith { lanes, lane, .. }
            | Expr::SimdLoad { lanes, lane, .. } => Repr::Simd {
                lanes: *lanes,
                lane: *lane,
            },
            Expr::SimdLane { lane, .. } => Repr::Flat(*lane),
            Expr::SimdStore { .. } => Repr::Array(Elems::Flat),
            Expr::RegionNew
            | Expr::SharedNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => Repr::Region,
            // Смещение внутри области (§3.6), адрес нагрузки одолженного массива
            // и адрес своей функции, видимой C (§5.3), - все три плоское слово
            // ширины указателя, то есть ровно то, чем уровень 1 считает `CPtr`.
            Expr::ArrayData { .. }
            | Expr::Exported(_)
            // Адрес трамплина (§5.3, уровень 2) - то же слово.
            | Expr::Trampoline(_)
            | Expr::Userdata(_)
            | Expr::RegionLast { .. } => Repr::Flat(PrimTy::UInt64),
            Expr::RegionRead { stride, .. } => stride.element(),
            Expr::Erased
            | Expr::Construct { .. }
            // Среда колбэка (§5.3) - объект с двумя указательными слотами.
            | Expr::Environment { .. }
            | Expr::ConstructClosure { .. }
            // Ответ сравнения - конструктор `Bool` (§4.3), то есть
            // непосредственное значение: аргументы плоские, ответ нет.
            | Expr::Compare { .. }
            | Expr::Closure { .. }
            // Ответ хендлера даёт ветка `return`, ответ операции - ветка
            // операции, и обе отвечают указателем: ветки идут через кадр, а
            // слот кадра единообразен (§4.11).
            | Expr::Handle { .. }
            | Expr::Perform { .. }
            // Ответ питомника - значение корневого файбера, ответ его операции
            // - значение ветки либо круга; отмена отдаёт то же разбираемое.
            | Expr::Nursery { .. }
            | Expr::Fiber { .. }
            | Expr::Cancel { .. }
            // Ответ возобновления - ответ хендлера: возобновлённое вычисление
            // договаривает под ним же (§3.4, глубокий хендлер).
            | Expr::Resume { .. }
            // Ответ маски есть ответ вычисления под ней, а оно указательное:
            // маска стоит вокруг `{ρ} A` (§3.4).
            | Expr::Mask { .. }
            | Expr::Apply { .. } => Repr::Boxed,
        }
    }

    /// Отступ уровня `depth`.
    fn pad(depth: usize) -> String {
        "    ".repeat(depth)
    }

    /// Эмитит выражение и отдаёт имя, в котором лежит его значение.
    ///
    /// Точек приостановки здесь не бывает: их снимает дробление
    /// ([`crate::split`]), и приходят они сюда хвостом куска, а не значением.
    /// Операция в тихой программе - не точка приостановки (вопрос 74) и
    /// значением бывает; её берёт [`Emitter::performing`].
    fn value(&mut self, expr: &Expr, depth: usize) -> String {
        self.emitted(expr, depth)
    }

    /// Эмитит выражение и отдаёт имя, в котором лежит его значение.
    ///
    /// Каждый составной узел получает своё имя: порядок вычисления виден в
    /// тексте, а не выводится из правил C.
    #[allow(
        clippy::too_many_lines,
        reason = "разбор узлов - одна таблица, и делить её значило бы прятать её половину"
    )]
    fn emitted(&mut self, expr: &Expr, depth: usize) -> String {
        match expr {
            Expr::Local(local) => format!("v{}", local.0),
            Expr::Erased => "ADAMAS_ERASED".to_owned(),
            Expr::Literal { ty, bits } => self.literal(*ty, *bits, depth),
            Expr::Primitive {
                op,
                ty,
                left,
                right,
            } => self.arithmetic(*op, *ty, left, right, depth),
            Expr::Compare {
                op,
                ty,
                left,
                right,
                yes,
                no,
            } => self.comparison(*op, *ty, left, right, (*yes, *no), depth),
            Expr::Layout { size, align } => self.descriptor(*size, *align, depth),
            Expr::LayoutField { descriptor, align } => {
                self.descriptor_field(*descriptor, *align, depth)
            }
            Expr::Pack {
                packing,
                variant,
                fields,
            } => self.pack(*packing, *variant, fields, depth),
            Expr::Unpack {
                packing,
                variant,
                field,
                value,
            } => self.unpack(*packing, *variant, *field, value, depth),
            Expr::ArrayNew { .. } | Expr::ArraySet { .. } | Expr::ArrayIndex { .. } => {
                self.array(expr, depth)
            }
            Expr::SimdSplat { .. }
            | Expr::SimdSet { .. }
            | Expr::SimdLane { .. }
            | Expr::SimdArith { .. }
            | Expr::SimdLoad { .. }
            | Expr::SimdStore { .. } => self.vector(expr, depth),
            Expr::RegionNew
            | Expr::SharedNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => self.region(expr, depth),
            Expr::Construct {
                constructor,
                reuse,
                arguments,
            } => self.construct(*constructor, *reuse, arguments, depth),
            Expr::ConstructClosure { constructor } => self.building(*constructor, depth),
            Expr::Call {
                function,
                arguments,
            } => self.call(*function, arguments, depth),
            Expr::Foreign {
                function,
                arguments,
            } => self.foreign(*function, arguments, depth),
            Expr::Exported(id) => self.exported(*id, depth),
            Expr::Trampoline(id) => self.trampolined(*id, depth),
            // Адрес среды словом: сам объект остаётся связыванием, и дропает
            // его вставка RC после чужого вызова - та же пара, что у буфера.
            Expr::Userdata(local) => self.carried(*local, depth),
            Expr::Environment {
                constructor,
                closure,
            } => self.userdata(*constructor, closure, depth),
            Expr::ArrayData { array } => self.lending(array, depth),
            Expr::Closure { function, captured } => self.closure(*function, captured, depth),
            Expr::Handle {
                handler,
                captured,
                computation,
            } => self.handling(*handler, captured, computation, depth),
            Expr::Mask { label, computation } => self.masking(*label, computation, depth),
            // Питомник в чистой функции - **корень своего стека**, тем же
            // правом, каким его заводит хендлер: row у `withNursery` пуста, и
            // наружу круга не уходит ни одной операции (§3.4, погашение
            // расширением справа).
            Expr::Nursery { body } => self.nursing(body, depth),
            // Операция значением бывает только в тихой программе (вопрос 74):
            // там она не точка приостановки, и дробление её не выносит.
            Expr::Perform {
                label,
                operation,
                arguments,
            } => self.performing(*label, *operation, arguments, depth),
            // Прочие точки приостановки значением не бывают: их снимает
            // дробление ([`crate::split`]), и в чистый отрезок они не попадают.
            // Операция питомника среди них безусловно: тишина её не касается -
            // уступка режет сегмент по построению.
            Expr::Closing { .. }
            | Expr::Resume { .. }
            | Expr::Fiber { .. }
            | Expr::Cancel { .. } => {
                unreachable!("точка приостановки в чистом отрезке: дробление её не сняло")
            }
            Expr::Apply { callee, argument } => self.applying(callee, argument, depth),
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis(scrutinee, arms, depth),
            Expr::Bind { .. }
            | Expr::Dup { .. }
            | Expr::Drop { .. }
            | Expr::Reclaim { .. }
            | Expr::Discard { .. } => self.bookkeeping(expr, depth),
        }
    }

    /// Узлы, у которых своего значения нет: связывание и учёт ссылок (§5.1).
    ///
    /// Каждый печатает строку и уходит в тело - значением служит оно.
    fn bookkeeping(&mut self, expr: &Expr, depth: usize) -> String {
        let body = self.bookkept(expr, depth);
        self.value(body, depth)
    }

    /// Он же без ухода в тело: тело отдаётся вызывающему.
    ///
    /// Нужно дроблению: там тело идёт хвостом куска, а не значением.
    fn bookkept<'e>(&mut self, expr: &'e Expr, depth: usize) -> &'e Expr {
        let pad = Self::pad(depth);
        match expr {
            Expr::Bind {
                binding,
                value,
                body,
            } => {
                let value = self.value(value, depth);
                let _ = writeln!(
                    self.out,
                    "{pad}{} v{} = {value}; /* {} */",
                    c_type(binding.fact.repr),
                    binding.local.0,
                    escaped(&binding.name)
                );
                body.as_ref()
            }
            Expr::Dup { local, body } => {
                let _ = writeln!(self.out, "{pad}adamas_dup(v{});", local.0);
                body.as_ref()
            }
            Expr::Drop {
                local,
                salvage,
                body,
            } => {
                if salvage.collapses() {
                    self.salvaged(*local, salvage, None, depth);
                } else {
                    self.dropped(*local, depth);
                }
                body.as_ref()
            }
            Expr::Reclaim {
                local,
                token,
                salvage,
                body,
            } => {
                if salvage.collapses() {
                    self.salvaged(*local, salvage, Some(*token), depth);
                } else {
                    let _ = writeln!(
                        self.out,
                        "{pad}adamas_value v{} = adamas_reclaim_value(v{});",
                        token.0, local.0
                    );
                }
                body.as_ref()
            }
            // Придержанный блок, которому постояльца не нашлось (§10 вопрос
            // 173). `adamas_free`, а не `adamas_drop_value`: счётчик он уже
            // отдал, а поля release обошёл на месте придержания. `NULL` -
            // разделённое разобранное, и отдавать нечего.
            Expr::Discard { token, body } => {
                let _ = writeln!(self.out, "{pad}adamas_free(v{});", token.0);
                body.as_ref()
            }
            other => other,
        }
    }

    /// Дроп разобранного, схлопнутый с `dup` его полей (§5.1, [`Salvage`]).
    ///
    /// Две ветви, и различает их уникальность в рантайме - та же, на которой
    /// стоит reuse (`adamas_is_unique`, §10 вопрос 149).
    ///
    /// **Уникальный.** Взятые поля переходят ветви даром: `dup` и обход release
    /// вернули бы им ровно те ссылки, которые ветвь взяла. Невзятые дропаются
    /// здесь же - блок освобождается без release, а тот их дропнул бы. Форма
    /// освобождения зависит от того, придерживается ли блок: у дропа он идёт
    /// куче, у [`Expr::Reclaim`] достаётся `token`.
    ///
    /// **Разделённый.** Всё как прежде: ссылка на каждое взятое поле, потом
    /// счётчик родителя вниз. Придержать блок разделённого нечем - `NULL`.
    ///
    /// Общий `adamas_drop_value` здесь годится, а не свой у резумпции
    /// ([`Emitter::dropped`]): разобранное - объект данных, резумпцию не
    /// разбирает никакой конструктор.
    fn salvaged(
        &mut self,
        local: LocalId,
        salvage: &Salvage,
        token: Option<LocalId>,
        depth: usize,
    ) {
        let pad = Self::pad(depth);
        if let Some(token) = token {
            let _ = writeln!(self.out, "{pad}adamas_value v{};", token.0);
        }
        let _ = writeln!(self.out, "{pad}if (adamas_is_unique(v{})) {{", local.0);
        for field in &salvage.spare {
            let _ = writeln!(self.out, "{pad}    adamas_drop_value(v{});", field.0);
        }
        match token {
            Some(token) => {
                let _ = writeln!(self.out, "{pad}    v{} = v{};", token.0, local.0);
            }
            None => {
                let _ = writeln!(self.out, "{pad}    adamas_free(v{});", local.0);
            }
        }
        let _ = writeln!(self.out, "{pad}}} else {{");
        for field in &salvage.taken {
            let _ = writeln!(self.out, "{pad}    adamas_dup(v{});", field.0);
        }
        let _ = writeln!(self.out, "{pad}    adamas_drop_value(v{});", local.0);
        if let Some(token) = token {
            let _ = writeln!(self.out, "{pad}    v{} = NULL;", token.0);
        }
        let _ = writeln!(self.out, "{pad}}}");
    }

    /// Дескриптор укладки значением (§4.11): два слова на кадре.
    fn descriptor(&mut self, size: u32, align: u32, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_layout {name}; {name}.size = {size}u; {name}.align = {align}u;"
        );
        name
    }

    /// Число из дескриптора: размер либо выравнивание.
    fn descriptor_field(&mut self, descriptor: LocalId, align: bool, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let field = if align { "align" } else { "size" };
        let _ = writeln!(
            self.out,
            "{pad}uint32_t {name} = v{}.{field};",
            descriptor.0
        );
        name
    }

    /// Конструктор значением: замыкание, копящее аргументы.
    fn building(&mut self, constructor: CtorId, depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = &self.program.constructors[usize::from(constructor.0)];
        let arity = described.binders.len();
        let title = escaped(&described.name);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_closure(make_{}, \
             adamas_release_value, {arity}u, 0u); /* {title} */",
            constructor.0
        );
        name
    }

    /// Применение значения к одному аргументу **в первой форме**.
    ///
    /// Вектор идёт `NULL`: за указателем могла бы оказаться и вторая форма, но
    /// производить она не вправе - применить её из чистой окружающей значило бы
    /// погасить непустую row пустой (§3.4), а этого элаборация не пропускает.
    ///
    /// Ручка стека **своя**, и это не симметрия: за границей замыкания стоит
    /// динамика, и вызываемый вправе оказаться дроблёным - лямбда с ресурсом
    /// либо с собственным хендлером. Такой кладёт кадры и отдаёт значение
    /// вершине, а не себе, поэтому его ответ доводит трамплин. Ячейки кучи
    /// корень не стоит вовсе: пустой стек - два слова на кадре, и пустой цикл.
    fn applying(&mut self, callee: &Expr, argument: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        // Замыкание **заимствуется** (`adamas.h`), отдаёт его отдельный `Drop`
        // после применения; аргумент идёт владением.
        let callee = self.value(callee, depth);
        let argument = self.value(argument, depth);
        let name = self.temp();
        if self.hidden {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value {name} = adamas_apply({callee}, {FORWARD}, {argument});"
            );
            return name;
        }
        let root = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_kont {root};");
        let _ = writeln!(self.out, "{pad}adamas_kont_init(&{root});");
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_apply({callee}, NULL, &{root}, {argument});"
        );
        let _ = writeln!(self.out, "{pad}{name} = adamas_kont_run(&{root}, {name});");
        name
    }

    /// Плоский агрегат: поля кладутся по своим смещениям (§4.11).
    ///
    /// `memcpy`, а не приведение указателя: поле стоит по своей границе внутри
    /// байтового массива, и читать его как `float *` значило бы обещать
    /// компилятору выравнивание, которого правило §4.11 не даёт.
    fn pack(&mut self, packing: PackId, variant: u32, fields: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = self.program.packings[packing.0 as usize].clone();
        let given: Vec<String> = fields
            .iter()
            .map(|field| self.value(field, depth))
            .collect();
        let name = self.temp();
        // Теговая укладка зануляется: короткий вариант оставил бы хвост
        // payload'а неинициализированным, а байты агрегата копируются целиком.
        let seed = if described.tag == 0 { "" } else { " = {0}" };
        let _ = writeln!(
            self.out,
            "{pad}{} {name}{seed};",
            c_type(Repr::Packed(packing))
        );
        if described.tag > 0 {
            let _ = writeln!(
                self.out,
                "{pad}{{ uint{}_t adamas_variant = {variant}u; \
                 memcpy({name}.bytes, &adamas_variant, {}u); }}",
                described.tag * 8,
                described.tag
            );
        }
        for (slot, value) in described.variants[variant as usize]
            .slots
            .iter()
            .zip(&given)
        {
            let _ = writeln!(
                self.out,
                "{pad}memcpy({name}.bytes + {}, &{value}, {}u);",
                slot.offset,
                slot.ty.width(&self.program.packings)
            );
        }
        name
    }

    /// Поле плоского агрегата: чтение по смещению.
    fn unpack(
        &mut self,
        packing: PackId,
        variant: u32,
        field: u32,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let slot = self.program.packings[packing.0 as usize].variants[variant as usize].slots
            [field as usize];
        let value = self.value(value, depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}{} {name};", c_type(slot.ty.repr()));
        let _ = writeln!(
            self.out,
            "{pad}memcpy(&{name}, {value}.bytes + {}, {}u);",
            slot.offset,
            slot.ty.width(&self.program.packings)
        );
        name
    }

    /// Литерал: биты, а не написанное число.
    ///
    /// Так он доезжает побитово, и ни `INT64_MIN` без суффикса, ни двойное
    /// округление `Float32` его не портят.
    fn literal(&mut self, ty: PrimTy, bits: u64, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}{} {name} = adamas_bits_{}({bits:#x}ULL);",
            c_type(Repr::Flat(ty)),
            ty.name()
        );
        name
    }

    /// Примитивная операция над двумя плоскими значениями.
    fn arithmetic(
        &mut self,
        op: PrimOp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let left = self.value(left, depth);
        let right = self.value(right, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}{} {name} = adamas_{}_{}({left}, {right});",
            c_type(Repr::Flat(ty)),
            operation(op),
            ty.name()
        );
        name
    }

    /// Разбор трёх узлов массива (§4.11) по своим печатям.
    ///
    /// Отдельной ступенькой по тому же доводу, что у [`Self::vector`]: у
    /// [`Self::emitted`] длина на пределе, и разбирать эти три врозь от
    /// остальных незачем - они разбираются только вместе.
    fn array(&mut self, expr: &Expr, depth: usize) -> String {
        match expr {
            Expr::ArrayNew {
                stride,
                count,
                initial,
            } => self.array_new(*stride, count, initial, depth),
            Expr::ArraySet {
                stride,
                array,
                at,
                value,
            } => self.array_set(*stride, array, at, value, depth),
            Expr::ArrayIndex {
                stride,
                owned,
                array,
                at,
            } => self.array_index(*stride, *owned, array, at, depth),
            other => self.emitted(other, depth),
        }
    }

    /// Разбор шести узлов вектора (§4.9) по своим печатям.
    ///
    /// Отдельной ступенькой, а не шестью ветвями в [`Self::emitted`]: у той
    /// длина уже на пределе, и пятая форма представления не повод её ломать.
    fn vector(&mut self, expr: &Expr, depth: usize) -> String {
        match expr {
            Expr::SimdSplat { lanes, lane, value } => self.simd_splat(*lanes, *lane, value, depth),
            Expr::SimdSet {
                lanes,
                lane,
                vector,
                at,
                value,
            } => self.simd_set(*lanes, *lane, vector, at, value, depth),
            Expr::SimdLane {
                lanes,
                lane,
                vector,
                at,
            } => self.simd_lane(*lanes, *lane, vector, at, depth),
            Expr::SimdArith {
                op,
                lanes,
                lane,
                left,
                right,
            } => self.simd_arith(*op, *lanes, *lane, left, right, depth),
            Expr::SimdLoad {
                lanes,
                lane,
                owned,
                array,
                at,
                ..
            } => self.simd_load(*lanes, *lane, *owned, array, at, depth),
            Expr::SimdStore {
                lanes,
                lane,
                array,
                at,
                value,
                ..
            } => self.simd_store(*lanes, *lane, array, at, value, depth),
            other => self.emitted(other, depth),
        }
    }

    /// Окно колонки вектором (§4.9): `lanes` ячеек подряд одной загрузкой.
    ///
    /// Пара к [`Self::array_index`], и решения те же: адрес берёт рантайм,
    /// байты читает **сама программа**, владение снимает Perceus (§10 вопрос
    /// 171). Отличий два, и оба названы. Адрес даёт `adamas_array_window`, а
    /// не `adamas_array_at`: проверять надо хвост окна, и `at` этого не
    /// делает. Приведение идёт к **невыровненному** близнецу
    /// ([`vector_loose_type`]) - ячейка стоит по шагу колонки, и выровненный
    /// тип разрешил бы `movaps`.
    fn simd_load(
        &mut self,
        lanes: u32,
        lane: PrimTy,
        owned: bool,
        array: &Expr,
        at: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let at = self.value(at, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}{} {name} = *(const {} *)adamas_array_window({array}, (size_t){at}, {lanes}u);",
            vector_type(lanes, lane),
            vector_loose_type(lanes, lane)
        );
        if owned {
            let _ = writeln!(self.out, "{pad}adamas_drop({array}, adamas_release_value);");
        }
        name
    }

    /// Запись окна колонки (§4.9): пара к [`Self::array_set`].
    ///
    /// Уникальность спрашивается **после** того, как посчитаны все аргументы,
    /// тем же `adamas_array_writable` и по той же причине: чтение из той же
    /// колонки успевает отдать свою ссылку, и `simdStore xs i (simdLoad xs i)`
    /// переписывает, а не копирует. Разъехаться с LLVM-эмиттером тут нельзя -
    /// счётчик выданных блоков у двух бэкендов сверяется числом.
    fn simd_store(
        &mut self,
        lanes: u32,
        lane: PrimTy,
        array: &Expr,
        at: &Expr,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let at = self.value(at, depth);
        let value = self.value(value, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_array_writable({array}, adamas_release_value);"
        );
        let _ = writeln!(
            self.out,
            "{pad}*({} *)adamas_array_window({name}, (size_t){at}, {lanes}u) = {value};",
            vector_loose_type(lanes, lane)
        );
        name
    }

    /// Вектор, все дорожки которого заняты одним значением (§4.9).
    ///
    /// Списковая инициализация, а не цикл: в ней gcc видит splat и кладёт
    /// одну инструкцию широковещания, тогда как цикл пришлось бы ещё
    /// векторизовать. Имя значения уже временное, поэтому повторение его
    /// `lanes` раз вычисления не повторяет.
    fn simd_splat(&mut self, lanes: u32, lane: PrimTy, value: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let value = self.value(value, depth);
        let name = self.temp();
        let filled = vec![value; lanes as usize].join(", ");
        let _ = writeln!(
            self.out,
            "{pad}{} {name} = ({}){{ {filled} }};",
            vector_type(lanes, lane),
            vector_type(lanes, lane)
        );
        name
    }

    /// Тот же вектор с переписанной дорожкой (§4.9).
    ///
    /// Копия плюс присваивание по индексу: вектор здесь значение, а не объект,
    /// и `simdSet` функционален - прежний остаётся прежним. Копия эта живёт в
    /// регистре и оптимизатором снимается, когда прежнее значение больше не
    /// читается.
    fn simd_set(
        &mut self,
        lanes: u32,
        lane: PrimTy,
        vector: &Expr,
        at: &Expr,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let vector = self.value(vector, depth);
        let at = self.value(at, depth);
        let value = self.value(value, depth);
        let name = self.temp();
        let ty = vector_type(lanes, lane);
        let _ = writeln!(self.out, "{pad}{ty} {name} = {vector};");
        // Номер вне ширины - обрыв, а не тихая запись мимо. Текст берётся у
        // представления: LLVM-сторона печатает тот же, и второй записи не
        // заводится (§4.9, `ir::LANE_OUTSIDE`).
        let _ = writeln!(
            self.out,
            "{pad}if ({at} >= {lanes}u) {{ adamas_fail(\"{}\"); }}",
            crate::ir::LANE_OUTSIDE
        );
        let _ = writeln!(self.out, "{pad}{name}[{at}] = {value};");
        name
    }

    /// Значение дорожки (§4.9).
    fn simd_lane(
        &mut self,
        lanes: u32,
        lane: PrimTy,
        vector: &Expr,
        at: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let vector = self.value(vector, depth);
        let at = self.value(at, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}if ({at} >= {lanes}u) {{ adamas_fail(\"{}\"); }}",
            crate::ir::LANE_OUTSIDE
        );
        let _ = writeln!(
            self.out,
            "{pad}{} {name} = {vector}[{at}];",
            scalar(Repr::Flat(lane))
        );
        name
    }

    /// Подорожечная арифметика (§4.9).
    ///
    /// Оператор прямо на векторе - это и есть расширение: `a + b` над
    /// `vector_size` есть одна инструкция, а не цикл. Целое считается в
    /// беззнаковом спутнике и приводится обратно, ровно как скаляр в
    /// `ADAMAS_FLAT_INTEGER`: §4.3 требует заворачивания, а не UB. Плавающее
    /// идёт как есть, без единого ключа быстрой математики - тот же строгий
    /// режим, что у скаляра (трек F).
    fn simd_arith(
        &mut self,
        op: PrimOp,
        lanes: u32,
        lane: PrimTy,
        left: &Expr,
        right: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let left = self.value(left, depth);
        let right = self.value(right, depth);
        let name = self.temp();
        let ty = vector_type(lanes, lane);
        let sign = match op {
            PrimOp::Add => '+',
            PrimOp::Sub => '-',
            PrimOp::Mul => '*',
            PrimOp::Div
            | PrimOp::Rem
            | PrimOp::And
            | PrimOp::Or
            | PrimOp::Xor
            | PrimOp::Shl
            | PrimOp::Shr => {
                self.lanewise_refused(op);
                '+'
            }
        };
        if lane.floating() {
            let _ = writeln!(self.out, "{pad}{ty} {name} = {left} {sign} {right};");
        } else {
            let word = vector_word_type(lanes, lane);
            let _ = writeln!(
                self.out,
                "{pad}{ty} {name} = ({ty})(({word}){left} {sign} ({word}){right});"
            );
        }
        name
    }

    /// Сравнение: плоские аргументы, ответ - конструктор `Bool` (§4.3).
    ///
    /// Порядок считает `flat.c` - ключом по ширине типа, тем же, каким его
    /// считает свёртка ядра. Знаковость и `totalOrder` плавающих поэтому не
    /// записаны здесь вторично: разъехаться двум записям было бы нечем
    /// помешать, а сходятся они прогоном (`tests/agreement.rs`).
    ///
    /// Ячейки кучи не возникает: `True` и `False` полей не имеют, и рантайм
    /// кладёт их непосредственным значением.
    fn comparison(
        &mut self,
        op: PrimCmp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
        verdict: (CtorId, CtorId),
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let left = self.value(left, depth);
        let right = self.value(right, depth);
        let (yes, no) = verdict;
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_{}_{}({left}, {right}) ? adamas_con0({}u) : adamas_con0({}u);",
            comparison(op),
            ty.name(),
            yes.0,
            no.0
        );
        name
    }

    /// Шаг индексации выражением C.
    ///
    /// Константа - у мономорфизованного кода, поле дескриптора - у обобщённого
    /// (§4.11). Разница видна ровно здесь и больше нигде: остальной массив у
    /// обоих один.
    fn step(&self, stride: Stride) -> String {
        match stride {
            Stride::Static(ty) => format!("{}u", ty.size()),
            // Размер агрегата посчитан по §4.11 понижением, и здесь он
            // константа наравне с шириной примитива.
            Stride::Packed(pack) => format!("{}u", self.program.packings[pack.0 as usize].size),
            Stride::Dynamic(local) => format!("(size_t)v{}.size", local.0),
        }
    }

    /// Новый массив: одна аллокация на всю длину (§4.11).
    ///
    /// Заполняет его рантайм: ссылок на начальное значение нужно `count`, а
    /// длина - величина рантайма, и вставке RC её не видно.
    fn array_new(
        &mut self,
        stride: Option<Stride>,
        count: &Expr,
        initial: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let count = self.value(count, depth);
        let initial = self.value(initial, depth);
        let name = self.temp();
        let step = stride.map_or_else(|| "0u".to_owned(), |it| self.step(it));
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_array_alloc((size_t){count}, {step});"
        );
        match stride {
            // Известный тип лежит в переменной, неизвестный - уже буфером.
            Some(Stride::Static(_)) => {
                let _ = writeln!(self.out, "{pad}adamas_array_fill_flat({name}, &{initial});");
            }
            // Агрегат - структура на кадре, и байты его начинаются с `bytes`.
            Some(Stride::Packed(_)) => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_fill_flat({name}, {initial}.bytes);"
                );
            }
            Some(Stride::Dynamic(_)) => {
                let _ = writeln!(self.out, "{pad}adamas_array_fill_flat({name}, {initial});");
            }
            None => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_fill({name}, {initial}, adamas_release_value);"
                );
            }
        }
        name
    }

    /// Запись ячейки: массив сперва делается пригодным к записи.
    ///
    /// `adamas_array_writable` отдаёт тот же блок, когда он уникален (`rc ==
    /// 0`), и копию иначе - это и есть переписывание по месту из §4.11.
    /// Уникальность спрашивается **после** того, как посчитаны все аргументы:
    /// чтение из того же массива успевает отдать свою ссылку, и `arraySet xs i
    /// (arrayIndex xs j)` переписывает, а не копирует.
    fn array_set(
        &mut self,
        stride: Option<Stride>,
        array: &Expr,
        at: &Expr,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let at = self.value(at, depth);
        let value = self.value(value, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_array_writable({array}, adamas_release_value);"
        );
        match stride {
            Some(stride) => self.store(
                &format!("adamas_array_at({name}, (size_t){at})"),
                stride,
                &value,
                depth,
            ),
            None => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_put({name}, (size_t){at}, {value}, adamas_release_value);"
                );
            }
        }
        name
    }

    /// Кладёт плоское значение по адресу ячейки.
    ///
    /// Известный тип пишется своим C-типом, неизвестный - `memcpy` шагом:
    /// байты есть, имени у них нет.
    fn store(&mut self, cell: &str, stride: Stride, value: &str, depth: usize) {
        let pad = Self::pad(depth);
        match stride {
            Stride::Static(ty) => {
                let _ = writeln!(
                    self.out,
                    "{pad}*({} *)({cell}) = {value};",
                    c_type(Repr::Flat(ty))
                );
            }
            // Агрегат кладётся байтами: приведение к его C-типу обещало бы
            // выравнивание ячейки, а ячейка стоит по шагу массива.
            Stride::Packed(_) => {
                let step = self.step(stride);
                let _ = writeln!(self.out, "{pad}memcpy({cell}, {value}.bytes, {step});");
            }
            Stride::Dynamic(_) => {
                let step = self.step(stride);
                let _ = writeln!(self.out, "{pad}memcpy({cell}, {value}, {step});");
            }
        }
    }

    /// Чтение ячейки. Массив приходит владением и отдаётся рантайму здесь же -
    /// либо **заимствуется** (§10 вопрос 171): наружу уходят биты без
    /// заголовка, владелец потребит массив позже, и счётчик не трогается
    /// вовсе. Заимствованное плоское чтение - прямой типизированный load,
    /// симметричный записи (`Emitter::array_set` пишет тем же приведением);
    /// проверку границы делает `adamas_array_at`, как и у записи.
    ///
    /// Плоский элемент неизвестного типа копируется в буфер **на кадре**:
    /// указателем внутрь массива он бы пережил его дроп. Буфер - массив
    /// переменной длины, потому что длина известна только в рантайме.
    fn array_index(
        &mut self,
        stride: Option<Stride>,
        owned: bool,
        array: &Expr,
        at: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let at = self.value(at, depth);
        let name = self.temp();
        match stride {
            Some(Stride::Static(ty)) if !owned => {
                let _ = writeln!(
                    self.out,
                    "{pad}{c} {name} = *(const {c} *)adamas_array_at({array}, (size_t){at});",
                    c = c_type(Repr::Flat(ty))
                );
            }
            Some(Stride::Static(ty)) => {
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Flat(ty)));
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_read({array}, (size_t){at}, &{name}, \
                     adamas_release_value);"
                );
            }
            Some(Stride::Packed(pack)) if !owned => {
                let step = self.step(Stride::Packed(pack));
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Packed(pack)));
                let _ = writeln!(
                    self.out,
                    "{pad}memcpy({name}.bytes, adamas_array_at({array}, (size_t){at}), {step});"
                );
            }
            Some(Stride::Packed(pack)) => {
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Packed(pack)));
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_read({array}, (size_t){at}, {name}.bytes, \
                     adamas_release_value);"
                );
            }
            Some(stride @ Stride::Dynamic(_)) if !owned => {
                let step = self.step(stride);
                let buffer = self.temp();
                let _ = writeln!(self.out, "{pad}char {buffer}[{step}];");
                let _ = writeln!(
                    self.out,
                    "{pad}memcpy({buffer}, adamas_array_at({array}, (size_t){at}), {step});"
                );
                let _ = writeln!(self.out, "{pad}char *{name} = {buffer};");
            }
            Some(stride @ Stride::Dynamic(_)) => {
                let step = self.step(stride);
                let buffer = self.temp();
                let _ = writeln!(self.out, "{pad}char {buffer}[{step}];");
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_read({array}, (size_t){at}, {buffer}, \
                     adamas_release_value);"
                );
                let _ = writeln!(self.out, "{pad}char *{name} = {buffer};");
            }
            None => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_array_take({array}, (size_t){at}, \
                     adamas_release_value);"
                );
            }
        }
        name
    }

    /// Граница нагрузки - вторая половина шага (§4.11).
    ///
    /// У примитива она равна ширине, у агрегата взята из его укладки, у
    /// обобщённого кода приходит полем дескриптора - тем же, откуда приходит
    /// размер. Отдельно от [`Self::step`] она нужна потому, что курсор региона
    /// поднимается **до** границы, а потом уже на размер: сложи их в одно
    /// число - и `Vec3` встал бы по 12 байт вместо 4.
    fn bound(&self, stride: Stride) -> String {
        match stride {
            Stride::Static(ty) => format!("{}u", ty.size()),
            Stride::Packed(pack) => format!("{}u", self.program.packings[pack.0 as usize].align),
            Stride::Dynamic(local) => format!("(size_t)v{}.align", local.0),
        }
    }

    /// Операция над регионом (§3.6): семь форм одним разбором.
    ///
    /// Отдельным разбором, а не ветвями общего, потому что форм у региона
    /// столько же, сколько у всего остального вместе.
    fn region(&mut self, expr: &Expr, depth: usize) -> String {
        match expr {
            Expr::RegionNew => self.region_new("adamas_region_new", depth),
            // Разделяемая область расходится с обычной **только здесь**:
            // дальше её ведут те же шесть операций, и различает их рантайм по
            // тегу (§3.6, `SharedAllocStrategy when AllocStrategy`).
            Expr::SharedNew => self.region_new("adamas_shared_new", depth),
            Expr::RegionAlloc {
                stride,
                region,
                value,
            } => self.region_alloc(*stride, region, value, depth),
            Expr::RegionLast { region } => self.region_last(region, depth),
            Expr::RegionRead { stride, region, at } => self.region_read(*stride, region, at, depth),
            Expr::RegionWrite {
                stride,
                region,
                at,
                value,
            } => self.region_write(*stride, region, at, value, depth),
            Expr::RegionRecycle { region, at } => {
                self.region_return("adamas_region_recycle", region, at, depth)
            }
            Expr::RegionPop { region, at } => {
                self.region_return("adamas_region_pop", region, at, depth)
            }
            other => unreachable!("не операция региона: {other:?}"),
        }
    }

    /// Пустая область: один блок кучи (§3.6). `call` различает обычную и
    /// разделяемую - и это единственное место, где они различаются.
    fn region_new(&mut self, call: &str, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name} = {call}();");
        name
    }

    /// Аллокация в регионе: курсор поднимается, байты ложатся внутрь области.
    ///
    /// Ячейки кучи под значение не выдаётся вовсе - в этом и состоит цена,
    /// ради которой §3.6 написан. Блок сперва делается пригодным к записи, как
    /// массив: уникальность спрашивается у рантайма (`rc == 0`), а не у
    /// кратности (§10 вопрос 149).
    fn region_alloc(
        &mut self,
        stride: Stride,
        region: &Expr,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let region = self.value(region, depth);
        let value = self.value(value, depth);
        let (size, align) = (self.step(stride), self.bound(stride));
        let bits = Self::bytes(stride, &value);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_region_alloc({region}, {bits}, {size}, {align});"
        );
        name
    }

    /// Хендл последней аллокации. Блок приходит владением и отдаётся здесь же.
    fn region_last(&mut self, region: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let region = self.value(region, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint64_t {name} = (uint64_t)adamas_region_last({region}, \
             adamas_release_value);"
        );
        name
    }

    /// Чтение по хендлу. Байты копируются на кадр: указателем внутрь области
    /// значение пережило бы её дроп - тот же довод, что у ячейки массива.
    fn region_read(&mut self, stride: Stride, region: &Expr, at: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let region = self.value(region, depth);
        let at = self.value(at, depth);
        let size = self.step(stride);
        let name = self.temp();
        let into = match stride {
            Stride::Static(ty) => {
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Flat(ty)));
                format!("&{name}")
            }
            Stride::Packed(pack) => {
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Packed(pack)));
                format!("{name}.bytes")
            }
            Stride::Dynamic(_) => {
                let buffer = self.temp();
                let _ = writeln!(self.out, "{pad}char {buffer}[{size}];");
                let _ = writeln!(self.out, "{pad}char *{name} = {buffer};");
                name.clone()
            }
        };
        let _ = writeln!(
            self.out,
            "{pad}adamas_region_read({region}, (size_t){at}, {into}, {size}, \
             adamas_release_value);"
        );
        name
    }

    /// Запись по хендлу: курсор не двигается, место уже размещено (§3.6).
    fn region_write(
        &mut self,
        stride: Stride,
        region: &Expr,
        at: &Expr,
        value: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let region = self.value(region, depth);
        let at = self.value(at, depth);
        let value = self.value(value, depth);
        let size = self.step(stride);
        let bits = Self::bytes(stride, &value);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_region_write({region}, (size_t){at}, {bits}, \
             {size});"
        );
        name
    }

    /// Возврат ячейки по хендлу: `regionRecycle` либо `regionPop` (§3.6).
    ///
    /// Обе идут одним текстом, потому что различает их только имя функции
    /// рантайма: нагрузки у возврата нет, размер ячейки помнит область.
    fn region_return(&mut self, call: &str, region: &Expr, at: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let region = self.value(region, depth);
        let at = self.value(at, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = {call}({region}, (size_t){at});"
        );
        name
    }

    /// Адрес байтов плоского значения: у известного типа - его переменная, у
    /// агрегата - поле `bytes`, у неизвестного - уже буфер.
    fn bytes(stride: Stride, value: &str) -> String {
        match stride {
            Stride::Static(_) => format!("&{value}"),
            Stride::Packed(_) => format!("{value}.bytes"),
            Stride::Dynamic(_) => value.to_owned(),
        }
    }

    /// Слоты объекта: плоское кладётся битами по значению, ссылка - владением.
    fn fill(&mut self, object: &str, described: &Constructor, given: &[String], depth: usize) {
        let pad = Self::pad(depth);
        for (slot, (argument, repr)) in given.iter().zip(described.slot_reprs()).enumerate() {
            match repr.primitive() {
                Some(ty) => {
                    let _ = writeln!(
                        self.out,
                        "{pad}adamas_slot_write({object}, {slot}, adamas_word_{}({argument}));",
                        ty.name()
                    );
                }
                None => {
                    let _ = writeln!(
                        self.out,
                        "{pad}adamas_set_field({object}, {slot}, {argument});"
                    );
                }
            }
        }
    }

    /// Объект конструктора: сперва аргументы, потом блок.
    ///
    /// Придержанная ячейка (§5.1) занимает место `adamas_alloc`: `adamas_reuse`
    /// её переписывает, а на пустой ячейке аллоцирует сам - разделённое значение
    /// переписывать нечем, и решается это в рантайме.
    fn construct(
        &mut self,
        constructor: CtorId,
        reuse: Option<LocalId>,
        arguments: &[Expr],
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let described = &self.program.constructors[usize::from(constructor.0)];
        let slots = described.slots();
        let title = escaped(&described.name);
        let present: Vec<usize> = described
            .binders
            .iter()
            .enumerate()
            .filter(|(_, fact)| fact.present)
            .map(|(position, _)| position)
            .collect();
        let given: Vec<String> = present
            .iter()
            .filter_map(|position| arguments.get(*position))
            .map(|argument| self.value(argument, depth))
            .collect();
        let name = self.temp();
        if slots == 0 {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value {name} = adamas_con0({}u); /* {title} */",
                constructor.0
            );
            return name;
        }
        match reuse {
            Some(token) => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_reuse(v{}, {}u, {slots}u); /* {title} */",
                    token.0, constructor.0
                );
            }
            None => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_alloc({}u, {slots}u); /* {title} */",
                    constructor.0
                );
            }
        }
        let described = self.program.constructors[usize::from(constructor.0)].clone();
        self.fill(&name, &described, &given, depth);
        name
    }

    /// Аргументы прямого вызова: скрытые формы, затем живые связывания.
    ///
    /// Вызываемый известен статически, поэтому известна и его форма: первая
    /// зовётся голым написанным (`adamas_lowered_first`), второй передаются
    /// свои вектор и ручка. Взять их первая форма не может ниоткуда, и такой
    /// пары [`emit`] не пропускает вовсе ([`EmitError::Hidden`]). Стёртые
    /// позиции в вызов не идут.
    ///
    /// Отдельно от печати, потому что печатей две: вызов значением
    /// ([`Self::call`]) и вызов под `return` ([`Self::returning`]). Порядок
    /// вычисления аргументов при этом один, и он виден в тексте.
    fn arguments(&mut self, function: FuncId, arguments: &[Expr], depth: usize) -> Vec<String> {
        let called = &self.program.functions[function.0];
        let form = called.form;
        let present: Vec<usize> = called
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let mut given: Vec<String> = match form {
            Form::Stack => Vec::new(),
            Form::Detached => vec![FORWARD.to_owned()],
        };
        for position in &present {
            let Some(argument) = arguments.get(*position) else {
                continue;
            };
            given.push(self.value(argument, depth));
        }
        given
    }

    /// Прямой вызов значением: ответ ложится во временное.
    ///
    /// Хвостовой самовызов печатается не здесь, а [`Self::returning`]: под
    /// временным приставке `musttail` стоять негде.
    fn call(&mut self, function: FuncId, arguments: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let title = escaped(&self.program.functions[function.0].name);
        let given = self.arguments(function, arguments, depth);
        let result = c_type(self.program.functions[function.0].result);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}{result} {name} = fn_{}({}); /* {title} */",
            function.0,
            given.join(", ")
        );
        name
    }

    /// Вызов чужой функции (§5.3, уровень 1).
    ///
    /// Символ зовётся именем из [`prototypes`], за которым стоит ассемблерная
    /// метка с настоящим именем: у линкера он под ним и лежит. Прототип
    /// напечатан шапкой единицы, поэтому здесь - ровно применение, и ничего
    /// между: ни распаковки, ни упаковки, ни касания счётчика. Это и есть та
    /// «нулевая» сторона §6, за которую отвечает поверхность: слово едет
    /// словом.
    /// Буфер, одолженный чужой стороне (§5.3): адрес нагрузки словом.
    ///
    /// Словом, а не `void *`, и это то же решение, каким живёт `CPtr`: через
    /// границу уровня 1 едет машинное слово, прототип чужого символа печатается
    /// `uint64_t`, и сойтись с написанием системного заголовка он не может по
    /// построению (за это отвечает `__asm__`-метка, см. [`prototypes`]). Два
    /// приведения подряд - `uintptr_t` и потом `uint64_t` - пишутся затем, что
    /// прямое приведение указателя к целому иной ширины есть предупреждение, а
    /// `uintptr_t` его ширину и означает.
    ///
    /// Счётчика не трогает: узел заимствует, а массив отдаёт вставка RC после
    /// чужого вызова (`perceus::applied_to`).
    fn lending(&mut self, array: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint64_t {name} = (uint64_t)(uintptr_t)adamas_array_data({array});"
        );
        name
    }

    /// Адрес своей функции, видимой C (§5.3): колбэк уровня 1.
    ///
    /// Приведений два подряд по тому же доводу, что у [`Emitter::lending`]:
    /// прямое приведение указателя к целому иной ширины есть предупреждение, а
    /// `uintptr_t` ширину указателя и означает. Берётся адрес **обёртки**, а не
    /// `fn_N`: у внутренней функции своё соглашение, и чужая сторона зовёт
    /// именно обёртку.
    fn exported(&mut self, id: ExportId, depth: usize) -> String {
        let pad = Self::pad(depth);
        let symbol = outward(&self.program.exports[id.0].symbol);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint64_t {name} = (uint64_t)(uintptr_t)&{symbol}; /* export \"C\" */"
        );
        name
    }

    /// Адрес трамплина колбэка уровня 2 (§5.3).
    ///
    /// Тем же ходом, что [`Emitter::exported`], и различие названо там же:
    /// адрес называет не обёртку определения, а трамплин, чья среда приезжает
    /// вторым словом.
    fn trampolined(&mut self, id: CallbackId, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint64_t {name} = (uint64_t)(uintptr_t)&{}; /* колбэк уровня 2 */",
            trampoline_symbol(id)
        );
        name
    }

    /// Адрес среды колбэка словом: то, что ляжет в `userdata` (§5.3).
    ///
    /// Сам объект остаётся связыванием, и дропает его вставка RC **после**
    /// чужого вызова - та же пара, что у одолженного буфера.
    fn carried(&mut self, local: LocalId, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint64_t {name} = (uint64_t)(uintptr_t)v{}; /* userdata */",
            local.0
        );
        name
    }

    /// Среда колбэка уровня 2: замыкание и вектор evidence в одном объекте.
    ///
    /// Вектор берётся **у кадра**, а не приходит выражением: в порождённом коде
    /// он зовётся `ev` и живёт скрытым аргументом второй формы. У первой формы
    /// его нет вовсе, и там ставится пустой - ровно тем же ходом, каким его
    /// заводит площадка хендлера в чистом отрезке ([`Emitter::rooted`]).
    ///
    /// Ссылка своя: в слоте объекта вектор живёт наравне с прочими детьми, и
    /// дропает его `adamas_release_value` - `ADAMAS_TAG_EVIDENCE` идёт там
    /// чужим тегом, то есть блок отдаётся рантайму целиком.
    fn userdata(&mut self, constructor: CtorId, closure: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let taken = self.value(closure, depth);
        let name = self.temp();
        let vector = if self.hidden {
            "adamas_evidence_dup((adamas_evidence *)ev)".to_owned()
        } else {
            "adamas_evidence_empty()".to_owned()
        };
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_alloc({}u, 2u); /* userdata колбэка */",
            constructor.0
        );
        let _ = writeln!(self.out, "{pad}adamas_set_field({name}, 0, {taken});");
        let _ = writeln!(
            self.out,
            "{pad}adamas_set_field({name}, 1, (adamas_value){vector});"
        );
        name
    }

    fn foreign(&mut self, function: ForeignId, arguments: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = self.program.foreigns[function.0].clone();
        let given: Vec<String> = arguments
            .iter()
            .map(|argument| self.value(argument, depth))
            .collect();
        let symbol = local(&described.symbol);
        let name = self.temp();
        match described.result {
            ForeignResult::Flat(ty) => {
                let result = scalar(Repr::Flat(ty));
                let _ = writeln!(
                    self.out,
                    "{pad}{result} {name} = {symbol}({}); /* extern \"C\" */",
                    given.join(", ")
                );
            }
            // `void`-символ значения не отдаёт, а выражению оно нужно: узел
            // отвечает единицей, собранной тут же. Ячейки кучи она не стоит -
            // нульарный конструктор рантайм кладёт непосредственным значением.
            ForeignResult::Unit(unit) => {
                let _ = writeln!(
                    self.out,
                    "{pad}{symbol}({}); /* extern \"C\" */",
                    given.join(", ")
                );
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_con0({}u);",
                    unit.0
                );
            }
        }
        name
    }

    /// Замыкание: код плюс среда по слотам.
    fn closure(&mut self, function: FuncId, captured: &[Expr], depth: usize) -> String {
        self.holding(function, captured, "box", depth)
    }

    /// Она же с названным трамплином: общим (`box`) либо забирающим (`take`).
    fn holding(&mut self, function: FuncId, captured: &[Expr], code: &str, depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = &self.program.functions[function.0];
        let title = escaped(&described.name);
        // Арность замыкания - **все** связывания ядра, стёртые в том числе:
        // применение к значению позиционно и типа вызываемого не знает.
        let arity = described.parameters.len();
        let present: Vec<usize> = described
            .captured
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let taken: Vec<String> = present
            .iter()
            .filter_map(|position| captured.get(*position))
            .map(|capture| self.value(capture, depth))
            .collect();
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_closure({code}_{}, adamas_release_value, \
             {arity}u, {}u); /* {title} */",
            function.0,
            taken.len()
        );
        for (slot, capture) in taken.iter().enumerate() {
            let _ = writeln!(
                self.out,
                "{pad}adamas_closure_set({name}, {slot}, {capture});"
            );
        }
        name
    }

    /// Хендлер в **первой** форме: корень стека, кадр, трамплин до дна.
    ///
    /// Ставить кадр нужно и той функции, чья собственная row пуста: `runIO`
    /// гасит `IO` внутри себя и наружу его не отдаёт. Скрытых аргументов у неё
    /// нет, и брать их неоткуда - значит она **корень**: заводит свой стек и
    /// пустой вектор. Это законно ровно потому, что row её пуста: операции
    /// наружу не уходит ни одной (§3.4, погашение расширением справа), и всё,
    /// что под ней производится, гасится внутри неё же. «Стек один» (§10
    /// вопрос 144) этим не нарушается - он один на всё, что друг друга видит.
    ///
    /// Вычисление под хендлером к этому месту - **вызов своей функции**
    /// ([`crate::split`]): дроблёный код есть цепочка C-функций, а вложенных
    /// функций в C нет. Ответ его идёт вершине стека, и до конца доводит
    /// трамплин: он же снимет кадр `HANDLER` и отдаст значение ветке `return`.
    fn handling(
        &mut self,
        handler: HandlerId,
        captured: &[Expr],
        computation: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let inner = Self::pad(depth + 1);
        let taken = self.environment(handler, captured, depth);
        let described = &self.program.handlers[handler.0 as usize];
        let label = described.label;
        let title = escaped(&self.program.labels[label.0 as usize].name);

        let name = self.temp();
        let root = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name}; /* handle {title} */");
        let _ = writeln!(self.out, "{pad}{{");
        self.rooted(&root, depth + 1);
        let (frame, vector) = self.installed(handler, &taken, depth + 1);
        let seed = self.temp();
        let _ = writeln!(self.out, "{inner}adamas_value {seed};");
        let _ = writeln!(self.out, "{inner}{{");
        let _ = writeln!(self.out, "{inner}    const adamas_evidence *ev = {vector};");
        let answer = self.value(computation, depth + 2);
        let _ = writeln!(self.out, "{inner}    {seed} = {answer};");
        let _ = writeln!(self.out, "{inner}}}");
        let _ = writeln!(self.out, "{inner}adamas_evidence_drop({vector});");
        let _ = writeln!(
            self.out,
            "{inner}{name} = adamas_kont_run(kont, {seed}); /* {frame} снимет трамплин */"
        );
        let _ = writeln!(self.out, "{inner}adamas_evidence_drop({root}_ev);");
        let _ = writeln!(self.out, "{pad}}}");
        name
    }

    /// Маска в чистом отрезке: вектор без записи, вычисление под ним.
    ///
    /// Кадра здесь нет и быть не может - маска ничего не откладывает, - поэтому
    /// ветка короче хендлерной ровно на кадр. Своя ссылка на вектор живёт до
    /// конца вычисления: кадры, которые вычисление положит, берут свою.
    fn masking(&mut self, label: LabelId, computation: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let inner = Self::pad(depth + 1);
        let title = escaped(&self.program.labels[label.0 as usize].name);
        let vector = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_evidence *{vector} = adamas_evidence_mask(ev, {}u); /* mask {title} */",
            label.0
        );
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name};");
        let _ = writeln!(self.out, "{pad}{{");
        let _ = writeln!(self.out, "{inner}const adamas_evidence *ev = {vector};");
        let answer = self.value(computation, depth + 1);
        let _ = writeln!(self.out, "{inner}{name} = {answer};");
        let _ = writeln!(self.out, "{pad}}}");
        let _ = writeln!(self.out, "{pad}adamas_evidence_drop({vector});");
        name
    }

    /// Кадр `HANDLER` со средой веток и расширенный вектор под вычисление.
    ///
    /// Общее у обеих форм: у первой кадр стоит на своём корне, у второй - на
    /// ручке, пришедшей аргументом, а сама постановка одна и та же.
    fn installed(
        &mut self,
        handler: HandlerId,
        taken: &[String],
        depth: usize,
    ) -> (String, String) {
        let pad = Self::pad(depth);
        let described = &self.program.handlers[handler.0 as usize];
        let label = described.label;
        let slots = taken.len();
        let frame = self.temp();
        let vector = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_frame *{frame} = adamas_kont_handler(kont, {}u, handler_{}, {}, {slots}u, ev);",
            label.0,
            handler.0,
            if slots == 0 {
                "NULL".to_owned()
            } else {
                format!("release_{}", handler.0)
            }
        );
        if slots > 0 {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value *{frame}_env = adamas_frame_env({frame});"
            );
            for (slot, capture) in taken.iter().enumerate() {
                let _ = writeln!(self.out, "{pad}{frame}_env[{slot}] = {capture};");
            }
        }
        let _ = writeln!(
            self.out,
            "{pad}adamas_evidence *{vector} = adamas_evidence_extend(ev, {}u, {frame});",
            label.0
        );
        (frame, vector)
    }

    /// Среда веток по слотам кадра: живые захваты в порядке объявления.
    fn environment(&mut self, handler: HandlerId, captured: &[Expr], depth: usize) -> Vec<String> {
        let present: Vec<usize> = self.program.handlers[handler.0 as usize]
            .captured
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        present
            .iter()
            .filter_map(|position| captured.get(*position))
            .map(|capture| self.value(capture, depth))
            .collect()
    }

    /// Корень стека у первой формы: свой `kont` и пустой вектор.
    ///
    /// Законно это ровно потому, что row такой функции пуста: операции наружу
    /// не уходит ни одной (§3.4, погашение расширением справа), и всё, что под
    /// ней производится, гасится внутри неё же.
    fn rooted(&mut self, root: &str, depth: usize) {
        let pad = Self::pad(depth);
        let _ = writeln!(self.out, "{pad}adamas_kont {root};");
        let _ = writeln!(self.out, "{pad}adamas_kont_init(&{root});");
        let _ = writeln!(self.out, "{pad}adamas_kont *kont = &{root};");
        let _ = writeln!(
            self.out,
            "{pad}adamas_evidence *{root}_ev = adamas_evidence_empty();"
        );
        let _ = writeln!(self.out, "{pad}const adamas_evidence *ev = {root}_ev;");
    }

    /// Шапка ветви: `case` с именем конструктора и связывания полей.
    ///
    /// Одна на три печати разбора - значением ([`Self::analysis`]), хвостом
    /// куска ([`Self::branching`]) и возвратом ([`Self::returning_analysis`]).
    /// Отдельной она стоит не ради краткости: поле читается **битами** либо
    /// ссылкой по представлению, и третья копия этого различия разъехалась бы
    /// молча, а стоило бы это чтения числа указателем.
    ///
    /// Ветви - альтернативы: счёт одной другой не виден. Поля владения не
    /// заводят - ссылку на нужное берёт `Dup`, поставленный `perceus::arm`, а
    /// ненужное поле не читается вовсе.
    fn arm_head(&mut self, arm: &Arm, scrutinee: &str, depth: usize) {
        let pad = Self::pad(depth);
        let described = &self.program.constructors[usize::from(arm.constructor.0)];
        let title = escaped(&described.name);
        let params = described.params as usize;
        let slots: Vec<Option<u32>> = (0..arm.fields.len())
            .map(|position| described.slot(params + position))
            .collect();
        let _ = writeln!(
            self.out,
            "{pad}case {}u: {{ /* {title} */",
            arm.constructor.0
        );
        for (binding, slot) in arm.fields.iter().zip(&slots) {
            let Some(slot) = slot else { continue };
            // Плоское поле читается битами слота: заголовка у него нет, и
            // указателем оно не бывает (§4.11).
            let taken = match binding.fact.repr.primitive() {
                Some(ty) => format!(
                    "adamas_bits_{}(adamas_slot_bits({scrutinee}, {slot}))",
                    ty.name()
                ),
                None => format!("adamas_field({scrutinee}, {slot})"),
            };
            let _ = writeln!(
                self.out,
                "{pad}    {} v{} = {taken}; /* {} */",
                c_type(binding.fact.repr),
                binding.local.0,
                escaped(&binding.name)
            );
        }
    }

    /// Разбор: `switch` по тегу заголовка.
    fn analysis(&mut self, scrutinee: &Expr, arms: &[Arm], depth: usize) -> String {
        let pad = Self::pad(depth);
        let answer = arms
            .first()
            .map_or(Repr::Boxed, |arm| self.shape(&arm.body));
        if let Repr::Packed(pack) = self.shape(scrutinee) {
            return self.packed_analysis(pack, scrutinee, arms, answer, depth);
        }
        // Разбираемое **заимствуется**: поля читаются по нему, а отдаёт его
        // ветвь - `Drop` либо `Reclaim` внутри неё (см. `perceus::arm`).
        let scrutinee = self.value(scrutinee, depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}{} {name};", c_type(answer));
        let _ = writeln!(self.out, "{pad}switch (adamas_tag({scrutinee})) {{");
        for arm in arms {
            self.arm_head(arm, &scrutinee, depth);
            let answer = self.value(&arm.body, depth + 1);
            let _ = writeln!(self.out, "{pad}    {name} = {answer};");
            let _ = writeln!(self.out, "{pad}    break;");
            let _ = writeln!(self.out, "{pad}}}");
        }
        // Счёт после разбора - счёт любой из ветвей: каждая обязана потребить
        // одно и то же (`perceus::arm`), поэтому берётся последняя.
        let _ = writeln!(
            self.out,
            "{pad}default: adamas_fail(\"разбор не знает конструктора\");"
        );
        let _ = writeln!(self.out, "{pad}}}");
        name
    }

    /// Разбор плотного семейства: тег читается байтами, поля - смещением
    /// своего варианта (§4.11, §10 вопрос 157).
    ///
    /// У бестегового - единственный конструктор - ветвь одна, и ни тега, ни
    /// `switch` не нужно.
    fn packed_analysis(
        &mut self,
        pack: PackId,
        scrutinee: &Expr,
        arms: &[Arm],
        answer: Repr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let packing = self.program.packings[pack.0 as usize].clone();
        let scrutinee = self.value(scrutinee, depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}{} {name};", c_type(answer));
        if packing.tag == 0 {
            if let Some(arm) = arms.first() {
                self.packed_arm(&packing, 0, &scrutinee, arm, &name, depth);
            }
            return name;
        }
        let tag = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}uint{}_t {tag} = 0; memcpy(&{tag}, {scrutinee}.bytes, {}u);",
            packing.tag * 8,
            packing.tag
        );
        let _ = writeln!(self.out, "{pad}switch ({tag}) {{");
        for arm in arms {
            let Some((at, _)) = packing.variant_of(arm.constructor) else {
                continue;
            };
            let described = &self.program.constructors[usize::from(arm.constructor.0)];
            let _ = writeln!(
                self.out,
                "{pad}case {at}u: {{ /* {} */",
                escaped(&described.name)
            );
            self.packed_arm(&packing, at, &scrutinee, arm, &name, depth + 1);
            let _ = writeln!(self.out, "{pad}    break;");
            let _ = writeln!(self.out, "{pad}}}");
        }
        let _ = writeln!(
            self.out,
            "{pad}default: adamas_fail(\"разбор не знает тега\");"
        );
        let _ = writeln!(self.out, "{pad}}}");
        name
    }

    /// Ветвь плотного разбора: связывания живых полей и тело.
    ///
    /// Стёртое поле связывания не получает - ссылок на него в теле нет по
    /// построению понижения, - поэтому живые идут по слотам подряд.
    fn packed_arm(
        &mut self,
        packing: &Packing,
        variant: u32,
        scrutinee: &str,
        arm: &Arm,
        name: &str,
        depth: usize,
    ) {
        let pad = Self::pad(depth);
        let slots = &packing.variants[variant as usize].slots;
        let mut slot = 0usize;
        for binding in &arm.fields {
            if !binding.fact.present {
                continue;
            }
            let described = slots[slot];
            slot += 1;
            let _ = writeln!(
                self.out,
                "{pad}{} v{}; memcpy(&v{}, {scrutinee}.bytes + {}, {}u); /* {} */",
                c_type(binding.fact.repr),
                binding.local.0,
                binding.local.0,
                described.offset,
                described.ty.width(&self.program.packings),
                escaped(&binding.name)
            );
        }
        let answer = self.value(&arm.body, depth);
        let _ = writeln!(self.out, "{pad}{name} = {answer};");
    }

    /* ---------------------------------------------------------------- */
    /* Дроблёное тело: куски и точки приостановки                        */
    /* ---------------------------------------------------------------- */

    /// Дроп связывания: у резумпции он свой.
    ///
    /// Отдать резумпцию значит **раскрутить** её приостановленный сегмент, а
    /// раскрутке нужна ручка стека (`adamas.h`). Общий `adamas_drop_value`
    /// ручки не носит и до этого пути доходит только из слота замыкания, где
    /// её взять неоткуда.
    fn dropped(&mut self, local: LocalId, depth: usize) {
        let pad = Self::pad(depth);
        if self.reprs.get(&local) == Some(&Repr::Resumption) {
            let _ = writeln!(self.out, "{pad}adamas_resumption_drop(kont, v{});", local.0);
            return;
        }
        let _ = writeln!(self.out, "{pad}adamas_drop_value(v{});", local.0);
    }

    /// Точка ли приостановки: кадр ставится ровно на неё (решение 3 волны 4).
    fn stops(&self, expr: &Expr) -> bool {
        crate::split::halts(expr, self.suspending)
    }

    /// Продолжение `λbinding. body` кадром, а его код - отдельным куском.
    ///
    /// # Что уезжает в среду кадра
    ///
    /// То, что продолжение называет и не вводит само. Владение переходит кадру,
    /// и код куска забирает слоты **обратно**, зануляя их: кадр освобождается
    /// сразу после кода (`adamas.h`), и `dup` с последующим дропом стоил бы
    /// пары счётчику на каждый живой слот. Дроп кадра тогда отдаёт единицы,
    /// то есть ничего, - а на брошенном кадре отдаёт настоящее.
    ///
    /// # Плоское значение в слоте
    ///
    /// Слот кадра - слово, и плоское значение лежит в нём **битами**, ровно как
    /// в слоте объекта (§4.11, `flat.c`). Счётчика у него нет, поэтому дроп
    /// среды его не трогает: какие слоты указательные, кусок знает по типам.
    fn reified(&mut self, binding: &Binding, body: &Expr, depth: usize) {
        let pad = Self::pad(depth);
        let mut called = BTreeSet::new();
        crate::split::mentioned(body, &mut called);
        let mut inner = BTreeSet::new();
        crate::split::introduces(body, &mut inner);
        inner.insert(binding.local);
        let mut env: Vec<(LocalId, Repr)> = called
            .into_iter()
            .filter(|local| !inner.contains(local))
            .filter_map(|local| self.reprs.get(&local).map(|repr| (local, *repr)))
            .collect();
        // Счётные слоты идут первыми, и это соглашение с рантаймом
        // (`adamas_kont_push`): копия сегмента дупает ровно их, а плоский слот
        // лежит битами - заголовка у него нет, и `adamas_dup` по нему написал
        // бы счётчик по чужому адресу. Сортировка устойчивая, поэтому порядок
        // внутри каждой половины прежний.
        env.sort_by_key(|(_, repr)| !repr.counted());
        let counted = env.iter().filter(|(_, repr)| repr.counted()).count();
        let at = self.chunks.len();
        self.chunks.push(String::new());
        let code = format!("fn_{}_k{at}", self.id.0);
        let release = if counted > 0 {
            format!("release_{}_k{at}", self.id.0)
        } else {
            "NULL".to_owned()
        };
        self.forward.push(format!("{};", chunk_signature(&code)));
        if counted > 0 {
            self.forward
                .push(format!("{};", frame_release_signature(&release)));
        }

        let frame = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_frame *{frame} = adamas_kont_push(kont, ADAMAS_MARK_PLAIN, 0u, {code}, \
             {release}, {}u, {counted}u, ev); /* продолжение */",
            env.len()
        );
        if !env.is_empty() {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value *{frame}_env = adamas_frame_env({frame});"
            );
        }
        for (slot, (local, repr)) in env.iter().enumerate() {
            if !worded(*repr) {
                self.parked(*repr);
            }
            let stored = into_word(*repr, &format!("v{}", local.0));
            let _ = writeln!(self.out, "{pad}{frame}_env[{slot}] = {stored};");
        }

        let held = std::mem::take(&mut self.out);
        // Свой вектор кусок не держит: его отдаёт тот кусок, что его завёл, а
        // сюда он приходит от кадра - заимствованным.
        let epilogue = std::mem::take(&mut self.epilogue);
        self.chunk(&code, &env, binding, body);
        if counted > 0 {
            self.chunk_release(&release, &env);
        }
        self.chunks[at] = std::mem::replace(&mut self.out, held);
        self.epilogue = epilogue;
    }

    /// Код куска: слоты забираются, пришедшее становится связыванием.
    fn chunk(&mut self, code: &str, env: &[(LocalId, Repr)], binding: &Binding, body: &Expr) {
        let _ = writeln!(self.out, "/* продолжение точки приостановки */");
        let _ = writeln!(self.out, "{} {{", chunk_signature(code));
        let _ = writeln!(
            self.out,
            "    const adamas_evidence *ev = adamas_frame_evidence(h);"
        );
        if !env.is_empty() {
            let _ = writeln!(self.out, "    adamas_value *env = adamas_frame_env(h);");
        }
        for (slot, (local, repr)) in env.iter().enumerate() {
            let taken = from_word(*repr, &format!("env[{slot}]"));
            // Указательный слот **забирается**: значение уезжает в связывание
            // владением, и дроп среды его больше не увидит. Плоский лежит
            // битами, счётчика у него нет, и забирать нечего.
            let cleared = if repr.primitive().is_some() {
                String::new()
            } else {
                format!(" env[{slot}] = ADAMAS_ERASED;")
            };
            let _ = writeln!(
                self.out,
                "    {} v{} = {taken};{cleared}",
                c_type(*repr),
                local.0
            );
        }
        assert!(
            binding.fact.present,
            "стёртое связывание на точке приостановки: значение у неё есть по построению"
        );
        // Пришедшее приходит словом: `adamas_frame_code` другого не носит.
        // Плоское значение поэтому едет битами - той же мерой, какой оно
        // переживает точку приостановки в слоте среды (§10 вопрос 164).
        if !worded(binding.fact.repr) {
            self.parked(binding.fact.repr);
        }
        let _ = writeln!(
            self.out,
            "    {} v{} = {}; /* {} */",
            c_type(binding.fact.repr),
            binding.local.0,
            from_word(binding.fact.repr, "incoming"),
            escaped(&binding.name)
        );
        self.tail(body, 1);
        let _ = writeln!(self.out, "}}\n");
    }

    /// Дроп среды куска: то, чего он не забрал, потому что не побежал.
    fn chunk_release(&mut self, release: &str, env: &[(LocalId, Repr)]) {
        let _ = writeln!(self.out, "/* среда продолжения */");
        let _ = writeln!(self.out, "{} {{", frame_release_signature(release));
        let _ = writeln!(self.out, "    adamas_value *env = adamas_frame_env(h);");
        for (slot, (_, repr)) in env.iter().enumerate() {
            if *repr == Repr::Resumption {
                // Забранный слот занят непосредственным значением, а резумпцией
                // оно не бывает: ручка сегмента - объект кучи. Сравнение
                // поэтому и есть «слот ещё не забрали».
                let _ = writeln!(
                    self.out,
                    "    if (!adamas_is_imm(env[{slot}])) {{ adamas_resumption_drop(kont, env[{slot}]); }}"
                );
            } else if repr.counted() {
                let _ = writeln!(self.out, "    adamas_drop_value(env[{slot}]);");
            }
        }
        let _ = writeln!(self.out, "    (void)kont;");
        let _ = writeln!(self.out, "}}\n");
    }

    /// Операция, подорожечной формы не имеющая (§4.9).
    fn lanewise_refused(&mut self, op: PrimOp) {
        if self.failure.is_none() {
            self.failure = Some(EmitError::Lanewise {
                function: self.program.functions[self.id.0].name.clone(),
                op,
            });
        }
    }

    /// Связывание, пережившее точку приостановки, но не влезающее в слот кадра.
    fn parked(&mut self, repr: Repr) {
        if self.failure.is_none() {
            self.failure = Some(EmitError::Parked {
                function: self.program.functions[self.id.0].name.clone(),
                shape: c_type(repr),
            });
        }
    }

    /// Возврат из куска: ответ уходит вершине стека, а трамплин отдаёт его
    /// следующему кадру.
    ///
    /// Эпилог печатается **после** вычисления ответа: в нём стоят дропы
    /// расширенных векторов, а ответ бывает вызовом, которому вектор и
    /// передаётся.
    ///
    /// Порядок этот **свидетеля не имеет**, и назван таковым: мутант,
    /// печатающий эпилог до ответа, выжил и под санитайзером тоже. Причина
    /// структурная - вызов и применение к моменту эпилога уже посчитаны
    /// [`Emitter::value`] во временное имя, а выражением сюда приходят только
    /// `adamas_frame_perform` и `adamas_kont_abort`, и расширенного вектора не
    /// читает ни тот, ни другой: ветка берёт вектор **своего** кадра.
    /// Различающая программа появится вместе с выражением, которому вектор
    /// передаётся, - её сегодня не строит ни один узел.
    ///
    /// `repr` - представление ответа. Оно тут значимо, потому что тип у границы
    /// один: плоский ответ уходит трамплину словом (§10 вопрос 164), а не
    /// собой, - иначе порождённый C не собрался бы.
    fn finish(&mut self, answer: &str, repr: Repr, depth: usize) {
        let pad = Self::pad(depth);
        if !worded(repr) {
            self.parked(repr);
        }
        let answer = into_word(repr, answer);
        if self.epilogue.is_empty() {
            let _ = writeln!(self.out, "{pad}return {answer};");
            return;
        }
        let held = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {held} = {answer};");
        for vector in self.epilogue.clone().iter().rev() {
            let _ = writeln!(self.out, "{pad}adamas_evidence_drop({vector});");
        }
        let _ = writeln!(self.out, "{pad}return {held};");
    }

    /// Берёт ли названный вызов приставку `musttail` (§6).
    ///
    /// Условия два, и оба измерены, а не выведены. Ответ обязан уходить
    /// регистром ([`returnable`]) - иначе gcc роняет **сборку**. Прототип
    /// вызываемого обязан совпасть с прототипом вызывающего дословно
    /// ([`prototype`]) - иначе сборку роняет clang.
    ///
    /// Самовызов оба условия выполняет по построению, и до трека D волны 5
    /// правило им и ограничивалось. Расширено оно потому, что ограничение
    /// стоило сигнала 11 на валидной программе: взаимная рекурсия двух
    /// `UInt64 -> UInt64 -> UInt64` роняла процесс на 43 487 витках при 2 MiB,
    /// хотя прототип у пары дословно один. Замер, которым прежнее правило
    /// обосновывалось, мерил **несовпадающие** прототипы (2 параметра против
    /// 16) и к этой паре отношения не имел.
    fn jumpable(&self, function: FuncId) -> bool {
        let called = &self.program.functions[function.0];
        returnable(called.result) && prototype(called) == self.proto
    }

    /// Есть ли в хвосте тела вызов, берущий приставку (§6).
    ///
    /// Спрашивается до печати и решает её форму: тело с таким вызовом печатает
    /// [`Self::returning`] - возврат на каждом пути, - а прочие печатаются как
    /// печатались, одним возвратом в конце. Разделение не украшение: приставка
    /// `musttail` требует, чтобы вызов стоял **под самим** `return`, а обычная
    /// печать кладёт его во временное. Ставить возврат в ветви всем подряд
    /// значило бы двинуть порождённый C у всего корпуса ради функций, которым
    /// это не нужно.
    ///
    /// Обход и печать спускаются в одно и то же и обязаны такими остаться.
    /// Найди обход вызов там, куда печать не пойдёт, приставки не появилось бы;
    /// найди печать вызов там, куда не ходил обход, форма сменилась бы у тела, о
    /// котором ничего не утверждается. Плотный разбор не берётся ни тем, ни
    /// другим ([`Self::packed_analysis`] печатает своё).
    fn tail_jumping(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Bind { body, .. }
            | Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. }
            | Expr::Discard { body, .. } => self.tail_jumping(body),
            Expr::Match {
                scrutinee, arms, ..
            } => {
                !matches!(self.shape(scrutinee), Repr::Packed(_))
                    && arms.iter().any(|arm| self.tail_jumping(&arm.body))
            }
            Expr::Call { function, .. } => self.jumpable(*function),
            _ => false,
        }
    }

    /// Тело чистого отрезка с возвратом на каждом пути (§6).
    ///
    /// Форма, в которой хвостовой вызов печатается приставкой. Всё, что
    /// хвостом не является, уходит в обычную печать значения и возвращается
    /// следом: различие между этими двумя путями и есть всё, что делает вызов
    /// гарантированным.
    fn returning(&mut self, expr: &Expr, depth: usize) {
        let pad = Self::pad(depth);
        match expr {
            Expr::Bind { .. }
            | Expr::Dup { .. }
            | Expr::Drop { .. }
            | Expr::Reclaim { .. }
            | Expr::Discard { .. } => {
                let body = self.bookkept(expr, depth);
                self.returning(body, depth);
            }
            Expr::Match {
                scrutinee, arms, ..
            } if !matches!(self.shape(scrutinee), Repr::Packed(_)) => {
                self.returning_analysis(scrutinee, arms, depth);
            }
            Expr::Call {
                function,
                arguments,
            } if self.jumpable(*function) => {
                let given = self.arguments(*function, arguments, depth);
                let title = escaped(&self.program.functions[function.0].name);
                let _ = writeln!(
                    self.out,
                    "{pad}ADAMAS_MUSTTAIL return fn_{}({}); /* {title} */",
                    function.0,
                    given.join(", ")
                );
            }
            other => {
                let answer = self.value(other, depth);
                let _ = writeln!(self.out, "{pad}return {answer};");
            }
        }
    }

    /// Разбор в возвратной позиции: возврат раздаётся ветвям.
    ///
    /// Временного под ответ здесь нет вовсе, и `break` тоже: каждая ветвь
    /// кончается своим `return`. Отказ стоит **после** `switch`, а не веткой
    /// `default`, по той же причине, что у [`Self::branching`], - выпасть из
    /// него можно только не совпав ни с одним тегом.
    fn returning_analysis(&mut self, scrutinee: &Expr, arms: &[Arm], depth: usize) {
        let pad = Self::pad(depth);
        let scrutinee = self.value(scrutinee, depth);
        let _ = writeln!(self.out, "{pad}switch (adamas_tag({scrutinee})) {{");
        for arm in arms {
            self.arm_head(arm, &scrutinee, depth);
            self.returning(&arm.body, depth + 1);
            let _ = writeln!(self.out, "{pad}}}");
        }
        let _ = writeln!(self.out, "{pad}}}");
        let _ = writeln!(
            self.out,
            "{pad}adamas_fail(\"разбор не знает конструктора\");"
        );
    }

    /// Хвост куска: код, кончающийся ровно одним возвратом на каждом пути.
    fn tail(&mut self, expr: &Expr, depth: usize) {
        match expr {
            Expr::Bind {
                binding,
                value,
                body,
            } if self.stops(value) => {
                self.reified(binding, body, depth);
                self.tail(value, depth);
            }
            Expr::Bind { .. }
            | Expr::Dup { .. }
            | Expr::Drop { .. }
            | Expr::Reclaim { .. }
            | Expr::Discard { .. } => {
                let body = self.bookkept(expr, depth);
                self.tail(body, depth);
            }
            Expr::Match {
                scrutinee, arms, ..
            } if self.stops(expr) => self.branching(scrutinee, arms, depth),
            Expr::Handle {
                handler,
                captured,
                computation,
            } => self.handling_tail(*handler, captured, computation, depth),
            Expr::Closing {
                closer,
                captured,
                body,
            } => self.scoped_tail(*closer, captured, body, depth),
            Expr::Mask { label, computation } => self.masking_tail(*label, computation, depth),
            Expr::Nursery { body } => {
                let body = self.value(body, depth);
                let call = format!(
                    "adamas_nursery_begin(kont, ev, {body}, adamas_release_value, \
                     adamas_promote_value)"
                );
                self.finish(&call, Repr::Boxed, depth);
            }
            Expr::Cancel { at, value } => {
                let value = self.value(value, depth);
                let call = format!("adamas_nursery_cancel(kont, {value}, {at}u)");
                self.finish(&call, Repr::Boxed, depth);
            }
            Expr::Fiber {
                op,
                label,
                operation,
                arguments,
            } => self.fibering(*op, *label, *operation, arguments, depth),
            Expr::Perform {
                label,
                operation,
                arguments,
            } => self.performing_tail(*label, *operation, arguments, depth),
            Expr::Resume { resumption, value } => {
                let pad = Self::pad(depth);
                let resumption = self.value(resumption, depth);
                let value = self.value(value, depth);
                // Звенья встают **над** уже положенным кадром продолжения:
                // ответ возобновлённого вычисления дойдёт до него трамплином.
                let _ = writeln!(self.out, "{pad}adamas_kont_resume(kont, {resumption});");
                let _ = writeln!(self.out, "{pad}adamas_resumption_drop(kont, {resumption});");
                // Аргумент резумпции указателен по договору понижения, и
                // возобновлённое вычисление ждёт от границы ровно его.
                self.finish(&value, Repr::Boxed, depth);
            }
            other => {
                let repr = self.shape(other);
                let answer = self.value(other, depth);
                self.finish(&answer, repr, depth);
            }
        }
    }

    /// Разбор, у которого ветвь приостанавливается: каждая - свой хвост.
    ///
    /// Продолжение здесь уже лежит кадром - его поставило связывание, чьим
    /// значением стоит разбор, - поэтому ветвь просто возвращает своё.
    fn branching(&mut self, scrutinee: &Expr, arms: &[Arm], depth: usize) {
        let pad = Self::pad(depth);
        let scrutinee = self.value(scrutinee, depth);
        let _ = writeln!(self.out, "{pad}switch (adamas_tag({scrutinee})) {{");
        for arm in arms {
            self.arm_head(arm, &scrutinee, depth);
            self.tail(&arm.body, depth + 1);
            let _ = writeln!(self.out, "{pad}}}");
        }
        let _ = writeln!(self.out, "{pad}}}");
        let _ = writeln!(
            self.out,
            "{pad}adamas_fail(\"разбор не знает конструктора\");"
        );
    }

    /// Хендлер во **второй** форме: кадр под уже стоящим продолжением.
    ///
    /// Вычисление идёт хвостом того же куска и под своим вектором; ответ его
    /// доходит до кадра `HANDLER` трамплином, и ветку `return` зовёт он же.
    /// Своей ссылки на расширенный вектор кусок не переживает - её отдаёт
    /// эпилог, - а кадры, положенные вычислением, берут свою.
    fn handling_tail(
        &mut self,
        handler: HandlerId,
        captured: &[Expr],
        computation: &Expr,
        depth: usize,
    ) {
        let pad = Self::pad(depth);
        let taken = self.environment(handler, captured, depth);
        let (_, vector) = self.installed(handler, &taken, depth);
        let _ = writeln!(self.out, "{pad}{{");
        let _ = writeln!(self.out, "{pad}    const adamas_evidence *ev = {vector};");
        self.epilogue.push(vector);
        self.tail(computation, depth + 1);
        self.epilogue.pop();
        let _ = writeln!(self.out, "{pad}}}");
    }

    /// Маска, под которой вычисление приостанавливается.
    ///
    /// Вектор её переживает кусок не своей ссылкой, а ссылками кадров: каждый
    /// кадр, положенный вычислением, дупает вектор себе, и продолжение читает
    /// его у кадра (`adamas_frame_evidence`). Своя ссылка уходит эпилогом на
    /// возврате - тем же путём, что у расширенного вектора хендлера.
    fn masking_tail(&mut self, label: LabelId, computation: &Expr, depth: usize) {
        let pad = Self::pad(depth);
        let title = escaped(&self.program.labels[label.0 as usize].name);
        let vector = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_evidence *{vector} = adamas_evidence_mask(ev, {}u); /* mask {title} */",
            label.0
        );
        let _ = writeln!(self.out, "{pad}{{");
        let _ = writeln!(self.out, "{pad}    const adamas_evidence *ev = {vector};");
        self.epilogue.push(vector);
        self.tail(computation, depth + 1);
        self.epilogue.pop();
        let _ = writeln!(self.out, "{pad}}}");
    }

    /// Выход из scope с ресурсом во второй форме: кадр `MARK_CLOSING` (§3.3).
    ///
    /// Тело идёт хвостом, а деструктор зовёт трамплин, дойдя до кадра, - и
    /// нормальный выход, и раскрутка идут теперь одним путём. LIFO выходит
    /// вложенностью кадров: внутренний scope лежит выше, раскрутка идёт сверху.
    fn scoped_tail(&mut self, closer: FuncId, captured: &[Expr], body: &Expr, depth: usize) {
        let pad = Self::pad(depth);
        // Замыкание деструктора строится **забирающим** трамплином: кадр его
        // единственный владелец, зовут его раз, и слоты уходят в деструктор
        // владением. Общий трамплин отдал бы ресурс разделённым.
        let closer = self.holding(closer, captured, "take", depth);
        let frame = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_frame *{frame} = adamas_kont_closing(kont, ev, release_closing, {closer});"
        );
        let _ = writeln!(self.out, "{pad}(void){frame};");
        self.tail(body, depth);
    }

    /// Операция значением: ветка бежит на месте, ответ - значение операции.
    ///
    /// Позиция не хвостовая, и это не пропуск дробления, а тихая программа
    /// (вопрос 74): все ветки всех площадок хвостовые, и обрыв невозможен по
    /// построению - `SUPPRESSED` требует разрезанного сегмента, а резать его
    /// в тихой программе некому. Вердикта остаётся два: ветка на месте либо
    /// операция без хендлера. Подавление здесь поэтому - нарушение инварианта
    /// тишины, и отвечает ему немедленный `adamas_fail`, а не молчаливое
    /// вычисление с чужим значением.
    fn performing(
        &mut self,
        label: LabelId,
        operation: u32,
        arguments: &[Expr],
        depth: usize,
    ) -> String {
        assert!(
            self.suspending.quiet,
            "операция значением в нетихой программе: дробление её не вынесло"
        );
        let pad = Self::pad(depth);
        let described = &self.program.labels[label.0 as usize];
        let title = escaped(&described.name);
        let operation_name = described
            .operations
            .get(operation as usize)
            .map_or_else(|| format!("#{operation}"), |name| escaped(name));
        let given: Vec<String> = arguments
            .iter()
            .map(|argument| self.value(argument, depth))
            .collect();

        let frame = self.temp();
        let verdict = self.temp();
        let operands = self.temp();
        let count = given.len();
        let _ = writeln!(
            self.out,
            "{pad}adamas_frame *{frame} = NULL; /* {title}.{operation_name} */"
        );
        let _ = writeln!(
            self.out,
            "{pad}int {verdict} = adamas_evidence_lookup(ev, {}u, &{frame});",
            label.0
        );
        if count == 0 {
            let _ = writeln!(self.out, "{pad}adamas_value *{operands} = NULL;");
        } else {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value {operands}[{count}] = {{ {} }};",
                given.join(", ")
            );
        }
        let _ = writeln!(
            self.out,
            "{pad}if ({verdict} == ADAMAS_LOOKUP_SUPPRESSED) {{ \
             adamas_fail(\"подавленная операция в тихой программе: {title}.{operation_name}\"); }}"
        );
        let _ = writeln!(
            self.out,
            "{pad}if ({verdict} != ADAMAS_LOOKUP_HANDLER) {{ \
             adamas_fail(\"операция без хендлера: {title}.{operation_name}\"); }}"
        );
        let answer = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {answer} = adamas_frame_perform({frame}, kont, {operation}u, \
             {operands}, {count}u);"
        );
        answer
    }

    /// Операция: вердикт вектора трёхзначен, и все три ответа написаны.
    ///
    /// `HANDLER` - ветка зовётся на месте; чем она ответит, решает её вердикт
    /// (`adamas_handler_code`), а сюда ответ приходит одинаково - возвратом
    /// вершине стека. `SUPPRESSED` - хендлер ответ уже дал, деться второму
    /// некуда: `adamas_kont_abort` и немедленный возврат. `MISSING` - операция
    /// без хендлера.
    ///
    /// Сводить вердикт к двум нельзя: операция деструктора ушла бы к
    /// одноимённому хендлеру снаружи - ровно тот дефект, который ревью
    /// 2026-09-05 нашло у машины.
    fn performing_tail(
        &mut self,
        label: LabelId,
        operation: u32,
        arguments: &[Expr],
        depth: usize,
    ) {
        let (operands, count) = self.operands(arguments, depth);
        self.performed_tail(label, operation, &operands, count, depth);
    }

    /// Аргументы операции массивом: одно соглашение о вызове на оба пути.
    ///
    /// Массивом, а не именами по одному, потому что владельца у них в IR нет:
    /// это соглашение о вызове ветки, а не узел. Отсюда и дроп на путях, где
    /// ветка не побежит, идёт по слоту массива - тот же жанр, что у
    /// подавленного вердикта.
    fn operands(&mut self, arguments: &[Expr], depth: usize) -> (String, usize) {
        let pad = Self::pad(depth);
        let given: Vec<String> = arguments
            .iter()
            .map(|argument| self.value(argument, depth))
            .collect();
        let operands = self.temp();
        if given.is_empty() {
            let _ = writeln!(self.out, "{pad}adamas_value *{operands} = NULL;");
        } else {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value {operands}[{}] = {{ {} }};",
                given.len(),
                given.join(", ")
            );
        }
        (operands, given.len())
    }

    /// Питомник в **чистой** функции: корень своего стека, круг, трамплин до дна.
    ///
    /// Тот же приём, что у хендлера первой формы ([`Emitter::handling`]), и то
    /// же основание: row у `withNursery` пуста, значит наружу круга не уходит
    /// ни одной операции, и стек этот один на всё, что друг друга видит.
    ///
    /// Тело считается **внутри** корня: под ним уже есть и вектор, и ручка, а
    /// снаружи первой формы их нет вовсе.
    fn nursing(&mut self, body: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let inner = Self::pad(depth + 1);
        let name = self.temp();
        let root = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name}; /* withNursery */");
        let _ = writeln!(self.out, "{pad}{{");
        self.rooted(&root, depth + 1);
        let body = self.value(body, depth + 1);
        let seed = self.temp();
        let _ = writeln!(
            self.out,
            "{inner}adamas_value {seed} = \
             adamas_nursery_begin(kont, ev, {body}, adamas_release_value, adamas_promote_value);"
        );
        let _ = writeln!(self.out, "{inner}{name} = adamas_kont_run(kont, {seed});");
        let _ = writeln!(self.out, "{inner}adamas_evidence_drop({root}_ev);");
        let _ = writeln!(self.out, "{pad}}}");
        name
    }

    /// Операция питомника: круг берёт её, только если он ближе хендлера (§5.2).
    ///
    /// Оба пути стоят рядом, и это не дублирование, а само правило: решает
    /// между ними **рантайм**, потому что `eval/fibers.adamas` пишет те же
    /// имена без всякого питомника, а написанный `handle` над той же меткой
    /// значит написанное. Обычный путь идёт следом тем же кодом, что у всякой
    /// операции: аргументы посчитаны однажды и годятся обоим.
    ///
    /// Свой аргумент у порождения и ожидания - **последний**: row стоит на
    /// последней стрелке. Прочие (синтезированный триггер приостановленного
    /// вычисления) на этом пути дропаются здесь: ветки, которая дропнула бы их
    /// сама, у круга нет.
    fn fibering(
        &mut self,
        op: FiberOp,
        label: LabelId,
        operation: u32,
        arguments: &[Expr],
        depth: usize,
    ) {
        let pad = Self::pad(depth);
        let inner = Self::pad(depth + 1);
        let (operands, count) = self.operands(arguments, depth);
        let described = &self.program.labels[label.0 as usize];
        let title = escaped(&described.name);
        let operation_name = described
            .operations
            .get(operation as usize)
            .map_or_else(|| format!("#{operation}"), |name| escaped(name));
        let taken = match op {
            FiberOp::Suspend => None,
            _ => count.checked_sub(1),
        };
        let _ = writeln!(
            self.out,
            "{pad}if (adamas_nursery_serves(ev, {}u)) {{ /* питомник: {title}.{operation_name} */",
            label.0
        );
        for slot in 0..count {
            if taken == Some(slot) {
                continue;
            }
            let _ = writeln!(self.out, "{inner}adamas_drop_value({operands}[{slot}]);");
        }
        let own = taken.map_or_else(
            || "ADAMAS_ERASED".to_owned(),
            |slot| format!("{operands}[{slot}]"),
        );
        let call = match op {
            FiberOp::Suspend => Some("adamas_nursery_suspend(kont, ev)".to_owned()),
            FiberOp::Detached => Some(format!(
                "adamas_nursery_spawn(kont, ev, {own}, ADAMAS_NO_TASK, 0u, 0u)"
            )),
            FiberOp::Spawn(Some(task)) => Some(format!(
                "adamas_nursery_spawn(kont, ev, {own}, {}u, {}u, {}u)",
                task.constructor.0, task.slots, task.at
            )),
            FiberOp::Await(Some(at)) => {
                Some(format!("adamas_nursery_await(kont, ev, {own}, {at}u)"))
            }
            // Форма задачи не сошлась: у машины это тот же отказ на месте, а не
            // молча собранное не то (`Machine::handle_value`).
            FiberOp::Spawn(None) | FiberOp::Await(None) => None,
        };
        match call {
            Some(call) => self.finish(&call, Repr::Boxed, depth + 1),
            None => {
                let _ = writeln!(
                    self.out,
                    "{inner}adamas_fail(\"тип задачи не подошёл: нужен один конструктор с одним \
                     полем (§5.2)\");"
                );
            }
        }
        let _ = writeln!(self.out, "{pad}}}");
        self.performed_tail(label, operation, &operands, count, depth);
    }

    /// Обычный путь операции: вердикт вектора трёхзначен, аргументы посчитаны.
    fn performed_tail(
        &mut self,
        label: LabelId,
        operation: u32,
        operands: &str,
        count: usize,
        depth: usize,
    ) {
        let pad = Self::pad(depth);
        let inner = Self::pad(depth + 1);
        let described = &self.program.labels[label.0 as usize];
        let title = escaped(&described.name);
        let operation_name = described
            .operations
            .get(operation as usize)
            .map_or_else(|| format!("#{operation}"), |name| escaped(name));

        let frame = self.temp();
        let verdict = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_frame *{frame} = NULL; /* {title}.{operation_name} */"
        );
        let _ = writeln!(
            self.out,
            "{pad}int {verdict} = adamas_evidence_lookup(ev, {}u, &{frame});",
            label.0
        );
        let _ = writeln!(self.out, "{pad}if ({verdict} == ADAMAS_LOOKUP_HANDLER) {{");
        let call =
            format!("adamas_frame_perform({frame}, kont, {operation}u, {operands}, {count}u)");
        self.finish(&call, Repr::Boxed, depth + 1);
        let _ = writeln!(
            self.out,
            "{pad}}} else if ({verdict} == ADAMAS_LOOKUP_SUPPRESSED) {{"
        );
        for slot in 0..count {
            let _ = writeln!(self.out, "{inner}adamas_drop_value({operands}[{slot}]);");
        }
        // Кадры, ради которых код бы продолжался, снимает сам обрыв - и кадр
        // продолжения этой операции в их числе. Прибирать здесь поэтому нечего:
        // владение уехало в среду кадра, а её отдаёт его дроп.
        self.finish("adamas_kont_abort(kont)", Repr::Boxed, depth + 1);
        let _ = writeln!(self.out, "{pad}}}");
        let _ = writeln!(
            self.out,
            "{pad}adamas_fail(\"операция без хендлера: {title}.{operation_name}\");"
        );
    }
}

/// Имя операции в `flat.c`: то же, что пишет `adamas_add_Int64`.
///
/// Берётся у [`PrimOp::prefix`], а не пишется вторым списком: имя примитива в
/// программе и имя спутника в `flat.c` обязаны совпадать буква в букву, и
/// разъехаться двум спискам было бы нечем помешать.
fn operation(op: PrimOp) -> &'static str {
    op.prefix()
}

/// Имя сравнения в `flat.c`: то же, что пишет `adamas_lt_Int64`.
fn comparison(op: PrimCmp) -> &'static str {
    match op {
        PrimCmp::Eq => "eq",
        PrimCmp::Ne => "ne",
        PrimCmp::Lt => "lt",
        PrimCmp::Le => "le",
        PrimCmp::Gt => "gt",
        PrimCmp::Ge => "ge",
    }
}

/// Строка, годная внутрь C-литерала и комментария.
///
/// Имена в Adamas бывают операторами и путями (`+`, `Boxes.Wrap`), и печатает
/// их ответ программы. Небезопасны из них ровно три знака: кавычка и слэш
/// ломают литерал, `*/` закрывает комментарий раньше времени.
fn escaped(name: &str) -> String {
    name.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace("*/", "* /")
}

#[cfg(test)]
mod tests {
    use adamas_core::prim::{PrimCmp, PrimOp, PrimTy};

    use super::{FLAT, comparison, kind, operation};

    /// Сорта слотов и имена операций у эмиттера и у `flat.c` одни.
    ///
    /// Печать и дроп различают число от ссылки **числом**, и разъехаться эти
    /// два места могут молча: порождённый C соберётся, а слот прочитается не
    /// тем. Тот же жанр, что `both_printers_cut_at_the_same_depth`, - вторая
    /// запись числа названа и оплачена здесь.
    #[test]
    fn the_kinds_match_the_printer() {
        assert!(FLAT.contains("#define ADAMAS_FLAT_BOXED 0u"));
        for ty in PrimTy::ALL {
            let written = format!(
                "#define ADAMAS_FLAT_{} {}u",
                ty.name().to_uppercase(),
                kind(ty)
            );
            assert!(
                FLAT.contains(&written),
                "`flat.c` не объявляет `{written}`: сорт слота разъехался с эмиттером"
            );
            let instantiated = FLAT.lines().any(|line| {
                line.starts_with("ADAMAS_FLAT_") && line.contains(&format!("({}, ", ty.name()))
            });
            assert!(
                instantiated,
                "`flat.c` не разворачивает макрос для `{}`: порождённый вызов не соберётся",
                ty.name()
            );
        }
        // Имена, которые эмиттер пишет в вызов, склеиваются макросом из
        // приставки и имени типа: проверяется приставка.
        for op in PrimOp::ALL {
            let defined = format!("adamas_{}_##name", operation(op));
            assert!(
                FLAT.contains(&defined),
                "`flat.c` не определяет `{defined}`: имя операции разъехалось с эмиттером"
            );
        }
        // Сравнений шесть, и определены они **дважды** - целым макросом и
        // плавающим: пропуск в одном из двух собрал бы половину программ.
        for op in PrimCmp::ALL {
            let defined = format!("adamas_{}_##name", comparison(op));
            assert_eq!(
                FLAT.matches(&defined).count(),
                2,
                "`flat.c` определяет `{defined}` не в обоих макросах: \
                 сравнение соберётся не над всяким примитивом"
            );
        }
        for helper in ["adamas_bits_##name", "adamas_word_##name"] {
            assert!(FLAT.contains(helper), "`flat.c` не определяет `{helper}`");
        }
    }

    /// У каждого типа есть спутник каждой операции, которая у него бывает.
    ///
    /// Предыдущий тест проверяет, что имя определено **хоть где-то**, и до
    /// трека A волны 4 этого хватало: три операции стояли в одном макросе на
    /// все восемь целых. Теперь макросов четыре - общий целый, знаковый,
    /// беззнаковый и плавающий, - и «определено хоть где-то» перестало значить
    /// «соберётся». Пропусти `adamas_shr_##name` знаковая половина, и первый
    /// тест остался бы зелёным: беззнаковая её определяет.
    ///
    /// Перечень «какая операция у какого типа бывает» берётся у
    /// [`PrimOp::over`], то есть у той же записи, по которой элаборация решает,
    /// существует ли имя. Разъехаться им негде.
    /// Разворот макроса: имя макроса и тип, которому он развёрнут.
    ///
    /// Отдельной функцией, а не цепочкой `&& let` внутри условия: цепочка
    /// принимается clippy, но отвергается MSRV 1.85 - `let` в этой позиции там
    /// ещё нестабилен, и проверяется это прогоном, а не грепом.
    fn expansion(line: &str) -> Option<(String, String)> {
        let rest = line.strip_prefix("ADAMAS_FLAT_")?;
        let (name, arguments) = rest.split_once('(')?;
        let ty = arguments.split(',').next()?;
        Some((name.to_owned(), ty.trim().to_owned()))
    }

    #[test]
    fn every_type_has_a_helper_for_every_operation_it_has() {
        // Макрос -> что он определяет; макрос -> для каких типов развёрнут.
        let mut defines: Vec<(String, String)> = Vec::new();
        let mut expands: Vec<(String, String)> = Vec::new();
        let mut current = String::new();
        let mut inside = false;
        for line in FLAT.lines() {
            if let Some(rest) = line.strip_prefix("#define ADAMAS_FLAT_") {
                current = rest.split('(').next().unwrap_or_default().to_owned();
                inside = true;
            } else if !inside {
                expands.extend(expansion(line));
            }
            if inside {
                for piece in line.split("adamas_").skip(1) {
                    if let Some((op, _)) = piece.split_once("_##name") {
                        defines.push((current.clone(), op.to_owned()));
                    }
                }
                inside = line.trim_end().ends_with('\\');
            }
        }
        assert!(!expands.is_empty(), "разворотов макросов не нашлось вовсе");

        for ty in PrimTy::ALL {
            for op in PrimOp::ALL.into_iter().filter(|op| op.over(ty)) {
                let found = expands.iter().filter(|(_, named)| named == ty.name()).any(
                    |(macro_name, _)| {
                        defines
                            .iter()
                            .any(|(owner, prefix)| owner == macro_name && prefix == op.prefix())
                    },
                );
                assert!(
                    found,
                    "`flat.c` не даёт `adamas_{}_{}`: порождённый вызов не соберётся",
                    op.prefix(),
                    ty.name()
                );
            }
        }
    }

    /// Текст обрыва по нулевому делителю у двух эмиттеров один.
    ///
    /// У LLVM-стороны он берётся из `ir::DIVISION_BY_ZERO` прямо, у C-стороны
    /// живёт в `flat.c`: проверка стоит внутри `adamas_div_*`, а `flat.c` -
    /// текст, а не печать. Вторая запись разошлась бы с первой молча, и здесь
    /// она оплачена.
    #[test]
    fn the_division_message_matches_the_helpers() {
        let written = format!(
            "#define ADAMAS_DIVISION_BY_ZERO \"{}\"",
            crate::ir::DIVISION_BY_ZERO
        );
        assert!(
            FLAT.contains(&written),
            "`flat.c` не объявляет `{written}`: текст обрыва разъехался с эмиттером"
        );
    }
}
