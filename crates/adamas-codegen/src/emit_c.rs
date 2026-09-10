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
//! Функция понижается **первой формой** (§13, 2026-09-08): обычная C-функция,
//! кадр на C-стеке, скрытых аргументов нет вовсе. Оба они - вектор evidence и
//! ручка стека - появляются только на границе замыкания, потому что граница эта
//! динамическая: какая из форм за указателем, место вызова не знает. Там они
//! идут `NULL`, и рантайм принимает `NULL` всюду, где их читает.
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

use adamas_core::prim::{PrimOp, PrimTy};

use crate::ir::{
    Arm, Constructor, CtorId, Elems, Expr, Form, FuncId, Function, LocalId, PackId, Packing,
    Program, Repr, Stride,
};

/// Как уложены элементы массива с таким шагом.
const fn elems(stride: Option<Stride>) -> Elems {
    match stride {
        Some(_) => Elems::Flat,
        None => Elems::Boxed,
    }
}

/// Плоское значение: биты слота, арифметика, печать.
const FLAT: &str = include_str!("flat.c");

/// Печать значения по таблице конструкторов.
const PRINTER: &str = include_str!("print.c");

/// Дроп детей по той же таблице.
const RELEASE: &str = include_str!("release.c");

/// Точка входа: печать ответа и счётчики блоков.
const ENTRY: &str = include_str!("main.c");

/// Почему эмиссия отказала.
#[derive(Debug, thiserror::Error)]
pub enum EmitError {
    /// Функция понижается второй формой.
    ///
    /// Скрытых аргумента у неё два - вектор evidence и ручка стека
    /// продолжения, - а кадр живёт в куче. Эмиттер её не досочиняет: форма
    /// приходит из IR, а кода под неё здесь нет.
    #[error("`{function}` понижается второй формой: кадр в куче этим срезом не эмитится")]
    Detached {
        /// Чья функция.
        function: String,
    },
}

/// Собирает единицу трансляции.
///
/// # Errors
///
/// [`EmitError`] - форма понижения, которой эмиттер не знает.
pub fn emit(program: &Program) -> Result<String, EmitError> {
    for function in &program.functions {
        if function.form == Form::Detached {
            return Err(EmitError::Detached {
                function: function.name.clone(),
            });
        }
    }
    let mut out = String::new();
    preamble(&mut out);
    out.push_str(FLAT);
    out.push('\n');
    packings(&mut out, program);
    table(&mut out, program);
    out.push_str(RELEASE);
    out.push('\n');
    out.push_str(PRINTER);
    out.push('\n');

    let boxed = wrapped(program);
    let built = builders(program);

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
    out.push('\n');

    for constructor in &program.constructors {
        if built.contains(&constructor.tag) {
            builder(&mut out, constructor);
        }
    }
    for function in &program.functions {
        body(&mut out, program, function);
        if boxed.contains(&function.id) {
            wrapper(&mut out, function);
        }
    }

    answer(&mut out, program);
    out.push_str(ENTRY);
    Ok(out)
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
fn kind(ty: PrimTy) -> u8 {
    let at = PrimTy::ALL.iter().position(|it| *it == ty).unwrap_or(0);
    u8::try_from(at + 1).unwrap_or(0)
}

/// Сорт слота: ноль у указательного.
fn slot_kind(repr: Repr) -> u8 {
    repr.primitive().map_or(0, kind)
}

/// C-тип связывания.
fn c_type(repr: Repr) -> String {
    match repr {
        // Плоский агрегат - свой тип на укладку: байты по значению, и передаётся
        // он как всякая структура C (§4.11).
        Repr::Packed(pack) => format!("adamas_pack_{}", pack.0),
        other => scalar(other).to_owned(),
    }
}

/// C-тип всего, кроме плоского агрегата: имя у него постоянное.
fn scalar(repr: Repr) -> &'static str {
    match repr {
        // Массив и запись - объекты кучи, и в C они такое же слово, как всякий
        // объект: различие плоского и указательного живёт **внутри** них.
        // Блок региона - такой же объект кучи, как массив: слово с заголовком,
        // а байты нагрузки лежат внутри (§3.6).
        Repr::Boxed | Repr::Array(_) | Repr::Region | Repr::Record(_) => "adamas_value",
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
    ));
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
                        format!("{}@{} {}", escaped(label), slot.offset, slot.ty.name())
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
fn table(out: &mut String, program: &Program) {
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
    match expr {
        Expr::Local(_)
        | Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::LayoutField { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => {}
        Expr::Unpack { value, .. } => walk(value, visit),
        Expr::RegionLast { region } => walk(region, visit),
        Expr::RegionAlloc { region, value, .. } => {
            walk(region, visit);
            walk(value, visit);
        }
        Expr::RegionRead { region, at, .. } => {
            walk(region, visit);
            walk(at, visit);
        }
        Expr::RegionWrite {
            region, at, value, ..
        } => {
            walk(region, visit);
            walk(at, visit);
            walk(value, visit);
        }
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => {
            for argument in arguments {
                walk(argument, visit);
            }
        }
        Expr::ArrayNew { count, initial, .. } => {
            walk(count, visit);
            walk(initial, visit);
        }
        Expr::ArraySet {
            array, at, value, ..
        } => {
            walk(array, visit);
            walk(at, visit);
            walk(value, visit);
        }
        Expr::ArrayIndex { array, at, .. } => {
            walk(array, visit);
            walk(at, visit);
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                walk(capture, visit);
            }
        }
        Expr::Primitive { left, right, .. } => {
            walk(left, visit);
            walk(right, visit);
        }
        Expr::Apply { callee, argument } => {
            walk(callee, visit);
            walk(argument, visit);
        }
        Expr::Bind { value, body, .. } => {
            walk(value, visit);
            walk(body, visit);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            walk(scrutinee, visit);
            for arm in arms {
                walk(&arm.body, visit);
            }
        }
        Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
            walk(body, visit);
        }
    }
}

/// Сигнатура функции: скрытые аргументы формы и живые связывания.
///
/// У первой формы скрытых нет **вовсе** (`adamas_lowered_first`): написанное и
/// есть всё. Захваченная среда сюда приходит обычными параметрами - трамплин
/// достаёт её из слотов замыкания и передаёт явно. Второй формы здесь не
/// бывает: [`emit`] отвергает её раньше.
fn signature(function: &Function) -> String {
    let live: Vec<String> = function
        .live_captured()
        .chain(function.live_parameters())
        .map(|binding| format!("{} v{}", c_type(binding.fact.repr), binding.local.0))
        .collect();
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

/// Тело функции.
fn body(out: &mut String, program: &Program, function: &Function) {
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
    let mut emitter = Emitter {
        program,
        out: String::new(),
        temps: 0,
        reprs: shapes(function),
    };
    let answer = emitter.value(&function.body, 1);
    out.push_str(&emitter.out);
    let _ = writeln!(out, "    return {answer};\n}}\n");
}

/// Трамплин: замыкание отдаёт слоты позиционно, функция берёт их аргументами.
///
/// Слоты принадлежат замыканию, а функция берёт аргументы **владением**, отсюда
/// `adamas_dup` на каждый: своё замыкание дропает применение
/// ([`perceus`](crate::perceus)), и без дублирования оно унесло бы слоты с
/// собой. Последний аргумент приходит владением уже от `adamas_apply`.
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
    let mut taken: Vec<String> = (0..env)
        .map(|slot| format!("adamas_dup(adamas_closure_get(self, {slot}))"))
        .collect();
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
    out: String,
    temps: u32,
    /// Что в каком связывании лежит: от этого C-тип временного имени.
    reprs: HashMap<LocalId, Repr>,
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
            Expr::Bind { body, .. }
            | Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. } => self.shape(body),
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
            } => Repr::Flat(
                self.program.packings[packing.0 as usize].variants[*variant as usize].slots
                    [*field as usize]
                    .ty,
            ),
            Expr::ArrayNew { stride, .. } | Expr::ArraySet { stride, .. } => {
                Repr::Array(elems(*stride))
            }
            Expr::ArrayIndex { stride, .. } => stride.map_or(Repr::Boxed, Stride::element),
            Expr::RegionNew | Expr::RegionAlloc { .. } | Expr::RegionWrite { .. } => Repr::Region,
            Expr::RegionLast { .. } => Repr::Flat(PrimTy::UInt64),
            Expr::RegionRead { stride, .. } => stride.element(),
            Expr::Erased
            | Expr::Construct { .. }
            | Expr::ConstructClosure { .. }
            | Expr::Closure { .. }
            | Expr::Apply { .. } => Repr::Boxed,
        }
    }

    /// Отступ уровня `depth`.
    fn pad(depth: usize) -> String {
        "    ".repeat(depth)
    }

    /// Эмитит выражение и отдаёт имя, в котором лежит его значение.
    ///
    /// Каждый составной узел получает своё имя: порядок вычисления виден в
    /// тексте, а не выводится из правил C.
    fn value(&mut self, expr: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
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
            Expr::ArrayIndex { stride, array, at } => self.array_index(*stride, array, at, depth),
            Expr::RegionNew => self.region_new(depth),
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
            Expr::Closure { function, captured } => self.closure(*function, captured, depth),
            Expr::Apply { callee, argument } => self.applying(callee, argument, depth),
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
                self.value(body, depth)
            }
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis(scrutinee, arms, depth),
            Expr::Dup { local, body } => {
                let _ = writeln!(self.out, "{pad}adamas_dup(v{});", local.0);
                self.value(body, depth)
            }
            Expr::Drop { local, body } => {
                let _ = writeln!(self.out, "{pad}adamas_drop_value(v{});", local.0);
                self.value(body, depth)
            }
            Expr::Reclaim { local, token, body } => {
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value v{} = adamas_reclaim_value(v{});",
                    token.0, local.0
                );
                self.value(body, depth)
            }
        }
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

    /// Применение значения к одному аргументу.
    ///
    /// Оба скрытых аргумента пусты: хендлеров в чистом фрагменте нет, а `NULL`
    /// рантайм принимает всюду, где их читает.
    fn applying(&mut self, callee: &Expr, argument: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        let callee = self.value(callee, depth);
        let argument = self.value(argument, depth);
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_apply({callee}, NULL, NULL, {argument});"
        );
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
                slot.ty.size()
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
        let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Flat(slot.ty)));
        let _ = writeln!(
            self.out,
            "{pad}memcpy(&{name}, {value}.bytes + {}, {}u);",
            slot.offset,
            slot.ty.size()
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

    /// Чтение ячейки. Массив приходит владением и отдаётся рантайму здесь же.
    ///
    /// Плоский элемент неизвестного типа копируется в буфер **на кадре**:
    /// указателем внутрь массива он бы пережил его дроп. Буфер - массив
    /// переменной длины, потому что длина известна только в рантайме.
    fn array_index(
        &mut self,
        stride: Option<Stride>,
        array: &Expr,
        at: &Expr,
        depth: usize,
    ) -> String {
        let pad = Self::pad(depth);
        let array = self.value(array, depth);
        let at = self.value(at, depth);
        let name = self.temp();
        match stride {
            Some(Stride::Static(ty)) => {
                let _ = writeln!(self.out, "{pad}{} {name};", c_type(Repr::Flat(ty)));
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_array_read({array}, (size_t){at}, &{name}, \
                     adamas_release_value);"
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

    /// Пустой регион: одна область, один блок кучи (§3.6).
    fn region_new(&mut self, depth: usize) -> String {
        let pad = Self::pad(depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name} = adamas_region_new();");
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

    /// Прямой вызов: стёртые позиции в вызов не идут.
    fn call(&mut self, function: FuncId, arguments: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let called = &self.program.functions[function.0];
        let title = escaped(&called.name);
        let present: Vec<usize> = called
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let given: Vec<String> = present
            .iter()
            .filter_map(|position| arguments.get(*position))
            .map(|argument| self.value(argument, depth))
            .collect();
        let result = c_type(called.result);
        let name = self.temp();
        // Вызываемый известен статически, поэтому зовётся прямо и скрытых
        // аргументов не берёт вовсе (`adamas_lowered_first`).
        let _ = writeln!(
            self.out,
            "{pad}{result} {name} = fn_{}({}); /* {title} */",
            function.0,
            given.join(", ")
        );
        name
    }

    /// Замыкание: код плюс среда по слотам.
    fn closure(&mut self, function: FuncId, captured: &[Expr], depth: usize) -> String {
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
            "{pad}adamas_value {name} = adamas_closure(box_{}, adamas_release_value, \
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

    /// Разбор: `switch` по тегу заголовка.
    fn analysis(&mut self, scrutinee: &Expr, arms: &[Arm], depth: usize) -> String {
        let pad = Self::pad(depth);
        let answer = arms
            .first()
            .map_or(Repr::Boxed, |arm| self.shape(&arm.body));
        if let Repr::Packed(pack) = self.shape(scrutinee) {
            return self.packed_analysis(pack, scrutinee, arms, answer, depth);
        }
        let scrutinee = self.value(scrutinee, depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}{} {name};", c_type(answer));
        let _ = writeln!(self.out, "{pad}switch (adamas_tag({scrutinee})) {{");
        for arm in arms {
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
            let answer = self.value(&arm.body, depth + 1);
            let _ = writeln!(self.out, "{pad}    {name} = {answer};");
            let _ = writeln!(self.out, "{pad}    break;");
            let _ = writeln!(self.out, "{pad}}}");
        }
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
                described.ty.size(),
                escaped(&binding.name)
            );
        }
        let answer = self.value(&arm.body, depth);
        let _ = writeln!(self.out, "{pad}{name} = {answer};");
    }
}

/// Имя операции в `flat.c`: то же, что пишет `adamas_add_Int64`.
fn operation(op: PrimOp) -> &'static str {
    match op {
        PrimOp::Add => "add",
        PrimOp::Sub => "sub",
        PrimOp::Mul => "mul",
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
    use adamas_core::prim::{PrimOp, PrimTy};

    use super::{FLAT, kind, operation};

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
        for helper in ["adamas_bits_##name", "adamas_word_##name"] {
            assert!(FLAT.contains(helper), "`flat.c` не определяет `{helper}`");
        }
    }
}
