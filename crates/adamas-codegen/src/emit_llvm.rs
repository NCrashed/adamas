//! Эмиттер LLVM: [`ir`](crate::ir) в текст `.ll` (§9 Фаза 7, волна 1, трек A).
//!
//! **Ядра этот модуль не читает** - ровно как [`emit_c`](crate::emit_c), и по
//! той же проверяемой причине: шов между ядром и эмиттером существует затем,
//! чтобы Фаза 7 добавила **второй эмиттер**, а не второй компилятор
//! (`docs/phase7-plan.md`, «Что Фаза 7 требует от Фазы 6»). Свидетель -
//! `tests/seam.rs`, читающий исходник этого файла.
//!
//! # Способ привязки - текст
//!
//! Не `inkwell` и не `llvm-sys`: решение 2026-09-15 на основании замеров
//! 2026-09-08 - разбор `.ll` берёт 6% времени бэкенда, и доля падает с
//! размером, а проверок текстовый путь не теряет, потому что делает их verifier
//! на прогоне, а не система типов Rust.
//!
//! Цена решения - **правило консервативного подмножества**: новых
//! необязательных атрибутов IR не использовать без причины. Проверяется правило
//! прогоном на минимальной поддерживаемой версии
//! ([`llvm::MINIMUM_MAJOR`](crate::llvm::MINIMUM_MAJOR)), а не грепом по
//! формам, - той же дисциплиной, что MSRV, и заведена она так потому, что греп
//! по формам врал трижды подряд.
//!
//! Что из правила следует построчно: у целочисленной арифметики **нет** `nsw` и
//! `nuw`; `getelementptr` не эмитится вовсе - именно его необязательный флаг
//! `nuw`, появившийся после 18, оказался единственным, ломающим чтение старой
//! версией; ни `target datalayout`, ни `target triple` не пишется - цель берёт
//! `llc` у хоста, и вписанная строка сделала бы `.ll` непереносимым между
//! архитектурами.
//!
//! # Что берёт этот срез
//!
//! Скалярный фрагмент, узкий намеренно: каркас важнее охвата, потому что правят
//! его пять треков волны. Берётся плоское **целое** (восемь типов §4.11 из
//! десяти), арифметика, сравнение, прямой вызов первой формы, `let`, разбор по
//! нульарному конструктору, `dup` и `drop`. Ответ программы обязан быть плоским
//! целым.
//!
//! Не берётся - и отвергается **названным** отказом ([`LlvmError`]): плавающее,
//! объекты с полями, замыкания, массивы, регионы, плотные агрегаты, вторая
//! форма понижения и всё, что за ней стоит, - хендлеры, резумпции, питомник.
//!
//! # Где встанут треки B-F
//!
//! Каждый режет в **одном** месте, и место названо здесь, чтобы его не искали
//! по тексту.
//!
//! - **B, алиасинг из QTT.** [`parameter_attributes`] получает [`Fact`]
//!   целиком: `noalias`, `dereferenceable` и `align` ставятся оттуда по
//!   [`Fact::unique`], а не по кратности (§10 вопрос 149). Scoped-метаданные
//!   регионов идут через [`Notes`] на инструкции и [`Module::metadata`] на
//!   модуле.
//! - **C, схлопывание RC.** Конвейер - **данные**
//!   ([`llvm::Pipeline`](crate::llvm::Pipeline)), список стадий; свой проход
//!   встаёт стадией между инлайнингом и остальным, а не переписыванием
//!   драйвера.
//! - **D, `musttail`. Закрыт**: [`Tail`] получил второе значение, и как оно
//!   выбирается, сказано ниже отдельным разделом.
//! - **E, DWARF.** [`Notes`] подписывает инструкцию, [`Module::metadata`] несёт
//!   узлы модуля.
//! - **F, строгий режим плавающей арифметики.** [`Builder::binary`] печатает
//!   флаги инструкции отдельным полем; плавающее сегодня отвергается, и трек F
//!   снимает отказ вместе с добавлением флагов.
//!
//! # Хвостовой вызов - свойство инструкции (трек D)
//!
//! Обещание §3.4 и §5.3 - «хвостовой вызов не растит стек» - держится здесь, а
//! не на ключах сборки. Три решения, и каждое взято замером.
//!
//! *Соглашение о вызове - [`CONVENTION`], а не C.* `musttail` при C-соглашении
//! требует **совпадения прототипов** вызывающего и вызываемого, а первая же
//! программа корпуса его ломает: `main` без параметров хвостом зовёт `mix`
//! двух. Отсюда `tailcc` на всех порождённых определениях и на всех вызовах к
//! ним. Точка входа [`ENTRY_SYMBOL`] остаётся с C-соглашением - её зовёт
//! спутник, - и вызов из неё хвостовым не помечается.
//!
//! *Хвостовая позиция считается **анализом**, а не полем узла.* Признака
//! хвоста у [`Expr::Call`] нет и заводить его не следует: хвост есть свойство
//! **контекста**, а не вызова, и всякая правка представления его меняет. Ближе
//! всего пример Perceus: дроп, вставленный **после** вызова, хвост отнимает, а
//! вставленный до - оставляет; поле пришлось бы пересчитывать в проходе,
//! который про хвосты ничего не знает. Обход [`Builder::tail`] это различает по
//! построению - `Expr::Drop { body }` спускает хвост в тело, `Expr::Bind {
//! value }` не спускает.
//!
//! *`phi` в хвостовой позиции не строится вовсе.* LLVM требует, чтобы за
//! `musttail` немедленно шёл `ret`; ветвь разбора, кончающаяся `br label
//! %join`, требование ломает. Поэтому разбор в хвостовой позиции печатается
//! **без** блока стыковки: каждая ветвь возвращает сама
//! ([`Builder::analysis_tail`]). Цена - вторая печать разбора рядом с
//! [`Builder::analysis`]; выигрыш - на витке нет ни `phi`, ни лишнего блока.
//!
//! # Чем срез платит рантайму, и это измерено
//!
//! Сравнение (§4.3) отвечает конструктором `Bool`, а строит и разбирает его
//! **рантайм** - `adamas_con0` и `adamas_tag`. Для `opt` они непрозрачны, и на
//! `workload-scalar` после `-O2` остаётся цикл с двумя вызовами на виток
//! (проверено 2026-09-15 чтением `opt`-выхода: `tailrecurse` со вставленными
//! `fn_0`, `fn_1`, `fn_2`, и в нём `call @adamas_con0`, `call @adamas_tag`).
//!
//! У C-бэкенда та же пара вызовов есть в тексте и **исчезает на сборке**:
//! строка стенда `-std=c11 -O2 -flto` даёт ноль вызовов обоих имён в готовом
//! бинаре (проверено тем же днём, `objdump -d`). Разница не в качестве
//! кодогенерации, а в том, что рантайм приезжает к C битовым кодом LTO, а к
//! `.ll` - готовым объектником.
//!
//! Отсюда два следствия. Мерить LLVM против C сегодня нельзя: число мерило бы
//! LTO, а не бэкенд. И снимается это стадией в конвейере
//! ([`llvm::Pipeline`](crate::llvm::Pipeline)) - рантайм, собранный в
//! `.bc` и приложенный `llvm-link` перед `opt`, - а не правкой эмиттера.
//!
//! # Что рядом с `.ll` и почему
//!
//! Спутник на C ([`Artefacts::support`]): печать ответа и точка входа. Он не
//! уступка - это **те же** `flat.c` и `main.c`, что собирает C-бэкенд, взятые
//! дословно теми же `include_str!`. Разъедься две печати - разошёлся бы и
//! договор «печатает то же», а причина была бы не в вычислении. Программу
//! считает `.ll` целиком; спутник её только печатает.

use std::collections::HashMap;
use std::fmt::Write as _;

use adamas_core::prim::{PrimCmp, PrimOp, PrimTy};

use adamas_core::source::Location;

use crate::ir::{Arm, Binding, Expr, Fact, Form, FuncId, Function, LocalId, Program, Repr, Source};

/// Почему эмиссия в LLVM отказала.
///
/// Отказ **названный**, как у понижения: молча посчитать не то хуже, чем не
/// посчитать. Мера среза читается прогоном по корпусу (`tests/llvm.rs`), а не
/// оценкой, и каждая причина здесь - строка этой меры.
#[derive(Debug, thiserror::Error)]
pub enum LlvmError {
    /// Узел представления, которого скалярный фрагмент не знает.
    #[error("`{function}`: {node} - узел вне скалярного фрагмента")]
    Node {
        /// Чья функция.
        function: String,
        /// Какой узел.
        node: &'static str,
    },

    /// Представление, которое в регистр целого не ложится.
    #[error("`{function}`: {place} - {shape}, а срез берёт только плоское целое")]
    Shape {
        /// Чья функция.
        function: String,
        /// Что именно: параметр, ответ, промежуточное значение.
        place: String,
        /// Как оно представлено.
        shape: String,
    },

    /// Плавающая арифметика: её берёт трек F вместе с флагами инструкций.
    #[error("`{function}`: плавающее {ty} - флаги контракции ставит трек F")]
    Real {
        /// Чья функция.
        function: String,
        /// Какого типа.
        ty: &'static str,
    },

    /// Вторая форма понижения: кадр отчуждается в кучу (§3.4).
    #[error("`{function}`: вторая форма понижения - кадров этот срез не кладёт")]
    Detached {
        /// Чья функция.
        function: String,
    },

    /// Разбор объекта с полями: за ним стоит весь объектный слой рантайма.
    #[error("`{function}`: ветвь связывает поля `{constructor}` - объектов срез не читает")]
    Fields {
        /// Чья функция.
        function: String,
        /// Какого конструктора.
        constructor: String,
    },
}

/// Что даёт эмиссия: текст `.ll` и спутник на C.
#[derive(Clone, Debug)]
pub struct Artefacts {
    /// Текст `.ll`: программа целиком.
    pub ll: String,
    /// Спутник на C: печать ответа и точка входа.
    pub support: String,
}

/// Имя точки входа, которую спутник зовёт из `.ll`.
const ENTRY_SYMBOL: &str = "adamas_entry";

/// Имя константы с текстом обрыва по неизвестному тегу.
const TAG_MESSAGE: &str = "@.str.tag";

/// Имя константы с текстом обрыва в дропе детей.
const RELEASE_MESSAGE: &str = "@.str.release";

/// Атрибуты определения функции.
///
/// `nounwind` - утверждение о **нашем** коде: раскрутки в порождённом нет
/// вовсе, обрыв идёт через `adamas_fail`. На объявления рантайма он не
/// ставится: про чужой код это было бы обещанием, а не фактом.
const DEFINITION_ATTRIBUTES: &str = "nounwind";

/// Соглашение о вызове порождённых функций (трек D).
///
/// `tailcc`, а не C-соглашение, и причина одна: при C-соглашении `musttail`
/// требует совпадения прототипов вызывающего с вызываемым, а хвостовой вызов
/// между разными сигнатурами в языке обычен - `main : UInt64` хвостом зовёт
/// `mix : UInt64 -> UInt64 -> UInt64` в первой же программе корпуса. `tailcc`
/// это требование снимает и разрешает вызываемому **больше** аргументов, чем у
/// вызывающего; ровно этого не умеет и обычная оптимизация хвостового вызова в
/// `llc` (измерено, `tests/tail.rs`).
///
/// Соглашение обязано совпадать у определения и у каждого вызова, поэтому
/// печатается оно и там и там. Исключение одно - [`ENTRY_SYMBOL`]: его зовёт
/// спутник на C, и C-соглашение у него не выбор, а договор.
const CONVENTION: &str = "tailcc";

/// Собирает `.ll` и спутник на C.
///
/// # Errors
///
/// [`LlvmError`] - форма понижения вне скалярного фрагмента.
pub fn emit(program: &Program) -> Result<Artefacts, LlvmError> {
    let entry = &program.functions[program.entry.0];
    // Ответ обязан быть плоским целым: печатает его спутник, а печать плоского
    // ответа - единственная, которую он знает. Граница здесь у **печати**, не у
    // вычисления, и именно она отвергает большую часть корпуса.
    let answer = integral(entry.result).ok_or_else(|| LlvmError::Shape {
        function: entry.name.clone(),
        place: "ответ программы".to_owned(),
        shape: describe(entry.result),
    })?;
    // Точка входа зовётся без аргументов, и подать их было бы неоткуда: `main`
    // с параметром есть функция значением, а её ответ печатать нечем и у
    // C-бэкенда (`agreement.rs`, `LANGUAGE`).
    if entry.live_parameters().next().is_some() {
        return Err(LlvmError::Shape {
            function: entry.name.clone(),
            place: "точка входа".to_owned(),
            shape: "функция с параметрами".to_owned(),
        });
    }

    let mut module = Module::default();
    // Отладочная информация появляется **от исходника**, а не от ключа сборки:
    // нет текста - нечего и называть отладчику, и выход тогда байт в байт тот
    // же, что был до трека E.
    if let Some(source) = &program.source {
        module.dwarf = Some(Dwarf::new(&mut module.metadata, source));
    }
    for function in &program.functions {
        module.function(program, function)?;
    }
    Ok(Artefacts {
        ll: module.finish(program, answer),
        support: support(answer),
    })
}

/// Плоское **целое** представление. `None` - всё прочее, включая плавающее.
fn integral(repr: Repr) -> Option<PrimTy> {
    repr.primitive().filter(|ty| !ty.floating())
}

/// Как назвать представление в тексте отказа.
fn describe(repr: Repr) -> String {
    match repr {
        Repr::Flat(ty) => format!("плоское {}", ty.name()),
        Repr::Boxed => "объект кучи".to_owned(),
        Repr::Packed(_) => "плотный агрегат".to_owned(),
        Repr::Layout => "дескриптор укладки".to_owned(),
        Repr::Opaque => "плоское неизвестной ширины".to_owned(),
        Repr::Array(_) => "массив".to_owned(),
        Repr::Region => "блок региона".to_owned(),
        Repr::Record(_) => "запись".to_owned(),
        Repr::Resumption => "резумпция".to_owned(),
    }
}

/// Тип LLVM у плоского значения.
///
/// Знаковость типом не выражается вовсе - её несёт инструкция (`sdiv` против
/// `udiv`, `slt` против `ult`), и это не потеря: §4.11 различает `Int64` и
/// `UInt64` шириной и правилом сравнения, а ширина здесь та же.
///
/// Плавающие два ряда сегодня не достигаются - их отвергает [`integral`], - но
/// названы верно: трек F снимает отказ, а не дописывает таблицу.
const fn machine(ty: PrimTy) -> &'static str {
    match ty {
        PrimTy::Int8 | PrimTy::UInt8 => "i8",
        PrimTy::Int16 | PrimTy::UInt16 => "i16",
        PrimTy::Int32 | PrimTy::UInt32 => "i32",
        PrimTy::Int64 | PrimTy::UInt64 => "i64",
        PrimTy::Float32 => "float",
        PrimTy::Float64 => "double",
    }
}

/// Сорт вызова (трек D).
///
/// `musttail` есть свойство **инструкции**, а не ключей пользователя (§3.4,
/// §5.3): оптимизация хвостового вызова, которую `llc` делает сам, идёт только
/// с `-O2` и только там, где кадру вызываемого хватает места вызывающего.
/// Приставка снимает оба условия.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tail {
    /// Обычный вызов: кадр вызывающего живёт дальше.
    Plain,
    /// Хвостовой: кадр вызывающего замещается кадром вызываемого.
    ///
    /// Требование LLVM к такому вызову одно, и его обязан выполнить эмиттер: за
    /// инструкцией немедленно следует `ret` того же значения. Отсюда разбор без
    /// `phi` в хвостовой позиции ([`Builder::analysis_tail`]).
    Must,
}

impl Tail {
    /// Приставка инструкции вызова.
    const fn prefix(self) -> &'static str {
        match self {
            Self::Plain => "",
            Self::Must => "musttail ",
        }
    }
}

/// Метаданные **одной** инструкции.
///
/// Аргумент [`Builder::instruction`], а не поле билдера, и разница
/// принципиальная: суффикс, лежащий полем, одинаков у всех инструкций подряд, а
/// ни одни из требуемых метаданных таковыми не являются. `!dbg` различается от
/// инструкции к инструкции - у пролога он свой (трек E, [`Builder::prologue`]);
/// scoped `!alias.scope`/`!noalias` стоят на загрузке и записи, а не на
/// арифметике рядом с ними (трек B).
///
/// Собирается цепочкой: [`Notes::none`] плюс [`Notes::and`] на каждый узел.
/// Окружающие метаданные - те, что несёт всякая инструкция тела, - отдаёт
/// [`Builder::here`], и своё дописывается к ним:
/// `self.here().and("alias.scope", "!7")`.
#[derive(Clone, Debug, Default)]
struct Notes {
    /// Узлы в порядке печати.
    items: Vec<String>,
}

impl Notes {
    /// Ни одной.
    const fn none() -> Self {
        Self { items: Vec::new() }
    }

    /// Дописывает узел: `!kind !N`.
    fn and(mut self, kind: &str, node: &str) -> Self {
        self.items.push(format!("!{kind} {node}"));
        self
    }

    /// Хвост инструкции. Пустой список не печатает даже запятой.
    fn suffix(self) -> String {
        if self.items.is_empty() {
            return String::new();
        }
        format!(", {}", self.items.join(", "))
    }
}

/// Атрибуты параметра: место `noalias`, `dereferenceable` и `align` (трек B).
///
/// [`Fact`] приходит целиком **намеренно**. Уникальность берётся из
/// производства - `unique data`/`resource` и локально свежий объект, - а из
/// кратности не берётся никогда (§10 вопрос 149, закрыт): `both shared shared`
/// на кратности `1` принимается, и `noalias` там был бы UB. Поле
/// [`Fact::unique`] сегодня не заполняет никто, и отсюда пусто по построению, а
/// не по забывчивости.
fn parameter_attributes(fact: &Fact) -> String {
    let _ = fact;
    String::new()
}

/// Узлы метаданных модуля, нумерованные порядком заведения.
///
/// Номер выдаётся при записи и возвращается ссылкой `!N`: узлы DWARF ссылаются
/// друг на друга, и держать номер в голове пришлось бы иначе на каждом.
#[derive(Debug, Default)]
struct Metadata {
    /// Узлы по номеру.
    nodes: Vec<String>,
    /// Уже заведённые узлы: текст к ссылке.
    ///
    /// LLVM уникализирует неразличимые узлы сама, поэтому вторая копия
    /// `!DIBasicType(name: "Int64", ...)` не ошибка - она просто занимает место
    /// в тексте. Копий выходит по одной на каждое упоминание типа, и на
    /// программе из сотни функций это сотни строк ни о чём. `distinct` в кеш не
    /// идёт: он затем и написан, чтобы копии различались.
    seen: HashMap<String, String>,
    /// Именованные метаданные: имя и список ссылок.
    named: Vec<(String, Vec<String>)>,
}

impl Metadata {
    /// Заводит узел и отдаёт ссылку на него.
    fn node(&mut self, text: &str) -> String {
        if let Some(known) = self.seen.get(text) {
            return known.clone();
        }
        let at = self.nodes.len();
        self.nodes.push(text.to_owned());
        let reference = format!("!{at}");
        if !text.starts_with("distinct ") {
            self.seen.insert(text.to_owned(), reference.clone());
        }
        reference
    }

    /// Заводит именованный список: `!имя = !{...}`.
    fn name(&mut self, name: &str, refs: Vec<String>) {
        self.named.push((name.to_owned(), refs));
    }

    /// Печатает всё: сперва именованные, потом нумерованные.
    fn print(&self, out: &mut String) {
        for (name, refs) in &self.named {
            let _ = writeln!(out, "!{name} = !{{{}}}", refs.join(", "));
        }
        for (at, node) in self.nodes.iter().enumerate() {
            let _ = writeln!(out, "!{at} = {node}");
        }
    }
}

/// Общие узлы DWARF: файл, единица трансляции, пустой список.
///
/// Заводится ровно тогда, когда у программы назван исходник
/// ([`Program::source`](crate::ir::Program::source)). Нет исходника - нет и
/// отладочной информации, а выход байт в байт тот, что был до трека E.
///
/// `DW_LANG_C99`, а не `DW_LANG_Haskell` или свой код: язык в DWARF выбирает,
/// **каким синтаксисом отладчик разбирает выражения**, и на C-режиме `print x`
/// работает как ожидается. Кода Adamas в DWARF нет, а Haskell-режим включил бы
/// чужие правила печати. Цена названа: имя Adamas, не являющееся идентификатором
/// C (`f'`), отладчику придётся квотировать.
#[derive(Debug)]
struct Dwarf {
    /// Ссылка на `!DIFile`.
    file: String,
    /// Ссылка на `!DICompileUnit`.
    unit: String,
}

impl Dwarf {
    /// Заводит шапку DWARF: флаги модуля, файл, единицу трансляции.
    fn new(metadata: &mut Metadata, source: &Source) -> Self {
        let empty = metadata.node("!{}");
        let file = metadata.node(&format!(
            "!DIFile(filename: \"{}\", directory: \"{}\")",
            source.file, source.directory
        ));
        let unit = metadata.node(&format!(
            "distinct !DICompileUnit(language: DW_LANG_C99, file: {file}, \
             producer: \"adamas\", isOptimized: false, runtimeVersion: 0, \
             emissionKind: FullDebug, enums: {empty})"
        ));
        // Обе версии обязательны, и вторая - не украшение: без «Debug Info
        // Version» verifier выбрасывает метаданные целиком, и `.ll` собирается
        // молча без DWARF. Пятая версия читается и восемнадцатой, и двадцать
        // первой - проверено прогоном, а не таблицей совместимости.
        let dwarf_version = metadata.node("!{i32 7, !\"Dwarf Version\", i32 5}");
        let info_version = metadata.node("!{i32 2, !\"Debug Info Version\", i32 3}");
        metadata.name("llvm.dbg.cu", vec![unit.clone()]);
        metadata.name("llvm.module.flags", vec![dwarf_version, info_version]);
        Self { file, unit }
    }

    /// Тип DWARF под представление слота.
    ///
    /// Имя берётся у **Adamas** (§4.11), а не у машинного типа: `UInt64`, а не
    /// `i64`. Ради этого трек и заведён - отладчик показывает типы языка, а не
    /// типы бэкенда. Знаковость несёт кодировка, ширину - размер.
    fn ty(metadata: &mut Metadata, repr: Repr) -> String {
        match integral(repr) {
            Some(prim) => {
                let encoding = if prim.signed() {
                    "DW_ATE_signed"
                } else {
                    "DW_ATE_unsigned"
                };
                metadata.node(&format!(
                    "!DIBasicType(name: \"{}\", size: {}, encoding: {encoding})",
                    prim.name(),
                    prim.size() * 8
                ))
            }
            // Объект кучи: своего имени у него в IR нет - представление знает
            // только, что это указатель. Показать «указатель» честнее, чем
            // выдумать имя типа, которого представление не несёт.
            None => metadata.node(
                "!DIDerivedType(tag: DW_TAG_pointer_type, name: \"объект\", \
                 baseType: null, size: 64)",
            ),
        }
    }

    /// Заводит `!DISubprogram` функции и её локацию тела.
    ///
    /// `linkageName` **не пишется**, и это измерено: с ним gdb показывает в
    /// кадре `fn_3`, без него - имя Adamas. Ради имени трек и существует, а
    /// связь с символом отладчик всё равно берёт по адресам.
    fn subprogram(
        &self,
        metadata: &mut Metadata,
        function: &Function,
        at: Location,
        signature: &[String],
    ) -> Scope {
        let types = metadata.node(&format!("!{{{}}}", signature.join(", ")));
        let subroutine = metadata.node(&format!("!DISubroutineType(types: {types})"));
        let subprogram = metadata.node(&format!(
            "distinct !DISubprogram(name: \"{}\", scope: {}, file: {}, line: {}, \
             type: {subroutine}, scopeLine: {}, \
             spFlags: DISPFlagDefinition | DISPFlagLocalToUnit, unit: {})",
            escaped_name(&function.name),
            self.file,
            self.file,
            at.line,
            at.line,
            self.unit
        ));
        let here = metadata.node(&format!(
            "!DILocation(line: {}, column: {}, scope: {subprogram})",
            at.line, at.column
        ));
        // Строка нуль - «код написан не человеком», и она здесь не заглушка, а
        // требование: `llc` ставит `prologue_end` на первую инструкцию с
        // ненулевой строкой, и без нулевого пролога точка останова вставала бы
        // **до** записи параметра в кадр. Измерено сеансом: параметр печатался
        // нулём вместо своего значения.
        let prologue = metadata.node(&format!("!DILocation(line: 0, scope: {subprogram})"));
        Scope {
            subprogram,
            here,
            prologue,
            at,
        }
    }
}

/// Отладочная подпись одной функции.
#[derive(Clone, Debug)]
struct Scope {
    /// Ссылка на `!DISubprogram`.
    subprogram: String,
    /// Локация тела: строка определения.
    here: String,
    /// Локация пролога: строка нуль.
    prologue: String,
    /// Где определение написано - им же датируются локальные переменные.
    at: Location,
}

/// Имя в кавычках метаданных: обратный слеш и кавычка экранируются.
fn escaped_name(name: &str) -> String {
    name.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Модуль целиком.
#[derive(Debug, Default)]
struct Module {
    /// Тела функций.
    bodies: String,
    /// Узлы метаданных модуля.
    metadata: Metadata,
    /// Шапка DWARF. `None` - исходника у программы нет.
    dwarf: Option<Dwarf>,
}

impl Module {
    /// Эмитит одну функцию.
    fn function(&mut self, program: &Program, function: &Function) -> Result<(), LlvmError> {
        if function.form == Form::Detached {
            return Err(LlvmError::Detached {
                function: function.name.clone(),
            });
        }
        if let Some(binding) = function.captured.first() {
            return Err(LlvmError::Shape {
                function: function.name.clone(),
                place: format!("захват `{}`", binding.name),
                shape: "среда замыкания".to_owned(),
            });
        }
        let result = slot_or(function, "ответ", function.result)?;

        let mut parameters = Vec::new();
        for binding in function.live_parameters() {
            let ty = slot_or(
                function,
                &format!("параметр `{}`", binding.name),
                binding.fact.repr,
            )?;
            let attributes = parameter_attributes(&binding.fact);
            let spaced = if attributes.is_empty() {
                String::new()
            } else {
                format!("{attributes} ")
            };
            parameters.push(format!("{ty} {spaced}%v{}", binding.local.0));
        }

        // Подпись функции для DWARF собирается **до** тела: `!DISubprogram`
        // обязан существовать раньше, чем на него сошлётся первая локация.
        let scope = match (&self.dwarf, function.position) {
            (Some(dwarf), Some(at)) => {
                let mut signature = vec![Dwarf::ty(&mut self.metadata, function.result)];
                signature.extend(
                    function
                        .live_parameters()
                        .map(|binding| Dwarf::ty(&mut self.metadata, binding.fact.repr)),
                );
                Some(dwarf.subprogram(&mut self.metadata, function, at, &signature))
            }
            _ => None,
        };

        let mut builder = Builder::new(
            program,
            function,
            result,
            &mut self.metadata,
            self.dwarf.as_ref(),
            scope.clone(),
        );
        builder.parameters_in_frame(function);
        // Тело стоит в **возвратной** позиции целиком, и обход её разносит:
        // хвостовой вызов печатается `musttail`, всё прочее - `ret`. Печатает
        // `ret` сам обход, потому что у разбора в хвосте их столько, сколько
        // ветвей (трек D).
        builder.tail(&function.body)?;

        let signed = scope.map_or_else(String::new, |scope| format!(" !dbg {}", scope.subprogram));
        let _ = writeln!(self.bodies, "; {}", function.name);
        let _ = writeln!(
            self.bodies,
            "define internal {CONVENTION} {result} @fn_{}({}) {DEFINITION_ATTRIBUTES}{signed} {{",
            function.id.0,
            parameters.join(", ")
        );
        self.bodies.push_str("entry:\n");
        self.bodies.push_str(&builder.head);
        self.bodies.push_str(&builder.body);
        self.bodies.push_str("}\n\n");
        Ok(())
    }

    /// Складывает модуль: шапка, объявления, константы, тела, метаданные.
    fn finish(self, program: &Program, answer: PrimTy) -> String {
        let mut out = String::new();
        out.push_str(concat!(
            "; Порождено понижением Adamas. Править нечего: правится тот, кто\n",
            "; породил. Договор с рантаймом - `adamas.h`.\n",
            ";\n",
            "; Подмножество IR консервативное (`emit_llvm.rs`): ни `nsw`/`nuw` у\n",
            "; арифметики, ни `getelementptr`, ни строк цели - её берёт `llc` у\n",
            "; хоста. Проверяется прогоном на минимальной версии, а не грепом.\n",
            "\n",
            "; Рантайм: те же точки входа, что зовёт C-бэкенд.\n",
            "declare ptr @adamas_con0(i16)\n",
            "declare i16 @adamas_tag(ptr)\n",
            "declare ptr @adamas_dup(ptr)\n",
            "declare void @adamas_drop(ptr, ptr)\n",
            "declare void @adamas_fail(ptr) noreturn\n",
            "\n",
        ));

        if self.dwarf.is_some() {
            out.push_str(concat!(
                "; Отладочная информация. Вызов интринсика, а не запись\n",
                "; `#dbg_declare`: записи не читает восемнадцатая версия, а\n",
                "; вызов читают обе.\n",
                "declare void @llvm.dbg.declare(metadata, metadata, metadata)\n",
                "\n",
            ));
        }

        let _ = writeln!(
            out,
            "{TAG_MESSAGE} = private unnamed_addr constant [{} x i8] c\"{}\"",
            terminated(TAG_TEXT).len(),
            escaped(&terminated(TAG_TEXT))
        );
        let _ = writeln!(
            out,
            "{RELEASE_MESSAGE} = private unnamed_addr constant [{} x i8] c\"{}\"\n",
            terminated(RELEASE_TEXT).len(),
            escaped(&terminated(RELEASE_TEXT))
        );

        out.push_str(concat!(
            "; Дроп детей: срез берёт только нульарные конструкторы, а они\n",
            "; непосредственны (`adamas_con0`) и до release не доходят вовсе.\n",
            "; Не отказ, а обрыв: доехав сюда, срез считал бы не то, что обещал.\n"
        ));
        let _ = writeln!(
            out,
            "define internal void @adamas_release_none(ptr %value) {DEFINITION_ATTRIBUTES} {{"
        );
        out.push_str("entry:\n");
        let _ = writeln!(out, "  call void @adamas_fail(ptr {RELEASE_MESSAGE})");
        out.push_str("  unreachable\n}\n\n");

        out.push_str(&self.bodies);

        let _ = writeln!(out, "; Точка входа для спутника на C.");
        let _ = writeln!(
            out,
            "; Соглашение здесь C - её зовёт спутник; порождённые между собой\n\
             ; ходят по `{CONVENTION}` (трек D), и вызов ниже это называет."
        );
        let _ = writeln!(
            out,
            "define {} @{ENTRY_SYMBOL}() {DEFINITION_ATTRIBUTES} {{",
            machine(answer)
        );
        out.push_str("entry:\n");
        let _ = writeln!(
            out,
            "  %answer = call {CONVENTION} {} @fn_{}()",
            machine(answer),
            program.entry.0
        );
        let _ = writeln!(out, "  ret {} %answer", machine(answer));
        out.push_str("}\n");

        if !self.metadata.nodes.is_empty() {
            out.push('\n');
            self.metadata.print(&mut out);
        }
        out
    }
}

/// Текст обрыва по неизвестному тегу.
const TAG_TEXT: &str = "разбор не знает конструктора";

/// Текст обрыва в дропе детей.
const RELEASE_TEXT: &str = "release в скалярном фрагменте: у нульарного детей нет";

/// Байты строки с завершающим нулём.
fn terminated(text: &str) -> Vec<u8> {
    let mut bytes = text.as_bytes().to_vec();
    bytes.push(0);
    bytes
}

/// Байты строковой константы в форме `.ll`.
///
/// Экранируется всё, кроме печатной латиницы и пробела: русский текст занимает
/// два байта на букву, и печатать их сырыми значило бы полагаться на кодировку
/// файла там, где `.ll` объявлен байтовым.
fn escaped(bytes: &[u8]) -> String {
    let mut out = String::new();
    for byte in bytes {
        if *byte == b' ' || (byte.is_ascii_graphic() && *byte != b'"' && *byte != b'\\') {
            out.push(char::from(*byte));
        } else {
            let _ = write!(out, "\\{byte:02X}");
        }
    }
    out
}

/// Тип регистра, в который представление ложится. `None` - не ложится.
///
/// Указательное здесь ровно одно - [`Repr::Boxed`], - и в срезе за ним стоит
/// **только нульарный конструктор**: единственный узел, порождающий указатель
/// без аллокации, - это [`Expr::Compare`] (§4.3, ответ `Bool`), а всё, что
/// заводит объект с полями, срез отвергает узлом. Отсюда законность и `drop`
/// через `@adamas_release_none`: у непосредственного значения детей нет.
///
/// Запись и резумпция сюда **не** входят, хотя в рантайме они тот же указатель:
/// у первой есть поля, у второй - свой дроп, и обе означали бы объектный слой.
fn slot(repr: Repr) -> Option<&'static str> {
    match repr {
        Repr::Boxed => Some("ptr"),
        other => integral(other).map(machine),
    }
}

/// Он же с названным отказом.
fn slot_or(function: &Function, place: &str, repr: Repr) -> Result<&'static str, LlvmError> {
    if let Some(ty) = repr.primitive().filter(|ty| ty.floating()) {
        return Err(LlvmError::Real {
            function: function.name.clone(),
            ty: ty.name(),
        });
    }
    slot(repr).ok_or_else(|| LlvmError::Shape {
        function: function.name.clone(),
        place: place.to_owned(),
        shape: describe(repr),
    })
}

/// Состояние эмиссии одного тела.
struct Builder<'a> {
    program: &'a Program,
    function: &'a Function,
    /// Тип регистра, в котором функция отдаёт ответ.
    ///
    /// Нужен обходу хвостовой позиции: `ret` печатает он, а не вызывающий, и
    /// печатей этих у разбора столько, сколько ветвей.
    result: &'static str,
    /// Что в каком связывании лежит: от этого тип регистра.
    reprs: HashMap<LocalId, Repr>,
    /// Чем связывание представлено в тексте.
    ///
    /// Подстановка, а не своё имя на связывание: `let` в IR - дерево, значение
    /// у него единственное, и лишний регистр пришлось бы заводить инструкцией,
    /// у которой для указателя нет формы (`add ptr` не бывает).
    operands: HashMap<LocalId, String>,
    /// Начало блока `entry`: только `alloca`.
    ///
    /// Отдельно от тела, потому что ячейка кадра обязана лежать в `entry`:
    /// `alloca` в блоке разбора была бы динамической, а по динамической
    /// `llvm.dbg.declare` не даёт постоянного смещения в кадре, и отладчик
    /// показал бы переменную не там. Запись в ячейку остаётся на месте, где
    /// значение посчитано, - так же делает всякий компилятор на `-O0`.
    head: String,
    /// Текст тела: блоки в порядке печати.
    body: String,
    /// Узлы метаданных модуля: сюда идут переменные и локации.
    metadata: &'a mut Metadata,
    /// Шапка DWARF, если исходник назван.
    dwarf: Option<&'a Dwarf>,
    /// Подпись этой функции. `None` - позиции у неё нет, и DWARF ей не пишется.
    scope: Option<Scope>,
    /// Счётчик ячеек кадра, заведённых ради отладчика.
    frames: u32,
    /// Счётчик временных имён.
    temps: u32,
    /// Счётчик разборов: им нумеруются блоки.
    matches: u32,
    /// Имя блока, в который печатается инструкция.
    ///
    /// Нужно `phi`: предшественник ветви - блок, которым она **закончилась**, а
    /// не тот, которым началась, и различаются они, как только внутри ветви
    /// встал ещё один разбор.
    block: String,
}

impl<'a> Builder<'a> {
    fn new(
        program: &'a Program,
        function: &'a Function,
        result: &'static str,
        metadata: &'a mut Metadata,
        dwarf: Option<&'a Dwarf>,
        scope: Option<Scope>,
    ) -> Self {
        let mut reprs = HashMap::new();
        let mut operands = HashMap::new();
        for binding in function.captured.iter().chain(&function.parameters) {
            reprs.insert(binding.local, binding.fact.repr);
        }
        // Значение получают только **дожившие** (§3.3): стёртого в рантайме нет
        // вовсе, и в сигнатуре его нет тоже. Упомяни его тело - и отказ придёт
        // названным, а не неопределённым именем в `.ll`.
        for binding in function.live_captured().chain(function.live_parameters()) {
            operands.insert(binding.local, format!("%v{}", binding.local.0));
        }
        collect(&function.body, &mut reprs);
        Self {
            program,
            function,
            result,
            reprs,
            operands,
            head: String::new(),
            body: String::new(),
            metadata,
            dwarf,
            scope,
            frames: 0,
            temps: 0,
            matches: 0,
            block: "entry".to_owned(),
        }
    }

    /// Кладёт параметры в кадр, чтобы отладчик их видел.
    ///
    /// Ячейка **сверх** регистра, а не вместо него: вычисление по-прежнему идёт
    /// по `%vN`, а ячейка существует ровно ради `llvm.dbg.declare`. Переписывать
    /// тело на чтение из ячейки незачем - параметр в Adamas не переприсваивается,
    /// и записанное в прологе остаётся верным до конца.
    ///
    /// Цена названа: на `-O0` это лишняя запись в кадр на параметр. На `-O2`
    /// ячейка исчезает вместе с `mem2reg`, а вместе с ней и наблюдаемость - тот
    /// же размен, что у всякого компилятора.
    fn parameters_in_frame(&mut self, function: &Function) {
        if self.scope.is_none() {
            return;
        }
        for (at, binding) in function.live_parameters().enumerate() {
            let Some(ty) = slot(binding.fact.repr) else {
                continue;
            };
            let cell = self.frame_cell(ty);
            let prologue = self.synthetic();
            self.instruction(
                &format!("store {ty} %v{}, ptr {cell}", binding.local.0),
                prologue.clone(),
            );
            let argument = u32::try_from(at + 1).unwrap_or(u32::MAX);
            self.declare(
                &binding.name,
                binding.fact.repr,
                Some(argument),
                &cell,
                prologue,
            );
        }
    }

    /// Заводит ячейку кадра и отдаёт её имя.
    fn frame_cell(&mut self, ty: &str) -> String {
        let cell = format!("%f{}", self.frames);
        self.frames += 1;
        let _ = writeln!(self.head, "  {cell} = alloca {ty}");
        cell
    }

    /// Объявляет отладчику переменную, лежащую в названной ячейке.
    ///
    /// `llvm.dbg.declare`, а не `llvm.dbg.value`: восемнадцатая версия печатает
    /// отладочные записи вызовами интринсиков, двадцать первая - записями
    /// `#dbg_declare`, и **общий** у них ровно вызов: новая читает старую форму
    /// и поднимает её, старая новую не читает вовсе. Проверено прогоном обеих
    /// цепочек, а не таблицей совместимости.
    fn declare(&mut self, name: &str, repr: Repr, argument: Option<u32>, cell: &str, notes: Notes) {
        let (Some(dwarf), Some(scope)) = (self.dwarf, self.scope.clone()) else {
            return;
        };
        let ty = Dwarf::ty(self.metadata, repr);
        let arg = argument.map_or_else(String::new, |at| format!("arg: {at}, "));
        let variable = self.metadata.node(&format!(
            "!DILocalVariable(name: \"{}\", {arg}scope: {}, file: {}, line: {}, type: {ty})",
            escaped_name(name),
            scope.subprogram,
            dwarf.file,
            scope.at.line
        ));
        self.instruction(
            &format!(
                "call void @llvm.dbg.declare(metadata ptr {cell}, \
                 metadata {variable}, metadata !DIExpression())"
            ),
            notes,
        );
    }

    /// Кладёт связывание `let` в кадр - ради отладчика, как и параметры.
    ///
    /// Ячейка в `entry`, запись здесь: до этой записи значения ещё нет, и
    /// отладчик, остановленный раньше, покажет мусор. Так же ведёт себя всякая
    /// неинициализированная переменная на `-O0`, и врать об этом нечем.
    fn in_frame(&mut self, binding: &Binding, value: &str) {
        if self.scope.is_none() || !binding.fact.present {
            return;
        }
        let Some(ty) = slot(binding.fact.repr) else {
            return;
        };
        let cell = self.frame_cell(ty);
        self.instruction(&format!("store {ty} {value}, ptr {cell}"), self.here());
        self.declare(&binding.name, binding.fact.repr, None, &cell, self.here());
    }

    /// Локация ненаписанного кода: строка нуль. Пусто без отладочной
    /// информации.
    ///
    /// Не путать с `Builder::prologue` трека D: тот снимает узлы-приставки, а
    /// это - подпись инструкций, которых в исходнике нет.
    fn synthetic(&self) -> Notes {
        match &self.scope {
            Some(scope) => Notes::none().and("dbg", &scope.prologue),
            None => Notes::none(),
        }
    }

    /// Свежее временное имя.
    fn temp(&mut self) -> String {
        let name = format!("%t{}", self.temps);
        self.temps += 1;
        name
    }

    /// Единственная точка печати инструкции.
    ///
    /// Одна на весь эмиттер намеренно: форма суффикса метаданных живёт здесь, а
    /// не в двух десятках мест печати. Сами метаданные приходят **аргументом** -
    /// почему, сказано у [`Notes`].
    fn instruction(&mut self, text: &str, notes: Notes) {
        let _ = writeln!(self.body, "  {text}{}", notes.suffix());
    }

    /// Метаданные, которые несёт всякая инструкция тела.
    ///
    /// Сегодня это `!dbg` - строка определения. Своё дописывается поверх:
    /// `self.here().and("noalias", "!7")`.
    fn here(&self) -> Notes {
        match &self.scope {
            Some(scope) => Notes::none().and("dbg", &scope.here),
            None => Notes::none(),
        }
    }

    /// Начинает новый блок.
    fn start(&mut self, label: &str) {
        let _ = writeln!(self.body, "\n{label}:");
        label.clone_into(&mut self.block);
    }

    /// Отказ, названный этой функцией.
    fn node(&self, node: &'static str) -> LlvmError {
        LlvmError::Node {
            function: self.function.name.clone(),
            node,
        }
    }

    /// Текст, которым связывание попадает в инструкцию.
    fn operand(&self, local: LocalId) -> Result<String, LlvmError> {
        self.operands
            .get(&local)
            .cloned()
            .ok_or_else(|| self.node("связывание без значения"))
    }

    /// Представление значения выражения.
    fn shape(&self, expr: &Expr) -> Repr {
        match expr {
            Expr::Local(local) => self.reprs.get(local).copied().unwrap_or(Repr::Boxed),
            Expr::Literal { ty, .. } | Expr::Primitive { ty, .. } => Repr::Flat(*ty),
            Expr::Call { function, .. } => self.program.functions[function.0].result,
            Expr::Bind { body, .. } | Expr::Dup { body, .. } | Expr::Drop { body, .. } => {
                self.shape(body)
            }
            Expr::Match { arms, .. } => arms
                .first()
                .map_or(Repr::Boxed, |arm| self.shape(&arm.body)),
            // Ответ сравнения - конструктор `Bool` (§4.3): аргументы плоские,
            // ответ указательный. Прочее срез отвергает, и представление его
            // здесь не спрашивается.
            _ => Repr::Boxed,
        }
    }

    /// Тип регистра, в котором лежит значение выражения.
    fn typed(&self, expr: &Expr) -> Result<&'static str, LlvmError> {
        let repr = self.shape(expr);
        slot(repr).ok_or_else(|| LlvmError::Shape {
            function: self.function.name.clone(),
            place: "промежуточное значение".to_owned(),
            shape: describe(repr),
        })
    }

    /// Печатает узлы-приставки до упора и отдаёт то, что под ними.
    ///
    /// Приставка - `let`, `dup` и `drop`: узел печатает голову и передаёт
    /// позицию телу. Одна печать на **обе** позиции намеренно: разъедься они -
    /// хвостовой путь потерял бы счётчик молча, а расхождение вылезло бы
    /// течью, а не отказом.
    ///
    /// Отсюда же и то, что хвост считается контекстом, а не полем узла: дроп,
    /// вставленный Perceus **после** вызова, попадает в `value` и хвоста не
    /// получает; вставленный до - остаётся здесь, и хвост уезжает дальше в
    /// тело. Ни одного признака в представлении для этого не нужно.
    ///
    /// Цикл, а не рекурсия: цепочка `let` в понижении бывает длинной, и
    /// рекурсия по ней клала бы стек компилятора на ровном месте.
    fn prologue<'e>(&mut self, expr: &'e Expr) -> Result<&'e Expr, LlvmError> {
        let mut at = expr;
        loop {
            match at {
                Expr::Bind {
                    binding,
                    value,
                    body,
                } => {
                    let computed = self.value(value)?;
                    let _ = writeln!(self.body, "  ; {computed} - {}", binding.name);
                    self.in_frame(binding, &computed);
                    self.operands.insert(binding.local, computed);
                    at = body;
                }
                Expr::Dup { local, body } => {
                    let value = self.operand(*local)?;
                    let name = self.temp();
                    self.instruction(
                        &format!("{name} = call ptr @adamas_dup(ptr {value})"),
                        self.here(),
                    );
                    at = body;
                }
                Expr::Drop {
                    local,
                    salvage,
                    body,
                } => {
                    if salvage.collapses() {
                        return Err(self.node("схлопнутый дроп разобранного"));
                    }
                    let value = self.operand(*local)?;
                    self.instruction(
                        &format!("call void @adamas_drop(ptr {value}, ptr @adamas_release_none)"),
                        self.here(),
                    );
                    at = body;
                }
                other => return Ok(other),
            }
        }
    }

    /// Эмитит выражение в **возвратной** позиции: блок кончается `ret`.
    ///
    /// Хвостовой вызов печатается `musttail` с `ret` следом - этого и требует
    /// LLVM, - а разбор раздаёт возвратную позицию своим ветвям, вместо того
    /// чтобы сводить их `phi` (трек D). `ret` печатает поэтому обход, а не
    /// вызывающий: у разбора их столько, сколько ветвей.
    fn tail(&mut self, expr: &Expr) -> Result<(), LlvmError> {
        let expr = self.prologue(expr)?;
        match expr {
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis_tail(scrutinee, arms),
            Expr::Call {
                function,
                arguments,
            } => {
                // `musttail` требует, чтобы `ret` вернул **значение вызова**, а
                // значит чтобы типы сошлись. У нашего понижения они сходятся по
                // построению - ответ функции и есть ответ хвостового вызова, -
                // но полагаться на это нечем: разойдись они, verifier отверг бы
                // модуль целиком. Обычный вызов в этом случае честнее отказа.
                let agreed = slot(self.program.functions[function.0].result)
                    .is_some_and(|it| it == self.result);
                let sort = if agreed { Tail::Must } else { Tail::Plain };
                let name = self.call(*function, arguments, sort)?;
                let result = self.result;
                self.instruction(&format!("ret {result} {name}"), self.here());
                Ok(())
            }
            other => {
                let value = self.value(other)?;
                let result = self.result;
                self.instruction(&format!("ret {result} {value}"), self.here());
                Ok(())
            }
        }
    }

    /// Эмитит выражение и отдаёт операнд, в котором лежит его значение.
    fn value(&mut self, expr: &Expr) -> Result<String, LlvmError> {
        let expr = self.prologue(expr)?;
        match expr {
            Expr::Local(local) => self.operand(*local),
            Expr::Literal { ty, bits } => self.literal(*ty, *bits),
            Expr::Primitive {
                op,
                ty,
                left,
                right,
            } => self.arithmetic(*op, *ty, left, right),
            Expr::Compare {
                op,
                ty,
                left,
                right,
                yes,
                no,
            } => self.comparison(*op, *ty, left, right, (yes.0, no.0)),
            Expr::Call {
                function,
                arguments,
            } => self.call(*function, arguments, Tail::Plain),
            // Приставки сняты `prologue` выше, и досюда узел не
            // доезжает. Ветвь стоит ради исчерпывающего разбора: пропади она,
            // новый узел-приставка ушёл бы в тихий отказ вместо ошибки сборки.
            Expr::Bind { .. } | Expr::Dup { .. } | Expr::Drop { .. } => {
                Err(self.node("узел-приставка после снятия приставок"))
            }
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis(scrutinee, arms),
            Expr::Erased => Err(self.node("стёртая позиция значением")),
            Expr::Construct { .. } | Expr::ConstructClosure { .. } => Err(self.node("конструктор")),
            Expr::Closure { .. } | Expr::Apply { .. } => Err(self.node("замыкание")),
            Expr::Reclaim { .. } => Err(self.node("придержанная ячейка")),
            Expr::Pack { .. } | Expr::Unpack { .. } => Err(self.node("плотный агрегат")),
            Expr::Layout { .. } | Expr::LayoutField { .. } => Err(self.node("дескриптор укладки")),
            Expr::ArrayNew { .. } | Expr::ArraySet { .. } | Expr::ArrayIndex { .. } => {
                Err(self.node("массив"))
            }
            Expr::RegionNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => Err(self.node("регион")),
            Expr::Handle { .. } | Expr::Perform { .. } | Expr::Mask { .. } => {
                Err(self.node("эффект"))
            }
            Expr::Resume { .. } => Err(self.node("резумпция")),
            Expr::Closing { .. } => Err(self.node("выход из scope с ресурсом")),
            Expr::Nursery { .. } | Expr::Fiber { .. } | Expr::Cancel { .. } => {
                Err(self.node("питомник"))
            }
        }
    }

    /// Литерал: биты, обрезанные по ширине типа (§4.3).
    ///
    /// Беззнаковое десятичное: LLVM принимает всё, что укладывается в ширину, а
    /// биты в представлении уже обрезаны понижением.
    fn literal(&mut self, ty: PrimTy, bits: u64) -> Result<String, LlvmError> {
        self.numeric(ty)?;
        Ok(bits.to_string())
    }

    /// Отказ, если тип плавающий: это шов трека F, а не забытая ветвь.
    fn numeric(&self, ty: PrimTy) -> Result<(), LlvmError> {
        if ty.floating() {
            return Err(LlvmError::Real {
                function: self.function.name.clone(),
                ty: ty.name(),
            });
        }
        Ok(())
    }

    /// Арифметика: `add`, `sub`, `mul` без `nsw` и `nuw`.
    ///
    /// Отсутствие флагов - не забывчивость: §4.3 требует **заворачивания**, то
    /// есть определённого поведения, а `nsw`/`nuw` объявили бы переполнение
    /// невозможным и отдали бы его оптимизатору как `poison`.
    fn arithmetic(
        &mut self,
        op: PrimOp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
    ) -> Result<String, LlvmError> {
        self.numeric(ty)?;
        let opcode = match op {
            PrimOp::Add => "add",
            PrimOp::Sub => "sub",
            PrimOp::Mul => "mul",
        };
        let left = self.value(left)?;
        let right = self.value(right)?;
        Ok(self.binary(opcode, "", machine(ty), &left, &right))
    }

    /// Двуместная инструкция.
    ///
    /// `flags` - поле трека F: `fadd` и `fmul` получат там запрет контракции, и
    /// запрет этот обязан стоять на **инструкции**, а не на ключах сборки.
    fn binary(&mut self, opcode: &str, flags: &str, ty: &str, left: &str, right: &str) -> String {
        let spaced = if flags.is_empty() {
            String::new()
        } else {
            format!("{flags} ")
        };
        let name = self.temp();
        self.instruction(
            &format!("{name} = {opcode} {spaced}{ty} {left}, {right}"),
            self.here(),
        );
        name
    }

    /// Сравнение: `icmp`, затем нульарный конструктор `Bool` (§4.3).
    ///
    /// Тег выбирается `select`'ом, а значение строит **рантайм**
    /// (`adamas_con0`): непосредственное представление принадлежит ему, и
    /// вторая его запись здесь разъехалась бы с первой молча.
    fn comparison(
        &mut self,
        op: PrimCmp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
        verdict: (u16, u16),
    ) -> Result<String, LlvmError> {
        self.numeric(ty)?;
        let predicate = match (op, ty.signed()) {
            (PrimCmp::Eq, _) => "eq",
            (PrimCmp::Ne, _) => "ne",
            (PrimCmp::Lt, true) => "slt",
            (PrimCmp::Lt, false) => "ult",
            (PrimCmp::Le, true) => "sle",
            (PrimCmp::Le, false) => "ule",
            (PrimCmp::Gt, true) => "sgt",
            (PrimCmp::Gt, false) => "ugt",
            (PrimCmp::Ge, true) => "sge",
            (PrimCmp::Ge, false) => "uge",
        };
        let left = self.value(left)?;
        let right = self.value(right)?;
        let verdicted = self.binary("icmp", predicate, machine(ty), &left, &right);
        let (yes, no) = verdict;
        let tag = self.temp();
        self.instruction(
            &format!("{tag} = select i1 {verdicted}, i16 {yes}, i16 {no}"),
            self.here(),
        );
        let name = self.temp();
        self.instruction(
            &format!("{name} = call ptr @adamas_con0(i16 {tag})"),
            self.here(),
        );
        Ok(name)
    }

    /// Прямой вызов: стёртые позиции в вызов не идут.
    ///
    /// `sort` - шов трека D: [`Tail::Must`] печатает `musttail`, и следом за
    /// такой инструкцией обязан идти `ret` - его ставит [`Self::tail`].
    /// Соглашение [`CONVENTION`] печатается **всегда**, и не для красоты: оно
    /// объявлено у определения, и вызов, не назвавший его, звал бы по другому.
    fn call(
        &mut self,
        function: FuncId,
        arguments: &[Expr],
        sort: Tail,
    ) -> Result<String, LlvmError> {
        let called = &self.program.functions[function.0];
        if called.form == Form::Detached {
            return Err(LlvmError::Detached {
                function: called.name.clone(),
            });
        }
        let result = slot(called.result).ok_or_else(|| LlvmError::Shape {
            function: self.function.name.clone(),
            place: format!("ответ `{}`", called.name),
            shape: describe(called.result),
        })?;
        let present: Vec<usize> = called
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let mut given = Vec::new();
        for position in present {
            let Some(argument) = arguments.get(position) else {
                continue;
            };
            let ty = self.typed(argument)?;
            let operand = self.value(argument)?;
            given.push(format!("{ty} {operand}"));
        }
        let name = self.temp();
        self.instruction(
            &format!(
                "{name} = {}call {CONVENTION} {result} @fn_{}({})",
                sort.prefix(),
                function.0,
                given.join(", ")
            ),
            self.here(),
        );
        Ok(name)
    }

    /// Голова разбора: отказ по полям, тег, `switch` и блок обрыва.
    ///
    /// Полей ветвь не связывает: за полем стоит объект кучи, а срез его не
    /// читает. Нульарный конструктор непосредствен, и тег у него - он сам.
    ///
    /// Одна на обе позиции намеренно: разъедься головы - хвостовой разбор
    /// поехал бы по другому тегу, и заметить это было бы нечем. Отдаёт номер
    /// разбора и метки ветвей; ветви печатает вызывающий, потому что позиция у
    /// них его.
    fn dispatch(
        &mut self,
        scrutinee: &Expr,
        arms: &[Arm],
    ) -> Result<(u32, Vec<String>), LlvmError> {
        if arms.is_empty() {
            return Err(self.node("разбор пустого типа"));
        }
        for arm in arms {
            if arm.fields.iter().any(|field| field.fact.present) {
                return Err(LlvmError::Fields {
                    function: self.function.name.clone(),
                    constructor: self.program.constructors[usize::from(arm.constructor.0)]
                        .name
                        .clone(),
                });
            }
        }

        let scrutinised = self.value(scrutinee)?;
        let at = self.matches;
        self.matches += 1;
        let tag = self.temp();
        self.instruction(
            &format!("{tag} = call i16 @adamas_tag(ptr {scrutinised})"),
            self.here(),
        );

        let labels: Vec<String> = (0..arms.len()).map(|it| format!("m{at}.a{it}")).collect();
        let fail = format!("m{at}.fail");
        let cases: Vec<String> = arms
            .iter()
            .zip(&labels)
            .map(|(arm, label)| format!("i16 {}, label %{label}", arm.constructor.0))
            .collect();
        self.instruction(
            &format!("switch i16 {tag}, label %{fail} [ {} ]", cases.join(" ")),
            self.here(),
        );

        self.start(&fail);
        self.instruction(
            &format!("call void @adamas_fail(ptr {TAG_MESSAGE})"),
            self.here(),
        );
        self.instruction("unreachable", self.here());
        Ok((at, labels))
    }

    /// Разбор значением: ветви сводятся `phi` в блоке стыковки.
    fn analysis(&mut self, scrutinee: &Expr, arms: &[Arm]) -> Result<String, LlvmError> {
        let (at, labels) = self.dispatch(scrutinee, arms)?;
        let answer = self.typed(&arms[0].body)?;
        let join = format!("m{at}.join");

        let mut incoming = Vec::new();
        for (arm, label) in arms.iter().zip(&labels) {
            self.start(label);
            let value = self.value(&arm.body)?;
            // Предшественник - блок, которым ветвь **закончилась**: вложенный
            // разбор внутри неё сменил бы его.
            incoming.push(format!("[ {value}, %{} ]", self.block));
            self.instruction(&format!("br label %{join}"), self.here());
        }

        self.start(&join);
        let name = self.temp();
        self.instruction(
            &format!("{name} = phi {answer} {}", incoming.join(", ")),
            self.here(),
        );
        Ok(name)
    }

    /// Разбор в хвостовой позиции: ветвь возвращает сама, `phi` не строится.
    ///
    /// Так и снимается препятствие трека D. `musttail` требует `ret` **в том же
    /// блоке**, а ветвь, кончающаяся `br label %join`, его не даёт; блока
    /// стыковки здесь нет вовсе, и хвост уезжает в каждую ветвь целым.
    fn analysis_tail(&mut self, scrutinee: &Expr, arms: &[Arm]) -> Result<(), LlvmError> {
        let (_, labels) = self.dispatch(scrutinee, arms)?;
        for (arm, label) in arms.iter().zip(&labels) {
            self.start(label);
            self.tail(&arm.body)?;
        }
        Ok(())
    }
}

/// Представления связываний, заведённых телом.
fn collect(expr: &Expr, found: &mut HashMap<LocalId, Repr>) {
    match expr {
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
        _ => {}
    }
    for child in expr.children() {
        collect(child, found);
    }
}

/// Спутник на C: печать ответа и точка входа.
///
/// `flat.c` и `main.c` берутся **дословно** теми же `include_str!`, какими их
/// берёт C-бэкенд: печать у двух бэкендов обязана быть одной, иначе «печатает
/// то же» держалось бы на совпадении двух печатей, а не на их тождестве.
fn support(answer: PrimTy) -> String {
    let mut out = String::new();
    out.push_str(concat!(
        "/* Порождено понижением Adamas: спутник `.ll`.\n",
        " *\n",
        " * Программу считает `.ll` целиком; здесь только печать её ответа и\n",
        " * точка входа. `flat.c` и `main.c` - те же файлы, что собирает\n",
        " * C-бэкенд, взятые дословно.\n",
        " */\n",
        "\n",
        "#include \"adamas.h\"\n",
        "\n",
        "#include <stdio.h>\n",
        "\n",
    ));
    out.push_str(crate::emit_c::FLAT);
    out.push('\n');
    let ctype = crate::emit_c::scalar(Repr::Flat(answer));
    out.push_str("/* Ответ считает `.ll`, печатает `main.c` ниже. */\n");
    let _ = writeln!(out, "{ctype} {ENTRY_SYMBOL}(void);");
    let _ = writeln!(out, "#define ADAMAS_ENTRY {ENTRY_SYMBOL}");
    let _ = writeln!(
        out,
        "#define ADAMAS_ANSWER_FLAT adamas_word_{}",
        answer.name()
    );
    let _ = writeln!(out, "#define ADAMAS_ANSWER_TYPE {ctype}");
    let _ = writeln!(
        out,
        "#define ADAMAS_ANSWER_KIND {}u",
        crate::emit_c::kind(answer)
    );
    out.push('\n');
    out.push_str(crate::emit_c::ENTRY);
    out
}
