//! Объявления C-рантайма. Смысл каждой функции - в `include/adamas.h`.
//!
//! Модуль держит ABI дословно и ничего к нему не добавляет: имя, аргументы,
//! возврат. Расхождение с заголовком ловится линковкой, а не чтением.

// Рантайм - ровно тот случай, ради которого `unsafe_code` объявлен `deny`, а не
// `forbid` (корневой `Cargo.toml`): Perceus и FFI без него не пишутся.
#![allow(unsafe_code)]

use core::ffi::c_int;

/// Объект кучи Perceus. Непрозрачен: форму задаёт заголовок.
#[derive(Debug)]
#[repr(C)]
pub struct Object {
    _opaque: [u8; 0],
}

/// Кадр отложенной работы.
#[derive(Debug)]
#[repr(C)]
pub struct Frame {
    _opaque: [u8; 0],
}

/// Сегмент продолжения.
#[derive(Debug)]
#[repr(C)]
pub struct Segment {
    _opaque: [u8; 0],
}

/// Вектор evidence.
#[derive(Debug)]
#[repr(C)]
pub struct Evidence {
    _opaque: [u8; 0],
}

/// Слово-значение: непосредственное при младшем бите 1, иначе объект.
pub type Value = *mut Object;

/// Дроп детей объекта; блок не освобождает.
pub type Release = Option<unsafe extern "C" fn(Value)>;

/// Код замыкания: сам себе `userdata`, вектор evidence, последний аргумент.
pub type Code = Option<unsafe extern "C" fn(Value, *const Evidence, Value) -> Value>;

/// Чем занять место, когда придёт значение.
pub type FrameCode = Option<unsafe extern "C" fn(*mut Frame, Value) -> Value>;

/// Дроп среды кадра; блок не освобождает.
pub type FrameRelease = Option<unsafe extern "C" fn(*mut Frame)>;

/// Стек продолжения второй формы понижения.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Kont {
    /// Вершина: ближайшая работа.
    pub top: *mut Frame,
    /// Кадров в стеке.
    pub depth: usize,
}

/// Обычная отложенная работа.
pub const MARK_PLAIN: u16 = 0;
/// Хендлер: на нём режется сегмент.
pub const MARK_HANDLER: u16 = 1;
/// Маска: пропускает один подходящий хендлер.
pub const MARK_MASKING: u16 = 2;
/// Раскручиваемый хендлер: метка на время деструкторов.
pub const MARK_SUPPRESSING: u16 = 3;
/// Питомник файберов.
pub const MARK_NURSERY: u16 = 4;
/// Scope, держащий ресурс: деструктор в слоте 0.
pub const MARK_CLOSING: u16 = 5;

/// Хендлера метки нет вовсе.
pub const LOOKUP_MISSING: c_int = 0;
/// Нашёлся живой хендлер.
pub const LOOKUP_HANDLER: c_int = 1;
/// Нашёлся подавленный: операция обрывает свой деструктор.
pub const LOOKUP_SUPPRESSED: c_int = 2;

/// Тег замыкания в заголовке.
pub const TAG_CLOSURE: u16 = 0xFFFF;
/// Тег вектора evidence.
pub const TAG_EVIDENCE: u16 = 0xFFFE;
/// Тег сегмента продолжения.
pub const TAG_SEGMENT: u16 = 0xFFFD;

unsafe extern "C" {
    /// Сколько блоков выдано с начала потока.
    pub fn adamas_stat_allocated() -> usize;
    /// Сколько блоков живо сейчас.
    pub fn adamas_stat_live() -> usize;
    /// Обнуляет счётчики потока.
    pub fn adamas_stat_reset();

    /// Непосредственное ли значение.
    pub fn adamas_is_imm(value: Value) -> c_int;
    /// Машинное целое как значение.
    pub fn adamas_imm(number: isize) -> Value;
    /// Число из непосредственного значения.
    pub fn adamas_imm_get(value: Value) -> isize;
    /// Нульарный конструктор.
    pub fn adamas_con0(tag: u16) -> Value;
    /// Значение `()`.
    pub fn adamas_unit() -> Value;

    /// Объект под `fields` полей.
    pub fn adamas_alloc(tag: u16, fields: usize) -> Value;
    /// Освобождает объект, детей не дропая.
    pub fn adamas_free(value: Value);
    /// Номер конструктора.
    pub fn adamas_tag(value: Value) -> u16;
    /// Счётчик лишних ссылок.
    pub fn adamas_rc(value: Value) -> u32;
    /// Берёт лишнюю ссылку.
    pub fn adamas_dup(value: Value) -> Value;
    /// Объект без лишних ссылок.
    pub fn adamas_is_unique(value: Value) -> c_int;
    /// Отдаёт ссылку; на последней зовёт `release` и освобождает блок.
    pub fn adamas_drop(value: Value, release: Release);
    /// Дроп, отдающий блок под переиспользование.
    pub fn adamas_drop_reuse(value: Value, release: Release) -> Value;
    /// Занимает блок под конструктор либо аллоцирует.
    pub fn adamas_reuse(block: Value, tag: u16, fields: usize) -> Value;
    /// Поле объекта.
    pub fn adamas_field(value: Value, index: usize) -> Value;
    /// Записывает поле объекта.
    pub fn adamas_set_field(value: Value, index: usize, field: Value);

    /// Пустой вектор evidence.
    pub fn adamas_evidence_empty() -> *mut Evidence;
    /// Вектор родителя плюс запись о хендлере метки.
    pub fn adamas_evidence_extend(
        parent: *const Evidence,
        label: u32,
        handler: *mut Frame,
    ) -> *mut Evidence;
    /// Записей в векторе.
    pub fn adamas_evidence_count(evidence: *const Evidence) -> usize;
    /// Кадр хендлера по статической позиции.
    pub fn adamas_evidence_at(evidence: *const Evidence, index: usize) -> *mut Frame;
    /// Метка записи по позиции.
    pub fn adamas_evidence_label_at(evidence: *const Evidence, index: usize) -> u32;
    /// Ближайший хендлер метки, пропустив `skip` подходящих.
    /// Ближайшая запись метки: вердикт трёхзначный, кадр идёт в `handler`.
    pub fn adamas_evidence_lookup(
        evidence: *const Evidence,
        label: u32,
        skip: usize,
        handler: *mut *mut Frame,
    ) -> c_int;
    /// Копия вектора со своим счётчиком.
    pub fn adamas_evidence_copy(evidence: *const Evidence) -> *mut Evidence;
    /// Помечает подавленной запись этого кадра-хендлера.
    pub fn adamas_evidence_suppress(evidence: *mut Evidence, handler: *const Frame);
    /// Берёт лишнюю ссылку на вектор.
    pub fn adamas_evidence_dup(evidence: *mut Evidence) -> *mut Evidence;
    /// Отдаёт ссылку на вектор.
    pub fn adamas_evidence_drop(evidence: *mut Evidence);

    /// Замыкание на `arity` аргументов с `captured` слотами среды.
    pub fn adamas_closure(code: Code, release: Release, arity: u32, captured: u32) -> Value;
    /// Записывает слот замыкания.
    pub fn adamas_closure_set(closure: Value, index: usize, field: Value);
    /// Слот замыкания.
    pub fn adamas_closure_get(closure: Value, index: usize) -> Value;
    /// Указатель на код замыкания.
    pub fn adamas_closure_code(closure: Value) -> Code;
    /// Сколько аргументов замыкание ещё ждёт.
    pub fn adamas_closure_missing(closure: Value) -> u32;
    /// Дроп замыкания как `Release`.
    pub fn adamas_closure_release(closure: Value);
    /// Применение: аргумент берётся владением.
    pub fn adamas_apply(closure: Value, evidence: *const Evidence, argument: Value) -> Value;

    /// Пустой стек.
    pub fn adamas_kont_init(kont: *mut Kont);
    /// Кладёт кадр на вершину и отдаёт его.
    pub fn adamas_kont_push(
        kont: *mut Kont,
        mark: u16,
        label: u32,
        code: FrameCode,
        release: FrameRelease,
        fields: usize,
        evidence: *mut Evidence,
    ) -> *mut Frame;
    /// Среда кадра.
    pub fn adamas_frame_env(frame: *mut Frame) -> *mut Value;
    /// Слотов в среде кадра.
    pub fn adamas_frame_fields(frame: *const Frame) -> usize;
    /// Метка кадра.
    pub fn adamas_frame_mark(frame: *const Frame) -> u16;
    /// Метка эффекта у меченого кадра.
    pub fn adamas_frame_label(frame: *const Frame) -> u32;
    /// Вектор evidence, действовавший на месте кадра.
    pub fn adamas_frame_evidence(frame: *mut Frame) -> *mut Evidence;
    /// Режет стек от вершины до кадра хендлера включительно.
    pub fn adamas_kont_cut(kont: *mut Kont, handler: *mut Frame) -> *mut Segment;
    /// Ставит сегмент обратно на вершину.
    pub fn adamas_kont_restore(kont: *mut Kont, segment: *mut Segment);
    /// Крутит стек, пока он не опустеет.
    pub fn adamas_kont_run(kont: *mut Kont, value: Value) -> Value;

    /// Кадров в сегменте.
    pub fn adamas_segment_depth(segment: *const Segment) -> usize;
    /// Нижний кадр сегмента.
    pub fn adamas_segment_base(segment: *mut Segment) -> *mut Frame;
    /// Копия сегмента: звенья свои, поля общие через `dup`.
    pub fn adamas_segment_copy(segment: *const Segment) -> *mut Segment;
    /// Раскрутка: деструкторы LIFO, затем освобождение.
    pub fn adamas_segment_unwind(segment: *mut Segment);
    /// Сегмент как значение.
    pub fn adamas_segment_value(segment: *mut Segment) -> Value;
    /// Значение как сегмент.
    pub fn adamas_segment_of(value: Value) -> *mut Segment;
    /// Дроп резумпции: последняя ссылка разматывает сегмент.
    pub fn adamas_resumption_drop(value: Value);
}
