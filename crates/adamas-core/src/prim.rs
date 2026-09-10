//! Примитивы: типы с машинным представлением и операции над ними (§4.3, §4.11).
//!
//! До этого модуля числа в языке были индуктивными: `Nat` - семейство, `42` -
//! сорок два конструктора, а `Flat` считал укладку от тега. §4.11 перечисляет
//! примитивы поимённо, и здесь они заведены как **узел ядра**, а не как
//! определения сигнатуры. Причина одна и измеримая: [`crate::eval::eval`]
//! сигнатуры не видит, поэтому сложение, спрятанное за именем, ей нечем было бы
//! посчитать - а считать его обязаны все три вычислителя одинаково.
//!
//! # Массив входит сюда же
//!
//! `Array n a` (§4.11) и три операции над ним - узел ядра по тому же доводу и
//! по тому же правилу имени. Довод: `arrayIndex` обязан **сводиться**, а
//! сведение примитивов живёт в [`crate::eval`], которая сигнатуры не видит;
//! имя, объявленное программой, потребовало бы второго правила счёта у машины,
//! а три вычислителя обязаны считать одинаково. Правило имени: `Array`,
//! `arrayNew`, `arraySet`, `arrayIndex` заняты языком - на имени стоит
//! **представление**, а не значение, и переопределяемое имя дало бы два
//! `Array` с разной укладкой.
//!
//! Имя `Vect` (§4.1, §4.11) при этом **не занято**: §4.1 пишет `data Vect` как
//! пользовательское объявление, и корпус пишет тоже
//! (`tests/golden/programs/vect.adamas`). Занять его значило бы отвергнуть оба.
//!
//! # Что взято
//!
//! Десять числовых типов из §4.11 и три операции. `Bool` и `Char` из того же
//! перечня **не** взяты: `Bool` в корпусе объявляется программой и уже плоский
//! тегом в байт, а литерала `Char` в поверхностном языке нет вовсе. Деления,
//! сравнений и преобразований между примитивами тоже нет - §4.3 их формы не
//! называет, а свидетель пишется без них.
//!
//! # Переполнение
//!
//! Целочисленные операции **заворачиваются** по ширине типа. §4.3 прямо не
//! говорит про переполнение, но требует от сгенерированного C ключ `-fwrapv`,
//! то есть определённое поведение вместо неопределённого; заворачивание - это
//! оно и есть, и оно же детерминировано на всех бэкендах.

use std::fmt;

/// Примитивный тип (§4.11).
///
/// Порядок перечисления - как в §4.11: знаковые, беззнаковые, плавающие.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {
    /// Знаковое целое в байт.
    Int8,
    /// Знаковое целое в два байта.
    Int16,
    /// Знаковое целое в четыре байта.
    Int32,
    /// Знаковое целое в восемь байт.
    Int64,
    /// Беззнаковое целое в байт.
    UInt8,
    /// Беззнаковое целое в два байта.
    UInt16,
    /// Беззнаковое целое в четыре байта.
    UInt32,
    /// Беззнаковое целое в восемь байт.
    UInt64,
    /// Плавающее одинарной точности.
    Float32,
    /// Плавающее двойной точности.
    Float64,
}

impl PrimTy {
    /// Все примитивные типы в порядке §4.11.
    pub const ALL: [Self; 10] = [
        Self::Int8,
        Self::Int16,
        Self::Int32,
        Self::Int64,
        Self::UInt8,
        Self::UInt16,
        Self::UInt32,
        Self::UInt64,
        Self::Float32,
        Self::Float64,
    ];

    /// Имя, которым тип пишется в программе.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Int8 => "Int8",
            Self::Int16 => "Int16",
            Self::Int32 => "Int32",
            Self::Int64 => "Int64",
            Self::UInt8 => "UInt8",
            Self::UInt16 => "UInt16",
            Self::UInt32 => "UInt32",
            Self::UInt64 => "UInt64",
            Self::Float32 => "Float32",
            Self::Float64 => "Float64",
        }
    }

    /// Тип по написанному имени.
    #[must_use]
    pub fn named(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|it| it.name() == text)
    }

    /// Ширина в байтах. Она же выравнивание: §4.9 отказался от
    /// пере-выравнивания, и `V4 Float32` имеет `align 4`, а не 16.
    #[must_use]
    pub const fn size(self) -> u32 {
        match self {
            Self::Int8 | Self::UInt8 => 1,
            Self::Int16 | Self::UInt16 => 2,
            Self::Int32 | Self::UInt32 | Self::Float32 => 4,
            Self::Int64 | Self::UInt64 | Self::Float64 => 8,
        }
    }

    /// Ширина в битах.
    const fn width(self) -> u32 {
        self.size() * 8
    }

    /// Плавающий ли это тип.
    #[must_use]
    pub const fn floating(self) -> bool {
        matches!(self, Self::Float32 | Self::Float64)
    }

    /// Знаковый ли это целый тип.
    #[must_use]
    pub const fn signed(self) -> bool {
        matches!(self, Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64)
    }

    /// Обрезает биты по ширине типа: хранимое представление всегда нормальное.
    const fn masked(self, bits: u64) -> u64 {
        match self.width() {
            64 => bits,
            width => bits & ((1u64 << width) - 1),
        }
    }

    /// Целое без знака в биты - если оно помещается.
    ///
    /// Знаковый тип принимает лишь то, что укладывается в его положительную
    /// половину: `128` не `Int8`, и промолчать об этом значило бы записать в
    /// программу `-128`.
    #[must_use]
    pub fn from_unsigned(self, value: u128) -> Option<u64> {
        if self.floating() {
            return None;
        }
        let limit = if self.signed() {
            (1u128 << (self.width() - 1)) - 1
        } else {
            (1u128 << self.width()) - 1
        };
        if value > limit {
            return None;
        }
        u64::try_from(value).ok().map(|bits| self.masked(bits))
    }

    /// Отрицательное целое в биты - если оно помещается.
    ///
    /// `magnitude` - модуль написанного числа. Беззнаковый тип отрицательного
    /// не принимает вовсе.
    #[must_use]
    pub fn from_negative(self, magnitude: u128) -> Option<u64> {
        if !self.signed() {
            return None;
        }
        let limit = 1u128 << (self.width() - 1);
        if magnitude > limit {
            return None;
        }
        let value = magnitude.wrapping_neg();
        u64::try_from(value & u128::from(u64::MAX))
            .ok()
            .map(|bits| self.masked(bits))
    }

    /// Плавающее число в биты. Целые типы дробного литерала не принимают.
    #[must_use]
    pub fn from_fraction(self, value: f64) -> Option<u64> {
        match self {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "сужение до Float32 - это и есть смысл записи `3.14 : Float32`"
            )]
            Self::Float32 => Some(u64::from((value as f32).to_bits())),
            Self::Float64 => Some(value.to_bits()),
            _ => None,
        }
    }

    /// Прочитанное значение знаковым целым.
    ///
    /// Биты приходят обрезанными - см. [`Prim::literal`]; второй обрезки здесь
    /// нет по той же причине, по какой её нет там.
    fn as_signed(self, bits: u64) -> i128 {
        let value = i128::from(bits);
        let top = 1i128 << (self.width() - 1);
        if self.signed() && value >= top {
            value - (top << 1)
        } else {
            value
        }
    }
}

impl fmt::Display for PrimTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Примитивная операция (§4.3).
///
/// Операторных классов здесь нет: класс обещает существование определения, а в
/// машинную инструкцию переводится содержание (§4.9 говорит то же про `Simd`).
/// Инстанс `Add Int64` пишется программой и телом своим берёт `addInt64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimOp {
    /// Сложение.
    Add,
    /// Вычитание.
    Sub,
    /// Умножение.
    Mul,
}

impl PrimOp {
    /// Все операции.
    pub const ALL: [Self; 3] = [Self::Add, Self::Sub, Self::Mul];

    /// Приставка имени: `add` у `addInt64`.
    #[must_use]
    pub const fn prefix(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
        }
    }

    /// Операция и тип по написанному имени: `mulFloat32`.
    #[must_use]
    pub fn named(text: &str) -> Option<(Self, PrimTy)> {
        Self::ALL.into_iter().find_map(|op| {
            text.strip_prefix(op.prefix())
                .and_then(PrimTy::named)
                .map(|ty| (op, ty))
        })
    }

    /// Считает операцию над двумя литералами одного типа.
    ///
    /// Целые заворачиваются по ширине типа; плавающие считаются в своей
    /// точности - `Float32` именно в одинарной, а не в двойной с округлением
    /// после.
    #[must_use]
    #[expect(
        clippy::cast_possible_truncation,
        reason = "биты `Float32` лежат в младшей половине слова по построению"
    )]
    pub fn fold(self, ty: PrimTy, left: u64, right: u64) -> u64 {
        match ty {
            PrimTy::Float32 => {
                let single = self.single(f32::from_bits(left as u32), f32::from_bits(right as u32));
                u64::from(single.to_bits())
            }
            PrimTy::Float64 => self
                .double(f64::from_bits(left), f64::from_bits(right))
                .to_bits(),
            _ => {
                let folded = match self {
                    Self::Add => left.wrapping_add(right),
                    Self::Sub => left.wrapping_sub(right),
                    Self::Mul => left.wrapping_mul(right),
                };
                ty.masked(folded)
            }
        }
    }

    /// Арифметика одинарной точности - именно в `f32`, а не в `f64` с
    /// округлением после: §4.3 обещает воспроизводимость основных операций, а
    /// двойное округление её ломает.
    fn single(self, left: f32, right: f32) -> f32 {
        match self {
            Self::Add => left + right,
            Self::Sub => left - right,
            Self::Mul => left * right,
        }
    }

    /// То же в двойной точности.
    fn double(self, left: f64, right: f64) -> f64 {
        match self {
            Self::Add => left + right,
            Self::Sub => left - right,
            Self::Mul => left * right,
        }
    }
}

impl fmt::Display for PrimOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.prefix())
    }
}

/// Операция над массивом (§4.11).
///
/// Массив в языке один, представления у него два, и различает их наличие
/// `Flat` у элемента. Операций три, и они ровно те, которых требует
/// мутабельный `Array` §4.11: завести, переписать ячейку, прочесть ячейку.
///
/// `arraySet` **функционален по семантике и переписывает по исполнению**:
/// значение он отдаёт новое, а перепишет ли он прежний блок, решает счётчик
/// ссылок в рантайме (`rc == 0`, §5.1). Это тот же договор, что у reuse, и
/// другого способа выразить `unique data` §3.3 у понижения нет (§10 вопрос
/// 149: кратность про потребление, уникальность про производство).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArrayOp {
    /// `arrayNew n x` - массив длины `n`, все ячейки заняты `x`.
    New,
    /// `arraySet xs i x` - тот же массив с переписанной ячейкой `i`.
    Set,
    /// `arrayIndex xs i` - значение ячейки `i`.
    Index,
}

impl ArrayOp {
    /// Все операции.
    pub const ALL: [Self; 3] = [Self::New, Self::Set, Self::Index];

    /// Имя, которым операция пишется в программе.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::New => "arrayNew",
            Self::Set => "arraySet",
            Self::Index => "arrayIndex",
        }
    }

    /// Операция по написанному имени.
    #[must_use]
    pub fn named(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|it| it.name() == text)
    }
}

impl fmt::Display for ArrayOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Операция региона (§3.6).
///
/// Регион здесь - **представление**, а не типовая сторона: `Alloc r`, `Ref r a`
/// и `withRegion` объявляются программой и стоят на эффектах (трек B). Ниже них
/// лежит то, что §3.6 называет «primitive allocator-функции, привязанные к
/// runtime backend'у», и вот они.
///
/// # Почему узел ядра, а не имя сигнатуры
///
/// Довод тот же, что у массива, и он тот же проверяемый: чтение обязано
/// **сводиться**, а сведение живёт в [`crate::eval`], которая сигнатуры не
/// видит. Второй довод сильнее: смещение внутри блока считается по укладке
/// нагрузки, и считать его обязаны все три вычислителя одинаково.
///
/// # Блок один, операций пять
///
/// `AllocStrategy` §3.6 называет три метода - `new`, `alloc`, `deallocate`, - а
/// эффект `Alloc r` ещё три - `allocIn`, `read`, `write`. Здесь их пять, и
/// расхождение с обоими перечнями объяснимо построчно.
///
/// `alloc` и `allocIn` слиты в [`Self::Alloc`]: `alloc : Block -> Nat -> Ptr`
/// отдаёт хендл **и** двигает блок, а ядро чисто - две вещи разом операция не
/// отдаёт. Слитая форма заодно снимает возможность соврать: размер нагрузки
/// приходит не числом от вызывающего, а укладкой её типа.
///
/// Хендл поэтому берётся у блока следом - [`Self::Last`]. Это тот же `Ptr`,
/// что §3.6 возвращает из `alloc`, только спрошенный после, а не отданный
/// вместе.
///
/// `deallocate` операцией **не является**: блок есть объект кучи Perceus, и
/// освобождает его дроп - одним `free` на всю область, как §3.6 и требует
/// («освобождение одно на всю область»). Отдельная операция позволила бы
/// освободить живой регион.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegionOp {
    /// `regionNew` - пустой регион. `AllocStrategy.new` (§3.6).
    New,
    /// `regionAlloc r x` - тот же регион, в конце которого лежит `x`.
    Alloc,
    /// `regionLast r` - хендл последней аллокации.
    Last,
    /// `regionRead r p` - значение, лежащее по хендлу `p`.
    Read,
    /// `regionWrite r p x` - тот же регион с переписанным местом `p`.
    Write,
}

impl RegionOp {
    /// Все операции.
    pub const ALL: [Self; 5] = [Self::New, Self::Alloc, Self::Last, Self::Read, Self::Write];

    /// Имя, которым операция пишется в программе.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::New => "regionNew",
            Self::Alloc => "regionAlloc",
            Self::Last => "regionLast",
            Self::Read => "regionRead",
            Self::Write => "regionWrite",
        }
    }

    /// Операция по написанному имени.
    #[must_use]
    pub fn named(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|it| it.name() == text)
    }

    /// Несёт ли операция нагрузку - то есть стоят ли перед блоком стёртые
    /// связывания типа нагрузки и её словаря `Flat` (§3.6).
    #[must_use]
    pub const fn carries(self) -> bool {
        matches!(self, Self::Alloc | Self::Read | Self::Write)
    }
}

impl fmt::Display for RegionOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Имя класса представления (§4.11).
///
/// Класс объявляется программой - соглашение то же, каким `if` берёт `Bool`, -
/// а имя его знают трое: вывод инстансов (`adamas-elab/src/flat.rs`), понижение
/// (дескриптор укладки в телескопе) и тип операции региона (§3.6). Общая
/// константа стоит здесь, потому что расхождение в написании было бы тихим.
pub const FLAT: &str = "Flat";

/// Имя типа массива (§4.11).
pub const ARRAY: &str = "Array";

/// Имя типа региона (§3.6): runtime-представление области.
pub const BLOCK: &str = "Block";

/// Имя типа хендла (§3.6).
///
/// Отдельного узла ядра у него нет: `Ptr` есть смещение внутри блока, то есть
/// машинное слово, и написан он `UInt64`. §4.11 требует ровно этого - «ссылки
/// внутри плоских данных - хендлы, а не указатели», - и хендл-смещение
/// переживает всякое перемещение области, чего указатель не переживает.
///
/// Названная граница: типовой разницы с `UInt64` у `Ptr` нет, и читать по
/// хендлу другим типом, чем писали, ядро не мешает. Типизирует ссылку `Ref r a`
/// (§3.6, типовая сторона), а не `Ptr`.
pub const PTR: &str = "Ptr";

/// Примитив в терме: тип, литерал, операция, массив.
///
/// Один узел на все формы, а не узел на форму: все они - листья, и различает
/// их только то, чем они типизируются.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Prim {
    /// Тип: `Int64`.
    Ty(PrimTy),
    /// Литерал вместе со своим типом. Биты хранятся обрезанными по ширине
    /// типа, поэтому равенство их - равенство значений; у плавающих оно
    /// побитовое, ровно как `Eq Float` из §4.3.
    Lit(PrimTy, u64),
    /// Операция: `addInt64`.
    Op(PrimOp, PrimTy),
    /// Тип массива `Array n a` (§4.11). Применяется к длине и элементу.
    Array,
    /// Операция над массивом: `arrayIndex`.
    Over(ArrayOp),
    /// Тип региона `Block` (§3.6).
    Block,
    /// Операция над регионом: `regionAlloc`.
    In(RegionOp),
}

impl Prim {
    /// Литерал из уже нормализованных битов.
    ///
    /// Обрезки здесь нет **нарочно**, и это не упущение: нормализуют
    /// [`PrimTy::from_unsigned`], [`PrimTy::from_negative`],
    /// [`PrimTy::from_fraction`] и [`PrimOp::fold`], каждый по своему правилу.
    /// Вторая обрезка на выходе чинила бы сломанное первое место молча.
    /// Измерено: с ней мутант «складывать без обрезки по ширине типа» проходил
    /// корпус целиком - печать восстанавливала ширину за сложением.
    #[must_use]
    pub const fn literal(ty: PrimTy, bits: u64) -> Self {
        Self::Lit(ty, bits)
    }

    /// Имя, которым примитив пишется в программе. У литерала имени нет.
    #[must_use]
    pub fn written(self) -> Option<String> {
        match self {
            Self::Ty(ty) => Some(ty.name().to_owned()),
            Self::Op(op, ty) => Some(format!("{op}{ty}")),
            Self::Array => Some(ARRAY.to_owned()),
            Self::Over(op) => Some(op.name().to_owned()),
            Self::Block => Some(BLOCK.to_owned()),
            Self::In(op) => Some(op.name().to_owned()),
            Self::Lit(..) => None,
        }
    }

    /// Печатается ли примитив со знака: аргументу применения нужны скобки.
    #[must_use]
    pub fn negative(self) -> bool {
        match self {
            Self::Lit(ty, bits) if !ty.floating() => ty.as_signed(bits) < 0,
            Self::Lit(..) => self.to_string().starts_with('-'),
            Self::Ty(_)
            | Self::Op(..)
            | Self::Array
            | Self::Over(_)
            | Self::Block
            | Self::In(_) => false,
        }
    }

    /// Занято ли имя языком (§4.11, §3.6): примитив, массив, регион и операции
    /// над ними.
    #[must_use]
    pub fn taken(text: &str) -> bool {
        PrimTy::named(text).is_some()
            || PrimOp::named(text).is_some()
            || ArrayOp::named(text).is_some()
            || RegionOp::named(text).is_some()
            || text == ARRAY
            || text == BLOCK
            || text == PTR
    }
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ty(ty) => write!(f, "{ty}"),
            Self::Op(op, ty) => write!(f, "{op}{ty}"),
            Self::Array => f.write_str(ARRAY),
            Self::Over(op) => write!(f, "{op}"),
            Self::Block => f.write_str(BLOCK),
            Self::In(op) => write!(f, "{op}"),
            // Дробное печатается через `Debug`: `Display` у него сокращает
            // `1.0` до `1`, и литерал переставал бы отличаться от целого.
            #[expect(
                clippy::cast_possible_truncation,
                reason = "биты `Float32` лежат в младшей половине слова по построению"
            )]
            Self::Lit(PrimTy::Float32, bits) => write!(f, "{:?}", f32::from_bits(*bits as u32)),
            Self::Lit(PrimTy::Float64, bits) => write!(f, "{:?}", f64::from_bits(*bits)),
            Self::Lit(ty, bits) => write!(f, "{}", ty.as_signed(*bits)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Prim, PrimOp, PrimTy};

    /// Размеры §4.11: примитив занимает свою ширину и по ней же выравнивается.
    #[test]
    fn a_primitive_is_as_wide_as_its_name_says() {
        assert_eq!(PrimTy::Float32.size(), 4);
        assert_eq!(PrimTy::Int64.size(), 8);
        assert_eq!(PrimTy::UInt32.size(), 4);
        assert_eq!(PrimTy::Int8.size(), 1);
    }

    /// Знаковый тип принимает лишь свою половину: `128` не `Int8`.
    #[test]
    fn a_signed_type_refuses_the_other_half() {
        assert_eq!(PrimTy::Int8.from_unsigned(127), Some(127));
        assert_eq!(PrimTy::Int8.from_unsigned(128), None);
        assert_eq!(PrimTy::UInt8.from_unsigned(255), Some(255));
        assert_eq!(PrimTy::UInt8.from_unsigned(256), None);
    }

    /// Отрицательное беззнаковому не отдаётся, а знаковому - до `-2^(n-1)`.
    #[test]
    fn a_negative_literal_needs_a_signed_type() {
        assert_eq!(PrimTy::UInt8.from_negative(1), None);
        assert_eq!(PrimTy::Int8.from_negative(128), Some(0x80));
        assert_eq!(PrimTy::Int8.from_negative(129), None);
    }

    /// Целое заворачивается по ширине типа, а не по ширине слова.
    #[test]
    fn integer_arithmetic_wraps_within_its_width() {
        let bits = PrimOp::Add.fold(PrimTy::UInt8, 200, 100);
        assert_eq!(bits, 44);
        let bits = PrimOp::Sub.fold(PrimTy::Int8, 0, 1);
        assert_eq!(Prim::Lit(PrimTy::Int8, bits).to_string(), "-1");
    }

    /// Одинарная точность считается в одинарной: сумма, которую `f64`
    /// различает, а `f32` нет, обязана слиться.
    #[test]
    fn single_precision_rounds_like_single_precision() {
        let one = PrimTy::Float32.from_fraction(1.0).unwrap_or_default();
        let tiny = PrimTy::Float32.from_fraction(1e-9_f64).unwrap_or_default();
        let sum = PrimOp::Add.fold(PrimTy::Float32, one, tiny);
        assert_eq!(sum, one, "1.0 + 1e-9 в одинарной точности есть 1.0");
    }

    /// Печать литерала возвращает написанное: дробное со знаком после точки.
    #[test]
    fn a_literal_prints_the_way_it_is_written() {
        let bits = PrimTy::Float64.from_fraction(1.0).unwrap_or_default();
        assert_eq!(Prim::Lit(PrimTy::Float64, bits).to_string(), "1.0");
        assert_eq!(Prim::Ty(PrimTy::Int64).to_string(), "Int64");
        assert_eq!(Prim::Op(PrimOp::Mul, PrimTy::Int64).to_string(), "mulInt64");
    }

    /// Имя операции читается обратно вместе с типом.
    #[test]
    fn an_operation_name_reads_back() {
        assert_eq!(
            PrimOp::named("mulFloat32"),
            Some((PrimOp::Mul, PrimTy::Float32))
        );
        assert_eq!(PrimOp::named("addNat"), None);
        assert_eq!(PrimOp::named("Int64"), None);
    }
}
