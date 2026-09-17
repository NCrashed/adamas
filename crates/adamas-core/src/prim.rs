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
//! Десять числовых типов из §4.11, три арифметических операции и шесть
//! сравнений. `Bool` и `Char` **узлом ядра не стали**: `Bool` в корпусе
//! объявляется программой и уже плоский тегом в байт, а литерала `Char` в
//! поверхностном языке нет вовсе. Деления, остатка, сдвигов и преобразований
//! между примитивами нет - §4.3 их формы не называет.
//!
//! # Сравнение отвечает `Bool`, и оттого знает имя
//!
//! Арифметика замкнута в своём типе, сравнение - нет, а второго кандидата на
//! ответ у него не бывает: беззнаковый ноль-или-один разбором не берётся, и
//! `if` над ним не пишется. Поэтому [`BOOL`] с конструкторами - имена, взятые
//! у программы тем же соглашением, каким их берут `if` и [`FLAT`]. Занятыми
//! они не становятся: на имени `Bool` стоит не представление, а соглашение.
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

    /// Биты `+inf` и канонического тихого NaN. У целого типа их нет.
    ///
    /// Второй отличается от первого старшим разрядом мантиссы - это тот же
    /// NaN, что зовётся `f64::NAN` в Rust и приходит от свёртки констант LLVM.
    const fn special(self) -> Option<(u64, u64)> {
        match self {
            Self::Float32 => Some((0x7f80_0000, 0x7fc0_0000)),
            Self::Float64 => Some((0x7ff0_0000_0000_0000, 0x7ff8_0000_0000_0000)),
            _ => None,
        }
    }

    /// Ключ, чей беззнаковый порядок и есть порядок значений этого типа (§4.3).
    ///
    /// Беззнаковому ключом служат сами биты. Знаковому - биты с перевёрнутым
    /// старшим разрядом: дополнительный код становится монотонным. Плавающему -
    /// `totalOrder` IEEE-754, который §4.3 и назначает `Eq`/`Ord`, **по
    /// канонизированному значению**: отрицательное инвертируется целиком,
    /// отчего `-0.0` меньше `0.0`, а всякий NaN - один элемент порядка,
    /// стоящий выше `+inf`.
    ///
    /// # Почему NaN не различаются знаком и нагрузкой (вопрос 172)
    ///
    /// `totalOrder` определён на **представлениях**, а знак и нагрузку NaN,
    /// порождённого недопустимой операцией, IEEE-754 оставляет реализации:
    /// железо x86 отдаёт `0xFFF8000000000000`, свёртка констант LLVM -
    /// `0x7FF8000000000000`. Различать их порядком значило бы делать ответ
    /// программы зависимым от бэкенда, компилятора и уровня оптимизации -
    /// измерено 2026-09-15 и 2026-09-16, `docs/measurements/nan-canon/`.
    /// Отсюда канонизация: порядок остаётся `totalOrder`, но берётся от
    /// значения, в котором всякий NaN заменён каноническим тихим.
    ///
    /// Один ключ на все шесть сравнений и на все десять типов: разъехаться
    /// `lt` с `ge` тогда негде, они читают одно и то же число.
    fn key(self, bits: u64) -> u64 {
        if !self.floating() && !self.signed() {
            return bits;
        }
        let top = 1u64 << (self.width() - 1);
        // NaN узнаётся модулем, а не `is_nan`: ровно эту форму берут оба
        // бэкенда, где плавающего регистра под рукой нет вовсе.
        if let Some((infinity, quiet)) = self.special() {
            if bits & (top - 1) > infinity {
                // Канонический тихий NaN неотрицателен, поэтому ключ у него -
                // его биты со старшим разрядом.
                return quiet | top;
            }
        }
        // Одна маска на оба случая: знаковому целому и положительному
        // плавающему переворачивается старший разряд, отрицательному
        // плавающему - все. Записано исключающим ИЛИ, а не «либо приписать
        // бит, либо инвертировать»: там половина мутантов оказывалась
        // равносильной, потому что при снятом бите `|` и `^` не различаются.
        let mask = if self.floating() && bits & top != 0 {
            self.masked(u64::MAX)
        } else {
            top
        };
        bits ^ mask
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

/// Сравнение двух примитивов (§4.3).
///
/// Отдельное перечисление, а не шестёрка в [`PrimOp`]: у арифметики ответ того
/// же типа, что аргументы, а здесь - `Bool`, и различие это проходит насквозь -
/// через тип операции, через свёртку и через понижение, где арифметика живёт в
/// регистре, а конструктор есть непосредственное значение.
///
/// # Порядок у плавающих - `totalOrder`, а не IEEE
///
/// §4.3 решает это прямо: `Eq`/`Ord` для `Float` побитовы по IEEE-754
/// `totalOrder`, отчего `nan == nan` истинно, `0.0 /= -0.0`, а трихотомия
/// восстановлена. IEEE-семантика сравнения живёт отдельно - `ieeeEq`/`ieeeLt`
/// класса `Approximate`, - и примитивом здесь не является: класс без обещаний
/// пишется поверх, а якорь представления нужен тому порядку, по которому
/// `Float` годится ключом `Map`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimCmp {
    /// Равно.
    Eq,
    /// Не равно.
    Ne,
    /// Строго меньше.
    Lt,
    /// Меньше либо равно.
    Le,
    /// Строго больше.
    Gt,
    /// Больше либо равно.
    Ge,
}

impl PrimCmp {
    /// Все сравнения.
    pub const ALL: [Self; 6] = [Self::Eq, Self::Ne, Self::Lt, Self::Le, Self::Gt, Self::Ge];

    /// Приставка имени: `lt` у `ltInt64`.
    #[must_use]
    pub const fn prefix(self) -> &'static str {
        match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
        }
    }

    /// Сравнение и тип по написанному имени: `ltInt64`.
    #[must_use]
    pub fn named(text: &str) -> Option<(Self, PrimTy)> {
        Self::ALL.into_iter().find_map(|op| {
            text.strip_prefix(op.prefix())
                .and_then(PrimTy::named)
                .map(|ty| (op, ty))
        })
    }

    /// Считает сравнение над двумя литералами одного типа.
    #[must_use]
    pub fn holds(self, ty: PrimTy, left: u64, right: u64) -> bool {
        let order = ty.key(left).cmp(&ty.key(right));
        match self {
            Self::Eq => order.is_eq(),
            Self::Ne => order.is_ne(),
            Self::Lt => order.is_lt(),
            Self::Le => order.is_le(),
            Self::Gt => order.is_gt(),
            Self::Ge => order.is_ge(),
        }
    }
}

impl fmt::Display for PrimCmp {
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

/// Операция над вектором (§4.9).
///
/// Узел ядра по тому же доводу, что массив: `simdLane` обязан **сводиться**, а
/// сведение примитивов живёт в [`crate::eval`], которая сигнатуры не видит.
/// Правило имени то же: на `Simd` стоит представление, и переопределяемое имя
/// дало бы два вектора с разной шириной дорожки.
///
/// # Восемь операций, а не шестнадцать
///
/// §4.9 перечисляет `splat`, `fromVect`, `toVect`, `simdAdd`/`Sub`/`Mul`/`Div`,
/// `simdEq`/`Lt`/`Gt`, `sum`, `horizMax`, `shuffle`, `permute`, `load`, `store`.
/// Здесь взято восемь, и расхождение с перечнем объяснимо построчно.
///
/// `fromVect` и `toVect` **не взяты, и взяты быть не могут**: они названы через
/// `Vect`, а имя `Vect` языком намеренно не занято - §4.1 пишет `data Vect`
/// пользовательским объявлением, и корпус пишет тоже. Сводить конверсию было бы
/// нечем: [`crate::eval`] конструкторов чужого семейства не знает. Их работу
/// делают [`Self::Set`] и [`Self::Lane`] - вставка и чтение одной дорожки, то
/// есть `insertelement`/`extractelement`, из которых конверсия и состоит.
///
/// Деления нет по той же причине, по какой его нет у [`PrimOp`]: §4.3 формы
/// скалярного деления не называет, а вектор её опередить не вправе. Сравнений
/// нет потому, что ответ у них - маска, то есть `Simd n Bool`, а `Bool` не
/// примитив (§4.11 его среди десяти не перечисляет) и дорожкой быть не может.
/// Свёрток (`sum`, `horizMax`) и перестановок (`shuffle`, `permute`) нет по
/// цене: каждая - свой узел на всех трёх вычислителях, а выразимость от них не
/// зависит. Все пять названы в отчёте трека H как невзятое.
///
/// # `load`/`store` берут колонку, а не `AlignedBuffer`, и это расхождение
///
/// §4.9 пишет их через ресурсный тип: `load : AlignedBuffer n a -> {IO} (Simd n
/// a)`. Взята **не** эта форма, и довод не в цене ресурса, а в том, что
/// написанная форма не выражает того, ради чего §4.9 её заводит. Ширина буфера
/// там та же `n`, что у вектора, то есть буфер держит ровно один вектор; а тот
/// же §4.9 абзацем ниже требует, чтобы «внутренний цикл работал с `Simd 8
/// Float32` **над колонкой**». Окна по номеру внутри длинной колонки формой
/// `AlignedBuffer n a` не выразить вовсе.
///
/// [`Self::Load`] и [`Self::Store`] поэтому взяты над `Array m a` (§4.11) и
/// написаны парой к [`ArrayOp::Index`] и [`ArrayOp::Set`]: тот же массив, тот
/// же номер ячейки, тот же договор «функционален по семантике, переписывает по
/// исполнению». Эффекта `{IO}` у них нет по той же причине, по какой его нет у
/// [`ArrayOp::Set`]: массив в этом языке уже чист, и второй договор о записи
/// вывел бы колонное ядро из чистого отрезка, который его и понижает.
///
/// # Приставка `simd` у всех восьми
///
/// §4.9 пишет `splat`, `sum`, `load`, `store` голыми именами - «в prelude или
/// `Data.SIMD`». Голыми они здесь быть не могут: имя примитива **занято**
/// языком (см. [`Prim::taken`]), и занять `sum`, `load`, `store` значило бы
/// отвергнуть всякую программу, которая их объявляет. Приставка - то же
/// правило, каким `Array` зовётся `arrayNew`, а не `new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SimdOp {
    /// `simdSplat n x` - вектор ширины `n`, все дорожки заняты `x`.
    Splat,
    /// `simdSet v i x` - тот же вектор с переписанной дорожкой `i`.
    Set,
    /// `simdLane v i` - значение дорожки `i`.
    Lane,
    /// `simdAdd u v` - подорожечное сложение.
    Add,
    /// `simdSub u v` - подорожечное вычитание.
    Sub,
    /// `simdMul u v` - подорожечное умножение.
    Mul,
    /// `simdLoad n xs i` - окно из `n` ячеек колонки, начиная с `i` (§4.9).
    ///
    /// Ширина написана, а не выведена, и по той же причине, что у
    /// [`Self::Splat`]: выводить её из `Array m a` нечем - длина колонки к
    /// ширине регистра отношения не имеет.
    Load,
    /// `simdStore n xs i v` - та же колонка с переписанным окном (§4.9).
    Store,
}

impl SimdOp {
    /// Все операции.
    pub const ALL: [Self; 8] = [
        Self::Splat,
        Self::Set,
        Self::Lane,
        Self::Add,
        Self::Sub,
        Self::Mul,
        Self::Load,
        Self::Store,
    ];

    /// Имя, которым операция пишется в программе.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Splat => "simdSplat",
            Self::Set => "simdSet",
            Self::Lane => "simdLane",
            Self::Add => "simdAdd",
            Self::Sub => "simdSub",
            Self::Mul => "simdMul",
            Self::Load => "simdLoad",
            Self::Store => "simdStore",
        }
    }

    /// Операция по написанному имени.
    #[must_use]
    pub fn named(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|it| it.name() == text)
    }

    /// Скалярная операция, которую эта повторяет по дорожкам.
    ///
    /// `None` у построения и чтения: работы над числами у них нет. Общая с
    /// [`PrimOp`] она нарочно - §4.9 обещает element-wise семантику, и второй
    /// счёт сложения разошёлся бы с первым молча, причём разошёлся бы у
    /// плавающего, где `Float32` считается именно в одинарной точности.
    #[must_use]
    pub const fn arith(self) -> Option<PrimOp> {
        match self {
            Self::Add => Some(PrimOp::Add),
            Self::Sub => Some(PrimOp::Sub),
            Self::Mul => Some(PrimOp::Mul),
            Self::Splat | Self::Set | Self::Lane | Self::Load | Self::Store => None,
        }
    }

    /// Трогает ли операция память колонки (§4.9, `load`/`store`).
    ///
    /// Отделены они не по вкусу: у этих двух в спайне стоит массив, а значит
    /// свой счёт стёртых, своя проверка границы и своя строка у Perceus.
    /// Спрашивать это по имени пришлось бы в четырёх местах.
    #[must_use]
    pub const fn memory(self) -> bool {
        matches!(self, Self::Load | Self::Store)
    }
}

impl fmt::Display for SimdOp {
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
/// # Блок один, операций семь
///
/// `AllocStrategy` §3.6 называет три метода - `new`, `alloc`, `deallocate`, - а
/// эффект `Alloc r` ещё три - `allocIn`, `read`, `write`. Здесь их семь, и
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
///
/// # Ячейку отдают обратно двумя разными способами, и в этом вся стратегия
///
/// §3.6 обещает три базовые стратегии, и две из них - Pool («переиспользование
/// ячеек равного размера») и `StackAlloc` («LIFO») - без **поячеечного** возврата
/// пусты: отличать их от Arena было бы нечем. Возврат поэтому есть, и он
/// разный: [`Self::Recycle`] помечает ячейку свободной, [`Self::Pop`] опускает
/// курсор. Arena не зовёт ни ту, ни другую - её `free` пишется на самом языке
/// как `free r p = r`.
///
/// Отсюда правило [`Self::Alloc`]: **свободная ячейка равного размера, иначе
/// подъём курсора**. Это механизм, а не политика - политику задаёт то, какая
/// операция возврата ячейку освободила, - и у Arena свободных ячеек не бывает
/// вовсе, поэтому подъём у неё единственный путь.
///
/// Размер ячейки при возврате не пишется числом: его помнит сама область
/// (журнал аллокаций, `adamas.h`). Поэтому у обеих операций возврата нет
/// стёртой нагрузки - см. [`Self::carries`], - и `free : Block -> Ptr -> Block`
/// пишется без `{Flat a}`, которое иначе было бы не из чего решить.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegionOp {
    /// `regionNew` - пустой регион. `AllocStrategy.new` (§3.6).
    New,
    /// `sharedNew` - пустая **разделяемая** область (§3.6, §5.2).
    ///
    /// Второй операции у разделяемой области нет, и это не экономия узлов.
    /// §3.6 объявляет `SharedAllocStrategy when AllocStrategy`, то есть **те
    /// же члены**, и говорит прямо: «программист выбирает уровень при создании
    /// региона». Значит `store`, `here`, `load` и `free` у разделяемой
    /// стратегии пишутся теми же `regionAlloc`, `regionLast`, `regionRead`,
    /// `regionRecycle`/`regionPop`, а расходятся стратегии ровно в `new`.
    ///
    /// Различает две области **рантайм, по тегу**: обычная копируется при
    /// лишней ссылке, разделяемая есть тождество. Типовая сторона различает их
    /// запечатыванием - `SharedArena.Block` и `Arena.Block` суть разные
    /// абстрактные типы, как только стратегия запечатана (§4.8). Без
    /// запечатывания обе есть `Block`, и смешение ловится рантаймом, а не
    /// проверкой: названная граница, смежная с §10 вопросом 25(б) (правила
    /// миграции local → shared).
    ///
    /// Машина считает её **той же** чистой областью, что и [`Self::New`], и
    /// это не заглушка. Разделяемость есть свойство тождества, а область ядра
    /// есть значение; программа, различающая их, - это ровно программа, на
    /// которой машина и рантайм обязаны разойтись. Линейно протянутая область
    /// их не различает, и на ней договор трёх вычислителей цел.
    SharedNew,
    /// `regionAlloc r x` - тот же регион, в конце которого лежит `x`.
    Alloc,
    /// `regionLast r` - хендл последней аллокации.
    Last,
    /// `regionRead r p` - значение, лежащее по хендлу `p`.
    Read,
    /// `regionWrite r p x` - тот же регион с переписанным местом `p`.
    Write,
    /// `regionRecycle r p` - ячейка по хендлу свободна: Pool (§3.6).
    ///
    /// Курсор не двигается, занятое не убывает; следующая аллокация **равного
    /// размера** займёт это место. Хендл, не называющий занятой ячейки,
    /// оставляет область как есть.
    Recycle,
    /// `regionPop r p` - курсор опускается до хендла: `StackAlloc` (§3.6).
    ///
    /// Опускается он, только если хендл называет **последнюю** аллокацию, -
    /// это и есть LIFO. Всякий другой хендл оставляет область как есть, и
    /// стратегия тем самым отличается от Pool наблюдаемо.
    Pop,
}

impl RegionOp {
    /// Все операции.
    pub const ALL: [Self; 8] = [
        Self::New,
        Self::SharedNew,
        Self::Alloc,
        Self::Last,
        Self::Read,
        Self::Write,
        Self::Recycle,
        Self::Pop,
    ];

    /// Имя, которым операция пишется в программе.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::New => "regionNew",
            Self::SharedNew => "sharedNew",
            Self::Alloc => "regionAlloc",
            Self::Last => "regionLast",
            Self::Read => "regionRead",
            Self::Write => "regionWrite",
            Self::Recycle => "regionRecycle",
            Self::Pop => "regionPop",
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

/// Имя типа истинности и его конструкторов (§4.3).
///
/// Соглашение то же, каким `if` берёт `Bool`, и то же, каким `Flat` берётся по
/// имени: тип объявляется программой, а компилятор знает имя. Занятым оно при
/// этом **не** становится - в отличие от `Array` и `Block`, на которых стоит
/// представление. `Bool` объявляют программы корпуса, и заняв имя, ядро
/// отвергло бы их все.
///
/// Знают его трое, и все трое - следствие одного решения «сравнение отвечает
/// `Bool`»: тип сравнения ([`crate::check::prim_type`]), его свёртка
/// ([`crate::eval`]) и разбор литерального паттерна
/// ([`crate::pattern`]). Расхождение в написании было бы тихим, поэтому
/// константа одна.
pub const BOOL: &str = "Bool";

/// Конструктор истины.
pub const TRUE: &str = "True";

/// Конструктор лжи.
pub const FALSE: &str = "False";

/// Имя типа массива (§4.11).
pub const ARRAY: &str = "Array";

/// Имя типа вектора (§4.9).
pub const SIMD: &str = "Simd";

/// Имя класса дорожки (§4.9).
///
/// Класс объявляется программой - соглашение то же, каким `if` берёт `Bool`, а
/// регион берёт [`FLAT`], - а имя его знают двое: вывод инстансов
/// (`adamas-elab/src/primitive.rs`) и тип операции над вектором. Занятым имя при
/// этом **не** становится: на нём стоит соглашение, а не представление.
///
/// Перечень инстансов - те же десять §4.11, что перечисляет [`PrimTy`], и
/// совпадение с `Flat` тут неполное намеренно: запись из трёх `Float32` плоская,
/// но дорожкой быть не может (§4.9, «`Vec3` не `Simd`»).
pub const PRIMITIVE: &str = "Primitive";

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
    /// Сравнение: `ltInt64`. Ответ - `Bool`, а не свой тип.
    Cmp(PrimCmp, PrimTy),
    /// Тип массива `Array n a` (§4.11). Применяется к длине и элементу.
    Array,
    /// Операция над массивом: `arrayIndex`.
    Over(ArrayOp),
    /// Тип региона `Block` (§3.6).
    Block,
    /// Операция над регионом: `regionAlloc`.
    In(RegionOp),
    /// Тип вектора `Simd n a` (§4.9). Применяется к ширине и дорожке.
    Simd,
    /// Операция над вектором: `simdAdd`.
    Across(SimdOp),
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
            Self::Cmp(op, ty) => Some(format!("{op}{ty}")),
            Self::Array => Some(ARRAY.to_owned()),
            Self::Over(op) => Some(op.name().to_owned()),
            Self::Block => Some(BLOCK.to_owned()),
            Self::In(op) => Some(op.name().to_owned()),
            Self::Simd => Some(SIMD.to_owned()),
            Self::Across(op) => Some(op.name().to_owned()),
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
            | Self::Cmp(..)
            | Self::Array
            | Self::Over(_)
            | Self::Block
            | Self::In(_)
            | Self::Simd
            | Self::Across(_) => false,
        }
    }

    /// Занято ли имя языком (§4.11, §3.6): примитив, массив, регион и операции
    /// над ними.
    #[must_use]
    pub fn taken(text: &str) -> bool {
        PrimTy::named(text).is_some()
            || PrimOp::named(text).is_some()
            || PrimCmp::named(text).is_some()
            || ArrayOp::named(text).is_some()
            || RegionOp::named(text).is_some()
            || SimdOp::named(text).is_some()
            || text == ARRAY
            || text == BLOCK
            || text == PTR
            || text == SIMD
    }
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ty(ty) => write!(f, "{ty}"),
            Self::Op(op, ty) => write!(f, "{op}{ty}"),
            Self::Cmp(op, ty) => write!(f, "{op}{ty}"),
            Self::Array => f.write_str(ARRAY),
            Self::Over(op) => write!(f, "{op}"),
            Self::Block => f.write_str(BLOCK),
            Self::In(op) => write!(f, "{op}"),
            Self::Simd => f.write_str(SIMD),
            Self::Across(op) => write!(f, "{op}"),
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
    use super::{Prim, PrimCmp, PrimOp, PrimTy};

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
        assert_eq!(Prim::Cmp(PrimCmp::Lt, PrimTy::Int64).to_string(), "ltInt64");
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
        assert_eq!(
            PrimCmp::named("ltUInt8"),
            Some((PrimCmp::Lt, PrimTy::UInt8))
        );
        assert_eq!(PrimCmp::named("ltNat"), None);
        assert_eq!(PrimOp::named("ltInt64"), None);
    }

    /// Знак читается знаковым типом и не читается беззнаковым.
    ///
    /// Одни и те же биты: `0xff` есть `-1` у `Int8` и `255` у `UInt8`, и
    /// сравнение с нулём обязано разойтись. Мутант «сравнивать всегда как
    /// беззнаковое» валится ровно здесь.
    #[test]
    fn a_comparison_reads_the_sign_of_its_type() {
        let minus_one = PrimTy::Int8.from_negative(1).unwrap_or_default();
        assert!(PrimCmp::Lt.holds(PrimTy::Int8, minus_one, 0));
        assert!(PrimCmp::Gt.holds(PrimTy::UInt8, minus_one, 0));
    }

    /// Порядок плавающих - `totalOrder` §4.3, а не IEEE.
    ///
    /// Две точки расхождения названы разделом поимённо, и обе здесь: `nan`
    /// равен себе, `-0.0` строго меньше `0.0`.
    #[test]
    fn floating_order_is_total_not_ieee() {
        let nan = PrimTy::Float64.from_fraction(f64::NAN).unwrap_or_default();
        let zero = PrimTy::Float64.from_fraction(0.0).unwrap_or_default();
        let minus_zero = PrimTy::Float64.from_fraction(-0.0).unwrap_or_default();
        let one = PrimTy::Float64.from_fraction(1.0).unwrap_or_default();
        assert!(PrimCmp::Eq.holds(PrimTy::Float64, nan, nan));
        assert!(PrimCmp::Lt.holds(PrimTy::Float64, minus_zero, zero));
        assert!(PrimCmp::Lt.holds(PrimTy::Float64, zero, one));
        assert!(PrimCmp::Lt.holds(
            PrimTy::Float64,
            PrimTy::Float64.from_fraction(-1.0).unwrap_or_default(),
            minus_zero
        ));
    }

    /// Всякий NaN - один элемент порядка, стоящий выше `+inf` (вопрос 172).
    ///
    /// Знак и полезную нагрузку NaN, порождённого недопустимой операцией,
    /// IEEE-754 оставляет реализации, и до канонизации ответ программы зависел
    /// от того, кто NaN породил: железо x86 отдаёт `0xFFF8000000000000`,
    /// свёртка констант LLVM - `0x7FF8000000000000`. Здесь проверяется, что
    /// ключ их не различает - ни между собой, ни от NaN с нагрузкой, - и что
    /// при этом NaN остаётся выше бесконечности, а не равен ей.
    ///
    /// Обе ширины, потому что биты экспоненты у них разные и вторая запись
    /// разъехалась бы с первой молча.
    #[test]
    fn every_nan_is_one_element_of_the_order() {
        for (ty, quiet, negative, loaded, infinity, biggest) in [
            (
                PrimTy::Float64,
                0x7ff8_0000_0000_0000u64,
                0xfff8_0000_0000_0000u64,
                0x7ff8_0000_dead_beefu64,
                0x7ff0_0000_0000_0000u64,
                0x7fef_ffff_ffff_ffffu64,
            ),
            (
                PrimTy::Float32,
                0x7fc0_0000,
                0xffc0_0000,
                0x7fc0_beef,
                0x7f80_0000,
                0x7f7f_ffff,
            ),
        ] {
            assert!(
                PrimCmp::Eq.holds(ty, quiet, negative),
                "{ty}: знак различён"
            );
            assert!(
                PrimCmp::Eq.holds(ty, quiet, loaded),
                "{ty}: нагрузка различена"
            );
            assert!(
                PrimCmp::Gt.holds(ty, negative, infinity),
                "{ty}: отрицательный NaN не выше бесконечности"
            );
            assert!(
                PrimCmp::Gt.holds(ty, quiet, biggest),
                "{ty}: NaN не выше наибольшего конечного"
            );
            assert!(
                PrimCmp::Ne.holds(ty, quiet, infinity),
                "{ty}: NaN сравнялся с бесконечностью"
            );
        }
    }

    /// Одинарная точность сравнивается в своей ширине.
    ///
    /// Ключ строится по ширине **типа**: возьми он шестьдесят четыре бита у
    /// `Float32`, и знаковый разряд оказался бы не на своём месте - `-1.0`
    /// перестало бы быть меньше нуля.
    #[test]
    fn single_precision_compares_in_its_own_width() {
        let minus_one = PrimTy::Float32.from_fraction(-1.0).unwrap_or_default();
        let zero = PrimTy::Float32.from_fraction(0.0).unwrap_or_default();
        assert!(PrimCmp::Lt.holds(PrimTy::Float32, minus_one, zero));
        assert!(PrimCmp::Ge.holds(PrimTy::Float32, zero, minus_one));
    }
}
