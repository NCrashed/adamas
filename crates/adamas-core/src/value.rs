//! Семантические значения для `NbE`.
//!
//! Значения используют уровни де Брёйна, а термы - индексы. Разница в том,
//! откуда ведётся счёт: индекс отсчитывается от места использования, уровень -
//! от начала контекста. Уровень не меняется при входе под новое связывание,
//! поэтому значение, попавшее в замыкание, не нужно сдвигать - на этом `NbE` и
//! экономит по сравнению с подстановкой.

use std::fmt;
use std::rc::Rc;

use crate::level::Level;
use crate::mult::Mult;
use crate::prim::{ArrayOp, Prim, PrimOp, PrimTy};
use crate::row::{Row, RowVar};
use crate::term::{Binder, Field, Fields, Index, Mults, Name, Term, TermMeta};

/// Имя стёртого в отказах и печати.
///
/// Невыразимое: написать его автор не может, а увидеть - вправе. Всплывшее
/// наружу означает дыру в учёте кратностей (§3.3).
pub const ERASED: &str = "#erased";

/// Уровень де Брёйна: сколько связываний отсчитать от начала контекста.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lvl(pub u32);

impl Lvl {
    /// Индекс, которым этот уровень адресуется из контекста размера `size`.
    ///
    /// # Panics
    ///
    /// Если уровень не адресуем при таком `size`, то есть `self.0 >= size`.
    /// Это internal invariant: значение читается обратно в том же контексте,
    /// в котором построено. Проверка явная, потому что без неё вычитание в
    /// release молча заворачивается и наружу уходит индекс вроде `#4294967295`
    /// вместо отказа.
    #[must_use]
    pub fn to_index(self, size: u32) -> Index {
        Index(
            size.checked_sub(self.0)
                .and_then(|distance| distance.checked_sub(1))
                .unwrap_or_else(|| unreachable!("уровень {} вне контекста размера {size}", self.0)),
        )
    }
}

/// Окружение вычисления - список значений, голова которого соответствует
/// [`Index(0)`](Index).
///
/// Односвязный список на `Rc`, а не вектор: замыкание захватывает окружение
/// целиком, и копирование вектора на каждом связывании давало бы
/// квадратичность.
#[derive(Clone, Debug, Default)]
pub struct Env {
    head: Option<Rc<Cell>>,
    len: u32,
    /// Аргументы-row определения, которое сейчас вычисляется (§10 вопрос 73).
    ///
    /// Живут здесь, а не подставляются в терм заранее, и причина не в удобстве.
    /// Уровень **замкнут**, поэтому подставляется до вычисления; row - нет: её
    /// метка несёт термы, и `{State s}` при локальном `s` открыта. Положить
    /// такую row в замкнутое тело нечем, а окружение для того и заведено -
    /// оно уже носит открытые значения.
    rows: Rc<[Row<Rc<Value>>]>,
}

#[derive(Debug)]
struct Cell {
    value: Rc<Value>,
    rest: Option<Rc<Cell>>,
}

impl Env {
    /// Сколько значений в окружении.
    #[must_use]
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Пусто ли окружение.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Окружение с аргументами-row: так вычисляется тело определения при δ.
    #[must_use]
    pub fn rowed(rows: Rc<[Row<Rc<Value>>]>) -> Self {
        // Поля выписаны поимённо: у `Env` теперь свой `Drop`, а через него
        // синтаксис обновления структуры не проходит.
        Self {
            head: None,
            len: 0,
            rows,
        }
    }

    /// Аргумент-row по номеру параметра. `None` - параметра столько нет, и
    /// хвост остаётся собой: подставлять нечего.
    #[must_use]
    pub fn row(&self, RowVar(index): RowVar) -> Option<&Row<Rc<Value>>> {
        self.rows.get(index as usize)
    }

    /// Окружение с добавленным значением. Исходное не меняется.
    #[must_use]
    pub fn extend(&self, value: Rc<Value>) -> Self {
        Self {
            head: Some(Rc::new(Cell {
                value,
                rest: self.head.clone(),
            })),
            len: self.len + 1,
            rows: Rc::clone(&self.rows),
        }
    }

    /// Значение по индексу. `None` - индекс за пределами окружения, что
    /// означает незамкнутый терм.
    #[must_use]
    pub fn lookup(&self, Index(index): Index) -> Option<Rc<Value>> {
        let mut cell = self.head.as_ref()?;
        for _ in 0..index {
            cell = cell.rest.as_ref()?;
        }
        Some(Rc::clone(&cell.value))
    }
}

/// Замыкание: тело, ждущее ещё одного значения, вместе с захваченным
/// окружением.
#[derive(Clone, Debug)]
pub struct Closure {
    pub(crate) env: Env,
    pub(crate) body: Rc<Term>,
}

/// Row стрелки, ждущая значения её же аргумента.
///
/// Row стоит **под** связыванием, потому что описывает применение, а применение
/// аргумент уже знает: `(0 r : Region) -> {Alloc r} Nat` называет в эффекте
/// именно тот регион, который передали. Отсюда замыкание, а не готовая row:
/// вычислить метки до аргумента нечем, ровно как кодомен.
#[derive(Clone, Debug)]
pub struct RowClosure {
    pub(crate) env: Env,
    pub(crate) row: Row<Term>,
}

impl RowClosure {
    /// Row при известном значении аргумента.
    #[must_use]
    pub fn apply(&self, value: Rc<Value>) -> Row<Rc<Value>> {
        if self.row.is_empty() {
            return Row::empty();
        }
        crate::eval::row_of(&self.env.extend(value), &self.row)
    }

    /// Метки как они написаны: имена видны без вычисления.
    #[must_use]
    pub fn written(&self) -> &Row<Term> {
        &self.row
    }
}

/// Голова застрявшего вычисления.
///
/// Локальная переменная застревает всегда - её значение неизвестно по
/// построению. Определение застревает, только пока его не развернули: у
/// определения с телом разворот возможен (δ-редукция, [`crate::conv`]), у
/// постулата - нет.
///
/// Равенство структурное, и для аргументов уровня это работает только потому,
/// что [`Value::constant`] приводит их к нормальной форме. Нормальная форма
/// уровня - полный инвариант (см. [`crate::level`]), так что структурное
/// равенство нормализованных уровней и есть семантическое.
/// Равенство голов не выводится: аргументы-row несут значения, а у значений
/// равенство есть конвертируемость, и живёт она в [`crate::conv`]. Сравнивать
/// головы структурно значило бы завести второе, более грубое.
#[derive(Clone, Debug)]
pub enum Head {
    /// Переменная контекста.
    Local(Lvl),
    /// Определение с нормализованными аргументами уровня и аргументами row.
    ///
    /// Списка два, потому что и параметров у определения два набора (§10
    /// вопрос 73). Row здесь несут значения: аргументы метки - обычные термы,
    /// и на стороне значения они уже вычислены.
    Global(Name, Rc<[Level]>, Rc<[Row<Rc<Value>>]>, Mults),
    /// Нерешённая метапеременная терма.
    ///
    /// Застревает так же, как переменная контекста, и по той же причине:
    /// вычислять нечего, пока не известно, чем она окажется. Решённая головой
    /// не остаётся - её разворачивает `force` до того, как спайн понадобится.
    Meta(TermMeta),
    /// Примитивная операция (§4.3).
    ///
    /// Голова, а не значение: `addInt64 x 1` под связыванием считать нечем, и
    /// застревает оно ровно так же, как применение переменной. Сводится
    /// [`crate::eval::try_apply`], когда спайн набрал два литерала.
    Prim(PrimOp, PrimTy),
    /// Сравнение примитивов (§4.3).
    ///
    /// Голова по тому же доводу, что и [`Head::Prim`]. Сводится не в литерал, а
    /// в конструктор `Bool`, объявленный программой: ответа своего типа у
    /// сравнения нет.
    Cmp(crate::prim::PrimCmp, PrimTy),
    /// Тип массива `Array n a` (§4.11): голова, применяемая к длине и элементу.
    Array,
    /// Операция над массивом (§4.11).
    ///
    /// Голова по тому же доводу, что и [`Head::Prim`]. Спайн над ней - **второе**
    /// представление массива, оставшееся там, где первое не заводится:
    /// `arrayNew` с непримитивной ячейкой либо с нелитеральной длиной заводит
    /// цепочку, `arraySet` наращивает, `arrayIndex` её читает
    /// ([`crate::eval::try_apply`]). Первое представление - [`Head::Block`].
    ArrayOp(ArrayOp),
    /// Плоский массив: байты подряд с **идентичностью** (§4.11, §5.3).
    ///
    /// Первое представление массива и единственное, у которого есть адрес.
    /// Заводится δ-шагом `arrayNew` там, где длина - литерал, а ячейка -
    /// примитивный литерал; `arraySet` над ним даёт **новый** блок, `arrayIndex`
    /// читает ячейку прямо из байт ([`crate::eval::try_apply`]).
    ///
    /// Зачем оно, если спайн работал: спайн есть цепочка значений, и адреса у
    /// неё нет. Машина поэтому не могла одолжить буфер чужой стороне
    /// (§5.3, `RunError::ForeignBuffer`), и милестоун «три вычислителя дают один
    /// ответ» на буфере не брался. Блок это снимает: чужая запись по одолженному
    /// адресу меняет **те самые** байты, которые прочтёт следующий `arrayIndex`.
    Block(Rc<Block>),
    /// Операция над регионом (§3.6).
    ///
    /// Голова по тому же доводу, что и [`Head::ArrayOp`], и с той же добавкой:
    /// **значение блока и есть такой спайн**. `regionNew` заводит цепочку,
    /// `regionAlloc` и `regionWrite` её наращивают, `regionLast` с `regionRead`
    /// читают ([`crate::eval::try_apply`]).
    Region(crate::prim::RegionOp),
    /// Тип вектора `Simd n a` (§4.9): голова, применяемая к ширине и дорожке.
    Simd,
    /// Операция над вектором (§4.9).
    ///
    /// Голова по тому же доводу, что [`Head::ArrayOp`], и с той же добавкой:
    /// **значение вектора и есть такой спайн**. `simdSplat` заводит цепочку,
    /// `simdSet` наращивает её, арифметика надстраивает, а `simdLane` читает
    /// ([`crate::eval::try_apply`]).
    SimdOp(crate::prim::SimdOp),
}

/// Плоский массив значением: байты подряд, длина и тип ячейки (§4.11).
///
/// # Байты, а не ячейки-значения
///
/// Хранится ровно то, что хранит рантайм (`adamas-runtime/c/array.c`): ячейка
/// занимает [`PrimTy::size`] байт, ячейки лежат подряд, порядок байт -
/// машинный. Второй уклад разошёлся бы с первым молча на первом же `UInt8`,
/// а сойтись они обязаны: адрес этих байт и есть то, что машина одалживает
/// чужой стороне.
///
/// # Мутабельность - только чужая
///
/// [`RefCell`](std::cell::RefCell) стоит здесь **не** ради `arraySet`: наша
/// запись функциональна и даёт новый блок ([`Block::with_cell`]), как давала
/// новый спайн. Мутирует блок ровно один - чужая сторона, которой машина
/// одолжила адрес. Не будь мутабельности, заём отдавал бы копию, и то, что
/// чужая сторона написала, не прочёл бы никто.
///
/// # Предел
///
/// Блок заводится до [`Block::LIMIT`] байт. Выше остаётся спайн - то самое
/// поведение, какое было до блоков, - и заём такого массива машина отвергает
/// названной причиной. Предел есть цена того, что `arrayNew` теперь **считает**
/// байты: без него `arrayIndex (arrayNew 4000000000 x) 3` выделил бы четыре
/// гигабайта там, где прежде выделялся один узел. С пределом `adamas eval` этой
/// программы отвечает нулём за три миллисекунды.
#[derive(Debug)]
pub struct Block {
    /// Тип ячейки.
    ty: PrimTy,
    /// Тип элемента значением - его требует обратное чтение.
    ///
    /// Хранится, а не строится заново: у `arrayNew` он стоит стёртым
    /// аргументом, и второе его написание разъехалось бы с первым.
    elem: Rc<Value>,
    /// Длина в ячейках.
    count: u64,
    /// Байты подряд.
    cells: std::cell::RefCell<Vec<u8>>,
}

impl Block {
    /// Сколько байт блок берёт на себя, прежде чем массив останется спайном.
    ///
    /// Мегабайт: буфер чужой библиотеки такого порядка и бывает
    /// (`compress2` над фикстурой корпуса - килобайты), а вычислитель,
    /// наткнувшись на литеральную длину, дороже мегабайта за неё не заплатит.
    pub const LIMIT: usize = 1 << 20;

    /// Массив длины `count`, все ячейки заняты битами `init`.
    ///
    /// `None` - блока не будет: длина не влезает в [`Self::LIMIT`] либо памяти
    /// не нашлось. Вызывающий оставляет спайн, то есть прежнее поведение; отказ
    /// здесь не ошибка программы, и паниковать нечем.
    #[must_use]
    pub fn new(ty: PrimTy, elem: Rc<Value>, count: u64, init: u64) -> Option<Rc<Self>> {
        let stride = ty.size() as usize;
        let bytes = usize::try_from(count).ok()?.checked_mul(stride)?;
        if bytes > Self::LIMIT {
            return None;
        }
        let mut cells: Vec<u8> = Vec::new();
        cells.try_reserve_exact(bytes).ok()?;
        let word = encoded(init, stride);
        for _ in 0..count {
            cells.extend_from_slice(&word[..stride]);
        }
        Some(Rc::new(Self {
            ty,
            elem,
            count,
            cells: std::cell::RefCell::new(cells),
        }))
    }

    /// Тип ячейки.
    #[must_use]
    pub const fn ty(&self) -> PrimTy {
        self.ty
    }

    /// Длина в ячейках.
    #[must_use]
    pub const fn count(&self) -> u64 {
        self.count
    }

    /// Тип элемента значением.
    #[must_use]
    pub fn elem(&self) -> &Rc<Value> {
        &self.elem
    }

    /// Биты ячейки `at`. `None` - номер вне длины.
    ///
    /// Вне длины - **названная граница** §4.11, та же, что была у спайна:
    /// понижение там обрывает процесс, а машина не отвечает вовсе.
    #[must_use]
    pub fn read(&self, at: u64) -> Option<u64> {
        let (from, stride) = self.slice(at)?;
        let cells = self.cells.borrow();
        Some(decoded(cells.get(from..from + stride)?))
    }

    /// Тот же блок с переписанной ячейкой - **новым** блоком.
    ///
    /// Копия, а не запись на месте: `arraySet` функционален, и запись на месте
    /// показала бы новое значение через старое имя. Тем же правилом живёт
    /// рантайм - `adamas_array_writable` копирует разделённый блок, - и
    /// расходиться им негде: массив, который нужен и после записи, у рантайма
    /// разделён по построению.
    #[must_use]
    pub fn with_cell(&self, at: u64, bits: u64) -> Option<Rc<Self>> {
        let (from, stride) = self.slice(at)?;
        let mut copied = Vec::new();
        copied.try_reserve_exact(self.cells.borrow().len()).ok()?;
        copied.extend_from_slice(&self.cells.borrow());
        copied
            .get_mut(from..from + stride)?
            .copy_from_slice(&encoded(bits, stride)[..stride]);
        Some(Rc::new(Self {
            ty: self.ty,
            elem: Rc::clone(&self.elem),
            count: self.count,
            cells: std::cell::RefCell::new(copied),
        }))
    }

    /// Смещение ячейки и её ширина. `None` - номер вне длины.
    fn slice(&self, at: u64) -> Option<(usize, usize)> {
        if at >= self.count {
            return None;
        }
        let stride = self.ty.size() as usize;
        Some((usize::try_from(at).ok()?.checked_mul(stride)?, stride))
    }

    /// Одалживает адрес нагрузки на время вызова `borrower` (§5.3).
    ///
    /// Заём есть **вычисление адреса**, и байты за ним - те самые, которые
    /// прочтёт следующий [`Block::read`]. Что чужая сторона по этому адресу
    /// сделает, не знает никто: это содержание уровня 1 (§5.3).
    ///
    /// `None` - блок уже одолжен: заём внутри займа означал бы, что чужая
    /// сторона позвала нас обратно, а колбэков уровень 1 не имеет. Отказ, а не
    /// паника: до этого места доезжает пользовательский текст.
    pub fn lend<R>(&self, borrower: impl FnOnce(*mut u8) -> R) -> Option<R> {
        let mut cells = self.cells.try_borrow_mut().ok()?;
        Some(borrower(cells.as_mut_ptr()))
    }

    /// Те же ли это байты той же ширины и длины.
    ///
    /// Тождество здесь **не** спрашивается: конвертируемость есть равенство
    /// значений, а два `arrayNew 3 zero` суть одно значение в двух блоках.
    #[must_use]
    pub fn alike(&self, other: &Self) -> bool {
        self.ty == other.ty
            && self.count == other.count
            && *self.cells.borrow() == *other.cells.borrow()
    }
}

/// Биты литерала в байты ячейки - **машинным** порядком.
///
/// Порядок именно машинный, а не выбранный: байты эти читает чужая сторона по
/// одолженному адресу, и они обязаны лежать так же, как их кладёт рантайм
/// (`adamas-runtime/c/array.c` пишет ячейку обычным присваиванием). Своим
/// порядком блок разошёлся бы с понижением на всякой ячейке шире байта.
/// Значащие байты слова у ячейки шириной `stride` лежат в начале машинного
/// представления на little-endian и в конце - на big-endian; отсюда обе ветви.
fn encoded(bits: u64, stride: usize) -> [u8; 8] {
    let word = bits.to_ne_bytes();
    if cfg!(target_endian = "big") {
        let mut moved = [0u8; 8];
        moved[..stride].copy_from_slice(&word[8 - stride..]);
        return moved;
    }
    word
}

/// Байты ячейки обратно в биты литерала - тем же машинным порядком.
///
/// Расширение **нулём**, а не знаком: биты литерала ядра хранятся обрезанными
/// по ширине типа (`PrimTy::masked`), и знаковое расширение здесь завело бы
/// второе представление `-1 : Int8`.
fn decoded(bytes: &[u8]) -> u64 {
    let width = bytes.len().min(8);
    let mut word = [0u8; 8];
    if cfg!(target_endian = "big") {
        word[8 - width..].copy_from_slice(&bytes[..width]);
    } else {
        word[..width].copy_from_slice(&bytes[..width]);
    }
    u64::from_ne_bytes(word)
}

/// Элиминатор в спайне застрявшего вычисления.
///
/// Спайн - не просто список аргументов: разбор по конструктору тоже застревает
/// на неизвестном значении и тоже может быть продолжен применением
/// (`(case x of …) y`). Одно перечисление на оба вида снимает вопрос "в каком
/// порядке они шли" - порядок и есть порядок спайна.
#[derive(Clone, Debug)]
pub enum Elim {
    /// Применение к аргументу.
    App(Rc<Value>),
    /// Разбор по конструктору.
    Case(Rc<StuckCase>),
    /// Проекция поля записи.
    Project(Name),
    /// Переопределение полей записи: `{ p | x = v }`.
    ///
    /// Стоит в спайне, а не отдельным значением: проекция сквозь него
    /// считается (`{ p | x = v }.x` есть `v`, а `.y` - `p.y`), то есть ведёт
    /// себя ровно как элиминатор, застрявший на неизвестной базе.
    With(Rc<[(Name, Rc<Value>)]>),
}

/// Разбор, застрявший на неизвестном значении.
///
/// Мотив и ветви уже вычислены: [`crate::term::Case`] собственных связываний не
/// вводит, поэтому хранить замыкания незачем - это обычные значения
/// функционального типа.
#[derive(Clone, Debug)]
pub struct StuckCase {
    /// Индуктивный тип, по которому шёл разбор.
    pub data: Name,
    /// Аргументы уровня этого типа, уже нормализованные.
    pub levels: Rc<[Level]>,
    /// Сколько первых аргументов конструктора - параметры.
    pub params: u32,
    /// Кратность потребления разбираемого - см. [`crate::term::Case::consumed`].
    pub consumed: Mult,
    /// Мотив как значение.
    pub motive: Rc<Value>,
    /// Ветви в порядке объявления конструкторов.
    pub branches: Vec<StuckBranch>,
}

/// Ветвь застрявшего разбора.
#[derive(Clone, Debug)]
pub struct StuckBranch {
    /// Конструктор, который она разбирает.
    pub constructor: Name,
    /// Тело как значение - функция от полей конструктора.
    pub body: Rc<Value>,
}

/// Значение - терм, вычисленный до слабой головной нормальной формы.
#[derive(Clone, Debug)]
pub enum Value {
    /// Застрявшее вычисление: голова, к которой применены элиминаторы.
    ///
    /// Спайн хранится в порядке применения, то есть `x a b` - это голова `x`
    /// и спайн `[a, b]`.
    Neutral(Head, Vec<Elim>),
    /// Стёртое: значения нет, и вычислять было нечего (§3.3).
    ///
    /// Аргумент при связывании кратности `0` машина **не вычисляет** - на его
    /// место встаёт этот маркер. Так проверяется обещание «доказательства
    /// ничего не стоят в рантайме»: до понижения (§9 Фаза 6) стёртое ехало
    /// наравне с прочим и печаталось в значении.
    ///
    /// Маркер, а не значение: употребить его нельзя, и не потому, что запрещено,
    /// а потому, что употреблять нечего. Всплывший наружу означал бы дыру в
    /// учёте кратностей - проверка обязана держать стёртое в стёртых позициях.
    Erased,
    /// Функция.
    Lam(Mult, Name, Closure),
    /// Тип функции вместе с row того, что происходит при применении (§3.4).
    ///
    /// Row - замыкание по той же причине, что и кодомен: она стоит под
    /// связыванием и вправе называть аргумент.
    Pi(Binder, Name, Rc<Value>, RowClosure, Closure),
    /// Тип записи - телескоп полей вместе с окружением.
    ///
    /// Хранится термами, а не значениями: тип поля живёт под предыдущими
    /// полями, поэтому вычислить его можно только тогда, когда их значения
    /// известны. Ровно тот же приём, что у [`Closure`], только связываний в нём
    /// не одно.
    Record(Telescope),
    /// Значение записи. Зависимости здесь уже нет - поля вычислены.
    Object(Rc<[(Name, Rc<Value>)]>),
    /// Сорт рядов `Row ℓ`.
    RowKind(Level),
    /// Сорт `Effect` - то, чем оканчивается тип формера метки (§3.4).
    EffectKind,
    /// Ряд - тот же телескоп, но сортом он не тип, а ряд.
    Row(Telescope),
    /// Универсум.
    Universe(Level),
    /// Примитивный тип либо литерал (§4.3, §4.11).
    ///
    /// Операция сюда не попадает: она застревает головой спайна
    /// ([`Head::Prim`]) и сводится, когда оба аргумента оказались литералами.
    Prim(Prim),
}

/// Телескоп полей записи: термы вместе с окружением, в котором их вычислять.
#[derive(Clone, Debug)]
pub struct Telescope {
    pub(crate) env: Env,
    pub(crate) fields: Fields,
}

impl Telescope {
    /// Поля как они написаны - имена и кратности видны без вычисления.
    #[must_use]
    pub fn fields(&self) -> &[Field] {
        &self.fields.fields
    }

    /// Открыт ли ряд хвостом.
    #[must_use]
    pub fn is_open(&self) -> bool {
        self.fields.is_open()
    }

    /// Хвост-row как значение, если запись открыта.
    ///
    /// Вычисляется в окружении телескопа и **не** под полями: открытая запись
    /// зависимостей не имеет (§4.2, решение 2026-08-29), поэтому хвост от
    /// полей не зависит.
    #[must_use]
    pub fn tail(&self) -> Option<Rc<Value>> {
        self.fields
            .tail
            .as_ref()
            .map(|tail| crate::eval::eval(&self.env, tail))
    }

    /// Тип поля `index` при уже известных значениях предыдущих полей.
    ///
    /// # Panics
    ///
    /// Если значений меньше, чем полей до `index`: телескоп вычисляется по
    /// одному полю, и пропуск - баг вызывающего.
    #[must_use]
    pub fn at(&self, index: usize, earlier: &[Rc<Value>]) -> Rc<Value> {
        self.instantiated(index, earlier, &[], &[], &[])
    }

    /// То же с подставленными **собственными** параметрами поля.
    ///
    /// Поле записи связывает свои стёртые параметры (§10 вопрос 115), и
    /// проекция их инстанцирует - как всякая ссылка на определение. Пустые
    /// списки дают прежнее поведение: поле без параметров подставлять нечем.
    ///
    /// # Panics
    ///
    /// Если предыдущих полей дано меньше, чем нужно: телескоп вычисляется по
    /// порядку, и это баг вызывающего, а не ошибка проверяемой программы.
    #[must_use]
    pub fn instantiated(
        &self,
        index: usize,
        earlier: &[Rc<Value>],
        levels: &[crate::level::Level],
        rows: &[crate::row::Row<crate::term::Term>],
        mults: &[crate::mult::Mult],
    ) -> Rc<Value> {
        assert!(earlier.len() >= index, "телескоп вычисляется по порядку");
        let env = earlier[..index]
            .iter()
            .fold(self.env.clone(), |env, value| env.extend(Rc::clone(value)));
        let ty = &self.fields[index].ty;
        let ty = if levels.is_empty() && rows.is_empty() && mults.is_empty() {
            Rc::clone(ty)
        } else {
            Rc::new(
                ty.substitute_levels(levels)
                    .substitute_rows(rows)
                    .substitute_field_mults(mults),
            )
        };
        crate::eval::eval(&env, &ty)
    }
}

impl Value {
    /// Свободная переменная - нейтральное значение с пустым спайном.
    #[must_use]
    pub fn var(level: Lvl) -> Rc<Self> {
        Rc::new(Self::Neutral(Head::Local(level), Vec::new()))
    }

    /// Определение, ещё не развёрнутое.
    ///
    /// Аргументы уровня нормализуются здесь, и только здесь. Без этого
    /// `Box{max 0 1}` и `Box{1}` - разные головы, то есть один и тот же тип,
    /// записанный двумя способами, оказывается неконвертируемым сам с собой.
    /// У определения с телом это спасал бы δ-разворот, у постулата
    /// разворачивать нечего.
    #[must_use]
    pub fn constant(
        name: Name,
        levels: &[Level],
        rows: Rc<[Row<Rc<Self>>]>,
        mults: Mults,
    ) -> Rc<Self> {
        let normalized: Rc<[Level]> = levels.iter().map(Level::normalize).collect();
        Rc::new(Self::Neutral(
            Head::Global(name, normalized, rows, mults),
            Vec::new(),
        ))
    }
}

impl fmt::Display for Value {
    /// Печатает только форму значения: содержательный вывод получается
    /// обратным переводом в терм через [`crate::eval::quote`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Neutral(Head::Local(Lvl(level)), spine) => {
                write!(f, "@{level}·{}", spine.len())
            }
            Self::Neutral(Head::Global(name, ..), spine) => {
                write!(f, "{name}·{}", spine.len())
            }
            Self::Neutral(Head::Meta(TermMeta(name)), spine) => {
                write!(f, "?{name}·{}", spine.len())
            }
            Self::Neutral(Head::Prim(op, ty), spine) => {
                write!(f, "{op}{ty}·{}", spine.len())
            }
            Self::Neutral(Head::Cmp(op, ty), spine) => {
                write!(f, "{op}{ty}·{}", spine.len())
            }
            Self::Neutral(Head::Array, spine) => {
                write!(f, "{}·{}", crate::prim::ARRAY, spine.len())
            }
            Self::Neutral(Head::ArrayOp(op), spine) => {
                write!(f, "{op}·{}", spine.len())
            }
            // Содержимое здесь не печатается по тому же правилу, что и всюду в
            // этом impl'е: он показывает **форму** значения, а содержательный
            // вывод даёт обратное чтение.
            Self::Neutral(Head::Block(block), spine) => {
                write!(
                    f,
                    "[{} × {}]·{}",
                    block.count(),
                    block.ty().name(),
                    spine.len()
                )
            }
            Self::Neutral(Head::Region(op), spine) => {
                write!(f, "{op}·{}", spine.len())
            }
            Self::Neutral(Head::Simd, spine) => {
                write!(f, "{}·{}", crate::prim::SIMD, spine.len())
            }
            Self::Neutral(Head::SimdOp(op), spine) => {
                write!(f, "{op}·{}", spine.len())
            }
            Self::Prim(prim) => write!(f, "{prim}"),
            Self::Lam(mult, name, _) => write!(f, "\\({mult} {name}) -> …"),
            Self::Pi(binder, name, _, row, _) => {
                let (open, close) = binder.visibility.brackets();
                let row = row.written();
                write!(f, "{open}{} {name} : …{close} -> {row}…", binder.mult)
            }
            Self::Record(telescope) => write!(f, "{{…{}}}", telescope.fields().len()),
            Self::RowKind(level) => write!(f, "Row {level}"),
            Self::EffectKind => f.write_str("Effect"),
            Self::Row(telescope) => write!(f, "{{|{}}}", telescope.fields().len()),
            Self::Object(fields) => write!(f, "{{={}}}", fields.len()),
            Self::Universe(level) => write!(f, "Type {level}"),
            Self::Erased => f.write_str(ERASED),
        }
    }
}

/// Освобождение окружения идёт **циклом**, а не рекурсией.
///
/// Окружение - односвязный список ячеек, и его длина растёт с числом
/// связываний, а не с текстом программы: замыкание, снявшее окружение глубокой
/// раскрутки, носит его целиком. Рекурсивный `drop` кладёт стек там же, где и
/// на значении (§10 вопрос 92).
///
/// Разбор ячейки здесь свободен - [`Cell`] своего `Drop` не имеет, - поэтому
/// заглушка, нужная терму, тут не нужна.
impl Drop for Env {
    fn drop(&mut self) {
        let mut current = self.head.take();
        while let Some(cell) = current {
            // `None` - хвост делят с кем-то ещё, и дальше он не наш.
            let Some(cell) = Rc::into_inner(cell) else {
                break;
            };
            current = cell.rest;
        }
    }
}

/// Освобождение значения идёт **циклом**, а не рекурсией.
///
/// Цепочка конструкторов бывает какой угодно длины - список в сорок тысяч
/// звеньев есть `Cons x (Cons y …)` той же глубины, - и рекурсивный `drop`
/// кладёт на ней стек. Наблюдалось это как `SIGABRT` на программе, которая
/// глубокое значение **только строит и не обходит** (§10 вопрос 92): исполнение
/// к тому времени рекурсию уже не держало, а освобождение держало.
///
/// Снимаются только дети из спайна нейтрали: глубина берётся оттуда. Прочие
/// поля - окружение замыкания, телескоп записи - рвутся по-прежнему рекурсивно,
/// и предел у них остаётся; глубоким бывает и то и другое реже, а
/// единообразного способа отобрать `Rc<[T]>` по частям нет.
impl Drop for Value {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        detach(self, &mut pending);
        while let Some(value) = pending.pop() {
            // `None` - значение делят с кем-то ещё, и рвать его не наше дело.
            if let Some(mut owned) = Rc::into_inner(value) {
                detach(&mut owned, &mut pending);
            }
        }
    }
}

/// Отбирает у значения детей, которых предстоит освободить, не входя в них.
///
/// После этого собственный `drop` значения глубины не имеет: спайн пуст.
fn detach(value: &mut Value, into: &mut Vec<Rc<Value>>) {
    let Value::Neutral(_, spine) = value else {
        return;
    };
    for elim in spine.drain(..) {
        if let Elim::App(argument) = elim {
            into.push(argument);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{Elim, Env, Head, Lvl, Value};
    use crate::term::{Index, Term};

    /// Глубина, на которой рекурсивное освобождение кладёт стек теста
    /// заведомо: у тестового потока его два мегабайта.
    const DEEP: usize = 200_000;

    #[test]
    fn a_deep_constructor_chain_is_freed_without_the_rust_stack() {
        let mut value = Value::var(Lvl(0));
        for _ in 0..DEEP {
            value = Rc::new(Value::Neutral(Head::Local(Lvl(0)), vec![Elim::App(value)]));
        }
        drop(value);
    }

    #[test]
    fn a_deep_application_spine_is_freed_without_the_rust_stack() {
        let mut term = Rc::new(Term::Var(Index(0)));
        for _ in 0..DEEP {
            term = Rc::new(Term::App(Rc::new(Term::Var(Index(0))), term));
        }
        drop(term);
    }

    #[test]
    fn a_long_environment_is_freed_without_the_rust_stack() {
        let mut env = Env::default();
        for _ in 0..DEEP {
            env = env.extend(Value::var(Lvl(0)));
        }
        drop(env);
    }

    #[test]
    fn lookup_walks_outwards_from_the_innermost_binding() {
        let env = Env::default()
            .extend(Value::var(Lvl(0)))
            .extend(Value::var(Lvl(1)));

        // Index(0) - ближайшее связывание, то есть добавленное последним.
        assert!(matches!(
            *env.lookup(Index(0)).unwrap(),
            Value::Neutral(Head::Local(Lvl(1)), _)
        ));
        assert!(matches!(
            *env.lookup(Index(1)).unwrap(),
            Value::Neutral(Head::Local(Lvl(0)), _)
        ));
        assert!(env.lookup(Index(2)).is_none(), "за пределами окружения");
    }

    #[test]
    fn extending_does_not_disturb_the_original() {
        let outer = Env::default().extend(Value::var(Lvl(0)));
        let inner = outer.extend(Value::var(Lvl(1)));
        assert_eq!(outer.len(), 1);
        assert_eq!(inner.len(), 2);
    }

    #[test]
    fn levels_and_indices_are_mirror_images() {
        // В контексте размера 3 самое внешнее связывание - уровень 0 и
        // индекс 2; самое внутреннее - уровень 2 и индекс 0.
        assert_eq!(Lvl(0).to_index(3), Index(2));
        assert_eq!(Lvl(2).to_index(3), Index(0));
    }
}
