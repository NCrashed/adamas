//! Понижение термов ядра в [`ir`](crate::ir).
//!
//! Берётся **чистый фрагмент** - семейства и конструкторы, функции и
//! применение, разбор, рекурсия, `let` - плюс **эффекты одношотом целиком**:
//! хендлер всех трёх вердиктов ветки ([`Lowerer::handled`]), параметризованный
//! хендлер тем же путём (§10 вопрос 129) и маска ([`Lowerer::masked`]).
//! Мультишот отвергается своим отказом: молча посчитать не то хуже, чем не
//! посчитать.
//!
//! # Форма понижения выбрана, а не подразумевается
//!
//! Формы две (§13, обе записи 2026-09-08), и решает между ними **row
//! написанного типа** ([`form`]): меток нет - первая, есть - вторая, со своими
//! двумя скрытыми аргументами. Лямбда - единственное исключение, и оно не
//! послабление: написанного типа у её связывания в ядре нет вовсе, а угаданная
//! первая форма не дала бы ей произвести операцию. Цена исключения ноль -
//! прямого вызова у лямбды не бывает (см. [`Lowerer::closure`]).
//!
//! Функция первой формы, ставящая хендлер, - **корень своего стека**: скрытых
//! аргументов у неё нет, а кадр ставить надо. Законно это ровно потому, что
//! row её пуста: операции наружу не уходит ни одной (§3.4, погашение
//! расширением справа), и всё, что под ней производится, гасится внутри неё же.
//!
//! # Что здесь повторено за машиной, а не придумано заново
//!
//! **Стирание аргумента.** Машина стирает аргумент, когда вызываемое -
//! глобальное имя, а связывание его **типа** на этой позиции нулевое
//! (`adamas-interp/src/machine.rs`, `erases`). Кратность самой лямбды признаком
//! не служит: решение дырки терма есть цепочка лямбд при `0`, и значения в них
//! настоящие. Здесь ровно то же правило и ровно по тому же источнику - тип из
//! сигнатуры.
//!
//! **Поля ветви.** Ветвь получает связывания конструктора после параметров
//! семейства - столько же и в том же порядке, включая стёртые.
//!
//! # Откуда берётся представление (§4.11)
//!
//! Плоское значение заголовка не имеет вовсе (§13, 2026-09-08), поэтому
//! [`Repr`] обязан быть известен **до** эмиссии: от него зависят C-тип
//! связывания, наличие RC-трафика и то, чем считает слот дроп с печатью.
//!
//! Читается он там, где тип **написан**: домен `Pi` даёт представление
//! параметра и поля конструктора, аннотация `let` - своего связывания, а
//! литерал и операция несут тип в себе. Дальше представление **синтезируется**
//! снизу вверх - каждое выражение отдаёт своё вместе с собой, - и в объявленных
//! позициях сверяется. Расхождение отвергается
//! ([`LowerError::Representation`]), а не приводится молча: биты числа,
//! принятые за указатель, суть чтение по адресу этого числа.
//!
//! Написан тип не везде: у связывания лямбды его нет в ядре вовсе. Поэтому
//! связывание лямбды объявляется указательным, а плоское значение,
//! пришедшее в такую позицию, отвергается.
//!
//! **Дескриптор эту границу не снял, и это измерено.** План фазы ждал
//! обратного: дескриптор даёт **шаг**, а замыканию нужен единообразный
//! **слот**, и второе есть боксирование (§5.1, «боксирование при передаче
//! значения в позицию, скомпилированную по указательному представлению»), а
//! не индексация. Свидетель прежний и по-прежнему красный на попытке -
//! `tests/flat.rs`, `a_flat_value_does_not_cross_a_closure`.
//!
//! # Массив: представление одно на два случая (§4.11)
//!
//! `Array n a` есть один объект кучи независимо от элемента; раздваивается
//! **укладка ячеек**. При плоском элементе они лежат подряд по `stride` байт,
//! иначе - слотами указателей ([`Elems`]). Шаг читается не у массива, а у
//! **написанного типа элемента**, и приходит он двумя путями, которые §4.11
//! называет обоими:
//!
//! - элемент - примитив, и шаг известен типом ([`Stride::Static`]);
//! - элемент - переменная, о которой в телескопе функции есть словарь `Flat`,
//!   и шаг приходит его полем ([`Stride::Dynamic`]).
//!
//! Второе и есть «функция с `{Flat a}` в контексте получает дескриптор обычным
//! имплиситом». Мономорфизация (`adamas_elab::mono`) переводит второй путь в
//! первый, и оба обязаны давать один ответ - свидетель `tests/array.rs`.
//!
//! Функция **без** `{Flat a}` компилируется по указательному представлению, как
//! §4.11 и говорит, поэтому плоский массив в неё не проходит: это была бы
//! передача в позицию другого представления, то есть снова боксирование.
//!
//! # Арность берётся у типа, а не у тела (§10 вопрос 153)
//!
//! Определение приходит **свёрнутым по эте** от трёх источников сразу, и это
//! измерено, а не предположено. Мономорфизация: `add@_,Add#Int64` имеет тип
//! `Int64 -> Int64 -> Int64` и тело `Const("Add#Int64.add")`. Написанное от
//! руки целиком: `again = plus`. Написанное от руки частично: у `half x = plus
//! x` лямбда одна, а стрелок две. Бери арность у тела - и в первых двух случаях
//! её ноль, в третьем единица, а недоданные аргументы уходят применением к
//! значению, то есть через границу замыкания, где плоскому места нет.
//!
//! Поэтому параметров у функции столько, сколько **стрелок у типа**;
//! недостающие связывания достраиваются здесь и дописываются к спайну тела.
//! Терм при этом не переписывается: снятые лямбды остаются в среде де Брёйна
//! на своих местах, а достроенные в неё не попадают вовсе - тело на них
//! сослаться не может по построению. Отсюда и нет сдвигов.
//!
//! Тело, спайном не являющееся (`case`, `let`, лямбда под `0`-связыванием),
//! дописать некуда: достроенные параметры применяются к его значению обычным
//! путём, и плоское там по-прежнему отвергается.
//!
//! # Чего понижение не делает
//!
//! Не бета-редуцирует, не инлайнит, не кеширует значение определения без
//! параметров: оптимизаций на этом срезе нет вовсе, и предсказуемость выхода
//! дороже его длины.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use adamas_core::eval::{eval, quote};
use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::prim::{ArrayOp, Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::{CLOSING, DefinitionKind, Signature};
use adamas_core::term::{Case, Index, Name, Term};
use adamas_core::value::{Env, Lvl, Value};

use crate::ir::{
    Arm, Binding, Branch, Constructor, CtorId, Elems, Expr, Fact, FiberOp, Form, FuncId, Function,
    Handler, HandlerId, Label, LabelId, LocalId, PackId, Packing, Program, Repr, Slot as PackSlot,
    SlotTy, Stride, Task, Variant, Verdict,
};

/// Почему понижение отказало.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    /// Имя, которого нет в сигнатуре.
    #[error("имя `{name}` не объявлено")]
    Unknown {
        /// Оно самое.
        name: String,
    },

    /// Постулат: тип есть, тела нет, понижать нечего.
    #[error("`{name}` - постулат: тела нет, и понижать нечего")]
    Postulate {
        /// Имя постулата.
        name: String,
    },

    /// Питомник в позиции, где круга не завести (§5.2).
    ///
    /// Ненасыщенный `withNursery` был бы замыканием, а тело круга рантайм
    /// принимает значением на месте. Отмена задачи в первой форме - тот же
    /// жанр: раскрутка отменённого файбера кладётся кадром, а кадр умеет
    /// только вторая форма.
    #[error("`{name}` - питомник (§5.2): {why}")]
    Nursery {
        /// Имя постулата либо операции.
        name: String,
        /// Чем именно позиция не годится.
        why: &'static str,
    },

    /// Элиминатор хендлера, которого этот срез не ставит.
    ///
    /// Отказ **не про форму функции**: форму каждое определение получает по
    /// row своего типа, и эффектное получает вторую. Не поставлен кадр
    /// конкретно этого элиминатора.
    #[error("`{name}` - {why}")]
    Handler {
        /// Имя элиминатора.
        name: String,
        /// Чем именно он не берётся и чей это трек.
        why: &'static str,
    },

    /// Ветка хендлера, которую этот срез не понижает.
    ///
    /// Вердикт ветки трёхзначный (§3.4): хвостово-резумптивная зовётся на
    /// месте, абортивная снимает сегмент, общая режет его в резумпцию. Берётся
    /// здесь первая, и отказ называет, чем оказались остальные, - молча
    /// посчитать не то хуже, чем не посчитать.
    #[error("ветка `{operation}` хендлера `{effect}` {why}")]
    Verdict {
        /// Метка хендлера.
        effect: String,
        /// Операция, чья ветка.
        operation: String,
        /// Каким вердикт вышел и чей это трек.
        why: &'static str,
    },

    /// Метка эффекта либо её операция в позиции, где значения у неё нет.
    #[error("`{name}` - {why}")]
    Operation {
        /// Имя метки или операции.
        name: String,
        /// Почему не понижается.
        why: &'static str,
    },

    /// Семейство в позиции значения.
    #[error("`{name}` - семейство типов: значения у него в рантайме нет")]
    TypeValue {
        /// Имя семейства.
        name: String,
    },

    /// Форма терма, которой чистый фрагмент не знает.
    #[error("{form} этим срезом не берётся")]
    Unsupported {
        /// Что именно встретилось.
        form: &'static str,
    },

    /// Ответ программы - функция.
    #[error("ответ программы - функция: печатать её нечем")]
    FunctionAnswer,

    /// Конструкторов больше, чем тегов: верх диапазона занят рантаймом.
    #[error("конструкторов больше {limit}: верх диапазона тегов занят рантаймом")]
    TooManyConstructors {
        /// Сколько их помещается.
        limit: u16,
    },

    /// Переменная за пределами захваченной среды - дефект анализа свободных.
    #[error("переменная #{index} вне захваченной среды")]
    Unbound {
        /// Индекс де Брёйна.
        index: u32,
    },

    /// Живому связыванию не досталось аргумента.
    #[error("`{name}`: живому связыванию #{binder} не досталось аргумента")]
    Missing {
        /// Кому.
        name: String,
        /// Какому связыванию.
        binder: usize,
    },

    /// Представление значения разошлось с представлением позиции (§4.11).
    ///
    /// Отказ, а не приведение: заголовка у плоского значения нет вовсе, и
    /// положить его туда, где ждут указатель, значит отдать биты числа
    /// счётчику ссылок.
    #[error("{at}: ожидалось {want}, а пришло {got} (§4.11)")]
    Representation {
        /// В какой позиции.
        at: &'static str,
        /// Что там объявлено.
        want: String,
        /// Что туда пришло.
        got: String,
    },

    /// Примитивная операция без обоих аргументов.
    ///
    /// Значением она была бы замыканием, а замыкание принимает аргументы
    /// указательными: плоскому нужен дескриптор layout (§4.11), и это
    /// следующая половина трека.
    #[error("`{name}` без обоих аргументов: примитив значением требует дескриптора layout (§4.11)")]
    Partial {
        /// Имя операции.
        name: String,
    },

    /// Операция над массивом без всех аргументов.
    ///
    /// Недобранной она была бы замыканием, а через замыкание не проходит ни
    /// плоский элемент, ни дескриптор (§4.11).
    #[error("`{name}` без всех аргументов: операция над массивом значением этим срезом не берётся")]
    PartialArray {
        /// Имя операции.
        name: String,
    },

    /// Ответ программы - массив.
    ///
    /// Печатать его нечем, и это названная граница: `adamas eval` печатает
    /// цепочку `arrayNew`/`arraySet` со стёртыми аргументами, понижение -
    /// значение, и сводить эти две печати - работа не этого среза.
    #[error("ответ программы - массив: печатать его нечем (§4.11)")]
    ArrayAnswer,

    /// Операция над регионом без всех аргументов.
    ///
    /// Тот же довод, что у массива: недобранная была бы замыканием, а через
    /// границу замыкания не проходит ни блок, ни плоская нагрузка.
    #[error("`{name}` без всех аргументов: операция над регионом значением этим срезом не берётся")]
    PartialRegion {
        /// Имя операции.
        name: String,
    },

    /// Нагрузка региона не плоская (§3.6).
    ///
    /// Понижение спрашивает это **вторым**: первым спрашивает элаборация, и
    /// отказ её называет поле. Сюда доходит то, чего типовая сторона не видит:
    /// нагрузка, чью укладку понижение не выражает (§10 вопросы 157, 158).
    #[error("нагрузка региона `{written}` плоской укладки в понижении не имеет (§3.6, §4.11)")]
    RegionPayload {
        /// Как названо представление нагрузки.
        written: String,
    },

    /// Ответ программы - блок региона.
    ///
    /// Названная граница того же жанра, что массив в ответе: `adamas eval`
    /// печатает цепочку `regionNew`/`regionAlloc`, понижение - область байт.
    #[error("ответ программы - блок региона: печатать его нечем (§3.6)")]
    RegionAnswer,

    /// Ответ программы - плоский агрегат.
    ///
    /// Печать идёт по тегу заголовка, а у плоского агрегата заголовка нет
    /// вовсе (§4.11): в ответе лежат байты. Названная граница того же жанра,
    /// что массив в ответе.
    #[error("ответ программы - плоский агрегат: заголовка у него нет, печатать нечем (§4.11)")]
    PackedAnswer,

    /// Дескриптор укладки написан не той записью.
    #[error("дескриптор укладки ожидался записью `{{ layout = {{ size, align }} }}` (§4.11)")]
    Descriptor,

    /// Проекция из значения, чьей формы понижение не знает.
    ///
    /// Имени поля в рантайме нет - слот раздаёт форма записи (§4.2), - поэтому
    /// проекция без формы неисполнима. Формы нет там, где представление
    /// расширилось до указательного: поле полиморфного конструктора, связывание
    /// лямбды, ответ применения.
    #[error("`.{label}`: форма записи потеряна, слот брать неоткуда (§4.2)")]
    Shapeless {
        /// Какое поле берут.
        label: String,
    },

    /// Выход из scope пришёл не в той форме, в какой его ставит §3.3.
    ///
    /// `#closing` четырёхместен, и оба вычисления в нём приостановлены -
    /// `(ω _ : Unit) ->`. Понижение снимает приостановку разом, а не строит
    /// замыкание: замыкание стоило бы ячейки кучи на каждый scope.
    #[error("выход из scope без обоих приостановленных вычислений (§3.3)")]
    Scope,

    /// Проекция поля, которого в форме записи нет.
    #[error("`.{label}`: поля нет в форме `{shape}` (§4.2)")]
    NoField {
        /// Какое поле берут.
        label: String,
        /// Из чего берут.
        shape: String,
    },
}

/// Требует, чтобы все живые связывания жили указателем.
fn pointing(facts: &[Fact], at: &'static str) -> Result<(), LowerError> {
    for fact in facts {
        if fact.present && !fact.repr.pointer() {
            return Err(LowerError::Representation {
                at,
                want: describe(Repr::Boxed),
                got: describe(fact.repr),
            });
        }
    }
    Ok(())
}

/// Представление поля в слоте объекта кучи.
///
/// Слот несёт указатель либо биты примитива; плоскому агрегату с его
/// собственными байтами там места нет, и поле такого типа хранится
/// боксированным (§4.11). Переклад ставят места построения ([`Lowerer::moved`]).
fn slotted(repr: Repr) -> Repr {
    match repr {
        Repr::Packed(_) => Repr::Boxed,
        other => other,
    }
}

/// Годится ли пришедшее представление в объявленную позицию.
///
/// Совпадение - обычный случай. Послаблений два, и оба про **запись**: у неё
/// тот же C-тип, тот же заголовок и тот же счётчик, что у указателя, и
/// различает их одно - помнит ли понижение форму.
///
/// *Расширение* - запись в позицию указателя. Форма теряется, и проекция после
/// потери отвергается по имени ([`LowerError::Shapeless`]). Без него запись не
/// легла бы в поле полиморфного конструктора (`Cons { size = 4, align = 4 }
/// Nil`), а §4.11 пишет ровно такое.
///
/// *Сужение* - указатель в позицию записи. Здесь верят **объявлению**: форму
/// назвал написанный тип позиции, а значение потеряло её по дороге - в
/// связывании лямбды, у которого типа в ядре нет вовсе. Верить объявлению
/// безопасно не по построению, а потому, что промах виден: проекция понижается
/// разбором, и тег объекта сверяется в рантайме - форма не та, и прогон
/// обрывается на `default`, а не читает чужой слот.
fn fits(got: Repr, want: Repr) -> bool {
    got == want
        || (want.boxed() && got.pointer())
        || matches!((got, want), (Repr::Boxed, Repr::Record(_)))
}

/// Как представление называется в отказе.
fn describe(repr: Repr) -> String {
    match repr {
        Repr::Boxed => "указательное значение".to_owned(),
        Repr::Flat(ty) => format!("плоское `{ty}`"),
        Repr::Layout => "дескриптор укладки".to_owned(),
        Repr::Opaque => "плоский элемент неизвестного типа".to_owned(),
        Repr::Array(Elems::Flat) => "плоский массив".to_owned(),
        Repr::Array(Elems::Boxed) => "указательный массив".to_owned(),
        Repr::Region => "блок региона".to_owned(),
        Repr::Record(tag) => format!("запись формы #{}", tag.0),
        Repr::Resumption => "резумпция".to_owned(),
        Repr::Packed(pack) => format!("плоский агрегат укладки #{}", pack.0),
    }
}

/// Имя класса представления (§4.11).
///
/// Объявляет его программа - соглашение то же, каким `if` берёт `Bool`, - и
/// понижение читает его по имени ровно там же, где элаборация
/// (`adamas-elab/src/flat.rs`). Второго имени тут не заводится: словарь,
/// пришедший имплиситом, и есть дескриптор.
const FLAT: &str = "Flat";

/// Имя единственного метода `Flat` и полей его укладки (§4.11).
///
/// Читаются они по имени там же, где [`descriptor`] собирает дескриптор:
/// форма словаря записана в §4.11 дословно, и второго источника у неё нет.
const METHOD: &str = "layout";
/// Поле размера в укладке.
const SIZE: &str = "size";
/// Поле выравнивания в укладке.
const ALIGN: &str = "align";

/// Где лежат дескрипторы укладки: уровень описанного связывания - словарь.
///
/// Ключ - **уровень** типового связывания, о котором словарь говорит.
/// Значение - номер того связывания, в котором словарь лежит. Так и читается
/// §4.11 «функция с `{Flat a}` в контексте получает дескриптор обычным
/// имплиситом»: контекст - это телескоп, и найти в нём словарь по типу
/// элемента можно только сравнив, о каком связывании он говорит.
type Dicts = HashMap<u32, LocalId>;

/// Верх диапазона тегов занят служебными объектами рантайма (`adamas.h`).
const TAGS: u16 = 0xFFF0;

/// Невыразимые имена элиминаторов - те же, что ставит элаборация и читает
/// машина (`adamas-interp/src/effect.rs`).
const HANDLE: &str = "#handle.";
/// Мультишот: копирование сегмента - трек E волны 4.
const MULTI: &str = "#handleMulti.";
/// Параметризованный хендлер: кадр `Settling` - трек D волны 4.
const STATEFUL: &str = "#handleState.";
/// Маска: пропуск одного одноимённого хендлера.
const MASK: &str = "#mask.";

/// Имя единицы: приостановленное вычисление запускается её значением.
const UNIT: &str = "Unit";

/// Имена питомника и файберов (§5.2) - те же пять, что знает машина.
///
/// Читаются по имени, как их читает `adamas-interp/src/fiber.rs`. Постулатом
/// стоит `withNursery` - тело ему даёт рантайм; остальные четыре суть операции,
/// которые круг обслуживает сам. Второй записи имён не завести: имена эти
/// соглашение прелюдии, и обе стороны читают одно.
///
/// Узнавание по имени **не** решает, кто операцию обслужит: решает это рантайм
/// по вектору evidence, потому что ближайший выигрывает, а `eval/fibers.adamas`
/// пишет те же имена без всякого питомника.
const NURSERY: &str = "withNursery";
/// Уступка: файбер уходит в хвост очереди.
const SUSPEND: &str = "suspend";
/// Порождение без ответа.
const DETACHED: &str = "spawnDetached";
/// Порождение задачи.
const SPAWN: &str = "spawn";
/// Ожидание чужого ответа.
const AWAIT: &str = "await";

/// Понижает терм в программу.
///
/// `entry` - тело `main` с подставленными аргументами уровня и row, то есть
/// ровно то, что вычисляет `adamas eval`.
///
/// # Errors
///
/// [`LowerError`] - форма вне чистого фрагмента либо имя, которого не понизить.
pub fn lower(signature: &Signature, entry: &Term) -> Result<Program, LowerError> {
    Lowerer::new(signature).program(entry)
}

/// Аргумент спайна.
///
/// Написанных здесь большинство; достроенные приходят от эта-развёртки (§10
/// вопрос 153) - параметр объявлен типом, а в терме его нет.
enum Arg<'a> {
    /// Написан в терме.
    Written(&'a Term),
    /// Достроен по типу определения: связывания в терме нет.
    Supplied(&'a Binding),
}

/// Захват среды: связывания, их значения на месте и среда вложенного тела.
type Captured = (Vec<Binding>, Vec<Expr>, Vec<Slot>);

/// Площадка `handle` глазами одной ветки: всё, что у веток общее.
///
/// Одной записью, а не пятью аргументами: у каждой ветки эти четыре одни и те
/// же, различают их только тело и число связываний.
struct Site<'a> {
    /// Захваченная среда веток - она лежит в кадре хендлера.
    captured: &'a [Binding],
    /// Среда вложенного тела: чем видны захваты изнутри ветки.
    inner: &'a [Slot],
    /// Метка площадки - её называет отказ по вердикту.
    effect: &'a Name,
    /// Мультишотна ли площадка: `#handleMulti.L` против `#handle.L` (§3.4).
    multi: bool,
}

/// Где лежит связывание, видимое телу.
#[derive(Clone, Debug)]
enum Slot {
    /// Связано: номер и факты.
    Bound(LocalId, Fact),
    /// Не захвачено этой функцией: ссылаться на него неоткуда.
    Absent,
}

/// Локальное состояние одной понижаемой функции.
#[derive(Debug, Default)]
struct Scope {
    /// Сколько локальных номеров уже выдано.
    locals: u32,
    /// Связывания в порядке связывания: последнее - индекс 0.
    env: Vec<Slot>,
    /// Дескрипторы укладки, пришедшие имплиситами этой функции (§4.11).
    dicts: Dicts,
}

impl Scope {
    /// Свежий номер.
    fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.locals);
        self.locals += 1;
        id
    }

    /// Связывание по индексу де Брёйна.
    fn slot(&self, Index(index): Index) -> Result<&Slot, LowerError> {
        let from_top = usize::try_from(index).unwrap_or(usize::MAX);
        self.env
            .len()
            .checked_sub(from_top + 1)
            .and_then(|position| self.env.get(position))
            .ok_or(LowerError::Unbound { index })
    }
}

/// Понижение: сигнатура на входе, программа на выходе.
struct Lowerer<'a> {
    signature: &'a Signature,
    constructors: Vec<Constructor>,
    packings: Vec<Packing>,
    tags: HashMap<Name, CtorId>,
    functions: Vec<Function>,
    numbers: HashMap<Name, FuncId>,
    /// Метки эффектов по номеру: номер и есть то, чем метку ищет вектор.
    labels: Vec<Label>,
    /// Номер метки по имени.
    marks: HashMap<Name, LabelId>,
    /// Площадки `handle`.
    handlers: Vec<Handler>,
    /// Определения, чьи тела ещё не понижены.
    ///
    /// Терминацию счёта укладок держит [`recursive`]: поле рекурсивного
    /// семейства называет само семейство, и без проверки по объявлению
    /// `family_packing` разворачивался бы через таблицу конструкторов в себя
    /// до дна стека.
    pending: VecDeque<(FuncId, Name)>,
    /// Идёт ли понижение под ручкой стека - то есть во второй форме.
    ///
    /// Решает это одно: ставить ли кадр `MARK_CLOSING` на выходе из scope
    /// (§3.3). Кадр умеет только вторая форма - у первой стека нет вовсе, и
    /// обрываться в ней нечему. Флаг повторяет `Emitter::hidden` местами
    /// включения: тело второй формы, ветка хендлера, лямбда и **вычисление под
    /// `handle`** - последнее потому, что хендлер в чистой функции заводит
    /// корень своего стека, и scope под ним обязан быть кадром.
    detached: bool,
    /// Семейство, чей разбор есть отмена задачи (§5.2). `None` - питомника в
    /// программе нет вовсе, и отменять нечего.
    task_family: Option<Name>,
}

impl<'a> Lowerer<'a> {
    fn new(signature: &'a Signature) -> Self {
        Self {
            task_family: nursed_family(signature),
            signature,
            constructors: Vec::new(),
            packings: Vec::new(),
            tags: HashMap::new(),
            functions: Vec::new(),
            numbers: HashMap::new(),
            labels: Vec::new(),
            marks: HashMap::new(),
            handlers: Vec::new(),
            pending: VecDeque::new(),
            detached: false,
        }
    }

    /// Понижает точку входа и всё, до чего она дотягивается.
    fn program(mut self, entry: &Term) -> Result<Program, LowerError> {
        if matches!(entry, Term::Lam(..)) {
            return Err(LowerError::FunctionAnswer);
        }
        let entry_id = FuncId(0);
        self.functions.push(Function {
            id: entry_id,
            // Точка входа - первая форма, и написанного типа у неё здесь нет:
            // `entry` приходит термом с подставленными уровнями и row. Row её
            // пуста по построению корпуса - `IO` гасится внутри (`runIO`), а
            // недогашенная метка на верхнем уровне есть §10 вопрос 12, и он
            // волной не решается. Скрытые аргументы ей и передать некому:
            // зовёт её `main` рантайма, а не понижение.
            name: "main".to_owned(),
            form: Form::Stack,
            captured: Vec::new(),
            parameters: Vec::new(),
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let mut scope = Scope::default();
        let (mut body, mut repr) = self.expr(&mut scope, entry)?;
        // У точки входа объявленного типа нет - она уже инстанцирована, - и
        // представление ответа берётся у самого ответа.
        if matches!(repr, Repr::Array(_)) {
            return Err(LowerError::ArrayAnswer);
        }
        if repr == Repr::Region {
            return Err(LowerError::RegionAnswer);
        }
        // Плотный агрегат печатается упакованным: печать идёт по тегу
        // заголовка, а у плотного заголовка нет вовсе (§4.11). Упаковка тут не
        // выбор представления, а цена печати, и она одна на весь ответ.
        if let Repr::Packed(pack) = repr {
            if self.packings[pack.0 as usize]
                .sole()
                .is_some_and(|variant| variant.ctor.is_none())
            {
                let tag = self.boxed_shape(pack)?;
                body = self
                    .boxing(&mut scope, body, pack, tag)?
                    .ok_or(LowerError::PackedAnswer)?;
                repr = Repr::Record(tag);
            } else {
                // Семейство печатается собственным конструктором; не собрался
                // объект - печатать нечем, и это названная граница.
                body = self
                    .loosening(&mut scope, body, pack)?
                    .ok_or(LowerError::PackedAnswer)?;
                repr = Repr::Boxed;
            }
        }
        self.functions[entry_id.0].body = body;
        self.functions[entry_id.0].result = repr;

        // Очередь, а не рекурсия: имя получает номер до того, как понижено его
        // тело, поэтому рекурсия и взаимная рекурсия проходят сами собой.
        while let Some((id, name)) = self.pending.pop_front() {
            let (parameters, inner, taken, dicts) = self.peeled(&name)?;
            let mut scope = Scope {
                // Номера выданы всем параметрам, включая достроенные, а в среду
                // де Брёйна попадают только снятые: на достроенные тело
                // сослаться не может, их в нём нет.
                locals: u32::try_from(parameters.len()).unwrap_or(u32::MAX),
                env: Vec::with_capacity(taken),
                dicts,
            };
            for parameter in &parameters[..taken] {
                scope.env.push(Slot::Bound(parameter.local, parameter.fact));
            }
            let declared = self.functions[id.0].result;
            self.detached = self.functions[id.0].form == Form::Detached;
            let (mut body, repr) =
                self.saturated(&mut scope, &inner, &parameters[taken..], declared)?;
            if !fits(repr, declared) {
                // Ответ перекладывается, как всякая объявленная позиция:
                // проекция плотного поля отдаёт байты, а объявлен указатель.
                let Some(moved) = self.moved(&mut scope, &body, repr, declared)? else {
                    return Err(LowerError::Representation {
                        at: "ответ функции",
                        want: describe(declared),
                        got: describe(repr),
                    });
                };
                body = moved;
            }
            self.functions[id.0].body = body;
        }

        Ok(Program {
            constructors: self.constructors,
            packings: self.packings,
            labels: self.labels,
            handlers: self.handlers,
            functions: self.functions,
            entry: entry_id,
        })
    }

    /// Определение по имени.
    fn definition(&self, name: &Name) -> Result<&'a adamas_core::sig::Definition, LowerError> {
        self.signature
            .lookup(name)
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Параметры определения, тело под снятыми лямбдами и сколько их снято.
    ///
    /// Параметров столько, сколько **стрелок у типа** (§10 вопрос 153): тело
    /// приходит свёрнутым по эте от трёх источников, и арность по нему выходит
    /// меньше объявленной. Снять из них удаётся столько, сколько у тела ведущих
    /// лямбд, - это и есть `taken`; остальные достраиваются здесь, и в среду
    /// де Брёйна они не идут.
    ///
    /// Кратность и представление каждого берутся из **типа**, а не из лямбды -
    /// тем же правилом, каким машина решает, стирать ли аргумент. Лямбд бывает
    /// и больше, чем стрелок (тип за синонимом): лишние остаются
    /// указательными при `ω`, как и прежде.
    fn peeled(
        &mut self,
        name: &Name,
    ) -> Result<(Vec<Binding>, Rc<Term>, usize, Dicts), LowerError> {
        let definition = self.definition(name)?;
        let body = definition.body.as_ref().ok_or_else(|| {
            // Невыразимое имя без тела заводит элаборация эффектов: `#handle.L`,
            // `#handleMulti.L`, `#mask`, `#closing`. Звать их постулатами
            // формально верно и по существу неверно - автор постулата не писал,
            // а написал `handle`.
            if name.starts_with('#') {
                LowerError::Handler {
                    name: name.to_string(),
                    why: "невыразимое имя без тела: понижение зовёт его формой, а не вызовом",
                }
            } else {
                LowerError::Postulate {
                    name: name.to_string(),
                }
            }
        })?;
        // Словари телескопа считаются **до** параметров: представление массива
        // зависит от того, есть ли в контексте `Flat` на его элемент (§4.11).
        let dicts = dicts_of(self.signature, &definition.ty);
        let mut parameters = Vec::new();
        let mut current = Rc::new(body.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(_, bound, inner) = &*step else {
                break;
            };
            let (mult, repr) = self
                .binder_at(&definition.ty, parameters.len(), &dicts)?
                .unwrap_or((Mult::Many, Repr::Boxed));
            parameters.push(Binding {
                name: bound.to_string(),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult).shaped(repr),
            });
            current = Rc::clone(inner);
        }
        let taken = parameters.len();
        while let Some((mult, repr)) = self.binder_at(&definition.ty, parameters.len(), &dicts)? {
            parameters.push(Binding {
                name: format!("эта{}", parameters.len() - taken),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult).shaped(repr),
            });
        }
        Ok((parameters, current, taken, dicts))
    }

    /// Номер функции определения; тело откладывается в очередь.
    fn function(&mut self, name: &Name) -> Result<FuncId, LowerError> {
        if let Some(id) = self.numbers.get(name) {
            return Ok(*id);
        }
        let (parameters, _, _, dicts) = self.peeled(name)?;
        let ty = &self.definition(name)?.ty;
        let result = self.result_repr(ty, parameters.len(), &dicts)?;
        let form = form(ty);
        let id = FuncId(self.functions.len());
        self.functions.push(Function {
            id,
            name: name.to_string(),
            form,
            captured: Vec::new(),
            parameters,
            result,
            body: Expr::Erased,
        });
        self.numbers.insert(Rc::clone(name), id);
        self.pending.push_back((id, Rc::clone(name)));
        Ok(id)
    }

    /// Заводит теги всем конструкторам семейства разом.
    ///
    /// Разом потому, что разбор требует тега у каждой ветви, а не только у
    /// встреченных конструкторов.
    fn family(&mut self, data: &Name) -> Result<(), LowerError> {
        let definition = self.definition(data)?;
        let DefinitionKind::Data {
            constructors,
            params,
            ..
        } = &definition.kind
        else {
            return Err(LowerError::TypeValue {
                name: data.to_string(),
            });
        };
        for name in constructors {
            if self.tags.contains_key(name) {
                continue;
            }
            // Тег берётся **после** телескопа: поле-запись заводит свою форму,
            // и форма эта живёт в той же таблице. Возьми номер раньше - два
            // конструктора получили бы один тег.
            let ty = &self.definition(name)?.ty;
            let binders = self.binders_of(ty)?;
            let tag = u16::try_from(self.constructors.len())
                .ok()
                .filter(|tag| *tag < TAGS)
                .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
            self.constructors.push(Constructor {
                tag: CtorId(tag),
                name: name.to_string(),
                data: data.to_string(),
                binders,
                params: *params,
                labels: None,
            });
            self.tags.insert(Rc::clone(name), CtorId(tag));
        }
        Ok(())
    }

    /// Тег конструктора: семейство заводится целиком по дороге.
    fn tag(&mut self, name: &Name) -> Result<CtorId, LowerError> {
        if let Some(tag) = self.tags.get(name) {
            return Ok(*tag);
        }
        let DefinitionKind::Constructor { data } = &self.definition(name)?.kind else {
            return Err(LowerError::Unknown {
                name: name.to_string(),
            });
        };
        self.family(data)?;
        self.tags
            .get(name)
            .copied()
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Понижает выражение и отдаёт его представление (§4.11).
    ///
    /// Представление синтезируется, а не проверяется: у каждого узла оно своё,
    /// и в объявленных позициях сверяется [`Lowerer::shaped`].
    fn expr(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        match term {
            Term::Var(index) => match scope.slot(*index)? {
                Slot::Bound(local, fact) if fact.present => Ok((Expr::Local(*local), fact.repr)),
                Slot::Bound(..) => Ok((Expr::Erased, Repr::Boxed)),
                Slot::Absent => Err(LowerError::Unbound { index: index.0 }),
            },
            Term::Lam(..) => self.closure(scope, term),
            Term::App(..) | Term::Const(..) | Term::Prim(_) => {
                let (head, written) = spine(term);
                let arguments: Vec<Arg<'_>> = written.into_iter().map(Arg::Written).collect();
                self.application(scope, head, &arguments)
            }
            Term::Let(mult, name, ty, value, body) => {
                let depth = u32::try_from(scope.env.len()).unwrap_or(u32::MAX);
                let dicts = scope.dicts.clone();
                let declared = self.repr_of(ty, depth, &dicts)?;
                let value = self.shaped(scope, value, declared, "связанное значение")?;
                let binding = Binding {
                    name: name.to_string(),
                    local: scope.fresh(),
                    // Машина считает связанное значение, не спрашивая кратности:
                    // `let 0 x = …` вычисляется наравне с прочими.
                    fact: Fact::present(*mult).shaped(declared),
                };
                scope.env.push(Slot::Bound(binding.local, binding.fact));
                let body = self.expr(scope, body);
                scope.env.pop();
                let (body, repr) = body?;
                Ok((
                    Expr::Bind {
                        binding,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    repr,
                ))
            }
            Term::Case(case) => self.analysis(scope, case),
            // Словарь `Flat` - исключение из общего пути записей: форма его
            // записана в §4.11, а живёт он дескриптором, а не объектом кучи.
            Term::Object(fields) => match descriptor(fields) {
                Some((size, align)) => Ok((Expr::Layout { size, align }, Repr::Layout)),
                None => self.object(scope, fields),
            },
            Term::Project(record, label) => self.projection(scope, record, label),
            // Переопределение доживает до ядра только у **открытой** записи:
            // закрытую элаборация пересобирает полями (§4.2). Форма открытой
            // не перечислима - её знает хвост, - и слотов у неё поэтому нет.
            Term::With(..) => Err(LowerError::Unsupported {
                form: "переопределение открытой записи",
            }),
            Term::Record(_)
            | Term::Pi(..)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Row(_) => Err(LowerError::Unsupported {
                form: "тип в позиции значения",
            }),
            Term::Meta(_) => Err(LowerError::Unsupported {
                form: "неразрешённая дырка",
            }),
        }
    }

    /// Понижает подвыражение и требует от него объявленного представления.
    fn shaped(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        want: Repr,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        let (value, got) = self.expected(scope, term, want)?;
        if fits(got, want) {
            return Ok(value);
        }
        if let Some(moved) = self.moved(scope, &value, got, want)? {
            return Ok(moved);
        }
        Err(LowerError::Representation {
            at,
            want: describe(want),
            got: describe(got),
        })
    }

    /// Перекладывает значение между плотной укладкой и объектом кучи (§4.11).
    ///
    /// Два перехода, и оба стоят копии полей, а не приведения. **Упаковка** -
    /// плотный агрегат туда, где ждут указатель: объект кучи с заголовком,
    /// слот на поле. **Распаковка** - обратно: слоты читаются, байты ложатся
    /// подряд. `None` - перехода нет, и отвечать будет сверка представлений.
    ///
    /// Нужны они потому, что плоское и указательное встречаются в одной
    /// программе по построению: `Array n Vec3` требует плотного элемента
    /// (§4.11), а `Cons` и печать ответа говорят указателями. Цена названа и
    /// она поэлементная; убрать её - работа специализации, а не понижения.
    fn moved(
        &mut self,
        scope: &mut Scope,
        value: &Expr,
        got: Repr,
        want: Repr,
    ) -> Result<Option<Expr>, LowerError> {
        match (got, want) {
            (Repr::Packed(pack), Repr::Boxed | Repr::Record(_)) => {
                if self.packings[pack.0 as usize]
                    .sole()
                    .is_some_and(|variant| variant.ctor.is_none())
                {
                    let tag = self.boxed_shape(pack)?;
                    if !fits(Repr::Record(tag), want) {
                        return Ok(None);
                    }
                    return self.boxing(scope, value.clone(), pack, tag);
                }
                // Семейство: боксированная его форма - обычный объект с тегом
                // конструктора, записью она не бывает.
                if !want.boxed() {
                    return Ok(None);
                }
                self.loosening(scope, value.clone(), pack)
            }
            (Repr::Record(tag), Repr::Packed(pack)) => {
                Ok(self.tightening(scope, value.clone(), tag, pack))
            }
            (Repr::Boxed, Repr::Packed(pack)) => self.narrowing(scope, value.clone(), pack),
            // Примитив в указательной позиции: обёртка с прозрачной печатью -
            // реализация принятого решением §10 вопроса 158, заказчик - §10
            // вопрос 159 (поле параметрического семейства указательно, а
            // значение плоское). Цена - ячейка кучи на пересечение границы;
            // §5.1 называет её источником боксирования, и `@noalloc` её видит.
            (Repr::Flat(prim), Repr::Boxed) => {
                let tag = self.prim_wrapper(prim)?;
                Ok(Some(Expr::Construct {
                    constructor: tag,
                    reuse: None,
                    arguments: vec![value.clone()],
                }))
            }
            // Обратно: обёртка в позиции примитива - биты разбором. Кроме неё,
            // здесь стоять некому: позиция типизирована примитивом, а
            // единственная указательная форма примитива - обёртка.
            (Repr::Boxed, Repr::Flat(prim)) => {
                let tag = self.prim_wrapper(prim)?;
                let binding = Binding {
                    name: "биты".to_owned(),
                    local: scope.fresh(),
                    fact: Fact::present(Mult::Many).shaped(Repr::Flat(prim)),
                };
                let local = binding.local;
                Ok(Some(Expr::Match {
                    scrutinee: Box::new(value.clone()),
                    consumed: Mult::One,
                    arms: vec![Arm {
                        constructor: tag,
                        fields: vec![binding],
                        body: Expr::Local(local),
                    }],
                }))
            }
            _ => Ok(None),
        }
    }

    /// Обёртка примитива: объект кучи с одним плоским слотом и прозрачной
    /// печатью (§10 вопросы 158, 159).
    ///
    /// Имя пустое, и это не пропуск, а сентинель печати: у машины обёртки в
    /// терме не существует, поэтому печатается только payload - пустое имя
    /// узнаёт `print.c`. Дроп обычный: слот плоский, следовать по нему некуда.
    fn prim_wrapper(&mut self, prim: PrimTy) -> Result<CtorId, LowerError> {
        let fact = Fact::declared(Mult::One).shaped(Repr::Flat(prim));
        let found = self
            .constructors
            .iter()
            .find(|it| it.name.is_empty() && it.binders == [fact]);
        if let Some(constructor) = found {
            return Ok(constructor.tag);
        }
        let tag = u16::try_from(self.constructors.len())
            .ok()
            .filter(|tag| *tag < TAGS)
            .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
        self.constructors.push(Constructor {
            tag: CtorId(tag),
            name: String::new(),
            data: "#обёртка".to_owned(),
            binders: vec![fact],
            params: 0,
            labels: None,
        });
        Ok(CtorId(tag))
    }

    /// Форма объекта кучи, отвечающая плотной укладке записи.
    ///
    /// Слот-агрегат в форме указателен: слот объекта несёт указатель либо
    /// биты примитива, и вложенный агрегат живёт в нём боксированным.
    fn boxed_shape(&mut self, pack: PackId) -> Result<CtorId, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        let Some(variant) = packing.sole().filter(|variant| variant.ctor.is_none()) else {
            // Семейной укладке отвечает не форма записи, а собственные
            // конструкторы семейства - см. [`Lowerer::loosening`].
            return Err(LowerError::PackedAnswer);
        };
        let facts: Vec<Fact> = variant
            .slots
            .iter()
            .map(|slot| Fact::declared(Mult::One).shaped(slotted(slot.ty.repr())))
            .collect();
        self.shape(&variant.labels.clone(), &facts)
    }

    /// Плотная запись объектом кучи: поля читаются смещением, кладутся слотом.
    ///
    /// Вложенный агрегат боксируется тем же перекладом рекурсивно; `None` -
    /// у вложенного боксированной формы нет, и переклада нет целиком.
    fn boxing(
        &mut self,
        scope: &mut Scope,
        value: Expr,
        pack: PackId,
        tag: CtorId,
    ) -> Result<Option<Expr>, LowerError> {
        let slots = self.packings[pack.0 as usize]
            .sole()
            .map(|variant| variant.slots.clone())
            .unwrap_or_default();
        let binding = Binding {
            name: "агрегат".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::Many).shaped(Repr::Packed(pack)),
        };
        let local = binding.local;
        let mut fields = Vec::with_capacity(slots.len());
        for (at, slot) in slots.iter().enumerate() {
            let taken = Expr::Unpack {
                packing: pack,
                variant: 0,
                field: u32::try_from(at).unwrap_or(u32::MAX),
                value: Box::new(Expr::Local(local)),
            };
            let field = match slot.ty {
                SlotTy::Prim(_) => taken,
                SlotTy::Pack(sub) => {
                    let Some(boxed) = self.moved(scope, &taken, Repr::Packed(sub), Repr::Boxed)?
                    else {
                        return Ok(None);
                    };
                    boxed
                }
            };
            fields.push(field);
        }
        Ok(Some(Expr::Bind {
            binding,
            value: Box::new(value),
            body: Box::new(Expr::Construct {
                constructor: tag,
                reuse: None,
                arguments: fields,
            }),
        }))
    }

    /// Согласуются ли поля конструктора со слотами варианта.
    ///
    /// Требуется для обоих перекладов семейства: живое связывание отвечает
    /// слоту тем же примитивом, агрегатному слоту - указателем (в таблице
    /// конструкторов вложенный агрегат живёт боксированным), стёртое слота не
    /// имеет. Расходятся они у **параметрического** семейства - поле `a` в
    /// таблице указательное, а слот считался по подставленному примитиву, - и
    /// тогда перекладывать нечем: боксированной формы у значения не бывает.
    fn variant_matches(described: &Constructor, variant: &Variant) -> bool {
        let fields: Vec<&Fact> = described
            .binders
            .iter()
            .skip(described.params as usize)
            .collect();
        let mut slots = variant.slots.iter();
        fields.iter().all(|fact| {
            if !fact.present {
                return true;
            }
            slots.next().is_some_and(|slot| match slot.ty {
                // Указательный факт над примитивным слотом - параметрическое
                // семейство: поле `a` в таблице указательно, слот считался по
                // подставленному примитиву. Переклад закрывает это обёрткой
                // (§10 вопрос 159), поэтому форма согласуется.
                SlotTy::Prim(prim) => fact.repr == Repr::Flat(prim) || fact.repr.boxed(),
                SlotTy::Pack(_) => fact.repr.boxed(),
            })
        }) && slots.next().is_none()
    }

    /// Связывания полей ветви по фактам, с именами из варианта.
    fn variant_fields(scope: &mut Scope, variant: &Variant, facts: &[Fact]) -> Vec<Binding> {
        facts
            .iter()
            .enumerate()
            .map(|(position, fact)| Binding {
                name: variant
                    .labels
                    .get(position)
                    .cloned()
                    .unwrap_or_else(|| format!("поле{position}")),
                local: scope.fresh(),
                fact: *fact,
            })
            .collect()
    }

    /// Плотное семейство объектом кучи: разбор по тегу, ветвь строит объект.
    ///
    /// Вложенный агрегат в поле боксируется рекурсивно. `None` - переклада
    /// нет: у параметрического семейства таблица конструкторов не знает
    /// подставленных полей, и объект под печать либо слот собрать нечем.
    fn loosening(
        &mut self,
        scope: &mut Scope,
        value: Expr,
        pack: PackId,
    ) -> Result<Option<Expr>, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        let mut arms = Vec::with_capacity(packing.variants.len());
        for variant in &packing.variants {
            let Some(tag) = variant.ctor else {
                return Ok(None);
            };
            let described = self.constructors[usize::from(tag.0)].clone();
            if !Self::variant_matches(&described, variant) {
                return Ok(None);
            }
            let params = described.params as usize;
            // Поля ветви связываются байтами своего варианта, объект строится
            // из них - агрегатное поле по дороге боксируется.
            let facts = self.branch_facts(Some(pack), tag);
            let fields = Self::variant_fields(scope, variant, &facts);
            let mut arguments: Vec<Expr> = (0..params).map(|_| Expr::Erased).collect();
            for (field, described_fact) in fields.iter().zip(described.binders.iter().skip(params))
            {
                if !field.fact.present {
                    arguments.push(Expr::Erased);
                    continue;
                }
                let argument = match field.fact.repr {
                    Repr::Packed(sub) => {
                        let Some(boxed) = self.moved(
                            scope,
                            &Expr::Local(field.local),
                            Repr::Packed(sub),
                            Repr::Boxed,
                        )?
                        else {
                            return Ok(None);
                        };
                        boxed
                    }
                    // Слот таблицы указателен, байты варианта плоские -
                    // параметрическое поле (§10 вопрос 159): payload
                    // оборачивается.
                    Repr::Flat(_) if described_fact.repr.boxed() => {
                        let Some(boxed) = self.moved(
                            scope,
                            &Expr::Local(field.local),
                            field.fact.repr,
                            Repr::Boxed,
                        )?
                        else {
                            return Ok(None);
                        };
                        boxed
                    }
                    _ => Expr::Local(field.local),
                };
                arguments.push(argument);
            }
            arms.push(Arm {
                constructor: tag,
                fields,
                body: Expr::Construct {
                    constructor: tag,
                    reuse: None,
                    arguments,
                },
            });
        }
        Ok(Some(Self::bound_match(
            scope,
            value,
            Repr::Packed(pack),
            Mult::One,
            arms,
        )))
    }

    /// Объект кучи плотным семейством: разбор по заголовку, ветвь пишет байты.
    ///
    /// Вложенный агрегат в поле пришёл бы указателем без формы, и сузить его
    /// нечем ([`Lowerer::moved`] умеет это только для семейств) - тогда
    /// переклада нет целиком, как и у [`Lowerer::loosening`].
    fn narrowing(
        &mut self,
        scope: &mut Scope,
        value: Expr,
        pack: PackId,
    ) -> Result<Option<Expr>, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        let mut arms = Vec::with_capacity(packing.variants.len());
        for (at, variant) in packing.variants.iter().enumerate() {
            let Some(tag) = variant.ctor else {
                return Ok(None);
            };
            let described = self.constructors[usize::from(tag.0)].clone();
            if !Self::variant_matches(&described, variant) {
                return Ok(None);
            }
            let params = described.params as usize;
            // Поля ветви приходят слотами объекта - фактами таблицы.
            let facts: Vec<Fact> = described.binders.iter().skip(params).copied().collect();
            let fields = Self::variant_fields(scope, variant, &facts);
            let mut taken = Vec::with_capacity(variant.slots.len());
            let mut slot = 0usize;
            for field in &fields {
                if !field.fact.present {
                    continue;
                }
                let wanted = variant.slots[slot].ty;
                slot += 1;
                let argument = match wanted {
                    // Поле пришло указателем таблицы, а слот примитивен -
                    // параметрическое поле (§10 вопрос 159): биты достаются
                    // из обёртки разбором.
                    SlotTy::Prim(prim) if field.fact.repr.boxed() => {
                        let Some(narrowed) = self.moved(
                            scope,
                            &Expr::Local(field.local),
                            field.fact.repr,
                            Repr::Flat(prim),
                        )?
                        else {
                            return Ok(None);
                        };
                        narrowed
                    }
                    SlotTy::Prim(_) => Expr::Local(field.local),
                    SlotTy::Pack(sub) => {
                        let Some(narrowed) = self.moved(
                            scope,
                            &Expr::Local(field.local),
                            field.fact.repr,
                            Repr::Packed(sub),
                        )?
                        else {
                            return Ok(None);
                        };
                        narrowed
                    }
                };
                taken.push(argument);
            }
            arms.push(Arm {
                constructor: tag,
                fields,
                body: Expr::Pack {
                    packing: pack,
                    variant: u32::try_from(at).unwrap_or(u32::MAX),
                    fields: taken,
                },
            });
        }
        Ok(Some(Expr::Match {
            scrutinee: Box::new(value),
            consumed: Mult::One,
            arms,
        }))
    }

    /// Разбор со связанным разбираемым: плотному нужен свой C-тип у имени.
    ///
    /// Вставка RC связывает не-переменную сама, но её временное имя
    /// указательное ([`Fact::opaque`]); плотное разбираемое поэтому
    /// связывается здесь, где представление известно.
    fn bound_match(
        scope: &mut Scope,
        value: Expr,
        repr: Repr,
        consumed: Mult,
        arms: Vec<Arm>,
    ) -> Expr {
        let binding = Binding {
            name: "разбираемое".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::Many).shaped(repr),
        };
        let local = binding.local;
        Expr::Bind {
            binding,
            value: Box::new(value),
            body: Box::new(Expr::Match {
                scrutinee: Box::new(Expr::Local(local)),
                consumed,
                arms,
            }),
        }
    }

    /// Объект кучи плотным агрегатом: разбор в одну ветвь, поля - в байты.
    ///
    /// Разбором, а не отдельным узлом, по той же причине, что и проекция:
    /// договор о владении у разбора уже есть, и разобранный объект отдаётся им.
    /// `None` - формы не сходятся полями, и отвечать будет сверка.
    fn tightening(
        &mut self,
        scope: &mut Scope,
        value: Expr,
        tag: CtorId,
        pack: PackId,
    ) -> Option<Expr> {
        let described = self.constructors[usize::from(tag.0)].clone();
        let packing = self.packings[pack.0 as usize].clone();
        let variant = packing.sole().filter(|variant| variant.ctor.is_none())?;
        if described.labels.as_deref() != Some(&variant.labels) {
            return None;
        }
        let matching = described
            .binders
            .iter()
            .zip(&variant.slots)
            .all(|(fact, slot)| fact.present && fact.repr == slot.ty.repr());
        if !matching || described.binders.len() != variant.slots.len() {
            return None;
        }
        let fields: Vec<Binding> = variant
            .labels
            .iter()
            .zip(&described.binders)
            .map(|(label, fact)| Binding {
                name: label.clone(),
                local: scope.fresh(),
                fact: *fact,
            })
            .collect();
        let taken = fields.iter().map(|it| Expr::Local(it.local)).collect();
        Some(Expr::Match {
            scrutinee: Box::new(value),
            consumed: Mult::One,
            arms: vec![Arm {
                constructor: tag,
                fields,
                body: Expr::Pack {
                    packing: pack,
                    variant: 0,
                    fields: taken,
                },
            }],
        })
    }

    /// Понижает выражение, зная, какого представления от него ждут.
    ///
    /// Ожидание читает ровно одна форма - значение записи, - и читает по делу:
    /// синтезом форма собирается из **значений** полей, а значения не всё
    /// знают. Стёртое поле там неотличимо от живого (`type T = Nat` в теле
    /// модуля - тип в позиции значения), а поле, потерявшее форму по дороге,
    /// дало бы форму, не равную объявленной. Объявление знает и то, и другое.
    fn expected(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        want: Repr,
    ) -> Result<(Expr, Repr), LowerError> {
        if let Term::Object(fields) = term {
            if descriptor(fields).is_none() {
                match want {
                    Repr::Record(tag) => return Ok((self.object_as(scope, fields, tag)?, want)),
                    Repr::Packed(pack) => return Ok((self.pack_as(scope, fields, pack)?, want)),
                    _ => {}
                }
            }
        }
        // Насыщенный конструктор плотного семейства строится сразу байтами
        // (§10 вопрос 157): синтез дал бы объект, и семя колонки
        // аллоцировалось бы, чтобы тут же переложиться и освободиться.
        if let Repr::Packed(pack) = want {
            let (head, arguments) = spine(term);
            if let Term::Const(name, ..) = head {
                let name = Rc::clone(name);
                if let Some(built) = self.pack_ctor_as(scope, &name, &arguments, pack)? {
                    return Ok((built, want));
                }
            }
        }
        self.expr(scope, term)
    }

    /// Значение конструктора, уложенное плотно по своему варианту.
    ///
    /// `None` - форма не та, и отвечать будет обычный путь с перекладом:
    /// имя не конструктор этого семейства, применение не насыщено, либо
    /// вариант расходится полями.
    fn pack_ctor_as(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[&Term],
        pack: PackId,
    ) -> Result<Option<Expr>, LowerError> {
        let Some(definition) = self.signature.lookup(name) else {
            return Ok(None);
        };
        if !matches!(definition.kind, DefinitionKind::Constructor { .. }) {
            return Ok(None);
        }
        let constructor = self.tag(name)?;
        let Some((variant, slots)) = self.packings[pack.0 as usize]
            .variant_of(constructor)
            .map(|(at, variant)| (at, variant.slots.clone()))
        else {
            return Ok(None);
        };
        let binders = self.constructors[usize::from(constructor.0)]
            .binders
            .clone();
        let params = self.constructors[usize::from(constructor.0)].params as usize;
        let saturated = arguments.len() <= binders.len()
            && (arguments.len() >= binders.len()
                || binders[arguments.len()..].iter().all(|fact| !fact.present));
        if !saturated {
            return Ok(None);
        }
        let mut given = Vec::with_capacity(slots.len());
        let mut slot = 0usize;
        for (position, fact) in binders.iter().enumerate().skip(params) {
            if !fact.present {
                continue;
            }
            let want = slots[slot].ty.repr();
            slot += 1;
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            given.push(self.shaped(scope, argument, want, "поле конструктора")?);
        }
        Ok(Some(Expr::Pack {
            packing: pack,
            variant,
            fields: given,
        }))
    }

    /// Значение записи: объект кучи со слотом на поле (§4.2).
    ///
    /// Форма берётся у **написанного** - метки и представления полей идут в том
    /// порядке, в каком они написаны, - и она же порядок печати. Форма из
    /// **типа** (параметр, аннотация, ответ) читается телескопом, и это тот же
    /// порядок ровно потому, что элаборация пересобирает обновление по
    /// телескопу (§4.2). Разойдись они - сверка представлений отвергает по
    /// имени, а не считает не то.
    fn object(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
    ) -> Result<(Expr, Repr), LowerError> {
        let mut labels = Vec::with_capacity(fields.len());
        let mut facts = Vec::with_capacity(fields.len());
        let mut values = Vec::with_capacity(fields.len());
        for (label, value) in fields {
            let (value, repr) = self.expr(scope, value)?;
            // Плоский агрегат в слот объекта не ложится - слот несёт
            // указатель либо биты примитива - и потому боксируется (§4.11).
            let (value, repr) = if matches!(repr, Repr::Packed(_)) {
                let boxed = self.moved(scope, &value, repr, Repr::Boxed)?.ok_or(
                    LowerError::Representation {
                        at: "поле записи",
                        want: describe(Repr::Boxed),
                        got: describe(repr),
                    },
                )?;
                (boxed, Repr::Boxed)
            } else {
                (value, repr)
            };
            labels.push(label.to_string());
            // Поле записи кладёт значение однажды - `check::infer_object`
            // объявляет его `1`, и другого источника кратности у значения нет.
            facts.push(Fact::declared(Mult::One).shaped(repr));
            values.push(value);
        }
        let tag = self.shape(&labels, &facts)?;
        Ok((
            Expr::Construct {
                constructor: tag,
                reuse: None,
                arguments: values,
            },
            Repr::Record(tag),
        ))
    }

    /// Значение записи, собранное по **объявленной** форме.
    ///
    /// Метки сверяются с формой позиция в позицию, а не по имени: слоты
    /// раздаёт форма, а печать идёт в порядке слотов, и `adamas eval` печатает
    /// поля как написаны (§4.2). Совпади множества, но разойдись порядок - две
    /// печати разошлись бы тоже, поэтому здесь отказ, а не перестановка.
    fn object_as(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
        tag: CtorId,
    ) -> Result<Expr, LowerError> {
        let described = self.constructors[usize::from(tag.0)].clone();
        let labels = described.labels.clone().unwrap_or_default();
        let mismatch = || LowerError::Representation {
            at: "поля записи",
            want: described.name.clone(),
            got: format!(
                "{{{}}}",
                fields
                    .iter()
                    .map(|(label, _)| label.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        if labels.len() != fields.len() {
            return Err(mismatch());
        }
        let mut arguments = Vec::with_capacity(fields.len());
        for (position, (label, value)) in fields.iter().enumerate() {
            if **label != *labels[position] {
                return Err(mismatch());
            }
            let fact = described.binders[position];
            if !fact.present {
                arguments.push(Expr::Erased);
                continue;
            }
            arguments.push(self.shaped(scope, value, fact.repr, "поле записи")?);
        }
        Ok(Expr::Construct {
            constructor: tag,
            reuse: None,
            arguments,
        })
    }

    /// Значение записи, уложенное **плоско** (§4.11).
    ///
    /// Отличается от [`Lowerer::object_as`] тем, куда ложатся поля: там слот
    /// объекта кучи, здесь смещение внутри байтов. Метки сверяются так же -
    /// позиция в позицию.
    fn pack_as(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
        pack: PackId,
    ) -> Result<Expr, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        // Записью укладывается только бестеговый вариант: значение записи
        // семейной укладки не пишется, его отвергнет сверка меток.
        let (labels, slots) = packing
            .sole()
            .filter(|variant| variant.ctor.is_none())
            .map(|variant| (variant.labels.clone(), variant.slots.clone()))
            .unwrap_or_default();
        let mismatch = || LowerError::Representation {
            at: "поля плоской записи",
            want: format!("{{{}}}", labels.join(", ")),
            got: format!(
                "{{{}}}",
                fields
                    .iter()
                    .map(|(label, _)| label.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        if labels.len() != fields.len() || fields.is_empty() {
            return Err(mismatch());
        }
        let mut given = Vec::with_capacity(fields.len());
        for (position, (label, value)) in fields.iter().enumerate() {
            if **label != *labels[position] {
                return Err(mismatch());
            }
            let want = slots[position].ty.repr();
            given.push(self.shaped(scope, value, want, "поле плоской записи")?);
        }
        Ok(Expr::Pack {
            packing: pack,
            variant: 0,
            fields: given,
        })
    }

    /// Проекция поля: чтение слота, найденного формой записи.
    ///
    /// Понижается **разбором в одну ветвь**, а не отдельным узлом, и это не
    /// экономия узлов: у разбора уже есть договор о владении - разобранное
    /// отдаётся, названное поле приходит `dup`'ом (`perceus::arm`), - и второй
    /// узел потребовал бы второй его копии.
    fn projection(
        &mut self,
        scope: &mut Scope,
        record: &Term,
        label: &Name,
    ) -> Result<(Expr, Repr), LowerError> {
        let (value, repr) = self.expr(scope, record)?;
        if repr == Repr::Layout && &**label == METHOD {
            return Ok(self.materialised(scope, value));
        }
        if let Repr::Packed(pack) = repr {
            // Плоский агрегат: поле адресуется **смещением**, а не слотом, - и
            // это названная цена варианта (а) вопроса 154. Проецируется только
            // запись: у семейной укладки полей без разбора нет.
            let packing = &self.packings[pack.0 as usize];
            let Some(variant) = packing.sole().filter(|variant| variant.ctor.is_none()) else {
                return Err(LowerError::Shapeless {
                    label: label.to_string(),
                });
            };
            let at = variant
                .labels
                .iter()
                .position(|it| **it == **label)
                .ok_or_else(|| LowerError::NoField {
                    label: label.to_string(),
                    shape: format!("{{{}}}", variant.labels.join(", ")),
                })?;
            let ty = variant.slots[at].ty;
            return Ok((
                Expr::Unpack {
                    packing: pack,
                    variant: 0,
                    field: u32::try_from(at).unwrap_or(u32::MAX),
                    value: Box::new(value),
                },
                ty.repr(),
            ));
        }
        let Repr::Record(tag) = repr else {
            return Err(LowerError::Shapeless {
                label: label.to_string(),
            });
        };
        let described = self.constructors[usize::from(tag.0)].clone();
        let at = described
            .labels
            .as_ref()
            .and_then(|labels| labels.iter().position(|it| **it == **label))
            .ok_or_else(|| LowerError::NoField {
                label: label.to_string(),
                shape: described.name.clone(),
            })?;
        let fields: Vec<Binding> = described
            .binders
            .iter()
            .enumerate()
            .map(|(position, fact)| Binding {
                name: described.labels.as_ref().map_or_else(
                    || format!("поле{position}"),
                    |labels| labels[position].clone(),
                ),
                local: scope.fresh(),
                fact: *fact,
            })
            .collect();
        let taken = fields[at].fact;
        let body = if taken.present {
            Expr::Local(fields[at].local)
        } else {
            Expr::Erased
        };
        Ok((
            Expr::Match {
                scrutinee: Box::new(value),
                // Запись потребляется проекцией целиком: прочие поля отдаёт
                // дроп разобранного.
                consumed: Mult::One,
                arms: vec![Arm {
                    constructor: tag,
                    fields,
                    body,
                }],
            },
            taken.repr,
        ))
    }

    /// Единственный метод `Flat` записью: `dict.layout` есть `{ size, align }`.
    ///
    /// Словарь `Flat` живёт дескриптором, а не объектом кучи ([`Repr::Layout`]),
    /// поэтому проекция его метода - не чтение слота, а **сборка** записи из
    /// двух чисел. Порядок полей тот же, что требует [`descriptor`]: сперва
    /// размер, потом выравнивание. Напиши программа `Layout` в другом порядке -
    /// формы разойдутся, и сверка представлений скажет об этом по имени.
    fn materialised(&mut self, scope: &mut Scope, descriptor: Expr) -> (Expr, Repr) {
        let labels = [SIZE.to_owned(), ALIGN.to_owned()];
        let pack = self.packing(&labels, &[PrimTy::UInt32, PrimTy::UInt32]);
        // Дескриптор связывается: полей у него два, а посчитан он однажды.
        let binding = Binding {
            name: "дескриптор".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::Many).shaped(Repr::Layout),
        };
        let local = binding.local;
        (
            Expr::Bind {
                binding,
                value: Box::new(descriptor),
                body: Box::new(Expr::Pack {
                    packing: pack,
                    variant: 0,
                    fields: vec![
                        Expr::LayoutField {
                            descriptor: local,
                            align: false,
                        },
                        Expr::LayoutField {
                            descriptor: local,
                            align: true,
                        },
                    ],
                }),
            },
            Repr::Packed(pack),
        )
    }

    /// Форма записи по меткам и представлениям полей; заводится однажды.
    ///
    /// Сравниваются метки **и** факты: `{ x : Int64 }` и `{ x : Nat }` - разные
    /// формы, потому что слот у первого несёт биты, а у второго ссылку.
    fn shape(&mut self, labels: &[String], facts: &[Fact]) -> Result<CtorId, LowerError> {
        let found = self
            .constructors
            .iter()
            .find(|it| it.labels.as_deref() == Some(labels) && it.binders == facts);
        if let Some(constructor) = found {
            return Ok(constructor.tag);
        }
        let tag = u16::try_from(self.constructors.len())
            .ok()
            .filter(|tag| *tag < TAGS)
            .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
        let written: Vec<&str> = labels.iter().map(String::as_str).collect();
        self.constructors.push(Constructor {
            tag: CtorId(tag),
            name: format!("{{{}}}", written.join(", ")),
            data: "запись".to_owned(),
            binders: facts.to_vec(),
            params: 0,
            labels: Some(labels.to_vec()),
        });
        Ok(CtorId(tag))
    }

    /// Понижает тело определения, дописав к его спайну достроенные параметры.
    ///
    /// Дописать удаётся ровно спайну (§10 вопрос 153): у него голова - имя, и
    /// лишние аргументы делают вызов насыщенным вместо того, чтобы уходить
    /// применением к значению. Прочие формы тела применяют достроенные параметры
    /// обычным путём - через границу замыкания, где плоское по-прежнему
    /// отвергается.
    ///
    /// # Из двух стражей свидетеля получил один
    ///
    /// Сверка достроенного аргумента ([`Lowerer::given`]) свидетелем **обзавелась**
    /// вместе с массивами: один и тот же написанный тип `Array 3 a` читается
    /// плоским там, где в контексте есть `Flat a`, и указательным там, где его
    /// нет, - и телескопы вызывающего и вызываемого расходятся по-настоящему
    /// (`tests/array.rs`, `a_supplied_argument_is_checked_by_its_representation`).
    /// Прежде разойтись им было нечем: оба читали один тип.
    ///
    /// Сверка **применяемого значения** здесь свидетеля не получила, и причина
    /// теперь структурная, а не «пока нечем»: позиция эта - вызываемое, то есть
    /// тип-стрелка, а стрелка указательна при любом представлении элементов.
    /// Чтобы страж сработал, потребовалось бы плоское значение функционального
    /// типа, а такого нет ни одного. Страж остаётся; звать его покрытым
    /// по-прежнему нельзя.
    fn saturated(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        extra: &[Binding],
        want: Repr,
    ) -> Result<(Expr, Repr), LowerError> {
        if extra.is_empty() {
            return self.expected(scope, term, want);
        }
        if matches!(term, Term::App(..) | Term::Const(..) | Term::Prim(_)) {
            let (head, written) = spine(term);
            let mut arguments: Vec<Arg<'_>> = written.into_iter().map(Arg::Written).collect();
            arguments.extend(extra.iter().map(Arg::Supplied));
            return self.application(scope, head, &arguments);
        }
        let (mut value, repr) = self.expr(scope, term)?;
        if !repr.boxed() {
            return Err(LowerError::Representation {
                at: "применяемое значение",
                want: describe(Repr::Boxed),
                got: describe(repr),
            });
        }
        for binding in extra {
            let argument = self.given(
                scope,
                &Arg::Supplied(binding),
                Repr::Boxed,
                "аргумент замыкания",
            )?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Понижает аргумент спайна и требует от него объявленного представления.
    ///
    /// Написанный проверяет `shaped`, достроенный - сверка ниже; свидетели
    /// стоят на обоих, см. [`Lowerer::saturated`].
    fn given(
        &mut self,
        scope: &mut Scope,
        argument: &Arg<'_>,
        want: Repr,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        match argument {
            Arg::Written(term) => self.shaped(scope, term, want, at),
            Arg::Supplied(binding) => {
                if !fits(binding.fact.repr, want) {
                    return Err(LowerError::Representation {
                        at,
                        want: describe(want),
                        got: describe(binding.fact.repr),
                    });
                }
                Ok(if binding.fact.present {
                    Expr::Local(binding.local)
                } else {
                    Expr::Erased
                })
            }
        }
    }

    /// Понижает применение с разложенным спайном.
    fn application(
        &mut self,
        scope: &mut Scope,
        head: &Term,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        if let Term::Prim(prim) = head {
            return self.primitive(scope, *prim, arguments);
        }
        // Голова - резумпция: применение к ней есть возобновление, а не вызов
        // замыкания. Различить их обязано понижение: за резумпцией стоит ручка
        // сегмента, а не код, и `adamas_apply` по ней оборвал бы процесс.
        if let Term::Var(index) = head {
            if let Slot::Bound(local, fact) = scope.slot(*index)? {
                if fact.repr == Repr::Resumption {
                    let (local, fact) = (*local, *fact);
                    return self.resuming(scope, local, fact, arguments);
                }
            }
        }
        let Term::Const(name, ..) = head else {
            // Голова - не имя: применяется значение, и стирания здесь не бывает.
            let mut value = self.shaped(scope, head, Repr::Boxed, "применяемое значение")?;
            for argument in arguments {
                let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        };
        // Выход из scope (§3.3) - обычное определение по виду, но тела у него
        // нет: его даёт понижение. Спрашивается он до вида поэтому.
        if &**name == CLOSING {
            return self.closing(scope, arguments);
        }
        // Питомник (§5.2) - постулат, чьё тело даёт рантайм. Тело у имени
        // означает, что так назвали своё, и в питомник его превращать нечего:
        // то же правило, каким узнаёт его машина.
        if &**name == NURSERY && self.definition(name)?.body.is_none() {
            return self.nursing(scope, name, arguments);
        }
        // Элиминаторы - невыразимые имена без тела, и спрашиваются они до вида
        // по той же причине, что и выход из scope: тела у них нет, а смысл есть.
        if let Some(effect) = name.strip_prefix(HANDLE) {
            let effect: Name = Rc::from(effect);
            return self.handled(scope, name, &effect, arguments, false);
        }
        // Мультишот идёт тем же путём, и различие ровно одно: ручка резумпции
        // помечается мультишотной, а вердикт всех веток - общий. Сколько раз
        // позовут ω-резумпцию, написанному телу не видно (§3.4).
        if let Some(effect) = name.strip_prefix(MULTI) {
            let effect: Name = Rc::from(effect);
            return self.handled(scope, name, &effect, arguments, true);
        }
        // Параметризованный идёт тем же путём, что одношотный: тип у третьего
        // элиминатора тот же, различие только в имени (§10 вопрос 129). Кадра
        // решения о смерти резумпции понижению не нужно - её смерть здесь
        // решает **владение**: нить состояния держит резумпцию в замыкании
        // `\s -> resume v s`, а обрывающая ветка не держит нигде, и дроп
        // ставит `perceus` обычным правилом.
        if let Some(effect) = name.strip_prefix(STATEFUL) {
            let effect: Name = Rc::from(effect);
            return self.handled(scope, name, &effect, arguments, false);
        }
        // Маска кадра не ставит вовсе: её понижение есть вектор без ближайшей
        // записи своей метки, и вычисление под ним.
        if let Some(effect) = name.strip_prefix(MASK) {
            let effect: Name = Rc::from(effect);
            return self.masked(scope, name, &effect, arguments);
        }
        match &self.definition(name)?.kind {
            DefinitionKind::Constructor { .. } => self.built(scope, name, arguments),
            DefinitionKind::Regular => self.called(scope, name, arguments),
            DefinitionKind::Data { .. } => Err(LowerError::TypeValue {
                name: name.to_string(),
            }),
            DefinitionKind::Effect { .. } => Err(LowerError::Operation {
                name: name.to_string(),
                why: "метка эффекта: значения у неё в рантайме нет",
            }),
            DefinitionKind::Operation { effect } => {
                let effect = Rc::clone(effect);
                self.performed(scope, name, &effect, arguments)
            }
        }
    }

    /// Возобновление: `resume v` ставит сегмент обратно и отдаёт ему `v`.
    ///
    /// Аргументов бывает больше одного, и лишние - обычные применения ответа:
    /// у параметризованного хендлера `resume v s` есть `(resume v) s`, потому
    /// что ответ такой резумпции сам функция от состояния (§3.4, сахар `state`).
    fn resuming(
        &mut self,
        scope: &mut Scope,
        local: LocalId,
        fact: Fact,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let Some((first, rest)) = arguments.split_first() else {
            // Резумпция значением: сохранить её ветка вправе (§3.4,
            // овеществление), но `Resumption` - ресурс, и этим срезом он не
            // берётся.
            return Ok((Expr::Local(local), fact.repr));
        };
        let value = self.given(scope, first, Repr::Boxed, "аргумент резумпции")?;
        let mut node = Expr::Resume {
            resumption: Box::new(Expr::Local(local)),
            value: Box::new(value),
        };
        for argument in rest {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            node = Expr::Apply {
                callee: Box::new(node),
                argument: Box::new(argument),
            };
        }
        Ok((node, Repr::Boxed))
    }

    /// Номер метки эффекта: им её находит `adamas_evidence_lookup`.
    ///
    /// Заводится по имени, потому что имя - единственное, что общего у места
    /// `handle` и места операции: первое знает метку из имени элиминатора,
    /// второе - из объявления операции.
    fn label(&mut self, effect: &Name) -> Result<LabelId, LowerError> {
        if let Some(id) = self.marks.get(effect) {
            return Ok(*id);
        }
        let DefinitionKind::Effect { operations, .. } = &self.definition(effect)?.kind else {
            return Err(LowerError::Operation {
                name: effect.to_string(),
                why: "не метка эффекта",
            });
        };
        let id = LabelId(u32::try_from(self.labels.len()).unwrap_or(u32::MAX));
        self.labels.push(Label {
            name: effect.to_string(),
            operations: operations.iter().map(ToString::to_string).collect(),
        });
        self.marks.insert(Rc::clone(effect), id);
        Ok(id)
    }

    /// Операция эффекта: хендлер ищется вектором evidence (§3.4).
    ///
    /// Аргументы берутся так же, как их берёт машина: после параметров метки и
    /// до арности, на которой операция производит (`performing`). Лишнее -
    /// синтезированный триггер приостановленного вычисления - едет ветке и
    /// дропается ею: сколько ветка связывает, знает место `handle`, а не это.
    fn performed(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        effect: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let label = self.label(effect)?;
        let DefinitionKind::Effect { operations, params } = &self.definition(effect)?.kind else {
            unreachable!("`label` уже проверил вид метки")
        };
        let params = *params as usize;
        let slot =
            operations
                .iter()
                .position(|it| it == name)
                .ok_or_else(|| LowerError::Operation {
                    name: name.to_string(),
                    why: "операции нет среди операций своей метки",
                })?;
        let ty = &self.definition(name)?.ty;
        let arity = performing(ty).ok_or_else(|| LowerError::Operation {
            name: name.to_string(),
            why: "у операции нет row ни на одной стрелке: производить нечем",
        })?;
        if arguments.len() < arity {
            // Недобранная операция была бы замыканием, а замыкание отдаёт
            // слоты указателями и хендлера не ищет вовсе.
            return Err(LowerError::Operation {
                name: name.to_string(),
                why: "операция значением: этим срезом она не берётся",
            });
        }
        let dicts = scope.dicts.clone();
        let result = self.result_repr(ty, arity, &dicts)?;
        if !result.pointer() {
            return Err(LowerError::Representation {
                at: "ответ операции",
                want: describe(Repr::Boxed),
                got: describe(result),
            });
        }
        // Стёртые связывания операции значения не имеют, и лезть в них нельзя:
        // `fail : a` объявляет собственный `{0 a}` перед триггером, и это
        // **тип**. Ветке они всё равно не достаются - `written` считается от
        // `params`, - но место операции обязано отдать столько аргументов,
        // сколько объявлено, иначе номера разъедутся с ветками.
        let mults = multiplicities(ty, arity);
        let mut given = Vec::with_capacity(arity - params);
        for (at, argument) in arguments[params..arity].iter().enumerate() {
            if mults.get(params + at) == Some(&Mult::Zero) {
                given.push(Expr::Erased);
                continue;
            }
            given.push(self.given(scope, argument, Repr::Boxed, "аргумент операции")?);
        }
        let operation = u32::try_from(slot).unwrap_or(u32::MAX);
        let mut value = match self.fiber_op(name)? {
            Some(op) => Expr::Fiber {
                op,
                label,
                operation,
                arguments: given,
            },
            None => Expr::Perform {
                label,
                operation,
                arguments: given,
            },
        };
        for argument in arguments.iter().skip(arity) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Питомник: `withNursery` (§5.2).
    ///
    /// Тело берётся **значением**, а не запускается здесь: приостановку с него
    /// снимет круг, применив его к единице уже под своим кадром. Этим питомник
    /// и отличается от хендлера с маской, которые вычисление под собой
    /// запускают сами ([`Lowerer::triggered`]): у тех оно одно и идёт немедля, а
    /// у круга их сколько угодно и порядок им задаёт очередь.
    fn nursing(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let Some(body) = arguments.first() else {
            return Err(LowerError::Nursery {
                name: name.to_string(),
                why: "постулат не насыщен, круг значением этим срезом не берётся",
            });
        };
        let body = self.given(scope, body, Repr::Boxed, "тело питомника")?;
        let mut value = Expr::Nursery {
            body: Box::new(body),
        };
        for argument in arguments.iter().skip(1) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Роль операции под питомником. `None` - обычная операция эффекта.
    ///
    /// Имя решает только **роль**; кто операцию обслужит, решает рантайм по
    /// вектору evidence, потому что ближайший выигрывает.
    fn fiber_op(&mut self, name: &Name) -> Result<Option<FiberOp>, LowerError> {
        match &**name {
            SUSPEND => Ok(Some(FiberOp::Suspend)),
            DETACHED => Ok(Some(FiberOp::Detached)),
            SPAWN => Ok(Some(FiberOp::Spawn(self.task_shape(name)?))),
            // Форму задачи называет `spawn`, а не `await`: у второго в домене
            // может стоять ведущий имплисит подъёма, и семейство читается
            // оттуда неоднозначно.
            AWAIT => {
                let spawn: Name = Rc::from(SPAWN);
                let at = match self.signature.lookup(&spawn) {
                    Some(_) => self.task_shape(&spawn)?.map(|shape| shape.at),
                    None => None,
                };
                Ok(Some(FiberOp::Await(at)))
            }
            _ => Ok(None),
        }
    }

    /// Чем назвать задачу: конструктор написанного результата `spawn` (§5.2).
    ///
    /// Требований два, и оба проверяются здесь, а не молча предполагаются, -
    /// те же, что у машины: один конструктор и одно живое поле, куда встанет
    /// невыразимое имя файбера. Не сошлось - `None`, и обслужить операцию круг
    /// не сможет; отказа тут нет, потому что тот же `spawn` без питомника есть
    /// обычная операция (`eval/fibers.adamas`).
    fn task_shape(&mut self, name: &Name) -> Result<Option<Task>, LowerError> {
        let Some(data) = result_head(&self.definition(name)?.ty) else {
            return Ok(None);
        };
        let Some([only]) = self.signature.constructors(&data) else {
            return Ok(None);
        };
        let only = Rc::clone(only);
        self.family(&data)?;
        let Some(&tag) = self.tags.get(&only) else {
            return Ok(None);
        };
        let described = &self.constructors[usize::from(tag.0)];
        let mut live = described
            .binders
            .iter()
            .enumerate()
            .filter(|(_, fact)| fact.present);
        let Some((binder, fact)) = live.next() else {
            return Ok(None);
        };
        if live.next().is_some() || !fact.repr.pointer() {
            return Ok(None);
        }
        let at = described.slot(binder).unwrap_or(0);
        Ok(Some(Task {
            constructor: tag,
            slots: 1,
            at,
        }))
    }

    /// Выход из scope, держащего ресурс: `#closing` (§3.3).
    ///
    /// # Формы две, и различает их ручка стека
    ///
    /// У машины scope овеществлён кадром (`Frame::Closing`), и это не
    /// украшение: обрыв через эффект находит отложенное **в брошенном
    /// сегменте**. Во **второй** форме тем же занят кадр `MARK_CLOSING`
    /// (`adamas.h`), и ставится он здесь: [`Expr::Closing`]. В **первой** стека
    /// нет вовсе, обрываться нечему, и остаётся то, что кадр делает на
    /// нормальном выходе, - тело, потом деструктор, потом ответ тела.
    ///
    /// Цена второй формы названа: деструктор становится **замыканием**, то есть
    /// ячейкой кучи на scope. Раскрутка ведёт его сама (`unwind_step`
    /// применяет его к единице), а взять там нечего, кроме значения. Первая
    /// форма за это по-прежнему не платит - тем и различаются две ветки ниже.
    ///
    /// # Почему у первой формы связывания, а не свой узел
    ///
    /// Договор о владении у [`Expr::Bind`] уже есть, и второй узел потребовал
    /// бы второй его копии - тот же довод, каким проекция §4.2 понижается
    /// разбором в одну ветвь. Ответ деструктора связывается и не
    /// употребляется, поэтому дропает его [`crate::perceus`] обычным правилом,
    /// а не отдельным знанием про scope.
    ///
    /// LIFO выходит вложенностью у обеих форм и ничего к ней не добавляет:
    /// связывание, стоящее ниже, обернуло при вставке меньший кусок
    /// (`adamas-elab/src/expr.rs`), значит его `#closing` лежит **внутри**, а
    /// внутренний деструктор зовётся раньше внешнего. У кадров то же выходит
    /// порядком цепочки: внутренний лежит выше, раскрутка идёт от вершины.
    fn closing(
        &mut self,
        scope: &mut Scope,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let [_, _, Arg::Written(body), Arg::Written(close)] = arguments else {
            return Err(LowerError::Scope);
        };
        if self.detached {
            if !matches!(close, Term::Lam(..)) {
                return Err(LowerError::Scope);
            }
            // Замыкание строится **до** тела: кадр стоит на стеке всё время,
            // пока тело считается, иначе обрыв прошёл бы мимо деструктора.
            // Ответ его отбрасывается внутри него самого - раскрутка о типе
            // ответа не знает и дропнула бы его без детей.
            let (closer, _) = self.discarding(scope, close)?;
            let Expr::Closure {
                function: closer,
                captured,
            } = closer
            else {
                return Err(LowerError::Scope);
            };
            // Имя деструктора в порождённом C: без него у кадра стоит номер
            // лямбды, и порядок кадров читается только по номерам.
            if let Some(named) = head(close) {
                self.functions[closer.0].name = format!("деструктор {named}");
            }
            let (body, repr) = self.resumed(scope, body)?;
            return Ok((
                Expr::Closing {
                    closer,
                    captured,
                    body: Box::new(body),
                },
                repr,
            ));
        }
        let (body, repr) = self.resumed(scope, body)?;
        let held = Binding {
            name: "ответ_scope".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::One).shaped(repr),
        };
        let answer = held.local;
        let (close, closed) = self.resumed(scope, close)?;
        let discarded = Binding {
            name: "ответ_деструктора".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::One).shaped(closed),
        };
        Ok((
            Expr::Bind {
                binding: held,
                value: Box::new(body),
                body: Box::new(Expr::Bind {
                    binding: discarded,
                    value: Box::new(close),
                    body: Box::new(Expr::Local(answer)),
                }),
            },
            repr,
        ))
    }

    /// Хендлер: `#handle.L` (§3.4, решения 1, 2 и 5 волны 4).
    ///
    /// # Что ставится
    ///
    /// Кадр `HANDLER` со средой веток, вектор evidence копией родителя плюс
    /// запись о нём, вычисление под этим вектором, ветка `return` на нормальном
    /// выходе. Ветки - статические функции, и среда у них общая: лежит она в
    /// кадре, а второй кадр ради экономии слота стоил бы дороже слота.
    ///
    /// # Что отвергается и чьё оно
    ///
    /// Вердикт ветки считается **по написанному**, а не по графу (решение 2):
    /// хвостово-резумптивная - `resume` в хвосте, абортивная - `resume` не
    /// зовётся, общая - всё прочее.
    ///
    /// # Мультишот
    ///
    /// `#handleMulti.L` понижается тем же путём, и различий два. Вердикт всех
    /// его веток - общий: «`resume` стоит в хвосте» у ω-резумпции не значит
    /// «зовётся один раз», а по написанному телу число вызовов не считается
    /// вовсе. И ручка резумпции помечается мультишотной - возобновление ставит
    /// копию сегмента (§3.4, «Стоимость multi-shot»).
    fn handled(
        &mut self,
        scope: &mut Scope,
        eliminator: &Name,
        effect: &Name,
        arguments: &[Arg<'_>],
        multi: bool,
    ) -> Result<(Expr, Repr), LowerError> {
        let label = self.label(effect)?;
        let DefinitionKind::Effect { operations, params } = &self.definition(effect)?.kind else {
            unreachable!("`label` уже проверил вид метки")
        };
        let operations: Vec<Name> = operations.clone();
        let params = *params as usize;
        // Параметры метки, `a`, `b`, вычисление, `return` и ветки.
        let arity = params + 4 + operations.len();
        if arguments.len() < arity {
            return Err(LowerError::Handler {
                name: eliminator.to_string(),
                why: "элиминатор не насыщен: хендлер значением этим срезом не берётся",
            });
        }
        let signature = self.definition(eliminator)?.ty.clone();
        let written: Vec<usize> = (0..operations.len())
            .map(|slot| {
                domain(&signature, params + 4 + slot)
                    .map(binders)
                    .and_then(|count| count.checked_sub(1))
                    .ok_or_else(|| LowerError::Handler {
                        name: eliminator.to_string(),
                        why: "у типа элиминатора нет ветки на объявленную операцию",
                    })
            })
            .collect::<Result<_, _>>()?;

        // Среда веток одна на все: она лежит в кадре, и делить её нечем.
        let mut free = BTreeSet::new();
        for argument in &arguments[params + 3..arity] {
            let Arg::Written(term) = argument else {
                return Err(LowerError::Handler {
                    name: eliminator.to_string(),
                    why: "ветка хендлера пришла достроенной, а не написанной",
                });
            };
            escaping(term, 0, &mut free);
        }
        let (captured, taken, inner) = Self::capturing(scope, &free, "захват ветки хендлера")?;

        let site = Site {
            captured: &captured,
            inner: &inner,
            effect,
            multi,
        };
        let mut branches = Vec::with_capacity(operations.len());
        for (slot, operation) in operations.iter().enumerate() {
            let Arg::Written(term) = &arguments[params + 4 + slot] else {
                unreachable!("написанность веток проверена выше")
            };
            let (function, verdict) = self.branch(&site, term, written[slot], operation)?;
            branches.push(Branch {
                function,
                written: written[slot],
                verdict,
            });
        }
        let Arg::Written(returned) = &arguments[params + 3] else {
            unreachable!("написанность веток проверена выше")
        };
        let returned = self.returning(&captured, &inner, returned, effect)?;

        let handler = HandlerId(u32::try_from(self.handlers.len()).unwrap_or(u32::MAX));
        self.handlers.push(Handler {
            label,
            multi,
            captured,
            branches,
            returned,
        });

        let Arg::Written(computation) = &arguments[params + 2] else {
            return Err(LowerError::Handler {
                name: eliminator.to_string(),
                why: "вычисление под хендлером пришло достроенным, а не написанным",
            });
        };
        // Под хендлером ручка стека есть всегда - её заводит сам `handle`,
        // включая корень в чистой функции, - поэтому scope с ресурсом здесь
        // ставит кадр даже у первой формы снаружи.
        let outer = std::mem::replace(&mut self.detached, true);
        let computation = self.triggered(scope, computation, "вычисление под хендлером");
        self.detached = outer;
        let computation = computation?;

        let mut value = Expr::Handle {
            handler,
            captured: taken,
            computation: Box::new(computation),
        };
        // Лишние аргументы - применение ответа хендлера. У параметризованного
        // такой ровно один: начальное состояние, которое элаборация ставит
        // снаружи элиминатора (`(#handleState … ) s0`, §3.4).
        for argument in arguments.iter().skip(arity) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Приостановленное вычисление, запущенное на месте.
    ///
    /// `{ε} A` есть нульместная функция (§3.4), и приостановка снимается там,
    /// где элиминатор её принял. Написанной лямбде хватает снятия связывания;
    /// всему прочему дописывается применение к единице, и оно идёт обычным
    /// путём: имя зовётся прямо, значение - через трамплин.
    ///
    /// Общее у хендлера и у маски: оба принимают вычисление и оба запускают его
    /// сами. Ручку стека это не решает - её ставит вызывающий.
    fn triggered(
        &mut self,
        scope: &mut Scope,
        computation: &Term,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        if let Term::Lam(_, _, body) = computation {
            let body = Rc::clone(body);
            scope.env.push(Slot::Absent);
            let lowered = self.shaped(scope, &body, Repr::Boxed, at);
            scope.env.pop();
            return lowered;
        }
        let unit = self.unit_name()?;
        let triggered = Term::App(Rc::new(computation.clone()), Rc::new(Term::constant(&unit)));
        self.shaped(scope, &triggered, Repr::Boxed, at)
    }

    /// Маска: `#mask.L` (§3.4, §10 вопрос 72).
    ///
    /// Кадра маска не ставит. Всё её понижение - вектор без ближайшей записи
    /// своей метки ([`Expr::Mask`]) и вычисление под ним. Счётчиком пропусков
    /// это не выражается: `skip` нужен **месту операции**, а операции лежат
    /// внутри маскируемого вычисления, то есть в чужой функции, и статического
    /// счёта у них нет. Вектор же приходит этому вычислению целиком.
    ///
    /// Метку берёт **имя элиминатора**, а не окружающая: `#mask.L` её называет,
    /// и второго источника у понижения нет.
    fn masked(
        &mut self,
        scope: &mut Scope,
        eliminator: &Name,
        effect: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let label = self.label(effect)?;
        let DefinitionKind::Effect { params, .. } = &self.definition(effect)?.kind else {
            unreachable!("`label` уже проверил вид метки")
        };
        // Параметры метки, `a`, вычисление.
        let arity = *params as usize + 2;
        if arguments.len() < arity {
            return Err(LowerError::Handler {
                name: eliminator.to_string(),
                why: "элиминатор не насыщен: маска значением этим срезом не берётся",
            });
        }
        let Arg::Written(computation) = &arguments[arity - 1] else {
            return Err(LowerError::Handler {
                name: eliminator.to_string(),
                why: "вычисление под маской пришло достроенным, а не написанным",
            });
        };
        let computation = self.triggered(scope, computation, "вычисление под маской")?;
        let mut value = Expr::Mask {
            label,
            computation: Box::new(computation),
        };
        for argument in arguments.iter().skip(arity) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Единственный конструктор `Unit`: им запускается приостановленное.
    fn unit_name(&self) -> Result<Name, LowerError> {
        match self.signature.constructors(UNIT) {
            Some([only]) => Ok(Rc::clone(only)),
            _ => Err(LowerError::Unknown {
                name: UNIT.to_owned(),
            }),
        }
    }

    /// Ветка операции: своя функция и вердикт при ней.
    ///
    /// Вердиктов берётся два из трёх (§3.4). **Хвостово-резумптивная**: `resume`
    /// в хвосте снят, а не сохранён, - ответ ветки и есть значение операции,
    /// продолжение остаётся на C-стеке, сегмент не режется. Это «tail-resumptive
    /// → inline» минус инлайнинг, который придёт вопросом 74. **Абортивная**:
    /// `resume` не зовётся вовсе, и снимать нечего - связывание его остаётся
    /// пустым слотом среды де Брёйна ровно так же. Ответ такой ветки есть ответ
    /// хендлера, и сегмент до его кадра срезается на месте операции.
    ///
    /// **Общая**: `resume` зовётся, но не в хвосте. Сегмент режется в значение
    /// и приходит ветке лишним параметром; возобновление ставит его обратно
    /// ([`Expr::Resume`]), а недожившая резумпция раскручивается своим дропом.
    ///
    /// У мультишотного хендлера вердикт **не считается**, а берётся общим у
    /// всех веток: две первые формы стоят на «резумпция зовётся не более
    /// одного раза», а ω-резумпция этого не обещает (§3.4). Цена названа -
    /// ветка `toss -> resume True` платит за разрез сегмента, которого
    /// одношотная не платила; снимет её инлайнинг, вопрос 74.
    fn branch(
        &mut self,
        site: &Site<'_>,
        term: &Term,
        written: usize,
        operation: &Name,
    ) -> Result<(FuncId, Verdict), LowerError> {
        let Site {
            captured,
            inner,
            effect,
            multi,
        } = *site;
        let mut nested = Scope {
            locals: u32::try_from(captured.len()).unwrap_or(u32::MAX),
            env: inner.to_vec(),
            // Дескрипторы наружу не едут - тот же довод, что у замыкания.
            dicts: Dicts::new(),
        };
        let mut bindings = Vec::with_capacity(written);
        let mut current = Rc::new(term.clone());
        for _ in 0..written {
            let step = Rc::clone(&current);
            let Term::Lam(mult, name, body) = &*step else {
                return Err(LowerError::Verdict {
                    effect: effect.to_string(),
                    operation: operation.to_string(),
                    why: "связывает меньше аргументов, чем объявила операция",
                });
            };
            bindings.push(Binding {
                name: name.to_string(),
                local: nested.fresh(),
                fact: Fact::present(*mult),
            });
            current = Rc::clone(body);
        }
        // Последнее связывание ветки - `resume`; имя вводит сама форма (§3.4).
        let Term::Lam(_, _, body) = &*Rc::clone(&current) else {
            return Err(LowerError::Verdict {
                effect: effect.to_string(),
                operation: operation.to_string(),
                why: "не связывает резумпцию: форма ветки нарушена",
            });
        };
        let body = Rc::clone(body);
        // Связываний под телом ветки: захваченная среда, аргументы операции и
        // сама резумпция. Число это нужно нормализации, а её - счёту вхождений.
        let context = u32::try_from(inner.len() + written + 1).unwrap_or(u32::MAX);
        // Хвостовая проверяется первой: `untail` спрашивает написанное, а
        // `mentions` - нормализованное, и ветка с имплиситом в аргументе
        // проходит только в этом порядке (измерено на
        // `region-allocates-and-reads`).
        let (rewritten, verdict) = if multi {
            ((*body).clone(), Verdict::General)
        } else {
            match untail(&body, 0, context) {
                // Хвост снят, и больше резумпция нигде не названа: сегмент цел.
                Some(rewritten) if !mentions(&rewritten, 0, context) => (rewritten, Verdict::Tail),
                // Резумпцию тело не зовёт, но **назвать** её редекс имплисита
                // может, а слот её пуст: тогда понижается нормализованное - там
                // имени уже нет.
                None if !mentions(&body, 0, context) => {
                    let mut free = BTreeSet::new();
                    escaping(&body, 0, &mut free);
                    let taken = if free.contains(&0) {
                        normalized(&body, context)
                    } else {
                        (*body).clone()
                    };
                    (taken, Verdict::Abortive)
                }
                // Общая. Понижается **написанное** тело, как у двух прочих
                // вердиктов: нормализация здесь сводила бы и `let`, то есть
                // размножала бы вычисление по вхождениям связывания.
                _ => ((*body).clone(), Verdict::General),
            }
        };

        for binding in &bindings {
            nested.env.push(Slot::Bound(binding.local, binding.fact));
        }
        // Связывание `resume`. У хвостовой и абортивной значения у него нет:
        // первая его сняла, вторая не звала вовсе. У общей оно есть - ручка
        // сегмента приходит лишним параметром, - и связывание настоящее.
        let mut parameters = bindings;
        if verdict == Verdict::General {
            let resumption = Binding {
                name: "резумпция".to_owned(),
                local: nested.fresh(),
                // Кратность стоит на самой резумпции: `1` у `handle`, `ω` у
                // `handleMulti` (§3.4). Вставке RC она безразлична - та считает
                // вхождения, - но факт этот принадлежит связыванию.
                fact: Fact::present(if multi { Mult::Many } else { Mult::One })
                    .shaped(Repr::Resumption),
            };
            nested
                .env
                .push(Slot::Bound(resumption.local, resumption.fact));
            parameters.push(resumption);
        } else {
            nested.env.push(Slot::Absent);
        }

        let function = FuncId(self.functions.len());
        self.functions.push(Function {
            id: function,
            name: format!("ветка {effect}.{operation}"),
            // Вторая форма: ветка вправе производить - её окружающая есть
            // окружающая применения `handle` (§3.4).
            form: Form::Detached,
            captured: captured.to_vec(),
            parameters,
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let outer = std::mem::replace(&mut self.detached, true);
        let lowered = self.shaped(&mut nested, &rewritten, Repr::Boxed, "тело ветки хендлера");
        self.detached = outer;
        self.functions[function.0].body = lowered?;
        Ok((function, verdict))
    }

    /// Ветка `return`: одноместная, ей идёт значение вычисления.
    fn returning(
        &mut self,
        captured: &[Binding],
        inner: &[Slot],
        term: &Term,
        effect: &Name,
    ) -> Result<FuncId, LowerError> {
        let Term::Lam(mult, name, body) = term else {
            return Err(LowerError::Verdict {
                effect: effect.to_string(),
                operation: "return".to_owned(),
                why: "не связывает значения вычисления: форма ветки нарушена",
            });
        };
        let mut nested = Scope {
            locals: u32::try_from(captured.len()).unwrap_or(u32::MAX),
            env: inner.to_vec(),
            dicts: Dicts::new(),
        };
        let binding = Binding {
            name: name.to_string(),
            local: nested.fresh(),
            fact: Fact::present(*mult),
        };
        nested.env.push(Slot::Bound(binding.local, binding.fact));
        let body = Rc::clone(body);

        let function = FuncId(self.functions.len());
        self.functions.push(Function {
            id: function,
            name: format!("ветка {effect}.return"),
            form: Form::Detached,
            captured: captured.to_vec(),
            parameters: vec![binding],
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let outer = std::mem::replace(&mut self.detached, true);
        let lowered = self.shaped(&mut nested, &body, Repr::Boxed, "тело ветки `return`");
        self.detached = outer;
        self.functions[function.0].body = lowered?;
        Ok(function)
    }

    /// Захват среды: связывания, их значения на месте и среда вложенного тела.
    ///
    /// Общее у замыкания и у кадра хендлера, и общее не случайно: оба уносят
    /// связывания наружу своего тела, оба кладут их слотами, и оба принимают
    /// только указательное - слот у них единообразен (§4.11).
    fn capturing(
        scope: &Scope,
        free: &BTreeSet<u32>,
        at: &'static str,
    ) -> Result<Captured, LowerError> {
        let depth = scope.env.len();
        let mut captured = Vec::new();
        let mut taken = Vec::new();
        let mut inner = Vec::with_capacity(depth);
        for (position, slot) in scope.env.iter().enumerate() {
            let index = u32::try_from(depth - position - 1).unwrap_or(u32::MAX);
            if !free.contains(&index) {
                inner.push(Slot::Absent);
                continue;
            }
            let Slot::Bound(local, fact) = slot else {
                return Err(LowerError::Unbound { index });
            };
            if fact.present && !fact.repr.pointer() {
                return Err(LowerError::Representation {
                    at,
                    want: describe(Repr::Boxed),
                    got: describe(fact.repr),
                });
            }
            let id = LocalId(u32::try_from(captured.len()).unwrap_or(u32::MAX));
            captured.push(Binding {
                name: format!("захвачено{}", captured.len()),
                local: id,
                fact: *fact,
            });
            taken.push(if fact.present {
                Expr::Local(*local)
            } else {
                Expr::Erased
            });
            inner.push(Slot::Bound(id, *fact));
        }
        Ok((captured, taken, inner))
    }

    /// Приостановленное вычисление `(ω _ : Unit) -> {ρ} a`, снятое на месте.
    ///
    /// Снятое, а не применённое: `(\_ -> e) ()` через общий путь стоило бы
    /// замыкания, то есть ячейки кучи на каждый scope с ресурсом.
    ///
    /// Триггер не связывается ничем. §3.3 строит приостановку сдвигом тела
    /// (`Elaborator::closing`), поэтому назвать его тело не может по
    /// построению; назови - придёт [`LowerError::Unbound`], а не тихий ответ.
    fn resumed(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        let Term::Lam(_, _, inner) = term else {
            return Err(LowerError::Scope);
        };
        scope.env.push(Slot::Absent);
        let lowered = self.expr(scope, inner);
        scope.env.pop();
        lowered
    }

    /// Понижает примитив: тип, литерал либо операцию (§4.3, §4.11).
    ///
    /// Ячейки кучи здесь не возникает ни на одной ветке - плоское значение
    /// живёт в регистре, - и это то самое, что показывает счётчик блоков.
    fn primitive(
        &mut self,
        scope: &mut Scope,
        prim: Prim,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        match prim {
            Prim::Ty(ty) => Err(LowerError::TypeValue {
                name: ty.name().to_owned(),
            }),
            Prim::Array => Err(LowerError::TypeValue {
                name: adamas_core::prim::ARRAY.to_owned(),
            }),
            Prim::Over(op) => self.array(scope, op, arguments),
            Prim::Block => Err(LowerError::TypeValue {
                name: adamas_core::prim::BLOCK.to_owned(),
            }),
            Prim::In(op) => self.region(scope, op, arguments),
            Prim::Lit(ty, bits) => {
                if arguments.is_empty() {
                    Ok((Expr::Literal { ty, bits }, Repr::Flat(ty)))
                } else {
                    Err(LowerError::Unsupported {
                        form: "литерал в позиции функции",
                    })
                }
            }
            Prim::Op(op, ty) => {
                let [left, right] = arguments else {
                    return Err(LowerError::Partial {
                        name: format!("{op}{ty}"),
                    });
                };
                let want = Repr::Flat(ty);
                let left = self.given(scope, left, want, "левый аргумент операции")?;
                let right = self.given(scope, right, want, "правый аргумент операции")?;
                Ok((
                    Expr::Primitive {
                        op,
                        ty,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    want,
                ))
            }
            // Ответ сравнения - конструктор `Bool` программы (§4.3), поэтому
            // теги берутся у неё по имени. Не объявлен - сюда бы и не доехало:
            // тип сравнения назвал `Bool` раньше, и отказала бы проверка.
            Prim::Cmp(op, ty) => {
                let [left, right] = arguments else {
                    return Err(LowerError::Partial {
                        name: format!("{op}{ty}"),
                    });
                };
                let flat = Repr::Flat(ty);
                let left = self.given(scope, left, flat, "левый аргумент сравнения")?;
                let right = self.given(scope, right, flat, "правый аргумент сравнения")?;
                let yes = self.tag(&Name::from(adamas_core::prim::TRUE))?;
                let no = self.tag(&Name::from(adamas_core::prim::FALSE))?;
                Ok((
                    Expr::Compare {
                        op,
                        ty,
                        left: Box::new(left),
                        right: Box::new(right),
                        yes,
                        no,
                    },
                    Repr::Boxed,
                ))
            }
        }
    }

    /// Операция над массивом (§4.11).
    ///
    /// Шаг индексации читается у **написанного** типа элемента - у того самого
    /// стёртого аргумента, который операция несёт вторым (у `arrayNew` -
    /// первым). Читается он там, а не у представления массива, ровно потому,
    /// что представление отвечает «плоский или указательный», а шаг - число, и
    /// приходит оно либо типом, либо дескриптором из контекста.
    fn array(
        &mut self,
        scope: &mut Scope,
        op: ArrayOp,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let wanted = match op {
            ArrayOp::New => 3,
            ArrayOp::Index => 4,
            ArrayOp::Set => 5,
        };
        if arguments.len() != wanted {
            return Err(LowerError::PartialArray {
                name: op.name().to_owned(),
            });
        }
        // Тип элемента: у `arrayNew` он единственный стёртый аргумент, у
        // прочих - второй, после длины.
        let at = usize::from(op != ArrayOp::New);
        let Arg::Written(element) = arguments[at] else {
            return Err(LowerError::PartialArray {
                name: op.name().to_owned(),
            });
        };
        let depth = u32::try_from(scope.env.len()).unwrap_or(u32::MAX);
        // Решение имплисита приезжает бета-редексом по контексту, поэтому тип
        // сперва нормализуется: `((\m -> #2) …)` переменной не является, а
        // после нормализации является.
        let element = normalized(element, depth);
        let dicts = scope.dicts.clone();
        let stride = self.stride_of(&element, depth, &dicts);
        // Представление ячейки: у плоского массива его даёт шаг, у
        // указательного - сам тип элемента. Второе не «просто указатель»:
        // `Array n Cell` держит записи, и форма их нужна проекции.
        let elements = match stride {
            Some(stride) => stride.element(),
            None => self.repr_of(&element, depth, &dicts)?,
        };
        let cells = stride.map_or(Elems::Boxed, |_| Elems::Flat);
        let word = Repr::Flat(PrimTy::UInt64);
        match op {
            ArrayOp::New => {
                let count = self.given(scope, &arguments[1], word, "длина массива")?;
                let initial = self.given(scope, &arguments[2], elements, "ячейка массива")?;
                Ok((
                    Expr::ArrayNew {
                        stride,
                        count: Box::new(count),
                        initial: Box::new(initial),
                    },
                    Repr::Array(cells),
                ))
            }
            ArrayOp::Index => {
                let array =
                    self.given(scope, &arguments[2], Repr::Array(cells), "читаемый массив")?;
                let at = self.given(scope, &arguments[3], word, "номер ячейки")?;
                Ok((
                    Expr::ArrayIndex {
                        stride,
                        array: Box::new(array),
                        at: Box::new(at),
                    },
                    elements,
                ))
            }
            ArrayOp::Set => {
                let array = self.given(
                    scope,
                    &arguments[2],
                    Repr::Array(cells),
                    "переписываемый массив",
                )?;
                let at = self.given(scope, &arguments[3], word, "номер ячейки")?;
                let value = self.given(scope, &arguments[4], elements, "ячейка массива")?;
                Ok((
                    Expr::ArraySet {
                        stride,
                        array: Box::new(array),
                        at: Box::new(at),
                        value: Box::new(value),
                    },
                    Repr::Array(cells),
                ))
            }
        }
    }

    /// Операция над регионом (§3.6).
    ///
    /// Ширина нагрузки читается у **написанного** её типа - того самого
    /// стёртого аргумента, который операция несёт первым, - и тем же
    /// [`Self::stride_of`], каким её читает массив. Иначе и быть не может:
    /// плоская укладка одна на язык, и два её счёта разъехались бы молча.
    ///
    /// Нагрузка, у которой шага нет, отвергается здесь названной причиной.
    /// Типовая сторона такую нагрузку обычно не пропускает - `{Flat a}` стоит
    /// в типе операции, - но перечни расходятся: `Flat` выводится для
    /// семейства с тегом и для вложенного агрегата, а плотной укладки в
    /// понижении у них нет (§10 вопрос 157).
    fn region(
        &mut self,
        scope: &mut Scope,
        op: adamas_core::prim::RegionOp,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        use adamas_core::prim::RegionOp;
        let wanted = match op {
            RegionOp::New => 0,
            RegionOp::Last => 1,
            RegionOp::Recycle | RegionOp::Pop => 2,
            RegionOp::Alloc | RegionOp::Read => 4,
            RegionOp::Write => 5,
        };
        if arguments.len() != wanted {
            return Err(LowerError::PartialRegion {
                name: op.name().to_owned(),
            });
        }
        let word = Repr::Flat(PrimTy::UInt64);
        if op == RegionOp::New {
            return Ok((Expr::RegionNew, Repr::Region));
        }
        if op == RegionOp::Last {
            let region = self.given(scope, &arguments[0], Repr::Region, "регион")?;
            return Ok((
                Expr::RegionLast {
                    region: Box::new(region),
                },
                word,
            ));
        }
        // Возврат ячейки нагрузки не несёт: размер её помнит область, а не
        // написанный тип. Отсюда и позиции - блок первым, хендл вторым.
        if matches!(op, RegionOp::Recycle | RegionOp::Pop) {
            let region = self.given(scope, &arguments[0], Repr::Region, "регион")?;
            let at = self.given(scope, &arguments[1], word, "хендл региона")?;
            let region = Box::new(region);
            let at = Box::new(at);
            let value = if op == RegionOp::Recycle {
                Expr::RegionRecycle { region, at }
            } else {
                Expr::RegionPop { region, at }
            };
            return Ok((value, Repr::Region));
        }
        // Тип нагрузки - первый стёртый аргумент; второй стёртый есть словарь
        // `Flat`, и понижение его не читает: шаг оно берёт у типа, а словарь
        // из телескопа находит [`Self::stride_of`] сам.
        let Arg::Written(payload) = arguments[0] else {
            return Err(LowerError::PartialRegion {
                name: op.name().to_owned(),
            });
        };
        let depth = u32::try_from(scope.env.len()).unwrap_or(u32::MAX);
        let payload = normalized(payload, depth);
        let dicts = scope.dicts.clone();
        let Some(stride) = self.stride_of(&payload, depth, &dicts) else {
            let repr = self.repr_of(&payload, depth, &dicts)?;
            return Err(LowerError::RegionPayload {
                written: describe(repr),
            });
        };
        let carried = stride.element();
        let region = self.given(scope, &arguments[2], Repr::Region, "регион")?;
        match op {
            RegionOp::Alloc => {
                let value = self.given(scope, &arguments[3], carried, "нагрузка региона")?;
                Ok((
                    Expr::RegionAlloc {
                        stride,
                        region: Box::new(region),
                        value: Box::new(value),
                    },
                    Repr::Region,
                ))
            }
            RegionOp::Read => {
                let at = self.given(scope, &arguments[3], word, "хендл региона")?;
                Ok((
                    Expr::RegionRead {
                        stride,
                        region: Box::new(region),
                        at: Box::new(at),
                    },
                    carried,
                ))
            }
            RegionOp::Write => {
                let at = self.given(scope, &arguments[3], word, "хендл региона")?;
                let value = self.given(scope, &arguments[4], carried, "нагрузка региона")?;
                Ok((
                    Expr::RegionWrite {
                        stride,
                        region: Box::new(region),
                        at: Box::new(at),
                        value: Box::new(value),
                    },
                    Repr::Region,
                ))
            }
            RegionOp::New | RegionOp::Last | RegionOp::Recycle | RegionOp::Pop => {
                unreachable!("разобраны выше")
            }
        }
    }

    /// Применение конструктора: насыщенное собирает объект, недобранное -
    /// замыкание.
    fn built(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let constructor = self.tag(name)?;
        let binders = self.constructors[usize::from(constructor.0)]
            .binders
            .clone();
        // Насыщено, если всё недоданное стёрто: у него значений нет вовсе.
        let complete = arguments.len() >= binders.len()
            || binders[arguments.len()..].iter().all(|fact| !fact.present);
        if !complete {
            // Недобранное собирается замыканием, а замыкание копит аргументы
            // слотами указателей: плоскому полю там места нет (§4.11).
            pointing(&binders, "поле недобранного конструктора")?;
            let mut value = Expr::ConstructClosure { constructor };
            for (position, argument) in arguments.iter().enumerate() {
                // Стёртая позиция применяется наравне с живой - замыкание
                // берёт **все** связывания ядра позиционно, - но написанное в
                // ней не понижается: параметром семейства стоит имя типа.
                let argument = if binders.get(position).is_some_and(|it| !it.present) {
                    Expr::Erased
                } else {
                    self.given(
                        scope,
                        argument,
                        Repr::Boxed,
                        "аргумент недобранного конструктора",
                    )?
                };
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        }
        let mut built = Vec::with_capacity(binders.len());
        for (position, fact) in binders.iter().enumerate() {
            if !fact.present {
                built.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            built.push(self.given(scope, argument, fact.repr, "поле конструктора")?);
        }
        // Переиспользование ставит вставка RC ([`crate::perceus`]): понижение
        // разобранного не помнит, а она помнит.
        let mut value = Expr::Construct {
            constructor,
            reuse: None,
            arguments: built,
        };
        for argument in arguments.iter().skip(binders.len()) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Применение определения: насыщенное зовёт напрямую, недобранное -
    /// замыкание.
    fn called(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let function = self.function(name)?;
        let parameters: Vec<Fact> = self.functions[function.0]
            .parameters
            .iter()
            .map(|it| it.fact)
            .collect();
        let result = self.functions[function.0].result;
        let complete = arguments.len() >= parameters.len()
            || parameters[arguments.len()..]
                .iter()
                .all(|fact| !fact.present);
        if !complete {
            // Недобранный вызов уходит замыканием, а трамплин отдаёт слоты
            // указателями: плоский параметр или плоский ответ через него не
            // проходят (§4.11).
            pointing(&parameters, "параметр недобранного вызова")?;
            if !result.boxed() {
                return Err(LowerError::Representation {
                    at: "ответ недобранного вызова",
                    want: describe(Repr::Boxed),
                    got: describe(result),
                });
            }
            let mut value = Expr::Closure {
                function,
                captured: Vec::new(),
            };
            for (position, argument) in arguments.iter().enumerate() {
                // Стёртая позиция применяется наравне с живой - замыкание
                // берёт **все** связывания ядра позиционно, - но написанное в
                // ней не понижается: значения у него нет, а стоять там может
                // и имя семейства.
                let argument = if parameters.get(position).is_some_and(|it| !it.present) {
                    Expr::Erased
                } else {
                    self.given(scope, argument, Repr::Boxed, "аргумент недобранного вызова")?
                };
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        }
        let mut given = Vec::with_capacity(parameters.len());
        for (position, fact) in parameters.iter().enumerate() {
            if !fact.present {
                given.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            given.push(self.given(scope, argument, fact.repr, "аргумент вызова")?);
        }
        let mut value = Expr::Call {
            function,
            arguments: given,
        };
        let extra = arguments.len().saturating_sub(parameters.len());
        if extra == 0 {
            return Ok((value, result));
        }
        // Пересып: определение отдало функцию, и остаток спайна применяется к
        // ней. Стирания здесь уже нет - имени нет тоже.
        if !result.boxed() {
            return Err(LowerError::Representation {
                at: "применяемое значение",
                want: describe(Repr::Boxed),
                got: describe(result),
            });
        }
        for argument in arguments.iter().skip(parameters.len()) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Понижает разбор.
    /// Факты полей ветви разбора.
    ///
    /// У плотного разбираемого поля приходят байтами своего варианта: их
    /// представления - подставленные примитивы слотов, а не факты таблицы, у
    /// которой параметр семейства указателен.
    fn branch_facts(&self, packed: Option<PackId>, constructor: CtorId) -> Vec<Fact> {
        let described = &self.constructors[usize::from(constructor.0)];
        let params = described.params as usize;
        match packed
            .and_then(|pack| self.packings[pack.0 as usize].variant_of(constructor))
            .map(|(_, variant)| variant.slots.clone())
        {
            Some(slots) => {
                let mut slot = 0usize;
                described
                    .binders
                    .iter()
                    .skip(params)
                    .map(|fact| {
                        if !fact.present {
                            return *fact;
                        }
                        let ty = slots[slot].ty;
                        slot += 1;
                        Fact::declared(fact.mult).shaped(ty.repr())
                    })
                    .collect()
            }
            None => described.binders.iter().skip(params).copied().collect(),
        }
    }

    /// Разбираемое и его плотная укладка, когда она семейная.
    ///
    /// Плотное семейство разбирается по собственному тегу (§10 вопрос 157);
    /// прочее приводится к объекту - тег лежит в его заголовке, а у плоской
    /// записи заголовка нет вовсе (§4.11).
    /// Оборачивает разбираемое отменой, если разбирается задача (§5.2).
    ///
    /// Потребить задачу мимо `await` можно одним способом - разобрать её
    /// значение, и так написан всякий деструктор; отмена поэтому стоит на
    /// **разборе**, а не на имени деструктора, которого сигнатура рантайма не
    /// знает. Явный `case` автора - то же потребление и та же отмена.
    ///
    /// Семейство берётся у **написанного** результата `spawn`, как берёт его
    /// машина, и без объявленного питомника отмены не бывает вовсе: разбор
    /// одноимённого типа в программе без круга есть обычный разбор.
    fn cancelling(&mut self, scrutinee: Expr, data: &Name) -> Result<Expr, LowerError> {
        if self.task_family.as_deref() != Some(&**data) {
            return Ok(scrutinee);
        }
        let spawn: Name = Rc::from(SPAWN);
        let Some(shape) = self.task_shape(&spawn)? else {
            return Ok(scrutinee);
        };
        if !self.detached {
            // Раскрутка отменённого файбера кладётся кадром, а кадр умеет
            // только вторая форма: у первой стека нет вовсе. Отказ, а не
            // молчание, - молча не отменить значит не досчитать деструкторов.
            return Err(LowerError::Nursery {
                name: data.to_string(),
                why: "отмена задачи в первой форме: ручки стека нет",
            });
        }
        Ok(Expr::Cancel {
            at: shape.at,
            value: Box::new(scrutinee),
        })
    }

    fn scrutinised(
        &mut self,
        scope: &mut Scope,
        term: &Term,
    ) -> Result<(Expr, Option<PackId>), LowerError> {
        let (scrutinee, got) = self.expr(scope, term)?;
        let packed = match got {
            Repr::Packed(pack) => self.packings[pack.0 as usize]
                .variants
                .first()
                .and_then(|variant| variant.ctor)
                .map(|_| pack),
            _ => None,
        };
        if packed.is_some() || fits(got, Repr::Boxed) {
            return Ok((scrutinee, packed));
        }
        if let Some(moved) = self.moved(scope, &scrutinee, got, Repr::Boxed)? {
            return Ok((moved, None));
        }
        Err(LowerError::Representation {
            at: "разбираемое",
            want: describe(Repr::Boxed),
            got: describe(got),
        })
    }

    fn analysis(&mut self, scope: &mut Scope, case: &Case) -> Result<(Expr, Repr), LowerError> {
        self.family(&case.data)?;
        let (scrutinee, packed) = self.scrutinised(scope, &case.scrutinee)?;
        let scrutinee = match packed {
            Some(_) => scrutinee,
            None => self.cancelling(scrutinee, &case.data)?,
        };
        // Пустой разбор ответа не даёт: тип пуст, и до печати дело не дойдёт.
        let mut answer = Repr::Boxed;
        let mut arms = Vec::with_capacity(case.branches.len());
        for branch in &case.branches {
            let constructor = self.tag(&branch.constructor)?;
            let facts = self.branch_facts(packed, constructor);
            let mut fields: Vec<Binding> = facts
                .iter()
                .enumerate()
                .map(|(position, fact)| Binding {
                    name: format!("поле{position}"),
                    local: scope.fresh(),
                    fact: *fact,
                })
                .collect();

            // Тело ветви есть функция от полей: сколько ведущих лямбд, столько
            // связываний снимается на месте, остаток применяется.
            let mut current = Rc::new((*branch.body).clone());
            let mut taken = 0;
            while taken < fields.len() {
                let step = Rc::clone(&current);
                let Term::Lam(_, bound, inner) = &*step else {
                    break;
                };
                fields[taken].name = bound.to_string();
                scope
                    .env
                    .push(Slot::Bound(fields[taken].local, fields[taken].fact));
                current = Rc::clone(inner);
                taken += 1;
            }
            let body = self.expr(scope, &current);
            scope.env.truncate(scope.env.len() - taken);
            let (mut body, mut repr) = body?;
            for field in fields.iter().skip(taken) {
                if !repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "применяемое значение",
                        want: describe(Repr::Boxed),
                        got: describe(repr),
                    });
                }
                if field.fact.present && !field.fact.repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "неснятое поле ветви",
                        want: describe(Repr::Boxed),
                        got: describe(field.fact.repr),
                    });
                }
                body = Expr::Apply {
                    callee: Box::new(body),
                    argument: Box::new(if field.fact.present {
                        Expr::Local(field.local)
                    } else {
                        Expr::Erased
                    }),
                };
                repr = Repr::Boxed;
            }
            // Ветви отвечают одним значением, значит и представление у них
            // одно: разойдись оно, у разбора не было бы C-типа.
            if arms.is_empty() {
                answer = repr;
            } else if fits(repr, answer) {
                // Годится как есть.
            } else if repr.pointer() && answer.pointer() {
                // Две записи разной формы либо запись с указателем: общее у них
                // одно - указатель, и форма теряется.
                answer = Repr::Boxed;
            } else if let Some(moved) = self.moved(scope, &body, repr, answer)? {
                // Поле параметрического семейства связано указателем таблицы,
                // а соседняя ветвь ответила примитивом (§10 вопрос 159):
                // ветви сводятся перекладом - обёртка примитива в обе стороны.
                body = moved;
            } else {
                return Err(LowerError::Representation {
                    at: "ветвь разбора",
                    want: describe(answer),
                    got: describe(repr),
                });
            }
            arms.push(Arm {
                constructor,
                fields,
                body,
            });
        }
        Ok((
            Expr::Match {
                scrutinee: Box::new(scrutinee),
                consumed: case.consumed,
                arms,
            },
            answer,
        ))
    }

    /// Понижает лямбду в замыкание: своя функция плюс захваченная среда.
    ///
    /// Связывания лямбды объявляются указательными: типа у них в ядре нет, и
    /// прочитать представление неоткуда. Плоское значение поэтому через
    /// границу замыкания не проходит - ни захватом, ни аргументом, - и это
    /// названная граница, а не упущение: §4.11 отдаёт этот случай дескриптору
    /// layout, которого в рантайме ещё нет.
    fn closure(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        self.abstraction(scope, term, false)
    }

    /// Она же с отброшенным ответом: тело считается, значение уходит в дроп.
    ///
    /// Нужно деструктору scope'а. Ответ его §3.3 отбрасывает, а зовут его двое -
    /// нормальный выход и раскрутка, - и раскрутка о типе ответа не знает
    /// ничего: дропнуть его она может только мелко, без детей. Значит отдавать
    /// его обязан сам деструктор, и отдаёт его обычное правило
    /// [`crate::perceus`]: связывание есть, употребления нет.
    fn discarding(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        self.abstraction(scope, term, true)
    }

    fn abstraction(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        discard: bool,
    ) -> Result<(Expr, Repr), LowerError> {
        let mut parameters: Vec<(Mult, String)> = Vec::new();
        let mut current = Rc::new(term.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(mult, name, inner) = &*step else {
                break;
            };
            parameters.push((*mult, name.to_string()));
            current = Rc::clone(inner);
        }

        // Захватывается то, на что тело смотрит наружу.
        let mut free = BTreeSet::new();
        escaping(term, 0, &mut free);
        let (captured, taken, inner) = Self::capturing(scope, &free, "захват замыкания")?;

        let mut nested = Scope {
            locals: u32::try_from(captured.len()).unwrap_or(u32::MAX),
            env: inner,
            // Дескрипторы наружу не едут: захват объявлен указательным, а
            // словарь им не является. Обобщённый код внутри лямбды поэтому
            // считает элемент указательным - названная граница §4.11.
            dicts: Dicts::new(),
        };
        // Лямбда получает значение всегда: стирает машина по типу глобального
        // имени, а здесь имени нет.
        let bindings: Vec<Binding> = parameters
            .iter()
            .map(|(mult, name)| Binding {
                name: name.clone(),
                local: nested.fresh(),
                fact: Fact::present(*mult),
            })
            .collect();
        for binding in &bindings {
            nested.env.push(Slot::Bound(binding.local, binding.fact));
        }

        let function = FuncId(self.functions.len());
        self.functions.push(Function {
            id: function,
            name: format!("лямбда{}", function.0),
            // Вторая форма у всякой лямбды, и это **не** обход решения 1
            // волны 4, а его единственное применение к случаю без row: у
            // связывания лямбды написанного типа в ядре нет вовсе - там же,
            // где нет и его представления (см. шапку модуля). Row её живёт в
            // ожидаемом типе позиции, а типов понижение по выражениям не
            // носит; выбрать первую форму значило бы выбрать её **угадав**, и
            // угаданная лямбда под `handle` операции произвести не может.
            //
            // Цена этого выбора - ноль, и это единственный довод, которым он
            // отличается от произвола. Прямого вызова у лямбды не бывает: зовут
            // её через `adamas_apply`, а граница замыкания несёт оба скрытых
            // аргумента всегда - какая из форм за указателем, место вызова не
            // знает (`adamas.h`, `adamas_code`). Первая форма поэтому не теряет
            // ни одного прямого вызова, а вторая получает два аргумента, за
            // которые уже заплачено трамплином.
            form: Form::Detached,
            captured,
            parameters: bindings,
            // Ответ замыкания приходит через `adamas_apply`, а он говорит
            // указателями: плоский ответ ему не отдать.
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let outer = std::mem::replace(&mut self.detached, true);
        let body = self.shaped(&mut nested, &current, Repr::Boxed, "тело замыкания");
        self.detached = outer;
        let mut body = body?;
        if discard {
            let held = Binding {
                name: "ответ_деструктора".to_owned(),
                local: nested.fresh(),
                fact: Fact::present(Mult::One).shaped(Repr::Boxed),
            };
            let unit = self.tag(&self.unit_name()?)?;
            body = Expr::Bind {
                binding: held,
                value: Box::new(body),
                body: Box::new(Expr::Construct {
                    constructor: unit,
                    reuse: None,
                    arguments: Vec::new(),
                }),
            };
        }
        self.functions[function.0].body = body;
        Ok((
            Expr::Closure {
                function,
                captured: taken,
            },
            Repr::Boxed,
        ))
    }
}

/// Голова написанного результата определения. `None` - результат не имя.
///
/// Читается так же, как её читает машина (`adamas-interp/src/fiber.rs`): тип
/// задачи называет сам `spawn`, вшитого имени у него нет.
fn result_head(ty: &Term) -> Option<Name> {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    let mut head = current;
    while let Term::App(callee, _) = head {
        head = callee;
    }
    match head {
        Term::Const(name, ..) => Some(Rc::clone(name)),
        _ => None,
    }
}

/// Семейство, чей разбор есть отмена задачи. `None` - питомника в программе нет.
///
/// Без объявленного постулата круга не бывает, а без круга не бывает и файбера,
/// который отмена сняла бы: разбор одноимённого типа тогда обычный.
fn nursed_family(signature: &Signature) -> Option<Name> {
    let nursery = signature.lookup(NURSERY)?;
    if nursery.body.is_some() {
        return None;
    }
    let spawn = signature.lookup(SPAWN)?;
    if !matches!(spawn.kind, DefinitionKind::Operation { .. }) {
        return None;
    }
    result_head(&spawn.ty)
}

/// Имя головы спайна под лямбдами. `None` - голова не имя.
fn head(term: &Term) -> Option<String> {
    let mut current = term;
    loop {
        match current {
            Term::Lam(_, _, body) | Term::App(body, _) => current = body,
            Term::Const(name, _, _) => return Some(name.to_string()),
            _ => return None,
        }
    }
}

/// Форма понижения функции: её решает **row написанного типа**.
///
/// Меток в row нет - первая форма. Под общим хендлером такой функции не
/// оказаться: оказаться там значит производить эффект, а производимое стоит в
/// row. Метка есть - вторая: кадр отчуждается в кучу, и функция получает два
/// скрытых аргумента (§13, обе записи 2026-09-08).
///
/// **Пустая row - это «без меток», а не «без хвоста».** Auto-lift (§3.4)
/// дописывает свежую row-переменную всякой позиции сигнатуры, поэтому `sum :
/// List Int -> Int` имеет типом `List Int -> {| e0} Int`, и `Row::is_empty` на
/// нём ложь. Хвост говорит «что угодно сверх у вызывающего», а не «что-то
/// здесь»: погашение расширением справа кладёт его целиком **за** row
/// вызываемого, и производить он не заставляет ничего. Считай хвост меткой - и
/// вторую форму получила бы каждая функция программы.
///
/// Смотрятся **все** стрелки типа, а не последняя: параметров у функции
/// столько, сколько стрелок (§10 вопрос 153), и вызов её - применение сразу
/// ко всем. Метка на любой из них означает, что это применение производит.
///
/// Тоньше не надо: «способна оказаться под общим хендлером» статически не
/// отличима от «под любым», пока хендлер не виден в точке (§10 вопрос 74), а
/// инлайнинг - оптимизация после волны. Цена названа прямо: функция под
/// заведомо хвостово-резумптивной меткой платит за кадр.
fn form(ty: &Term) -> Form {
    let mut current = ty;
    while let Term::Pi(_, _, _, row, codomain) = current {
        if !row.labels().is_empty() {
            return Form::Detached;
        }
        current = codomain;
    }
    Form::Stack
}

/// На каком по счёту аргументе операция производит. `None` - row нигде нет.
///
/// То же правило, которым это решает машина (`adamas-interp/src/effect.rs`):
/// позиция row в типе не соглашение, а место, где объявление проверило форму
/// операции (§3.4).
fn performing(ty: &Term) -> Option<usize> {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, _, _, row, codomain) = current {
        count += 1;
        if !row.labels().is_empty() {
            return Some(count);
        }
        current = codomain;
    }
    None
}

/// Кратности первых `count` связываний типа, в порядке объявления.
fn multiplicities(ty: &Term, count: usize) -> Vec<Mult> {
    let mut current = ty;
    let mut found = Vec::with_capacity(count);
    while found.len() < count {
        let Term::Pi(mult, _, _, _, codomain) = current else {
            break;
        };
        found.push(mult.mult);
        current = codomain;
    }
    found
}

/// Сколько связываний у типа подряд.
fn binders(ty: &Term) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, _, _, _, codomain) = current {
        count += 1;
        current = codomain;
    }
    count
}

/// Домен связывания под номером `index`.
fn domain(ty: &Term, index: usize) -> Option<&Term> {
    match after(ty, index)? {
        Term::Pi(_, _, domain, _, _) => Some(domain),
        _ => None,
    }
}

/// Смотрит ли терм на связывание с индексом `index` под `context` связываниями.
///
/// Считает по **нормализованному** терму, и это не осторожность: решение
/// имплисита приезжает бета-редексом по всему контексту - `((\m₂ -> \m₁ -> \m₀
/// -> #2) #2 #1 #0)`, - то есть называет каждое связывание, включая резумпцию.
/// Считай по написанному, и всякая ветка с имплиситом в аргументе оказалась бы
/// «зовущей резумпцию и в хвосте, и до него»; измерено на
/// `eval/region-allocates-and-reads`, где имплиситы у `MkRef`.
fn mentions(term: &Term, index: u32, context: u32) -> bool {
    let mut free = BTreeSet::new();
    escaping(&normalized(term, context), 0, &mut free);
    free.contains(&index)
}

/// Ветка, зовущая резумпцию **в хвосте**: `resume e` заменяется на `e`.
///
/// `depth` - индекс связывания `resume` в этой точке. `None` значит «вердикт
/// не хвостово-резумптивный», и различить абортивную от общей вызывающему
/// остаётся по тому, упоминается ли резумпция вообще.
///
/// Хвост считается **по написанному** (решение 2 волны 4), поэтому цепочка
/// `let` сквозная - она вычисление, а не ветвление, - а всё прочее нет:
/// разбор в хвосте дал бы по ответу на ветвь, и снимать резумпцию пришлось бы
/// в каждой. Это не запрет, а граница среза: такая ветка уходит треку D
/// названным вердиктом, а не молчанием.
fn untail(term: &Term, depth: u32, context: u32) -> Option<Term> {
    match term {
        Term::App(callee, argument) => match &**callee {
            Term::Var(Index(index)) if *index == depth => Some((**argument).clone()),
            _ => None,
        },
        Term::Let(mult, name, ty, value, body) => {
            if mentions(value, depth, context) {
                return None;
            }
            Some(Term::Let(
                *mult,
                Rc::clone(name),
                Rc::clone(ty),
                Rc::clone(value),
                Rc::new(untail(body, depth + 1, context + 1)?),
            ))
        }
        _ => None,
    }
}

/// Дескриптор укладки, записанный по форме §4.11: `{ layout = { size, align } }`.
///
/// `None` - запись другой формы, и понижать её нечем: общего пути записей у
/// этого среза нет.
fn descriptor(fields: &[(Name, Rc<Term>)]) -> Option<(u32, u32)> {
    let [(name, inner)] = fields else {
        return None;
    };
    if &**name != "layout" {
        return None;
    }
    let Term::Object(pair) = &**inner else {
        return None;
    };
    let [(first, size), (second, align)] = &**pair else {
        return None;
    };
    if &**first != "size" || &**second != "align" {
        return None;
    }
    Some((number(size)?, number(align)?))
}

/// Литерал `UInt32` числом.
fn number(term: &Term) -> Option<u32> {
    match term {
        Term::Prim(Prim::Lit(PrimTy::UInt32, bits)) => u32::try_from(*bits).ok(),
        _ => None,
    }
}

/// Нормализует терм под `depth` связываниями контекста.
///
/// Нужно ровно одному месту - типу элемента массива: решение имплисита
/// приезжает бета-редексом `(\m₂ -> \m₁ -> \m₀ -> #2) #2 #1 #0`, и переменной
/// такой терм не является, пока редекс не сведён. Считает то же ядро, которым
/// считают все три вычислителя; своего правила здесь не заводится.
fn normalized(term: &Term, depth: u32) -> Term {
    let mut env = Env::default();
    for level in 0..depth {
        env = env.extend(Value::var(Lvl(level)));
    }
    quote(depth, &eval(&env, term))
}

/// Голова спайна и его аргументы слева направо.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut head = term;
    while let Term::App(callee, argument) = head {
        arguments.push(&**argument);
        head = callee;
    }
    arguments.reverse();
    (head, arguments)
}

/// Тип после `at` снятых связываний. `None` - связываний столько нет.
fn after(ty: &Term, at: usize) -> Option<&Term> {
    let mut current = ty;
    for _ in 0..at {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    Some(current)
}

/// Сколько алиасов подряд разворачивается по дороге к примитиву.
///
/// Цепочка `type Int = Int64` конечна по построению - ordered scoping (§4.8)
/// не даёт имени сослаться на себя, - но предел стоит: обход по чужой
/// сигнатуре не должен зависать, если она окажется собрана иначе.
const ALIASES: usize = 32;

/// Чтение представлений у **написанных** типов (§4.11, §4.2).
///
/// Методами, а не свободными функциями, потому что форма записи заводится по
/// дороге: у неё есть тег, и тег этот живёт в таблице конструкторов.
impl Lowerer<'_> {
    /// Представление значения написанного типа (§4.11, §4.2).
    ///
    /// Плоским считается ровно примитив: `Flat` над записями и семействами
    /// (§4.11, укладка тегом) существует типовой стороной, а укладывать его в
    /// понижении нечем, пока нет дескриптора layout, - это следующая половина
    /// трека.
    ///
    /// **Закрытая запись даёт форму** ([`Repr::Record`]): метки телескопа в его
    /// порядке, представления полей - тем же правилом рекурсивно. Открытая
    /// формы не даёт - её поля знает хвост, - и остаётся указательной.
    ///
    /// **Алиас разворачивается.** `Int` и `Float` - прелюдные синонимы `Int64` и
    /// `Float64` (§4.3, лог 2026-09-09), то есть каноническое имя написанной
    /// программы, и представление есть свойство типа, а не его написания: типовая
    /// сторона `Flat` (`adamas-elab/src/flat.rs`) читает укладку у **значения**
    /// типа и потому синоним видит насквозь. Разворачивается только имя без
    /// аргументов и только у определения, чей тип - универсум: параметризованный
    /// алиас требует подстановки, которой понижение не делает, и остаётся
    /// указательным.
    fn repr_of(&mut self, ty: &Term, depth: u32, dicts: &Dicts) -> Result<Repr, LowerError> {
        let current = unaliased(self.signature, ty).clone();
        if let Term::Prim(Prim::Ty(prim)) = current {
            return Ok(Repr::Flat(prim));
        }
        // Блок региона (§3.6) - объект кучи со своим дропом, как массив.
        if let Term::Prim(Prim::Block) = current {
            return Ok(Repr::Region);
        }
        // Спайн: массив применён к длине и типу элемента, класс `Flat` - к типу.
        let (head, arguments) = spine(&current);
        match head {
            Term::Prim(Prim::Array) if arguments.len() == 2 => {
                let element = arguments[1].clone();
                return Ok(match self.stride_of(&element, depth, dicts) {
                    Some(_) => Repr::Array(Elems::Flat),
                    None => Repr::Array(Elems::Boxed),
                });
            }
            // `Flat` - единственный класс, чей словарь не объект кучи: у него
            // один метод, и метод этот сам есть укладка (§4.11). Проверяется он
            // **до** разворота, иначе развернулся бы в обычную запись.
            Term::Const(name, ..) if &**name == FLAT && arguments.len() == 1 => {
                return Ok(Repr::Layout);
            }
            _ => {}
        }
        match &unfolded(self.signature, &current, depth) {
            // Запись из одних плоских полей плоская - §4.11 говорит это
            // дословно, и вложенный агрегат ложится собственным слотом (§10
            // вопрос 157). Прочие записи остаются объектом кучи:
            // поле-указатель в плотную укладку не ложится.
            Term::Record(fields) => match self.packed_shape(fields, depth, dicts)? {
                Some(packed) => Ok(packed),
                None => self.record_shape(fields, depth, dicts),
            },
            // Семейство остаётся объектом и тогда, когда у него есть плотная
            // укладка (§10 вопрос 157): плотная форма живёт в плоском
            // хранилище - колонке и кадре, - а голое значение ходит через
            // замыкания и слоты, где плоскому места нет. Перекладывают на
            // границе [`Lowerer::moved`] и разбор.
            _ => Ok(Repr::Boxed),
        }
    }

    /// Плоская укладка записи, если все её поля плоски (§4.11).
    ///
    /// `None` - хотя бы одно поле указательно: указатель в плотную укладку не
    /// ложится, а стёртое поле значения не имеет вовсе. Вложенный агрегат -
    /// запись либо плотное семейство - ложится собственным слотом (§10
    /// вопрос 157).
    fn packed_shape(
        &mut self,
        fields: &adamas_core::term::Fields,
        depth: u32,
        dicts: &Dicts,
    ) -> Result<Option<Repr>, LowerError> {
        if fields.is_open() || fields.is_empty() {
            return Ok(None);
        }
        let mut labels = Vec::with_capacity(fields.len());
        let mut slotted = Vec::with_capacity(fields.len());
        for (position, field) in fields.iter().enumerate() {
            if field.mult == Mult::Zero {
                return Ok(None);
            }
            let under = depth + u32::try_from(position).unwrap_or(0);
            let Some(slot) = self.packed_field(&field.ty, under, dicts)? else {
                return Ok(None);
            };
            labels.push(field.name.to_string());
            slotted.push(slot);
        }
        let made = packing_of_slots(&labels, &slotted, &self.packings);
        if made.size == 0 {
            return Ok(None);
        }
        Ok(Some(Repr::Packed(self.interned(made))))
    }

    /// Слот плоского агрегата для поля такого типа. `None` - поле указательно.
    fn packed_field(
        &mut self,
        ty: &Term,
        depth: u32,
        dicts: &Dicts,
    ) -> Result<Option<SlotTy>, LowerError> {
        let current = unaliased(self.signature, ty).clone();
        if let Term::Prim(Prim::Ty(prim)) = current {
            return Ok(Some(SlotTy::Prim(prim)));
        }
        match &unfolded(self.signature, &current, depth) {
            Term::Record(fields) => Ok(match self.packed_shape(fields, depth, dicts)? {
                Some(Repr::Packed(pack)) => Some(SlotTy::Pack(pack)),
                _ => None,
            }),
            expanded => {
                let (head, arguments) = spine(expanded);
                let Term::Const(name, ..) = head else {
                    return Ok(None);
                };
                let name = Rc::clone(name);
                Ok(self
                    .family_packing(&name, &arguments, depth)?
                    .map(SlotTy::Pack))
            }
        }
    }

    /// Форма записи, прочитанная у её типа.
    ///
    /// Тип поля стоит **под предыдущими полями** телескопа (§4.2), поэтому
    /// глубина растёт по одному на поле: без этого зависимое поле читалось бы
    /// не в своём контексте.
    fn record_shape(
        &mut self,
        fields: &adamas_core::term::Fields,
        depth: u32,
        dicts: &Dicts,
    ) -> Result<Repr, LowerError> {
        if fields.is_open() {
            return Ok(Repr::Boxed);
        }
        let mut labels = Vec::with_capacity(fields.len());
        let mut facts = Vec::with_capacity(fields.len());
        for (position, field) in fields.iter().enumerate() {
            let under = depth + u32::try_from(position).unwrap_or(0);
            let repr = slotted(self.repr_of(&field.ty, under, dicts)?);
            labels.push(field.name.to_string());
            // Типовой член (`type T` в сигнатуре модуля, §4.8) значения в
            // рантайме не имеет: тип стёрт (§3.3), а кратность у него `1` -
            // элаборация даёт её всем членам одинаково. Судить поэтому
            // приходится по **сорту** поля, а не по кратности.
            let mut fact = Fact::declared(field.mult).shaped(repr);
            if universal(&field.ty) {
                fact.present = false;
            }
            facts.push(fact);
        }
        Ok(Repr::Record(self.shape(&labels, &facts)?))
    }

    /// Шаг индексации массива с таким элементом. `None` - элемент указательный.
    ///
    /// Плоским элемент бывает по трём причинам, и §4.11 называет все три.
    /// Примитив - шаг известен типом. **Запись, все поля которой плоские** -
    /// шаг есть её размер, посчитанный [`packing_of`]; это и есть колонка
    /// `Vec3`, ради которой §4.11 писался. И переменная, о которой в
    /// контексте есть словарь `Flat`, - шаг приходит дескриптором, а код один
    /// на все плоские элементы.
    ///
    /// Названная граница: плоским агрегатом берётся запись из плоских полей
    /// и семейство с ними же - вложенность в том числе (§10 вопрос 157).
    fn stride_of(&mut self, ty: &Term, depth: u32, dicts: &Dicts) -> Option<Stride> {
        let current = unaliased(self.signature, ty).clone();
        if let Term::Prim(Prim::Ty(prim)) = current {
            return Some(Stride::Static(prim));
        }
        if let Term::Var(Index(index)) = current {
            let level = depth.checked_sub(index + 1)?;
            return dicts.get(&level).copied().map(Stride::Dynamic);
        }
        match self.packed_field(&current, depth, dicts) {
            Ok(Some(SlotTy::Pack(pack))) => Some(Stride::Packed(pack)),
            _ => None,
        }
    }

    /// Укладка агрегата по меткам и полям; заводится однажды.
    fn packing(&mut self, labels: &[String], fields: &[PrimTy]) -> PackId {
        let made = packing_of(labels, fields, &self.packings);
        self.interned(made)
    }

    /// Номер укладки: одинаковая заводится однажды.
    fn interned(&mut self, made: Packing) -> PackId {
        if let Some(at) = self.packings.iter().position(|it| *it == made) {
            return PackId(u32::try_from(at).unwrap_or(u32::MAX));
        }
        let id = PackId(u32::try_from(self.packings.len()).unwrap_or(u32::MAX));
        self.packings.push(made);
        id
    }

    /// Плотная укладка семейства при таких аргументах типа (§4.11, §10
    /// вопрос 157).
    ///
    /// `None` - семейство не укладывается: конструкторов нет, живое поле
    /// указательно - в том числе параметр, оставшийся переменной в обобщённом
    /// коде, - объявление рекурсивно, либо укладка пуста (единственный
    /// конструктор без полей - непосредственное значение, байтов ему не
    /// нужно). Рекурсия меряется по **объявлению**, а не по применению:
    /// `Box (Box Int8)` вложен конечно и плоский, хотя имя в нём повторяется
    /// (§4.11).
    fn family_packing(
        &mut self,
        data: &Name,
        arguments: &[&Term],
        depth: u32,
    ) -> Result<Option<PackId>, LowerError> {
        // Не-имя и не-семейство - не отказ, а обычное указательное значение:
        // сюда приходит всякий написанный тип.
        let Some(definition) = self.signature.lookup(data) else {
            return Ok(None);
        };
        let DefinitionKind::Data {
            constructors,
            params,
            ..
        } = &definition.kind
        else {
            return Ok(None);
        };
        let (constructors, params) = (constructors.clone(), *params as usize);
        if constructors.is_empty() || arguments.len() < params || recursive(self.signature, data) {
            return Ok(None);
        }
        self.family(data)?;
        let mut variants = Vec::with_capacity(constructors.len());
        for name in &constructors {
            let tag = self.tag(name)?;
            let Some((labels, fields)) =
                self.instantiated_fields(name, &arguments[..params], depth)?
            else {
                return Ok(None);
            };
            variants.push((tag, labels, fields));
        }
        let made = family_packing_of(&variants, &self.packings);
        if made.size == 0 {
            return Ok(None);
        }
        Ok(Some(self.interned(made)))
    }

    /// Поля конструктора при подставленных параметрах семейства: метки и
    /// слоты живых. `None` - живое поле указательно.
    ///
    /// Считает то же ядро, что типовая сторона (`adamas-elab/src/flat.rs`,
    /// `fields`): тип конструктора инстанцируется, параметры снимаются
    /// применением, стёртые связывания полями не считаются - байтов у них
    /// нет. Аргументы стёртых сортов не читаются: укладка от уровня, ряда и
    /// кратности не зависит, а подставить что-то обязан всякий берущий тип.
    #[expect(clippy::type_complexity, reason = "локальная пара варианта")]
    fn instantiated_fields(
        &mut self,
        constructor: &Name,
        params: &[&Term],
        depth: u32,
    ) -> Result<Option<(Vec<String>, Vec<SlotTy>)>, LowerError> {
        let Some(definition) = self.signature.lookup(constructor) else {
            return Ok(None);
        };
        let levels: Vec<Level> = vec![Level::Zero; definition.level_arity as usize];
        let rows: Vec<Row<Term>> = vec![Row::empty(); definition.row_arity as usize];
        let mults: Vec<Mult> = definition
            .mult_allowed
            .iter()
            .map(|allowed| allowed.first().copied().unwrap_or(Mult::Many))
            .collect();
        let mut env = Env::default();
        for level in 0..depth {
            env = env.extend(Value::var(Lvl(level)));
        }
        let mut current = definition.instantiate_type(&levels, &rows, &mults);
        for argument in params {
            let Value::Pi(_, _, _, _, codomain) = &*Rc::clone(&current) else {
                return Ok(None);
            };
            current = codomain.apply(eval(&env, argument));
        }
        let mut level = depth;
        let mut labels = Vec::new();
        let mut fields = Vec::new();
        let empty = Dicts::new();
        while let Value::Pi(binder, name, domain, _, codomain) = &*Rc::clone(&current) {
            if binder.mult != Mult::Zero {
                let written = quote(level, domain);
                let Some(slot) = self.packed_field(&written, level, &empty)? else {
                    return Ok(None);
                };
                labels.push(name.to_string());
                fields.push(slot);
            }
            current = codomain.apply(Value::var(Lvl(level)));
            level += 1;
        }
        Ok(Some((labels, fields)))
    }

    /// Кратность и представление `n`-го связывания типа.
    ///
    /// Ровно то же, что считает машина: `None` значит «не стёрто», потому что
    /// связывания на этом месте синтаксически не видно.
    fn binder_at(
        &mut self,
        ty: &Term,
        at: usize,
        dicts: &Dicts,
    ) -> Result<Option<(Mult, Repr)>, LowerError> {
        let depth = u32::try_from(at).unwrap_or(u32::MAX);
        let Some(Term::Pi(binder, _, domain, _, _)) = after(ty, at) else {
            return Ok(None);
        };
        let (mult, domain) = (binder.mult, domain.clone());
        Ok(Some((mult, self.repr_of(&domain, depth, dicts)?)))
    }

    /// Представление ответа после `taken` снятых связываний.
    ///
    /// Снято меньше, чем стрелок в типе, - ответ функция, то есть указатель.
    fn result_repr(&mut self, ty: &Term, taken: usize, dicts: &Dicts) -> Result<Repr, LowerError> {
        let depth = u32::try_from(taken).unwrap_or(u32::MAX);
        let Some(result) = after(ty, taken).cloned() else {
            return Ok(Repr::Boxed);
        };
        self.repr_of(&result, depth, dicts)
    }

    /// Факты о связываниях типа: телескоп до результата.
    ///
    /// Словарей здесь нет: телескоп этот принадлежит конструктору, а дескриптор
    /// приходит имплиситом **функции** (§4.11). Элемент-переменная в поле
    /// конструктора поэтому указательный.
    fn binders_of(&mut self, ty: &Term) -> Result<Vec<Fact>, LowerError> {
        let empty = Dicts::new();
        let mut facts = Vec::new();
        let mut current = ty;
        let mut at = 0u32;
        while let Term::Pi(binder, _, domain, _, codomain) = current {
            let repr = slotted(self.repr_of(domain, at, &empty)?);
            facts.push(Fact::declared(binder.mult).shaped(repr));
            at += 1;
            current = codomain;
        }
        Ok(facts)
    }
}

/// Разворачивает **применённое** имя: класс, сигнатуру модуля, алиас с
/// параметрами.
///
/// Отдельно от [`unaliased`], потому что цена разная. Там разворот - чтение
/// тела по имени; здесь он требует подстановки, то есть счёта: `class Functor
/// f where map : …` объявляет `Functor : (Type -> Type) -> Type` с телом
/// `\f -> { map : … }`, и увидеть запись можно только сведя применение.
///
/// Нужно ровно ради формы записи (§4.2): словарь класса и значение модуля -
/// записи в ядре, и без разворота проекция метода не знала бы номера слота.
/// Считает то же ядро, которым считают все три вычислителя.
fn unfolded(signature: &Signature, ty: &Term, depth: u32) -> Term {
    let mut current = ty.clone();
    for _ in 0..ALIASES {
        let (head, arguments) = spine(&current);
        let Term::Const(name, ..) = head else {
            return current;
        };
        let Some(definition) = signature.lookup(name) else {
            return current;
        };
        if !matches!(definition.kind, DefinitionKind::Regular) || !universal(&definition.ty) {
            return current;
        }
        let Some(body) = definition.body.as_ref() else {
            return current;
        };
        let mut applied = body.clone();
        for argument in arguments {
            applied = Term::App(Rc::new(applied), Rc::new(argument.clone()));
        }
        current = normalized(&applied, depth);
    }
    current
}

/// Оканчивается ли тип универсумом - то есть объявляет ли имя тип.
fn universal(ty: &Term) -> bool {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    matches!(current, Term::Universe(_))
}

/// Разворачивает цепочку синонимов до имени, у которого тела нет.
fn unaliased<'a>(signature: &'a Signature, ty: &'a Term) -> &'a Term {
    let mut current = ty;
    for _ in 0..ALIASES {
        // Ассоциированный тип модуля: `S.Block` после подстановки записи
        // модуля - проекция из известного значения (§10 вопрос 163). Поле
        // берётся из тела-записи и разворачивается дальше тем же циклом.
        // Запечатанное остаётся собственной головой: δ снаружи `:>` запрещён
        // и здесь.
        if let Term::Project(record, label) = current {
            let Term::Const(name, ..) = &**record else {
                return current;
            };
            let Some(definition) = signature.lookup(name) else {
                return current;
            };
            if definition.opaque {
                return current;
            }
            let Some(Term::Object(fields)) = definition.body.as_ref() else {
                return current;
            };
            let Some((_, found)) = fields.iter().find(|(it, _)| it == label) else {
                return current;
            };
            current = found;
            continue;
        }
        let Term::Const(name, ..) = current else {
            return current;
        };
        let Some(definition) = signature.lookup(name) else {
            return current;
        };
        if !matches!(definition.kind, DefinitionKind::Regular)
            || !matches!(definition.ty, Term::Universe(_))
        {
            return current;
        }
        let Some(body) = definition.body.as_ref() else {
            return current;
        };
        current = body;
    }
    current
}

/// Ближайшее сверху кратное `align`. То же правило, что в типовой стороне.
fn aligned(offset: u32, align: u32) -> u32 {
    offset.next_multiple_of(align.max(1))
}

/// Плоская укладка записи из примитивных полей (§4.11).
///
/// «Укладка последовательная, выравнивание по максимальному `align` полей» -
/// правило дословно, и числа отсюда обязаны совпасть с теми, что выводит
/// типовая сторона (`adamas-elab/src/flat.rs`). Совпадение стоит теста
/// (`tests/packed.rs`), потому что запись числа здесь вторая: `adamas-codegen`
/// на элаборацию не смотрит.
///
/// Названная граница: поля только примитивные. Вложенный агрегат §4.11
/// укладывает тем же правилом, но проекция сквозь него - путь, а не метка, и
/// путей у этого среза нет.
fn packing_of(labels: &[String], fields: &[PrimTy], packings: &[Packing]) -> Packing {
    let slotted: Vec<SlotTy> = fields.iter().map(|ty| SlotTy::Prim(*ty)).collect();
    packing_of_slots(labels, &slotted, packings)
}

/// То же для полей любого плоского сорта - вложенный агрегат в том числе.
fn packing_of_slots(labels: &[String], fields: &[SlotTy], packings: &[Packing]) -> Packing {
    let (slots, size, align) = sequential(fields, 0, packings);
    Packing {
        tag: 0,
        variants: vec![Variant {
            ctor: None,
            labels: labels.to_vec(),
            slots,
        }],
        size: aligned(size, align),
        align,
    }
}

/// Поля подряд от смещения `base`: слоты, конец и выравнивание.
fn sequential(fields: &[SlotTy], base: u32, packings: &[Packing]) -> (Vec<PackSlot>, u32, u32) {
    let mut slots = Vec::with_capacity(fields.len());
    let mut size = base;
    let mut align = 1u32;
    for ty in fields {
        let (width, at) = (ty.width(packings), ty.align(packings));
        let offset = aligned(size, at);
        slots.push(PackSlot { offset, ty: *ty });
        size = offset.saturating_add(width);
        align = align.max(at);
    }
    (slots, size, align)
}

/// Ширина и граница тега на `count` конструкторов (§4.11).
///
/// Один конструктор тега не требует - различать нечего, и `data` с ним
/// укладывается как запись. Ступени по степеням двойки - то же правило, что у
/// типовой стороны (`adamas-elab/src/flat.rs`), и совпадение чисел стоит
/// теста, а не обещания.
const fn tag_of(count: usize) -> (u32, u32) {
    match count {
        0 | 1 => (0, 1),
        2..=256 => (1, 1),
        257..=65536 => (2, 2),
        _ => (4, 4),
    }
}

/// Плотная укладка семейства: тег плюс payload размера максимума (§4.11).
///
/// Вариант на конструктор, поля каждого - подряд от общей границы payload'а;
/// сам payload начинается за тегом, выровненный по максимальной границе
/// своих полей. `Option Int64` отсюда занимает 16 байт, а не 8, - названная
/// §4.11 цена.
fn family_packing_of(
    variants: &[(CtorId, Vec<String>, Vec<SlotTy>)],
    packings: &[Packing],
) -> Packing {
    let (tag_size, tag_align) = tag_of(variants.len());
    let payload_align = variants
        .iter()
        .flat_map(|(_, _, fields)| fields.iter().map(|ty| ty.align(packings)))
        .max()
        .unwrap_or(1);
    let base = aligned(tag_size, payload_align);
    let mut made = Vec::with_capacity(variants.len());
    let mut end = tag_size;
    for (ctor, labels, fields) in variants {
        let (slots, size, _) = sequential(fields, base, packings);
        end = end.max(size);
        made.push(Variant {
            ctor: Some(*ctor),
            labels: labels.clone(),
            slots,
        });
    }
    let align = tag_align.max(payload_align);
    Packing {
        tag: tag_size,
        variants: made,
        size: aligned(end, align),
        align,
    }
}

/// Ссылается ли представление семейства на само себя (§4.11).
///
/// Свойство **объявления**, а не применения: §4.11 называет не плоским `List`
/// как таковой, а не `List Nat` отдельно от `List Bit`, и ровно поэтому
/// `Box (Box Int8)` плоский - имя повторяется применением, а не объявлением.
/// Косвенная рекурсия ловится достижимостью по всем именам в полях - через
/// соседа, синоним, запись; обход конечен, потому что имён в сигнатуре
/// конечное число.
///
/// Зеркало типовой стороны (`adamas-elab/src/flat.rs`, `recursive`): понижение
/// элаборацию не читает, и это вторая запись правила - цена шва, оплаченная
/// тестом на совпадение укладок.
fn recursive(signature: &Signature, of: &Name) -> bool {
    let mut seen: Vec<Name> = Vec::new();
    let mut queue = mentioned(signature, of);
    while let Some(name) = queue.pop() {
        if name == *of {
            return true;
        }
        if seen.contains(&name) {
            continue;
        }
        queue.extend(mentioned(signature, &name));
        seen.push(name);
    }
    false
}

/// Имена, стоящие в представлении определения.
///
/// У семейства это поля конструкторов, у синонима и записи - тело. Стёртые
/// связывания не считаются: индекс семейства в рантайме отсутствует (§3.3), а
/// речь о представлении.
fn mentioned(signature: &Signature, name: &Name) -> Vec<Name> {
    let mut found = Vec::new();
    let Some(definition) = signature.lookup(name) else {
        return found;
    };
    if definition.data_shape().is_some() {
        for constructor in signature.constructors(name).unwrap_or_default() {
            let Some(declared) = signature.lookup(constructor) else {
                continue;
            };
            let mut current = &declared.ty;
            while let Term::Pi(binder, _, domain, _, codomain) = current {
                if binder.mult != Mult::Zero {
                    constants(domain, &mut found);
                }
                current = codomain;
            }
            // Заключение конструктора не читается: оно называет само
            // семейство, и всякое семейство оказалось бы рекурсивным.
        }
    } else if let Some(body) = &definition.body {
        constants(body, &mut found);
    }
    found
}

/// Имена определений, стоящие в терме.
fn constants(term: &Term, into: &mut Vec<Name>) {
    match term {
        Term::Const(name, ..) => into.push(Rc::clone(name)),
        Term::Var(_)
        | Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Prim(_)
        | Term::Meta(_) => {}
        Term::Record(fields) | Term::Row(fields) => {
            for field in fields.iter() {
                constants(&field.ty, into);
            }
            if let Some(tail) = &fields.tail {
                constants(tail, into);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                constants(value, into);
            }
        }
        Term::With(base, fields) => {
            constants(base, into);
            for (_, value) in fields.iter() {
                constants(value, into);
            }
        }
        Term::Project(record, _) => constants(record, into),
        Term::Lam(_, _, body) => constants(body, into),
        Term::App(callee, argument) => {
            constants(callee, into);
            constants(argument, into);
        }
        Term::Pi(_, _, domain, row, codomain) => {
            constants(domain, into);
            constants(codomain, into);
            for label in row.labels() {
                for argument in &label.arguments {
                    constants(argument, into);
                }
            }
        }
        Term::Let(_, _, ty, value, body) => {
            constants(ty, into);
            constants(value, into);
            constants(body, into);
        }
        Term::Case(case) => {
            constants(&case.scrutinee, into);
            constants(&case.motive, into);
            for branch in &case.branches {
                constants(&branch.body, into);
            }
        }
    }
}

/// Словари `Flat` телескопа: какое связывание о каком типе говорит.
///
/// Связывание `i` описывает тип, стоящий на уровне `i - 1 - d`, где `d` -
/// индекс переменной внутри домена `Flat #d`. Номера связываний те же, что
/// раздаёт [`Lowerer::peeled`], - позиция в телескопе.
fn dicts_of(signature: &Signature, ty: &Term) -> Dicts {
    let mut found = Dicts::new();
    let mut current = ty;
    let mut at = 0u32;
    while let Term::Pi(binder, _, domain, _, codomain) = current {
        if binder.mult != Mult::Zero {
            let (head, arguments) = spine(unaliased(signature, domain));
            if let (Term::Const(name, ..), [Term::Var(Index(index))]) = (head, arguments.as_slice())
            {
                if &**name == FLAT {
                    if let Some(level) = at.checked_sub(index + 1) {
                        found.insert(level, LocalId(at));
                    }
                }
            }
        }
        at += 1;
        current = codomain;
    }
    found
}

/// Индексы, уходящие за `depth`, приведённые к внешнему счёту.
///
/// Обход идёт по позициям, где значение доживает до исполнения: типы, мотив
/// разбора и телескопы пропускаются - переменную оттуда захватывать незачем,
/// а понижение туда не заходит вовсе.
fn escaping(term: &Term, depth: u32, out: &mut BTreeSet<u32>) {
    match term {
        Term::Var(Index(index)) => {
            if *index >= depth {
                out.insert(index - depth);
            }
        }
        Term::Lam(_, _, body) => escaping(body, depth + 1, out),
        Term::App(callee, argument) => {
            escaping(callee, depth, out);
            escaping(argument, depth, out);
        }
        Term::Let(_, _, _, value, body) => {
            escaping(value, depth, out);
            escaping(body, depth + 1, out);
        }
        Term::Case(case) => {
            escaping(&case.scrutinee, depth, out);
            for branch in &case.branches {
                escaping(&branch.body, depth, out);
            }
        }
        _ => {}
    }
}
