//! Ошибка проверки типов: что не сошлось, где именно и в каком контексте.
//!
//! Форма принята §10 вопросом 49а. Ошибка несёт **значения**, а не готовую
//! строку: рендеринг живёт вне ядра, а здесь остаётся аварийный принтер на
//! индексах де Брёйна ([`Term`] реализует `Display`), нужный снапшотам уровня
//! ядра.
//!
//! # Три части
//!
//! - [`ErrorKind`] - что именно не сошлось. Термы в нём прочитаны обратно и
//!   зонканы в точке возбуждения: `Value` тащит замыкания с окружениями и
//!   границу не переживает, а незонкнутая дырка протухает вместе с `base`
//!   хранилища (§10 вопрос 51).
//! - [`TypeError::context`] - локальный телескоп точки отказа. Это та часть
//!   окружения, у которой нет другого дома: `check` спустился под связывания,
//!   которых у вызывающего никогда не было, и восстановить их снаружи нечем.
//!   Сигнатура, наоборот, не копируется - она у вызывающего по построению.
//! - [`TypeError::route`] - путь от входа до места отказа, кадрами. Кадры
//!   укладываются **на раскрутке**: каждая рекурсивная точка вызова, получив
//!   `Err`, дописывает свою роль. На успешном пути это стоит ноль, а кадр
//!   точен, потому что свою роль знает только сама точка вызова.
//!
//! # Почему маршрут, а не спаны
//!
//! Спаны на узлах `Term` отвергнуты: помимо веса на горячем пути `NbE`,
//! идентичность узла не переживает нормализацию. Маршрут строится заново в
//! момент отказа и переживать ничего не обязан. Как он ложится на исходник -
//! §10 вопрос 49б; отвечает на это элаборация, проходя тот же маршрут по
//! своему дереву.
//!
//! # Цена названа
//!
//! Форма рассчитана на редкость отказа: обратное чтение и сбор телескопа стоят
//! дорого и на успешном пути не выполняются вовсе. Фаза 3 сделает отказ
//! управляющим потоком (перебор кандидатов инстанса), и там эта цена станет
//! неприемлемой - §10 вопрос 52 записан ровно про эту границу.

use std::fmt;
use std::rc::Rc;

use crate::ctx::Ctx;
use crate::level::{Level, LevelMeta};
use crate::meta::Metas;
use crate::mult::Mult;
use crate::term::{Index, Name, Term};

/// Row в сообщении: пустая печатается `{}`, прочие - без хвостового пробела,
/// который [`crate::row::Row`] ставит для позиции перед типом.
fn shown(row: &crate::row::Row<crate::term::Term>) -> String {
    if row.is_empty() {
        return "{}".to_owned();
    }
    row.to_string().trim_end().to_owned()
}

/// Что именно не сошлось.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ErrorKind {
    /// Индекс не адресует ни одно связывание - терм незамкнут.
    #[error("{}", adamas_l10n::tr!("core-unbound-index", index = .index.0))]
    UnboundIndex {
        /// Сам индекс.
        index: Index,
    },

    /// В позиции типа оказался терм, тип которого не универсум.
    #[error("{}", adamas_l10n::tr!("core-not-a-type", term = .term, ty = .ty))]
    NotAType {
        /// Терм в позиции типа.
        term: Term,
        /// Его тип.
        ty: Term,
    },

    /// Применение чего-то, что не является функцией.
    #[error("{}", adamas_l10n::tr!("core-not-a-function", ty = .ty))]
    NotAFunction {
        /// Тип того, что применяли.
        ty: Term,
    },

    /// Тип не совпал с ожидаемым.
    #[error("{}", adamas_l10n::tr!("core-mismatch", expected = .expected, found = .found))]
    Mismatch {
        /// Тип, которого требовал контекст.
        expected: Term,
        /// Тип, который получился.
        found: Term,
    },

    /// Кратность лямбды разошлась с кратностью `Pi`, под который её проверяют.
    #[error("{}", adamas_l10n::tr!("core-lambda-multiplicity", found = .found, expected = .expected))]
    LambdaMultiplicity {
        /// Кратность из типа.
        expected: Mult,
        /// Кратность, написанная на лямбде.
        found: Mult,
    },

    /// Переменная использована чаще, чем разрешает её кратность.
    #[error("{}", adamas_l10n::tr!("core-usage-violation", name = .name, declared = .declared, actual = .actual))]
    UsageViolation {
        /// Имя связывания.
        name: Name,
        /// Разрешённая кратность (уже с учётом кратности суждения).
        declared: Mult,
        /// Фактическое использование.
        actual: Mult,
    },

    /// Тип терма нельзя синтезировать - нужна проверка против известного.
    #[error("{}", adamas_l10n::tr!("core-cannot-infer", term = .term))]
    CannotInfer {
        /// Проблемный терм.
        term: Term,
    },

    /// Ссылка на определение, которого нет в сигнатуре.
    #[error("{}", adamas_l10n::tr!("core-unknown-constant", name = .name))]
    UnknownConstant {
        /// Имя.
        name: Name,
    },

    /// Число аргументов уровня не совпало с арностью определения.
    #[error("{}", adamas_l10n::tr!("core-level-arity", name = .name, expected = .expected, found = .found))]
    LevelArity {
        /// Имя определения.
        name: Name,
        /// Объявленная арность.
        expected: u32,
        /// Сколько аргументов передано.
        found: u32,
    },

    /// Стёртое определение использовано в рантайм-позиции.
    #[error("{}", adamas_l10n::tr!("core-erased-constant", name = .name))]
    ErasedConstant {
        /// Имя определения.
        name: Name,
    },

    /// Факт ограничения не доказан ни вычислением, ни гипотезой контекста
    /// (§3.7). Телескоп отказа - те самые гипотезы, среди которых искали.
    #[error("{}", adamas_l10n::tr!("core-unproven", claim = .claim))]
    Unproven {
        /// Утверждение факта: `d /= 0` из `{d /= 0} =>`.
        claim: Term,
    },

    /// Нетотальное определение использовано в стёртом фрагменте.
    #[error("{}", adamas_l10n::tr!("core-partial-constant", name = .name))]
    PartialConstant {
        /// Имя определения.
        name: Name,
    },

    /// Имя уже занято.
    #[error("{}", adamas_l10n::tr!("core-duplicate-definition", name = .name))]
    DuplicateDefinition {
        /// Имя.
        name: Name,
    },

    /// Кратность `1` у определения верхнего уровня.
    #[error("{}", adamas_l10n::tr!("core-linear-definition", name = .name))]
    LinearDefinition {
        /// Имя.
        name: Name,
    },

    /// Отложенное ограничение на уровнях так и не сошлось.
    ///
    /// Откладываются те, что не решаются **сейчас**: `max ?a ?b ~ ?a` ждёт,
    /// пока соседние ограничения определят `?b`. Дошедшее сюда не определилось
    /// ничем, и выбирать за автора нечего - решений у него несколько.
    #[error("{}", adamas_l10n::tr!("core-unsettled-level", left = .left, right = .right))]
    UnsettledLevel {
        /// Левая сторона отложенного ограничения.
        left: crate::level::Level,
        /// Правая.
        right: crate::level::Level,
    },

    /// Отложенное ограничение на термах не сошлось к границе объявления.
    ///
    /// Обе стороны стояли дырками, поэтому сравнение было отложено (§10
    /// вопрос 91). К границе объявления соседние ограничения уже решены, и
    /// не сошедшееся здесь не сойдётся никогда.
    #[error("{}", adamas_l10n::tr!("core-unsettled-term", left = .left, right = .right))]
    UnsettledTerm {
        /// Левая часть.
        left: crate::term::Term,
        /// Правая часть.
        right: crate::term::Term,
    },

    /// После проверки остался неразрешённый уровень.
    #[error("{}", adamas_l10n::tr!("core-ambiguous-level", meta = .meta.0))]
    AmbiguousLevel {
        /// Метапеременная, оставшаяся без решения.
        meta: crate::level::LevelMeta,
    },

    /// После проверки осталась нерешённая дырка терма.
    ///
    /// Вывод её не заполнил, и заполнять больше нечему: ничто в оставшейся
    /// программе на неё не сошлётся. Обобщать её в параметр, в отличие от
    /// уровневой, нечем - аргумент терма пишется или выводится в месте
    /// использования, а не поднимается в сигнатуру.
    #[error("{}", ambiguous_term(*.meta, .owner.as_ref()))]
    AmbiguousTerm {
        /// Метапеременная, оставшаяся без решения.
        meta: crate::term::TermMeta,
        /// Чей это неявный аргумент, если дырка стоит аргументом имени.
        /// Номер дырки автору не говорит ничего, а имя - где её искать
        /// (§10 вопрос 217).
        owner: Option<Name>,
    },

    /// В определении, уходящем в сигнатуру, осталась дырка row.
    ///
    /// Третий сорт рядом с уровнем и термом, и довод тот же: хранилище живёт
    /// прогон элаборации, определение - всю программу. Пропущенный, этот отказ
    /// оборачивался не неверной программой, а **падением компилятора**:
    /// дырка уезжала в сохранённый тип живой и всплывала после `release`, где
    /// зонканье бралось за неё уже вне живого диапазона.
    #[error("{}", adamas_l10n::tr!("core-unsolved-definition-row", name = .name, meta = .meta.0))]
    UnsolvedDefinitionRow {
        /// Имя определения.
        name: Name,
        /// Метапеременная, оставшаяся без решения.
        meta: crate::row::RowMeta,
    },

    /// В определении, уходящем в сигнатуру, осталась дырка уровня.
    #[error("{}", adamas_l10n::tr!("core-unsolved-definition-level", name = .name, meta = .meta.0))]
    UnsolvedDefinitionLevel {
        /// Имя определения.
        name: Name,
        /// Метапеременная, оставшаяся без решения.
        meta: crate::level::LevelMeta,
    },

    /// Тип-формер не заканчивается универсумом.
    #[error("{}", adamas_l10n::tr!("core-not-a-data-sort", name = .name, found = .found))]
    NotADataSort {
        /// Имя типа.
        name: Name,
        /// Что оказалось на месте универсума.
        found: Term,
    },

    /// Тип-формер объявлен с большим числом параметров, чем у него связываний.
    #[error("{}", adamas_l10n::tr!("core-data-parameters", name = .name, expected = .expected, found = .found))]
    DataParameters {
        /// Имя типа.
        name: Name,
        /// Сколько параметров объявлено.
        expected: u32,
        /// Сколько связываний есть на самом деле.
        found: u32,
    },

    /// Конструктор объявлен для имени, которое не индуктивный тип.
    #[error("{}", adamas_l10n::tr!("core-not-a-data-type", name = .name))]
    NotADataType {
        /// Имя.
        name: Name,
    },

    /// Конструктор не повторяет телескоп параметров своего типа.
    #[error("{}", adamas_l10n::tr!("core-constructor-parameter", name = .name, data = .data, index = .index))]
    ConstructorParameter {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
        /// Номер параметра, на котором разошлось.
        index: u32,
    },

    /// Конструктор возвращает не тот тип, которому объявлен.
    #[error("{}", adamas_l10n::tr!("core-constructor-result", name = .name, data = .data, found = .found))]
    ConstructorResult {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
        /// Что оказалось результатом.
        found: Term,
    },

    /// Формер эффекта не заканчивается сортом `Effect` (§3.4).
    #[error("{}", adamas_l10n::tr!("core-not-an-effect-sort", name = .name, found = .found))]
    NotAnEffectSort {
        /// Имя эффекта.
        name: Name,
        /// Что оказалось на месте сорта.
        found: Term,
    },

    /// Операция не повторяет телескоп параметров эффекта дословно.
    #[error("{}", adamas_l10n::tr!("core-operation-parameter", name = .name, effect = .effect, index = .index))]
    OperationParameter {
        /// Имя операции.
        name: Name,
        /// Имя эффекта.
        effect: Name,
        /// Номер параметра, на котором разошлось.
        index: u32,
    },

    /// Операция производит не ровно объявляемую метку (§3.4).
    #[error("{}", adamas_l10n::tr!("core-operation-row", name = .name, effect = .effect, found = shown(.found)))]
    OperationRow {
        /// Имя операции.
        name: Name,
        /// Имя эффекта.
        effect: Name,
        /// Что оказалось её row.
        found: crate::row::Row<crate::term::Term>,
    },

    /// Row вызываемого не гасится окружающей (§3.4).
    #[error("{}", adamas_l10n::tr!("core-undischarged", wanted = shown(.wanted), ambient = shown(.ambient)))]
    Undischarged {
        /// Row вызываемого.
        wanted: crate::row::Row<crate::term::Term>,
        /// Окружающая row.
        ambient: crate::row::Row<crate::term::Term>,
    },

    /// Нарушена строгая позитивность.

    #[error("{}", adamas_l10n::tr!("core-not-strictly-positive", name = .name, data = .data))]
    NotStrictlyPositive {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
    },

    /// Рекурсивное вхождение меняет параметры.
    ///
    /// Правило считается той же проверкой, что и позитивность, но говорить о
    /// нём обязано **своё** сообщение. Про отрицательную позицию тут читать
    /// нечего: стрелки в поле может не быть вовсе, и отправлять читателя
    /// искать её - отправлять не туда. Различает эти два правила только текст:
    /// пока он был общим, сломать единообразие можно было незаметно для
    /// корпуса.
    #[error("{}", adamas_l10n::tr!("core-non-uniform-parameter", name = .name, data = .data))]
    NonUniformParameter {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
    },

    /// Поле конструктора живёт выше универсума самого типа.
    #[error("{}", adamas_l10n::tr!("core-constructor-universe", name = .name, field = .field, sort = .sort))]
    ConstructorUniverse {
        /// Имя конструктора.
        name: Name,
        /// Универсум поля.
        field: Level,
        /// Универсум типа.
        sort: Level,
    },

    /// Два поля записи с одним именем.
    #[error("{}", adamas_l10n::tr!("core-duplicate-field", name = .name))]
    DuplicateField {
        /// Имя поля.
        name: Name,
    },

    /// У записи с хвостом поле, чей тип зависит от предыдущего.
    ///
    /// §4.2: зависимость закрывает запись. Хвост обещает поля, которых
    /// объявление не знает, а тип `b : a` осмыслен только при известном `a`:
    /// расширение подставило бы чужое `a`, оставив прежнее `b`, и из этого
    /// строится житель любого типа.
    #[error("{}", adamas_l10n::tr!("core-open-dependent-record", name = .name))]
    OpenDependentRecord {
        /// Имя зависимого поля.
        name: Name,
    },

    /// У записи не столько полей, сколько у её типа.
    #[error("{}", adamas_l10n::tr!("core-record-fields", found = .found, expected = .expected))]
    RecordFields {
        /// Сколько полей у типа.
        expected: usize,
        /// Сколько написано.
        found: usize,
    },

    /// Хвост записи - не ряд.
    #[error("{}", adamas_l10n::tr!("core-not-a-row", ty = .ty))]
    NotARow {
        /// Тип того, что написано хвостом.
        ty: Term,
    },

    /// Проекция не из записи.
    #[error("{}", adamas_l10n::tr!("core-not-a-record", ty = .ty))]
    NotARecord {
        /// Тип того, из чего проецировали.
        ty: Term,
    },

    /// Переопределение полей у закрытой записи.
    ///
    /// `With` не пересчитывает зависимость между полями, поэтому база обязана
    /// быть открытой: у открытой записи зависимости нет (§4.2). Закрытая
    /// обновляется пересборкой - у неё поля перечислимы.
    #[error("{}", adamas_l10n::tr!("core-closed-with", ty = .ty))]
    ClosedWith {
        /// Тип базы.
        ty: Term,
    },

    /// У записи нет такого поля.
    #[error("{}", adamas_l10n::tr!("core-no-such-field", ty = .ty, name = .name))]
    NoSuchField {
        /// Имя поля.
        name: Name,
        /// Тип записи.
        ty: Term,
    },

    /// Стёртое поле в рантайм-позиции.
    ///
    /// То же правило, что у стёртой переменной: значения у поля нет, и вынуть
    /// его нечем.
    #[error("{}", adamas_l10n::tr!("core-erased-field", name = .name))]
    ErasedField {
        /// Имя поля.
        name: Name,
    },

    /// Разбирается значение, тип которого не то индуктивное семейство.
    #[error("{}", adamas_l10n::tr!("core-not-a-data-value", data = .data, ty = .ty))]
    NotADataValue {
        /// Имя типа из разбора.
        data: Name,
        /// Тип разбираемого значения.
        ty: Term,
    },

    /// Разбор объявлен потребляющим разбираемое нуль раз.
    ///
    /// Кратность `0` означает «стёрто», а ветвь выбирается по разбираемому в
    /// рантайме: `case⁰` сделал бы стирание не стиранием.
    #[error("{}", adamas_l10n::tr!("core-erased-scrutinee", data = .data))]
    ErasedScrutinee {
        /// Имя типа.
        data: Name,
    },

    /// Разбор записи в поля, который ядро не принимает (§10 вопрос 231):
    /// стёртый разбор, открытая запись, поля не те или с собственными
    /// параметрами.
    #[error("{}", adamas_l10n::tr!("core-split-shape", why = adamas_l10n::message(.why, &[])))]
    SplitShape {
        /// Что не так.
        why: &'static str,
    },

    /// Число параметров в разборе разошлось с объявлением типа.
    #[error("{}", adamas_l10n::tr!("core-case-parameters", data = .data, found = .found, expected = .expected))]
    CaseParameters {
        /// Имя типа.
        data: Name,
        /// Сколько параметров у типа.
        expected: u32,
        /// Сколько записано в разборе.
        found: u32,
    },

    /// Конструктор остался без ветви.
    #[error("{}", adamas_l10n::tr!("core-non-exhaustive", data = .data, constructor = .constructor))]
    NonExhaustive {
        /// Имя типа.
        data: Name,
        /// Непокрытый конструктор.
        constructor: Name,
    },

    /// Ветвь для того, чего разбирать не требуется.
    #[error("{}", adamas_l10n::tr!("core-redundant-branch", data = .data, constructor = .constructor))]
    RedundantBranch {
        /// Имя типа.
        data: Name,
        /// Конструктор ветви.
        constructor: Name,
    },

    /// Ветви идут не в порядке объявления конструкторов.
    #[error("{}", adamas_l10n::tr!("core-branch-order", data = .data, expected = .expected, found = .found))]
    BranchOrder {
        /// Имя типа.
        data: Name,
        /// Конструктор, ожидавшийся на этом месте.
        expected: Name,
        /// Конструктор, который там оказался.
        found: Name,
    },

    /// Определение ссылается на параметр уровня, которого у него нет.
    #[error("{}", adamas_l10n::tr!("core-level-var-out-of-scope", name = .name, var = .var, arity = .arity))]
    LevelVarOutOfScope {
        /// Имя определения.
        name: Name,
        /// Индекс переменной.
        var: u32,
        /// Объявленная арность.
        arity: u32,
    },

    /// Выводимый аргумент не укладывается в тип своей дырки.
    ///
    /// Отдельно от [`ErrorKind::Mismatch`], потому что дырка доезжает до
    /// отказа **нерешённой** и печатается собой: `(?22) #0` вместо причины.
    /// Здесь названы обе стороны - чего дырка требует и что на её месте нужно.
    #[error("{}", adamas_l10n::tr!("core-hole-misfit", hole = .hole, wanted = .wanted))]
    HoleMisfit {
        /// Тип дырки - то, чем ограничено решение.
        hole: Term,
        /// Что на её месте требуется.
        wanted: Term,
    },

    /// Параметры кратности связаны между собой, а сигнатура связь не выражает.
    ///
    /// Тело проверяется тогда не при всех сочетаниях, и множество законных
    /// подстановок перестаёт быть произведением по параметрам - принять его
    /// значило бы обещать больше законных сочетаний, чем есть.
    ///
    /// Чаще всего связь и есть произведение: у композиции домен собственного
    /// аргумента равен `q · r`, и пишется он `(q * r z : a)` (§10 вопрос 41).
    /// Отказ поэтому подсказывает форму, а не только называет беду. Связь,
    /// произведением не являющуюся - скажем, сумму, - написать по-прежнему
    /// нечем.
    #[error("{}", adamas_l10n::tr!("core-mult-entangled", name = .name))]
    MultEntangled {
        /// Имя определения.
        name: Name,
    },
}

/// Части сообщения, отдаваемые печати на переименование: термы, уровни, дырки
/// уровня и row.
pub type MessageParts<'a> = (
    Vec<&'a mut Term>,
    Vec<&'a mut Level>,
    Vec<&'a mut LevelMeta>,
    Vec<&'a mut crate::row::Row<Term>>,
);

impl ErrorKind {
    /// Части, попадающие в текст сообщения: термы, уровни, дырки и row.
    ///
    /// Печать человеку живёт вне ядра (§9 Фаза 2): там переменные получают
    /// имена телескопа, а дырки - локальные номера. Список мест, куда это
    /// подставлять, стоит здесь, рядом с вариантами: разбор исчерпывающий,
    /// поэтому новый вариант не пройдёт мимо молча, оставшись в сообщении с
    /// индексами де Брёйна.
    ///
    /// Row - четвёртая часть, и она такая же: аргументы её меток суть термы,
    /// а хвост её - дырка. Без неё «эффекты `{State #1 | ?21}` не погашены»
    /// печаталось рядом с блоком «в контексте», где то же связывание названо
    /// именем.
    #[must_use]
    pub fn parts_mut(&mut self) -> MessageParts<'_> {
        let (mut terms, mut levels, mut metas, mut rows): (Vec<_>, Vec<_>, Vec<_>, Vec<_>) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        match self {
            Self::NotAType { term, ty } => terms.extend([term, ty]),
            Self::HoleMisfit { hole, wanted } => terms.extend([hole, wanted]),
            Self::Mismatch { expected, found } => terms.extend([expected, found]),
            Self::UnsettledTerm { left, right } => terms.extend([left, right]),
            Self::UnsettledLevel { left, right } => levels.extend([left, right]),
            Self::NotAFunction { ty }
            | Self::CannotInfer { term: ty }
            | Self::Unproven { claim: ty }
            | Self::NotADataSort { found: ty, .. }
            | Self::NotAnEffectSort { found: ty, .. }
            | Self::ConstructorResult { found: ty, .. }
            | Self::NotARow { ty }
            | Self::NotARecord { ty }
            | Self::ClosedWith { ty }
            | Self::NoSuchField { ty, .. }
            | Self::NotADataValue { ty, .. } => terms.push(ty),
            Self::ConstructorUniverse { field, sort, .. } => levels.extend([field, sort]),
            Self::AmbiguousLevel { meta } | Self::UnsolvedDefinitionLevel { meta, .. } => {
                metas.push(meta);
            }
            Self::Undischarged { wanted, ambient } => rows.extend([wanted, ambient]),
            // У этих row тоже есть, но телескопа у них нет: `OperationRow`
            // печатает написанный тип операции до всякого контекста, а
            // `UnsolvedDefinitionRow` - одну дырку по имени определения.
            Self::OperationRow { .. }
            | Self::UnsolvedDefinitionRow { .. }
            | Self::RecordFields { .. }
            | Self::DuplicateField { .. }
            | Self::OpenDependentRecord { .. }
            | Self::ErasedField { .. }
            | Self::UnboundIndex { .. }
            | Self::LambdaMultiplicity { .. }
            | Self::UsageViolation { .. }
            | Self::UnknownConstant { .. }
            | Self::LevelArity { .. }
            | Self::ErasedConstant { .. }
            | Self::PartialConstant { .. }
            | Self::DuplicateDefinition { .. }
            | Self::LinearDefinition { .. }
            | Self::DataParameters { .. }
            | Self::NotADataType { .. }
            | Self::ConstructorParameter { .. }
            | Self::OperationParameter { .. }
            | Self::NotStrictlyPositive { .. }
            | Self::NonUniformParameter { .. }
            | Self::ErasedScrutinee { .. }
            | Self::SplitShape { .. }
            | Self::AmbiguousTerm { .. }
            | Self::CaseParameters { .. }
            | Self::NonExhaustive { .. }
            | Self::RedundantBranch { .. }
            | Self::BranchOrder { .. }
            | Self::LevelVarOutOfScope { .. }
            | Self::MultEntangled { .. } => {}
        }
        (terms, levels, metas, rows)
    }
}

/// Связывание в телескопе точки отказа.
///
/// Тип - терм, а не значение: [`crate::value::Value`] тащит замыкания с
/// окружениями и границу отказа не переживает.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// Имя, под которым связывание введено.
    ///
    /// §10 вопрос 49а оставлял этот слот пустым, потому что «имена - это (б)».
    /// Слот заполняется: имя уже лежит в [`Ctx`], и это то самое имя, которое
    /// туда положила элаборация. Открытым вопрос 49б от этого не перестаёт
    /// быть - он про **позицию** в исходнике, а не про имя.
    pub name: Name,
    /// Кратность, с которой связывание объявлено.
    pub mult: Mult,
    /// Тип.
    pub ty: Term,
}

/// Роль подтерма в объемлющем узле - один шаг маршрута.
///
/// Кадр называет **позицию**, а не узел: узел не переживает нормализацию, а
/// позиция - это то, что вызывающий может пройти по своему дереву.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Frame {
    /// Функция в применении.
    Callee,
    /// Аргумент применения.
    Argument,
    /// Домен `Pi`.
    Domain,
    /// Кодомен `Pi`.
    Codomain,
    /// Тело лямбды.
    Body,
    /// Тип связывания `let`.
    BindingType,
    /// Заявленный тип - тот, против которого проверяют.
    ///
    /// Единственный кадр, уводящий не в подтерм проверяемого терма: тип
    /// приходит отдельным термом, и без кадра маршрут в нём неотличим от
    /// маршрута в самом терме. Внутри рекурсии такого не бывает - там тип либо
    /// часть терма (`Pi`, `let`), либо построен самой проверкой.
    Stated,
    /// Значение связывания `let`.
    BindingValue,
    /// Тело `let`.
    BindingBody,
    /// Разбираемое значение.
    Scrutinee,
    /// Мотив разбора.
    Motive,
    /// Ветвь разбора по её номеру в порядке объявления конструкторов.
    Branch(u32),
    /// Тип члена группы по его номеру.
    MemberType(u32),
    /// Тело члена группы.
    MemberBody(u32),
    /// Тип конструктора по его номеру в объявлении.
    Constructor(u32),
}

impl fmt::Display for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use adamas_l10n::tr;
        f.write_str(&match self {
            Self::Callee => tr!("frame-callee"),
            Self::Argument => tr!("frame-argument"),
            Self::Domain => tr!("frame-domain"),
            Self::Codomain => tr!("frame-codomain"),
            Self::Body => tr!("frame-body"),
            Self::BindingType => tr!("frame-binding-type"),
            Self::Stated => tr!("frame-stated"),
            Self::BindingValue => tr!("frame-binding-value"),
            Self::BindingBody => tr!("frame-binding-body"),
            Self::Scrutinee => tr!("frame-scrutinee"),
            Self::Motive => tr!("frame-motive"),
            Self::Branch(index) => tr!("frame-branch", index = index),
            Self::MemberType(index) => tr!("frame-member-type", index = index),
            Self::MemberBody(index) => tr!("frame-member-body", index = index),
            Self::Constructor(index) => tr!("frame-constructor", index = index),
        })
    }
}

/// Отказ проверки типов.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{kind}")]
pub struct TypeError {
    /// Что не сошлось.
    pub kind: ErrorKind,
    /// Телескоп и маршрут. `None` - ни того, ни другого ещё нет.
    trace: Option<Box<Trace>>,
}

/// Телескоп точки отказа и маршрут до неё.
///
/// **За боксом.** `TypeError` возвращается из каждого рекурсивного вызова
/// проверки, и два вектора внутри - это 48 байт, которые успешный путь двигает
/// на каждом кадре, чтобы ни разу ими не воспользоваться. Отказ редок (см.
/// заголовок модуля), поэтому аллокация в нём дешевле веса на горячем пути.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Trace {
    /// Локальные связывания снаружи внутрь.
    context: Vec<Binding>,
    /// Кадры **изнутри наружу**: укладываются на раскрутке, поэтому первым
    /// лежит ближайший к месту отказа.
    route: Vec<Frame>,
}

impl TypeError {
    /// Телескоп точки отказа снаружи внутрь.
    ///
    /// Пуст, если отказ возбуждён там, где локального контекста нет вовсе, -
    /// например при объявлении определения.
    #[must_use]
    pub fn context(&self) -> &[Binding] {
        self.trace.as_ref().map_or(&[], |trace| &trace.context)
    }

    /// Кадры изнутри наружу - в том порядке, в каком они укладывались.
    #[must_use]
    pub fn route(&self) -> &[Frame] {
        self.trace.as_ref().map_or(&[], |trace| &trace.route)
    }

    /// Маршрут снаружи внутрь - в том порядке, в каком по нему идут.
    #[must_use]
    pub fn path(&self) -> impl DoubleEndedIterator<Item = Frame> + '_ {
        self.route().iter().rev().copied()
    }

    /// Отказ с телескопом, собранным снаружи проверки: поиск доказательства
    /// (§3.7) знает гипотезы по типу дырки, а не по [`Ctx`].
    #[must_use]
    pub fn within(kind: ErrorKind, context: Vec<Binding>) -> Self {
        Self {
            kind,
            trace: Some(Box::new(Trace {
                context,
                route: Vec::new(),
            })),
        }
    }

    /// Дописывает кадр. Зовётся на раскрутке, в точке рекурсивного вызова.
    #[must_use]
    pub fn in_frame(mut self, frame: Frame) -> Self {
        self.trace
            .get_or_insert_with(Box::default)
            .route
            .push(frame);
        self
    }
}

impl From<ErrorKind> for TypeError {
    fn from(kind: ErrorKind) -> Self {
        Self { kind, trace: None }
    }
}

/// Отказ с телескопом точки отказа.
///
/// Телескоп снимается здесь, а не на раскрутке: у вызывающего контекста этой
/// глубины уже нет, и восстановить его нечем. Обратное чтение и зонканье идут
/// тем же путём, что у термов внутри [`ErrorKind`], и по той же причине.
pub(crate) fn refuse(ctx: &Ctx<'_>, metas: &Metas, kind: ErrorKind) -> TypeError {
    // Спекулятивный проход отказ выбросит, и телескоп ему не нужен: сбор стоит
    // обхода локального контекста с обратным чтением каждого связывания, а
    // форма ошибки рассчитана на редкость отказа (§10 вопрос 52).
    if ctx.is_speculative() {
        return kind.into();
    }
    let context = telescope(ctx, metas);
    if context.is_empty() {
        return kind.into();
    }
    TypeError {
        kind,
        trace: Some(Box::new(Trace {
            context,
            route: Vec::new(),
        })),
    }
}

/// Локальные связывания снаружи внутрь.
fn telescope(ctx: &Ctx<'_>, metas: &Metas) -> Vec<Binding> {
    (0..ctx.size())
        .rev()
        .filter_map(|index| {
            let binding = ctx.lookup(Index(index))?;
            Some(Binding {
                name: Rc::clone(&binding.name),
                mult: binding.mult,
                ty: crate::check::read_back(ctx, metas, &binding.ty),
            })
        })
        .collect()
}

/// Текст отказа о невыведенном аргументе: по имени владельца, если он есть.
fn ambiguous_term(meta: crate::term::TermMeta, owner: Option<&Name>) -> String {
    match owner {
        Some(owner) => adamas_l10n::tr!(
            "core-ambiguous-term-owned",
            owner = crate::term::short(owner)
        ),
        None => adamas_l10n::tr!("core-ambiguous-term", meta = meta.0),
    }
}
