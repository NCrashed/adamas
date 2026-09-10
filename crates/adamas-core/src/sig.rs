//! Глобальный контекст: определения верхнего уровня.
//!
//! До этого модуля ядро умело только замкнутые термы сами по себе. Определения
//! дают две вещи, без которых Фаза 1 не заканчивается: universe polymorphism
//! (параметры уровня принадлежат определению, а не терму) и место, куда лягут
//! индуктивные типы - data-декларация тоже определение.
//!
//! # Единица объявления - группа
//!
//! Объявляется не определение, а **группа** ([`Group`]), одним вызовом
//! [`Signature::declare`] (§10 вопрос 50). Члены трёх видов - определение,
//! индуктивное семейство со своими конструкторами и метка эффекта со своими
//! операциями (§3.4); группа из одного члена и есть обычное определение. Промежуточных наблюдаемых состояний сигнатуры
//! нет: снаружи группа либо добавлена целиком, либо не добавлена вовсе.
//!
//! Проверка идёт в четыре фазы, и порядок в них существенный:
//!
//! - **(A)** типы членов - против сигнатуры **без** группы. Здесь ловится
//!   `f : f -> Nat`: тип, ссылающийся на определяемое, цикличен. Цена правила -
//!   §10 вопрос 64: сосед в типе члена по той же причине не пишется.
//!
//!   Исключение одно, и оно названо: **тип-формер семейства видит семейства,
//!   объявленные раньше него в той же группе**, поэтому `data Held : Tag ->
//!   Type` рядом с `data Tag` пишется. Порядок здесь не компромисс, а верное
//!   правило: kind'ы взаимно рекурсивными быть не могут - `data A : B -> Type`
//!   вместе с `data B : A -> Type` не обосновано, - и симметрии, которую
//!   порядок мог бы нарушить, у них нет. У значений она есть, и их типы
//!   вставляются после прохода, как и прежде.
//! - **(B1)** типы конструкторов и операций - против сигнатуры **с** типами
//!   членов.
//! - **(B2)** тела определений - с типами членов и с объявлениями
//!   конструкторов. Отсюда рекурсия. δ по членам открытой группы не работает
//!   по построению: их тела в сигнатуру ещё не попали, и разворачивать нечего.
//! - **(C)** проверки над **закрытой** группой: строгая позитивность, укладка
//!   полей в универсум, вердикт тотальности по совместному графу вызовов.
//!
//! **Позитивность живёт в C, а не в B**, и это не косметика: она смотрит
//! сквозь определения, а определение с непроверенным телом видит без тела - и
//! тогда **принимает** негативный конструктор вместо отказа. Направление
//! консервативности здесь противоположно всем прочим проверкам ядра.
//!
//! **B1 живёт раньше B2** по симметричной причине: тело члена вправе разбирать
//! по семейству соседа, а правилу `case` мало имён конструкторов - оно берёт у
//! каждого тип, чтобы построить тип ветви. Список же конструкторов полон ещё
//! раньше, с фазы A: имена известны из объявления, а пустой список означал бы
//! «семейство необитаемо» и принял бы `absurd` над обитаемым типом.
//!
//! # Порядок объявления и рекурсия
//!
//! Группа видит уже добавленные группы - и себя саму. Между группами порядок
//! строгий: `g` увидит `f`, только если объявлена позже. Это ordered scoping
//! §4.8, а взаимная рекурсия выражается членством в одной группе.
//!
//! Завершаемость δ-разворота ([`crate::conv`]) не следует из ацикличности. Её
//! держат две вещи: проверка структурной рекурсии ([`crate::total`]) и то, что
//! нетотальное определение не разворачивается вовсе.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::check::{
    Frame, TypeError, check_body, check_constructor_content, check_constructor_shape,
    check_declaration, check_operation_shape, data_sort, effect_sort, unsolved_in_definition,
    unsolved_term_in_definition,
};
use crate::error::ErrorKind;
use crate::eval::eval;
use crate::level::{Level, LevelMeta, LevelVar};
use crate::meta::{Generalization, Metas, zonk_term};
use crate::mult::Mult;
use crate::row::Row;
use crate::term::{Args, Name, Term};
use crate::value::{Env, Value};

/// Невыразимое имя элиминатора scope, держащего ресурс (§3.3).
///
/// Стоит здесь, а не у того, кто его объявляет, потому что читают его трое:
/// элаборация вставляет его в точке выхода из scope, машина видит по нему, что
/// вошла в scope (`adamas-interp/src/effect.rs`), понижение раскрывает его в
/// связывание ответа и вызов деструктора (`adamas-codegen/src/lower.rs`).
/// Расхождение в написании было бы тихим - тот же довод, каким имена §4.11
/// лежат в [`crate::prim`].
pub const CLOSING: &str = "#closing";

/// Чем определение является помимо "имя с типом и, может быть, телом".
///
/// Индуктивный тип и его конструкторы - это те же определения без тела, но
/// проверяются они строже и связаны друг с другом. Различать их обязана
/// элиминация: сводить `case` можно только по конструктору, а не по
/// произвольному постулату похожей формы.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionKind {
    /// Обычное определение или постулат.
    Regular,
    /// Тип-формер индуктивного типа.
    Data {
        /// Конструкторы в порядке объявления. Порядок задаёт порядок ветвей
        /// `case`.
        ///
        /// Список полон с момента, когда семейство стало видимым, включая
        /// фазу B собственной группы: имена берутся из объявления и проверкой
        /// не меняются, поэтому заполнять его позже нечего. Дописать в него
        /// потом нечем - и поэтому `absurd`, принятая разбором с нулём ветвей,
        /// не переживёт появления у `Void` конструктора: появиться ему негде.
        constructors: Vec<Name>,
        /// Сколько первых связываний тип-формера - параметры: одни и те же во
        /// всех вхождениях типа внутри конструктора. Остальные - индексы, они
        /// от конструктора к конструктору меняются.
        params: u32,
        /// Универсум, в котором живёт тип. Поля конструкторов обязаны
        /// укладываться в него.
        sort: Level,
    },
    /// Конструктор индуктивного типа.
    Constructor {
        /// Тип, которому конструктор принадлежит.
        data: Name,
    },
    /// Формер метки эффекта (§3.4).
    Effect {
        /// Операции в порядке объявления. Порядок задаёт порядок веток
        /// хендлера - тем же доводом, каким конструкторы задают порядок
        /// ветвей разбора.
        operations: Vec<Name>,
        /// Сколько связываний формера - параметры метки. Все: результат
        /// метки всегда `Effect`, индексов у неё не бывает.
        params: u32,
    },
    /// Операция эффекта.
    Operation {
        /// Эффект, которому операция принадлежит.
        effect: Name,
    },
}

/// Что фаза B2 узнала о теле: сам терм, носители его параметров и дозволенные
/// подстановки кратностей (§10 вопрос 41).
type CheckedBody = (Term, crate::check::Body);

/// Полукольцо целиком - все подстановки, которые перебирает фаза B2.
pub(crate) const ALL_MULTS: [Mult; 3] = [Mult::Zero, Mult::One, Mult::Many];

/// Определение верхнего уровня.
#[derive(Clone, Debug)]
pub struct Definition {
    /// Кратность: `0` - существует только на этапе проверки типов, `ω` -
    /// доступно в рантайме. `1` бессмысленна: она означала бы "использовать не
    /// более одного раза на всю программу", а такого учёта нет.
    pub mult: Mult,
    /// Сколько параметров уровня. Внутри `ty` и `body` они видны как
    /// [`crate::level::LevelVar`] с индексами `0..arity`.
    pub level_arity: u32,
    /// Сколько параметров row - вторая компонента арности (§10 вопрос 73).
    ///
    /// Внутри `ty` и `body` они видны как [`crate::row::RowVar`], и место
    /// использования подставляет вместо каждого целую row.
    pub row_arity: u32,
    /// Значения, дозволенные каждому параметру кратности (§10 вопрос 41).
    ///
    /// Длина - третья компонента арности; внутри `ty` и `body` параметры видны
    /// как [`crate::mult::MultVar`]. Множество, а не одно только число, потому
    /// что **не всякая подстановка законна**: `id x = x` не проверяется при
    /// `q = 0`, а дублирующее тело - при `q = 1`. Считается оно перебором на
    /// объявлении: полукольцо конечно, и подстановок ровно `3ⁿ`.
    pub mult_allowed: Rc<[Rc<[Mult]>]>,
    /// Носители при каждой дозволенной подстановке кратностей.
    ///
    /// [`Definition::carriers`] сводит их к худшему, и на полиморфном
    /// комбинаторе этого мало: `applyTo` алиасит своё значение при `q = ω` и
    /// не алиасит при `q = 1`, а место использования подставляет одно из двух
    /// и знает какое.
    pub graded_carriers: Rc<[crate::check::Graded]>,
    /// Тип. Замкнут по локальным переменным, открыт по параметрам уровня.
    pub ty: Term,
    /// Тело. `None` - постулат: тип есть, вычислять нечего.
    pub body: Option<Term>,
    /// Индуктивная роль, если она есть.
    pub kind: DefinitionKind,
    /// Завершается ли определение на всех входах ([`crate::total`]).
    ///
    /// Выводится, а не объявляется: `total` из §4.7 - атрибут поверхностного
    /// языка, требующий от ядра ответа, а не сообщающий его. Ответ нужен ядру
    /// в любом случае - от него зависят два правила, - поэтому вычисляется он
    /// всегда, а атрибут превращается в требование "ответ обязан быть да".
    ///
    /// Постулат тотален: разворачивать нечего, значит и расходиться нечему.
    pub total: bool,
    /// Запечатано ли определение: `module M :> Sig` (§3.5).
    ///
    /// Непрозрачность **булева**: скрыто тело целиком, снаружи не
    /// редуцируется ничего. Семантика `abstract` Agda и `opaque` Lean.
    /// Проверке типов тело по-прежнему известно - оно проверено при
    /// объявлении, - а вот сравнение его не разворачивает, и потому
    /// `M.T` снаружи есть абстрактный тип, а не своё представление.
    ///
    /// Переход к полупрозрачным сигнатурам (уравнения прямо в сигнатуре,
    /// §10 вопрос 46) булево значение не ломает: оно его частный случай.
    pub opaque: bool,
    /// Кратности носителей по позициям телескопа ([`crate::carrier`]).
    ///
    /// Выводятся из тела, как и [`Definition::total`], и по той же причине:
    /// правила владения (§3.3) - поверхностные, а ответ им нужен от ядра.
    /// Сверяет их с владеемым типом элаборация, ядро только считает.
    pub carriers: Rc<[Mult]>,
    /// Чем определение аллоцирует в куче Perceus ([`crate::alloc`]). `None` -
    /// ничем, и это вердикт для `@noalloc` (§5.1).
    ///
    /// Не булево, потому что диагностика §5.1 обязана назвать источник: «`f`
    /// аллоцирует» без имени конструктора или вызванного не говорит, что
    /// чинить. Считается на границе объявления, где дырки ещё живы, и потому
    /// хранится, а не пересчитывается по требованию.
    pub allocates: Option<crate::alloc::Source>,
}

impl Definition {
    /// Тип, инстанцированный аргументами уровня.
    #[must_use]
    pub fn instantiate_type(
        &self,
        levels: &[Level],
        rows: &[Row<Term>],
        mults: &[Mult],
    ) -> Rc<Value> {
        let ty = self
            .ty
            .substitute_levels(levels)
            .substitute_rows(rows)
            .substitute_mults(mults);
        eval(&Env::default(), &ty)
    }

    /// Тело, инстанцированное аргументами уровня и row. `None` у постулата.
    ///
    /// Row подставляются **окружением**, а не по терму: метка несёт открытые
    /// термы, и вложить их в замкнутое тело нечем (§3.2). Оттого их и одна
    /// форма: подстановка по терму, написанная было рядом, δ-разворот
    /// обслужить не могла и не звалась ниоткуда.
    #[must_use]
    pub fn unfolded(
        &self,
        levels: &[Level],
        rows: Rc<[Row<Rc<Value>>]>,
        mults: &[Mult],
    ) -> Option<Rc<Value>> {
        let body = self.body.as_ref()?;
        Some(eval(
            &Env::rowed(rows),
            &body.substitute_levels(levels).substitute_mults(mults),
        ))
    }

    /// Число параметров и универсум тип-формера. `None` - не семейство.
    #[must_use]
    pub fn data_shape(&self) -> Option<(u32, &Level)> {
        match &self.kind {
            DefinitionKind::Data { params, sort, .. } => Some((*params, sort)),
            _ => None,
        }
    }

    /// Число параметров метки. `None` - не эффект.
    ///
    /// Универсума рядом нет, и это не пропуск: метка не тип, полем стоять не
    /// может, укладывать её некуда.
    #[must_use]
    pub fn effect_shape(&self) -> Option<u32> {
        match &self.kind {
            DefinitionKind::Effect { params, .. } => Some(*params),
            _ => None,
        }
    }
}

/// Арность параметров: объявлена руками или выводится обобщением.
///
/// Компонент два - уровни и row (§10 вопрос 73), - и оба ведут себя одинаково:
/// выводятся обобщением на границе определения либо объявляются вызывающим,
/// когда он посчитал их сам. Второе нужно группе взаимной рекурсии: там
/// арность считается по написанному типу члена, до проверки тел.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Arity {
    /// Параметров уровня; `None` - выводятся обобщением.
    ///
    /// Написанные стоят в терме как [`crate::level::LevelVar`], и дырка,
    /// оставшаяся при такой записи, - отказ: обобщать её некуда. Выведенные
    /// наоборот: параметров во входном терме нет вовсе, только дырки, и
    /// `check_level_scope` этим пользуется.
    levels: Option<u32>,
    /// Параметров row. Всегда написаны: класс (§4.4) несёт свой row-параметр
    /// **полями словаря**, то есть телом, а обобщение читает тип - вывести
    /// число оттуда нечем.
    rows: u32,
    /// Параметров кратности (§10 вопрос 41). Всегда написаны - других способов
    /// их ввести нет: неаннотированная стрелка по-прежнему `ω` (§3.2).
    mults: u32,
}

impl Arity {
    /// Всё выводится: ни одного написанного параметра.
    #[must_use]
    pub const fn inferred() -> Self {
        Self {
            levels: None,
            rows: 0,
            mults: 0,
        }
    }

    /// Написаны и уровни, и row.
    #[must_use]
    pub const fn declared(levels: u32, rows: u32) -> Self {
        Self {
            levels: Some(levels),
            rows,
            mults: 0,
        }
    }

    /// Написаны только row: уровни выводятся как обычно (§4.4).
    #[must_use]
    pub const fn rowed(rows: u32) -> Self {
        Self {
            levels: None,
            rows,
            mults: 0,
        }
    }

    /// Та же арность с написанными параметрами кратности.
    #[must_use]
    pub const fn with_mults(self, mults: u32) -> Self {
        Self { mults, ..self }
    }

    /// Написаны ли уровни.
    const fn is_declared(self) -> bool {
        self.levels.is_some()
    }

    /// Объявленная арность уровней; у выведенной - ноль.
    const fn level_count(self) -> u32 {
        match self.levels {
            Some(levels) => levels,
            None => 0,
        }
    }

    /// То же для row.
    const fn row_count(self) -> u32 {
        self.rows
    }

    /// То же для кратностей.
    const fn mult_count(self) -> u32 {
        self.mults
    }
}

/// Объявление внутри члена: конструктор семейства или операция эффекта.
///
/// Форма у них одна - имя плюс написанный тип, - и проходят они одними и теми
/// же фазами; различает их то, что проверяет форму (§3.4, §10 вопрос 50).
#[derive(Clone, Debug)]
pub struct MemberDecl {
    /// Имя.
    pub name: Name,
    /// Тип. Проверяется в фазе B - против сигнатуры, где формер уже есть.
    pub ty: Term,
    /// Сколько параметров кратности написано **самим членом** (§10 вопрос 116).
    ///
    /// У конструктора их не бывает: он инстанцируется элиминацией теми же
    /// аргументами, что и семейство. У операции бывают: она инстанцируется
    /// местом вызова, и своих параметров сверх параметров метки иметь вправе -
    /// ровно как уровней.
    pub mults: u32,
}

/// Член группы.
#[derive(Clone, Debug)]
pub enum Member {
    /// Определение или постулат.
    Definition {
        /// Имя.
        name: Name,
        /// Кратность.
        mult: Mult,
        /// Арность параметров уровня.
        arity: Arity,
        /// Тип.
        ty: Term,
        /// Тело. `None` - постулат.
        body: Option<Term>,
        /// Запечатано ли: тело есть, но развороту не подлежит (§3.5).
        opaque: bool,
    },
    /// Индуктивное семейство вместе со своими конструкторами.
    Data {
        /// Имя семейства.
        name: Name,
        /// Сколько первых связываний тип-формера - параметры.
        ///
        /// Разделение нужно уже здесь, а не в элаборации: параметры выведены
        /// из-под универсумной проверки конструкторов, иначе
        /// `List : Type u -> Type u` не объявить - его параметр живёт в
        /// `Type (u+1)`, то есть заведомо выше самого `List`.
        params: u32,
        /// Арность параметров уровня.
        arity: Arity,
        /// Тип-формер.
        ty: Term,
        /// Конструкторы в порядке объявления.
        constructors: Vec<MemberDecl>,
        /// Выведен ли универсум семейства, а не написан (§10 вопрос 109).
        ///
        /// Выведенный поднимается до универсумов полей: поверхностный язык
        /// уровня не пишет (§3.2), поэтому нуль в нём - умолчание, а не выбор
        /// автора. Написанный остаётся потолком, и поле выше него отвергается
        /// - это и есть импредикативность через data-декларацию.
        inferred_sort: bool,
    },
    /// Метка эффекта вместе со своими операциями (§3.4).
    Effect {
        /// Имя метки.
        name: Name,
        /// Сколько связываний формера - параметры. Телескоп их повторяется в
        /// каждой операции дословно.
        params: u32,
        /// Арность параметров уровня.
        arity: Arity,
        /// Формер: `params -> Effect`.
        ty: Term,
        /// Операции в порядке объявления.
        operations: Vec<MemberDecl>,
    },
}

impl Member {
    /// Определение с выведенной арностью.
    #[must_use]
    pub fn definition(name: &str, mult: Mult, ty: Term) -> Self {
        Self::Definition {
            name: name.into(),
            mult,
            arity: Arity::inferred(),
            ty,
            body: None,
            opaque: false,
        }
    }

    /// Запечатывает определение: тело остаётся, разворот - нет.
    ///
    /// # Panics
    ///
    /// В отладочной сборке - если член не определение: у семейства тела нет,
    /// и запечатывать там нечего.
    #[must_use]
    pub fn sealed(mut self) -> Self {
        match &mut self {
            Self::Definition { opaque, .. } => *opaque = true,
            Self::Data { .. } | Self::Effect { .. } => {
                debug_assert!(false, "запечатывается определение, а не формер");
            }
        }
        self
    }

    /// Метка эффекта с выведенной арностью и без операций.
    ///
    /// Эффект без операций законен по той же причине, что семейство без
    /// конструкторов: объявить его можно, производить нечем.
    #[must_use]
    pub fn effect(name: &str, params: u32, ty: Term) -> Self {
        Self::Effect {
            name: name.into(),
            params,
            arity: Arity::inferred(),
            ty,
            operations: Vec::new(),
        }
    }

    /// Добавляет операцию метке.
    ///
    /// # Panics
    ///
    /// В отладочной сборке - если член не метка.
    #[must_use]
    pub fn with_operation(mut self, name: &str, ty: Term, mults: u32) -> Self {
        debug_assert!(
            matches!(self, Self::Effect { .. }),
            "операция приписывается метке, а не семейству"
        );
        if let Self::Effect { operations, .. } = &mut self {
            operations.push(MemberDecl {
                name: name.into(),
                ty,
                mults,
            });
        }
        self
    }

    /// Индуктивное семейство с выведенной арностью и без конструкторов.
    ///
    /// Семейство без конструкторов законно: разбор с нулём ветвей и есть
    /// доказательство необитаемости.
    #[must_use]
    pub fn data(name: &str, params: u32, ty: Term) -> Self {
        Self::Data {
            name: name.into(),
            params,
            arity: Arity::inferred(),
            ty,
            constructors: Vec::new(),
            inferred_sort: false,
        }
    }

    /// Помечает универсум семейства **выведенным**, а не написанным.
    ///
    /// Разница решает, поднимать ли его до полей конструкторов (§10 вопрос
    /// 109). Написанный - потолок: `Small : Type 0` с полем `(0 A : Type)`
    /// отвергается, и это ровно импредикативность через data-декларацию.
    /// Выведенный - нижняя граница: поверхностный язык уровня не пишет
    /// (§3.2), поэтому нуль там не выбор автора, а умолчание.
    #[must_use]
    pub fn with_inferred_sort(mut self) -> Self {
        if let Self::Data { inferred_sort, .. } = &mut self {
            *inferred_sort = true;
        }
        self
    }

    /// Приписывает тело определению.
    ///
    /// # Panics
    ///
    /// В отладочной сборке - если член не определение: тела у семейства нет, и
    /// молча потерянное тело хуже отказа.
    #[must_use]
    pub fn with_body(mut self, term: Term) -> Self {
        debug_assert!(
            matches!(self, Self::Definition { .. }),
            "тело приписывается определению, а не семейству"
        );
        if let Self::Definition { body, .. } = &mut self {
            *body = Some(term);
        }
        self
    }

    /// Объявляет арность вместо вывода: сперва уровни, потом row.
    #[must_use]
    pub fn with_arity(mut self, levels: u32, rows: u32) -> Self {
        match &mut self {
            Self::Definition { arity, .. }
            | Self::Data { arity, .. }
            | Self::Effect { arity, .. } => {
                *arity = Arity::declared(levels, rows);
            }
        }
        self
    }

    /// Объявляет параметры кратности: уровни и row остаются как были.
    #[must_use]
    pub fn with_mults(mut self, mults: u32) -> Self {
        match &mut self {
            Self::Definition { arity, .. }
            | Self::Data { arity, .. }
            | Self::Effect { arity, .. } => {
                *arity = arity.with_mults(mults);
            }
        }
        self
    }

    /// Объявляет только row-арность: уровни остаются выведенными (§4.4).
    #[must_use]
    pub fn with_rows(mut self, rows: u32) -> Self {
        match &mut self {
            Self::Definition { arity, .. }
            | Self::Data { arity, .. }
            | Self::Effect { arity, .. } => {
                *arity = Arity::rowed(rows);
            }
        }
        self
    }

    /// Добавляет конструктор семейству.
    ///
    /// # Panics
    ///
    /// В отладочной сборке - если член не семейство: конструкторов у
    /// определения нет, и молча потерянный конструктор хуже отказа.
    #[must_use]
    pub fn with_constructor(mut self, name: &str, ty: Term) -> Self {
        debug_assert!(
            matches!(self, Self::Data { .. }),
            "конструктор приписывается семейству, а не определению"
        );
        if let Self::Data { constructors, .. } = &mut self {
            constructors.push(MemberDecl {
                name: name.into(),
                ty,
                mults: 0,
            });
        }
        self
    }

    /// Имя члена.
    #[must_use]
    pub fn name(&self) -> &Name {
        match self {
            Self::Definition { name, .. } | Self::Data { name, .. } | Self::Effect { name, .. } => {
                name
            }
        }
    }
}

/// Группа - единица объявления.
#[derive(Clone, Debug, Default)]
pub struct Group {
    members: Vec<Member>,
}

impl Group {
    /// Группа из одного члена - обычное определение.
    #[must_use]
    pub fn of(member: Member) -> Self {
        Self {
            members: vec![member],
        }
    }

    /// Добавляет члена.
    #[must_use]
    pub fn and(mut self, member: Member) -> Self {
        self.members.push(member);
        self
    }

    /// Члены в порядке объявления.
    #[must_use]
    pub fn members(&self) -> &[Member] {
        &self.members
    }
}

/// Набор определений, доступных терму.
#[derive(Clone, Debug, Default)]
pub struct Signature {
    definitions: HashMap<Name, Definition>,
}

impl Signature {
    /// Определение по имени.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&Definition> {
        self.definitions.get(name)
    }

    /// Имена всех определений - инвариантным тестам и инструментам.
    ///
    /// Порядок не обещается: хранилище - хеш-таблица, и потребитель, которому
    /// нужен детерминизм, сортирует сам.
    #[must_use]
    pub fn names(&self) -> Vec<Name> {
        self.definitions.keys().cloned().collect()
    }

    /// Запечатывает уже объявленное определение.
    ///
    /// Флаг ставится **после** объявления, а не при нём, потому что
    /// запечатывается группа: члены модуля видят друг друга при проверке, и
    /// непрозрачность, поставленная сразу, запретила бы δ соседу, который
    /// ещё проверяется. Снаружи же группы уже нет - есть имена, и δ по ним
    /// закрыто (§3.5).
    ///
    /// Имя, которого в сигнатуре нет, игнорируется: вызывающий перечисляет
    /// написанных членов, а объявился ли член, решала проверка.
    pub fn seal(&mut self, name: &str) {
        if let Some(definition) = self.definitions.get_mut(name) {
            definition.opaque = true;
        }
    }

    /// Объявляет `@noalloc` у постулата (§5.1).
    ///
    /// Внутри пакета вердикт выводится по графу вызовов, но через границу
    /// **объявляется**: тела там нет, и вывести его не из чего. Постулат и есть
    /// эта граница, поэтому написанный на нём атрибут снимает ответ «аллоцирует
    /// неизвестно чем», который ядро поставило по отсутствию тела. Проверить
    /// обещание нечем - ровно как у `@total`, который постулату верит по той же
    /// причине: разворачивать нечего.
    ///
    /// Определение **с телом** не трогается: там вердикт посчитан, и заменять
    /// его обещанием значило бы принимать аллоцирующее тело по одному атрибуту.
    pub fn promise_noalloc(&mut self, name: &str) {
        if let Some(definition) = self.definitions.get_mut(name) {
            if definition.body.is_none() {
                definition.allocates = None;
            }
        }
    }

    /// Сколько определений.
    #[must_use]
    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    /// Пуста ли сигнатура.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    /// Конструкторы индуктивного типа в порядке объявления.
    #[must_use]
    pub fn constructors(&self, data: &str) -> Option<&[Name]> {
        match &self.lookup(data)?.kind {
            DefinitionKind::Data { constructors, .. } => Some(constructors),
            _ => None,
        }
    }

    /// Ссылка на определение с **выведенными** аргументами уровня.
    ///
    /// Это и есть implicit universe polymorphism со стороны места
    /// использования: вместо аргументов подставляются свежие дырки, а решает их
    /// проверка типов, столкнув полученный тип с ожидаемым. Пользователь
    /// уровней не пишет - §3.2 требует именно этого.
    ///
    /// `None` - определения с таким именем нет.
    #[must_use]
    pub fn instantiate(&self, name: &str, metas: &mut Metas) -> Option<Term> {
        let definition = self.lookup(name)?;
        let (levels, rows) = (definition.level_arity, definition.row_arity);
        let allowed: Vec<Rc<[Mult]>> = definition.mult_allowed.to_vec();
        let levels: Rc<[Level]> = (0..levels).map(|_| metas.fresh_level()).collect();
        let rows: Vec<_> = (0..rows).map(|_| metas.fresh_row()).collect();
        let mults: Vec<_> = allowed.into_iter().map(|it| metas.fresh_mult(it)).collect();
        Some(Term::Const(name.into(), levels, Args::new(rows, mults)))
    }

    /// Проверяет группу и добавляет её целиком.
    ///
    /// Три фазы - в заголовке модуля. Хранилище метапеременных принимается, а
    /// не заводится: оно одно на прогон элаборации (§10 вопрос 51), и граница
    /// группы для него - точка освобождения.
    ///
    /// # Errors
    ///
    /// Имя занято или повторено внутри группы; кратность `1`; параметр уровня
    /// вне объявленной арности; тип не является типом; тело не соответствует
    /// типу; осталась нерешённая дырка уровня; конструктор не повторяет
    /// параметры или возвращает не то семейство; нарушена строгая позитивность;
    /// поле не укладывается в универсум.
    pub fn declare(&mut self, metas: &mut Metas, group: &Group) -> Result<(), TypeError> {
        // Отложенное перебирается **здесь**, у самой границы, а не только в
        // проверке написанного типа. Откладывать умеет и тело - `resume Zero
        // Nil` под параметризованным хендлером оставляет flexible-flexible на
        // элементе нити, - а перебора после тел не стояло, и граница роняла
        // процесс `assert`-ом вместо отказа (§10 вопрос 111).
        let outcome = self
            .declare_fresh(metas, group)
            .and_then(|()| crate::check::settle_terms(self, metas))
            .and_then(|()| match metas.settle() {
                Some((left, right)) => Err(ErrorKind::UnsettledLevel { left, right }.into()),
                None => Ok(()),
            });
        if outcome.is_err() {
            // Отказ закрывает границу тоже: объявление не состоится, а
            // значения в отложенном ссылаются на дырки, которые вот-вот
            // освободятся.
            metas.abandon();
        }
        // Граница группы: всё, что было живо, либо решено и подставлено, либо
        // обобщено в параметры, либо стало отказом.
        metas.release();
        outcome
    }

    /// Занятость имён и откат наполовину проверенной группы.
    ///
    /// Имена проверяются **до** фаз, потому что откат снимает имена группы: не
    /// проверь их раньше, и отказ по дубликату снял бы чужое определение, то
    /// есть ровно то, на что жаловался.
    fn declare_fresh(&mut self, metas: &mut Metas, group: &Group) -> Result<(), TypeError> {
        if let Some(name) = self.taken_name(group) {
            return Err(ErrorKind::DuplicateDefinition { name }.into());
        }
        let outcome = self.declare_group(metas, group);
        if outcome.is_err() {
            for name in group_names(group) {
                self.definitions.remove(name);
            }
        }
        outcome
    }

    /// Первое имя группы, которое уже занято - в сигнатуре или самой группой.
    fn taken_name(&self, group: &Group) -> Option<Name> {
        let mut seen = HashSet::new();
        group_names(group)
            .find(|name| self.definitions.contains_key(*name) || !seen.insert(*name))
            .map(Rc::clone)
    }

    /// Фазы без отката и без проверки имён - их делает [`Signature::declare_fresh`].
    fn declare_group(&mut self, metas: &mut Metas, group: &Group) -> Result<(), TypeError> {
        let members = group.members();

        // (A) типы членов против сигнатуры без группы - с одним исключением.
        //
        // **Тип-формер семейства видит семейства, объявленные раньше него в той
        // же группе** (§10 вопрос 64). Порядок здесь не компромисс, а верное
        // правило: kind'ы взаимно рекурсивными быть не могут - `data A : B ->
        // Type` вместе с `data B : A -> Type` не обосновано, - и симметрии,
        // которую порядок мог бы нарушить, у них нет. Действительно
        // циклическая пара получает `UnknownConstant` на том имени, которое
        // ещё не объявлено.
        //
        // Значения так не объявляются: у них взаимная рекурсия симметрична, и
        // порядок сделал бы смысл группы зависящим от того, что написано выше.
        // Их типы вставляются после прохода, как и прежде.
        let mut checked = Vec::with_capacity(members.len());
        for (index, member) in members.iter().enumerate() {
            let found = self
                .check_member_type(metas, member)
                .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?;
            if matches!(member, Member::Data { .. }) {
                self.definitions
                    .insert(Rc::clone(member.name()), found.declaration.clone());
            }
            checked.push(found);
        }
        for (member, checked) in members.iter().zip(&checked) {
            self.definitions
                .insert(Rc::clone(member.name()), checked.declaration.clone());
        }

        // (B1) типы конструкторов - раньше тел определений. Тело члена группы
        // вправе разбирать по семейству соседа, а правилу `case` для этого
        // мало имён: оно берёт у каждого конструктора тип, чтобы построить тип
        // ветви. Конструктор, чей собственный тип разбирает по семейству той
        // же группы, упрётся в `UnknownConstant` - громкий отказ, а не молча
        // принятый неполный список.
        // Конструкторы видят конструкторы членов, объявленных **раньше** в той
        // же группе: `data Held : Tag -> Type where One : Held Leaf` рядом с
        // `data Tag` пишется. Довод тот же, что у тип-формеров в фазе A:
        // взаимная ссылка конструкторов друг на друга не обоснована - `MkA : A
        // MkB` вместе с `MkB : B MkA` есть круг по значениям, - и симметрии,
        // которую порядок мог бы нарушить, здесь нет. Семейства при этом видны
        // **все**: их типы вставлены фазой A целиком, и на этом стоит
        // `Tree`/`Forest`.
        let mut constructors = Vec::with_capacity(members.len());
        for (index, (member, checked)) in members.iter().zip(&checked).enumerate() {
            let declarations = self
                .check_member_constructors(metas, member, checked)
                .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?;
            for (name, declaration) in member_names(member).zip(&declarations) {
                self.definitions
                    .insert(Rc::clone(name), declaration.clone());
            }
            constructors.push(declarations);
        }

        // (B1½) семейство с индексом-универсумом обобщается **после** своих
        // конструкторов (§10 вопрос 53).
        for (index, (member, declarations)) in members.iter().zip(&mut constructors).enumerate() {
            self.settle_family(metas, member, declarations, checked[index].deferred)
                .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?;
        }

        // (B1¾) семейство поднимается до универсумов своих полей (§10 вопрос
        // 109). До конструкторов знать это неоткуда, а написать автору нечем:
        // уровень в kind'е не пишется (§3.2).
        for (index, (member, declarations)) in members.iter().zip(&constructors).enumerate() {
            self.raise_family(metas, member, declarations)
                .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?;
        }

        // (B2) тела определений - с полной таблицей конструкторов.
        let mut bodies = Vec::with_capacity(members.len());
        for (index, (member, checked)) in members.iter().zip(&checked).enumerate() {
            bodies.push(
                self.check_member_body(metas, member, checked)
                    .map_err(|error| error.in_frame(Frame::MemberBody(at(index))))?,
            );
        }

        // Тела - в сигнатуру до фазы C: позитивность смотрит сквозь
        // определения, и определение без тела она видит непрозрачным. Носители
        // едут тем же ходом: они выведены из тела и до него не существуют.
        for (member, body) in members.iter().zip(bodies) {
            if let (Some((term, report)), Some(stored)) =
                (body, self.definitions.get_mut(member.name()))
            {
                stored.body = Some(term);
                stored.carriers = report.carriers;
                // Дозволенные подстановки кратностей до проверки тела были
                // полукольцом целиком; проверка их сузила (§10 вопрос 41).
                stored.mult_allowed = report.allowed;
                stored.graded_carriers = report.graded;
            }
        }

        // (C) группа закрыта: позитивность, укладка полей, вердикт тотальности.
        //
        // Позитивность меряется **по всей группе**: `Tree` становится
        // негативным через `Forest` ровно так же, как через себя, и проверка,
        // знающая только своё имя, такую пару принимала бы.
        let families: Vec<Name> = members
            .iter()
            .zip(&checked)
            .filter(|(_, it)| it.declaration.data_shape().is_some())
            .map(|(member, _)| Rc::clone(member.name()))
            .collect();
        for (index, (member, declarations)) in members.iter().zip(&constructors).enumerate() {
            // Семейство берётся **из сигнатуры**, а не снимком фазы A: с тех
            // пор его универсум успел подняться до полей (§10 вопрос 109), и
            // снимок сравнивал бы поля с сортом, которого у семейства уже нет.
            let Some(family) = self.definitions.get(member.name()).cloned() else {
                continue;
            };
            for (slot, (declared, constructor)) in
                constructor_decls(member).zip(declarations).enumerate()
            {
                check_constructor_content(
                    self,
                    metas,
                    &declared.name,
                    member.name(),
                    &families,
                    &family,
                    &constructor.ty,
                )
                .map_err(|error| {
                    error
                        .in_frame(Frame::Constructor(at(slot)))
                        .in_frame(Frame::MemberType(at(index)))
                })?;
            }
        }
        // Вердикт тотальности считается по **зонканным** телам: словарь метода
        // инстанса стоит в теле дыркой, и до подстановки решения рекурсия
        // через него не видна вовсе. Вызов, пришедший после подстановки
        // спайном метода-проекции, восстанавливает ограниченная головная
        // редукция в [`crate::total`] (§10 вопрос 134).
        self.settle_totality(metas, group);
        // Вердикт `@noalloc` - по тем же зонканным телам и здесь же, пока дырки
        // живы: после границы объявления они освобождаются, и зонканье падает.
        self.settle_allocation(metas, group);

        for member in members {
            self.seal_member(metas, member)?;
        }
        // Финальные ворота: всё, что легло в сигнатуру, проверяется ещё раз.
        self.recheck_group(metas, group)?;
        // Носители наследуются после зонканья: до него выводимый аргумент -
        // дырка, и что им станет, не видно (см. [`crate::carrier`]).
        self.settle_carriers(group);
        Ok(())
    }

    /// Переносит носители вызываемых на вызывающих до неподвижной точки.
    ///
    /// Цикл, а не один проход: внутри группы члены зовут друг друга, и
    /// унаследованное одним обязано доехать до другого. Профиль только
    /// ухудшается, а значений у кратности три, поэтому сходимость обеспечена
    /// решёткой, а не счётчиком.
    fn settle_carriers(&mut self, group: &Group) {
        loop {
            let mut moved = false;
            for name in group_names(group) {
                let Some(definition) = self.definitions.get(name) else {
                    continue;
                };
                let Some(body) = &definition.body else {
                    continue;
                };
                let inherited = crate::carrier::propagated(self, &definition.ty, body);
                let settled = crate::carrier::worst(&definition.carriers, &inherited);
                if *settled != *definition.carriers {
                    if let Some(stored) = self.definitions.get_mut(name) {
                        stored.carriers = settled;
                    }
                    moved = true;
                }
            }
            if !moved {
                return;
            }
        }
    }

    /// Фаза A для одного члена: проверить тип и обобщить арность.
    fn check_member_type(&self, metas: &mut Metas, member: &Member) -> Result<Checked, TypeError> {
        let (name, mult, arity, ty) = match member {
            Member::Definition {
                name,
                mult,
                arity,
                ty,
                ..
            } => (name, *mult, *arity, ty),
            // Кратность тип-формера `ω`: он живёт и в позиции типа (там σ = 0,
            // и `ω` это допускает), и как обычное значение - §3.2 разрешает
            // `List Type`.
            //
            // Метка эффекта живёт там же и по той же причине: она стоит
            // аргументом row, то есть в стёртом фрагменте, но запрещать ей
            // рантайм незачем.
            Member::Data {
                name, arity, ty, ..
            }
            | Member::Effect {
                name, arity, ty, ..
            } => (name, Mult::Many, *arity, ty),
        };

        let mut draft = Definition {
            mult,
            opaque: matches!(member, Member::Definition { opaque: true, .. }),
            level_arity: arity.level_count(),
            row_arity: arity.row_count(),
            // Дозволенное каждому параметру уточнит фаза B2 перебором: до
            // проверки тела известно только их число.
            mult_allowed: (0..arity.mult_count()).map(|_| ALL_MULTS.into()).collect(),
            graded_carriers: Rc::from([]),
            // Носители неизвестны, пока тело не проверено; фаза B2 их уточнит,
            // а постулат так и останется с `ω` - консервативным ответом.
            carriers: crate::carrier::unknown(ty),
            ty: ty.clone(),
            body: None,
            kind: DefinitionKind::Regular,
            total: true,
            // Вердикт `@noalloc` считает фаза C по телу; до неё член входит не
            // аллоцирующим, и понижает его неподвижная точка.
            allocates: None,
        };
        check_declaration(self, metas, name, &draft)?;

        // Зонканье идёт **до** обобщения: уровень, спрятавшийся в решении
        // дырки терма, иначе не виден. Дырка терма стоит доменом поднятого
        // implicit-параметра (§4.1), а решается она универсумом, чей уровень
        // и обязан стать параметром.
        draft.ty = zonk_term(metas, &draft.ty);

        // Обобщение идёт **до** проверки тела: рекурсивная ссылка обязана знать
        // окончательную арность, иначе член в собственном теле пишется с
        // числом аргументов уровня, которого у него ещё нет.
        //
        // Исключение - **алиас типа** (§10 вопрос 106): определение, чей тип
        // кончается голым универсумом. Обобщение сделало бы его уровень
        // параметром - `∀u. … -> Type u`, - а тело живёт на конкретном, и
        // `Type 0` под `Type u` не подходит. Написать уровень руками нельзя:
        // §3.2 держит их неявными. Дырка **результата** остаётся дыркой, и
        // решает её тело - как решало бы всякое другое ограничение.
        //
        // Обобщается при этом всё остальное: у `Twin : Type -> Type` уровень
        // домена обязан стать параметром - иначе его не определит ничто, - а
        // уровень результата обязан остаться дыркой, чтобы тело приравняло его
        // к домену. Порознь ни то ни другое не работает.
        //
        // Путь добавочный: определение, чей тип кончается универсумом, сегодня
        // отвергается **всегда**, поэтому проходящая программа сюда не
        // попадает.
        let aliasing = match member {
            Member::Definition { body: Some(_), .. } => alias_result(metas, &draft.ty),
            _ => None,
        };
        // Семейство с индексом-универсумом обобщается позже, в фазе B1½: его
        // уровень заземляют конструкторы (§10 вопрос 53). Арность при этом
        // объявляется сразу - числом дырок, - иначе ссылка на семейство внутри
        // конструктора получит `LevelArity` на ровном месте. Подставлять по
        // ней нечего: параметров в типе ещё нет, и аргументы ссылки инертны,
        // пока обобщение их не перепишет.
        let deferred = postponed(member, &draft.ty);
        let (mut declaration, generalization) = if let Some(result) = aliasing {
            generalize(metas, arity, draft, Some(result))
        } else if deferred {
            let mut counting = Generalization::default();
            counting.collect_term(metas, &draft.ty);
            let level_arity = counting.arity();
            (
                Definition {
                    level_arity,
                    ..draft
                },
                None,
            )
        } else {
            generalize(metas, arity, draft, None)
        };

        if let Member::Data {
            name,
            params,
            constructors,
            ..
        } = member
        {
            // Универсум берётся из уже обобщённого типа: до обобщения на его
            // месте стоит дырка, а конструкторы будут сравниваться с параметром.
            let sort = data_sort(name, *params, &declaration.ty)?;
            declaration.kind = DefinitionKind::Data {
                // Список полон сразу: имена берутся из объявления и проверкой
                // не меняются. Заполнять его позже нельзя - тело члена группы
                // проверяется раньше, а полнота ветвей `case` считается по
                // этому списку, и пустой означал бы «семейство необитаемо».
                constructors: constructors
                    .iter()
                    .map(|constructor| Rc::clone(&constructor.name))
                    .collect(),
                params: *params,
                sort,
            };
        }
        if let Member::Effect {
            name,
            params,
            operations,
            ..
        } = member
        {
            effect_sort(name, *params, &declaration.ty)?;
            declaration.kind = DefinitionKind::Effect {
                operations: operations
                    .iter()
                    .map(|operation| Rc::clone(&operation.name))
                    .collect(),
                params: *params,
            };
        }
        Ok(Checked {
            declaration,
            generalization,
            deferred,
        })
    }

    /// Фаза B1 для одного члена: типы его конструкторов. У определения их нет.
    fn check_member_constructors(
        &self,
        metas: &mut Metas,
        member: &Member,
        checked: &Checked,
    ) -> Result<Vec<Definition>, TypeError> {
        match member {
            Member::Definition { .. } => Ok(Vec::new()),
            Member::Data {
                name,
                arity,
                constructors,
                ..
            } => {
                let mut declarations = Vec::with_capacity(constructors.len());
                for (slot, constructor) in constructors.iter().enumerate() {
                    declarations.push(
                        self.check_constructor_type(
                            metas,
                            name,
                            *arity,
                            &checked.declaration,
                            constructor,
                            checked.deferred,
                        )
                        .map_err(|error| error.in_frame(Frame::Constructor(at(slot))))?,
                    );
                }
                Ok(declarations)
            }
            Member::Effect {
                name,
                arity,
                operations,
                ..
            } => {
                let mut declarations = Vec::with_capacity(operations.len());
                for (slot, operation) in operations.iter().enumerate() {
                    declarations.push(
                        self.check_operation_type(
                            metas,
                            name,
                            *arity,
                            &checked.declaration,
                            operation,
                        )
                        .map_err(|error| error.in_frame(Frame::Constructor(at(slot))))?,
                    );
                }
                Ok(declarations)
            }
        }
    }

    /// Фаза B1 для операции: тип, арность и форма.
    ///
    /// Отличие от конструктора одно, и оно всё: конструктор обязан **вернуть**
    /// своё семейство, а операция - **произвести** свою метку. Проверяется
    /// поэтому не результат, а row (§3.4).
    fn check_operation_type(
        &self,
        metas: &mut Metas,
        effect: &Name,
        arity: Arity,
        former: &Definition,
        operation: &MemberDecl,
    ) -> Result<Definition, TypeError> {
        let mut draft = Definition {
            mult: Mult::Many,
            level_arity: arity.level_count(),
            row_arity: arity.row_count(),
            // Свои параметры кратности у операции бывают (§10 вопрос 116): она
            // инстанцируется местом вызова, как всякое определение, и
            // дозволенное им уточнит не тело - его нет, - а само объявление.
            mult_allowed: (0..operation.mults).map(|_| ALL_MULTS.into()).collect(),
            graded_carriers: Rc::from([]),
            carriers: crate::carrier::stored(&operation.ty),
            opaque: false,
            ty: operation.ty.clone(),
            body: None,
            kind: DefinitionKind::Operation {
                effect: Rc::clone(effect),
            },
            // Тела у операции нет и не будет: развернуть её нечем до тех пор,
            // пока хендлер не подставит evidence. Расходиться, значит, нечему.
            total: true,
            // Аллоцирует ли операция, решает форма ветки хендлера: не
            // хвостово-резумптивная снимает продолжение в кучу (§5.1). Анализа
            // хвостовой резумптивности (§3.4) нет, ответ консервативный.
            allocates: Some(crate::alloc::Source::Operation(Rc::clone(&operation.name))),
        };
        check_declaration(self, metas, &operation.name, &draft)?;

        // Зонканье идёт **до** обобщения - тем же доводом, что и у члена: без
        // подстановки не виден уровень, спрятавшийся в решении дырки терма.
        // Дырка эта стоит доменом поднятого implicit-параметра (§4.1), и у
        // операции подъём случается ровно там, где нужен: `throw : e -> a`
        // поднимает `a`, домен ему - дырка, решается она универсумом. Без
        // зонканья уровень этого универсума не обобщался и всплывал при
        // запечатывании неразрешённым, отвергая всякую операцию со свободным
        // именем в типе.
        draft.ty = zonk_term(metas, &draft.ty);
        let (declaration, _) = generalize(metas, arity, draft, None);

        // Параметры метки обязаны стоять у операции первыми - телескоп метки
        // повторяется у неё дословно, - но своих сверх них операция иметь
        // вправе. Этим она отличается от конструктора: тот инстанцируется
        // элиминацией теми же аргументами, что и семейство, и лишний параметр
        // заполнить было бы нечем, а операция инстанцируется местом вызова.
        // Ветка хендлера при этом связывает лишний параметр наравне с
        // написанными аргументами - она честно полиморфна по нему, потому что
        // тип операции разбирается телескопом, а не по числу параметров метки.
        if declaration.level_arity < former.level_arity {
            return Err(ErrorKind::LevelArity {
                name: Rc::clone(&operation.name),
                expected: former.level_arity,
                found: declaration.level_arity,
            }
            .into());
        }

        check_operation_shape(
            self,
            metas,
            &operation.name,
            effect,
            former,
            &declaration.ty,
        )?;
        Ok(declaration)
    }

    /// Фаза B2 для одного члена: тело определения. `None` - постулат или
    /// семейство.
    fn check_member_body(
        &self,
        metas: &mut Metas,
        member: &Member,
        checked: &Checked,
    ) -> Result<Option<CheckedBody>, TypeError> {
        let Member::Definition {
            name,
            body: Some(body),
            ..
        } = member
        else {
            return Ok(None);
        };
        // Обобщение арности прошло по типу; та же подстановка идёт и по телу -
        // тем же отображением, а не построенным заново: дырка, решённая в
        // параметр типа, обязана стать тем же параметром.
        let body = match &checked.generalization {
            Some(generalization) => generalization.apply_term(metas, body),
            None => body.clone(),
        };
        let definition = Definition {
            body: Some(body.clone()),
            ..checked.declaration.clone()
        };
        let report = check_body(self, metas, name, &definition)?;
        Ok(Some((body, report)))
    }

    /// Фаза B1½: обобщение семейства, отложенное до его конструкторов.
    ///
    /// Обычное семейство обобщается в фазе A, и этого хватает: его параметры
    /// уровня конструктор **повторяет**, поэтому арности сходятся. Семейство с
    /// индексом-универсумом устроено иначе - конструктор индекс
    /// **инстанцирует**: `LitNat : Nat -> Expr Nat` требует `Nat : Type u`, то
    /// есть заземляет `u` нулём. Обобщи мы уровень раньше, он стал бы
    /// параметром, который конструктор потом заземлит, и арности разошлись бы
    /// - ровно тот отказ, из-за которого GADT §4.1 не объявлялся вовсе.
    ///
    /// Поэтому здесь: дырки семейства дожили до конструкторов открытыми, те их
    /// решили, и обобщается остаток - **совместно** по kind'у и по всем типам
    /// конструкторов, чтобы уцелевший параметр был у них общим.
    ///
    /// Аргументы уровня у внутригрупповых ссылок переписываются заново: до
    /// обобщения они инертны (подставлять их некуда - параметров нет), а после
    /// обязаны быть ровно параметрами семейства.
    fn settle_family(
        &mut self,
        metas: &mut Metas,
        member: &Member,
        constructors: &mut [Definition],
        deferred: bool,
    ) -> Result<(), TypeError> {
        let Member::Data { name, params, .. } = member else {
            return Ok(());
        };
        let Some(family) = self.definitions.get(name) else {
            return Ok(());
        };
        if !deferred {
            return Ok(());
        }
        // Аргументы уровня у внутригрупповых ссылок снимаются **до** сбора:
        // они инертны - подставлять по ним нечего, параметров у семейства ещё
        // нет, - и собранные наравне с прочими дырками они стали бы лишними
        // параметрами, которых семейство не просило.
        let stripped = |ty: &Term| relevelled(ty, name, &Rc::from([]));
        let family = stripped(&family.ty);
        // Зонкать типы конструкторов здесь нельзя, и это измерено: решение
        // дырки терма разворачивается цепочкой лямбд, и на месте домена встаёт
        // бета-редекс, которого синтезу не разобрать - `data Vec (a : Type) :
        // Nat -> Type` отвергается «тип `\(0 m0) -> Nat` невозможно
        // синтезировать». Оттого и цена: уровень **поднятого** типового имени
        // прячется в этой дырке, собрать его нечем, и `MkSome : a -> Some`
        // пишется явным связыванием `(0 a : Type)`.
        let bodies: Vec<Term> = constructors.iter().map(|it| stripped(&it.ty)).collect();
        let mut generalization = Generalization::default();
        generalization.collect_term(metas, &family);
        for constructor in &bodies {
            generalization.collect_term(metas, constructor);
        }
        let arity = generalization.arity();
        let levels: Rc<[Level]> = (0..arity)
            .map(|index| Level::Var(LevelVar(index)))
            .collect();
        let settle = |ty: &Term| relevelled(&generalization.apply_term(metas, ty), name, &levels);
        let ty = settle(&family);
        let sort = data_sort(name, *params, &ty)?;
        let Some(stored) = self.definitions.get_mut(name) else {
            return Ok(());
        };
        stored.ty = ty;
        stored.level_arity = arity;
        if let DefinitionKind::Data { sort: stored, .. } = &mut stored.kind {
            *stored = sort;
        }
        for (constructor, body) in constructors.iter_mut().zip(&bodies) {
            constructor.ty = settle(body);
            constructor.level_arity = arity;
        }
        for (constructor, declaration) in member_names(member).zip(constructors.iter()) {
            self.definitions
                .insert(Rc::clone(constructor), declaration.clone());
        }
        Ok(())
    }

    /// Фаза B1¾: универсум семейства поднимается до его полей.
    ///
    /// §4.1 называет правило - «поднятое в имплисит конструктора имя требует от
    /// семейства `Type (ℓ+1)`», - но потребовать этого автору нечем: уровень в
    /// kind'е не пишется. Поэтому считается он здесь, тем же ходом, каким
    /// элаборация уже поднимает сорт до универсумов **параметров**; поля
    /// добавляются к ним, когда конструкторы прочитаны.
    ///
    /// Поднимается только вверх: написанный автором универсум - нижняя
    /// граница, а не потолок.
    fn raise_family(
        &mut self,
        metas: &mut Metas,
        member: &Member,
        constructors: &[Definition],
    ) -> Result<(), TypeError> {
        let Member::Data {
            name,
            params,
            inferred_sort: true,
            ..
        } = member
        else {
            return Ok(());
        };
        let Some(family) = self.definitions.get(name) else {
            return Ok(());
        };
        let mut sort = data_sort(name, *params, &family.ty)?;
        for constructor in constructors {
            let found = crate::check::constructor_sort(self, metas, *params, &constructor.ty)?;
            sort = sort.max(found);
        }
        let sort = metas.zonk(&sort).normalize();
        let Some(stored) = self.definitions.get_mut(name) else {
            return Ok(());
        };
        stored.ty = resorted(&stored.ty, &sort);
        if let DefinitionKind::Data { sort: stored, .. } = &mut stored.kind {
            *stored = sort;
        }
        Ok(())
    }

    /// Фаза B1 для конструктора: тип, арность и форма.
    fn check_constructor_type(
        &self,
        metas: &mut Metas,
        data: &Name,
        arity: Arity,
        family: &Definition,
        constructor: &MemberDecl,
        deferred: bool,
    ) -> Result<Definition, TypeError> {
        let draft = Definition {
            mult: Mult::Many,
            // Запись арности у конструктора та же, что у семейства: объявленную
            // обобщать нечем - её параметры уже стоят в типе как `LevelVar`, - и
            // обобщение свело бы её к нулю, отвергнув всякий полиморфный
            // конструктор объявленного семейства.
            level_arity: arity.level_count(),
            row_arity: arity.row_count(),
            // Конструктор кладёт значение ровно однажды, поэтому носителю его
            // параметра ограничивать нечего; держателя ресурсного поля
            // проверяет отдельное правило (§3.3, вопрос 77).
            mult_allowed: Rc::from([]),
            graded_carriers: Rc::from([]),
            carriers: crate::carrier::stored(&constructor.ty),
            opaque: false,
            ty: constructor.ty.clone(),
            body: None,
            kind: DefinitionKind::Constructor {
                data: Rc::clone(data),
            },
            total: true,
            // Конструктор с рантайм-полем строит значение в куче - это и есть
            // аллокация (§5.1), а разрешает её только гарантированный reuse,
            // которого нет. Конструктор без таких полей объектом не становится
            // вовсе: его номер живёт в самом указателе (ABI, лог 2026-09-08).
            allocates: crate::alloc::constructed(&constructor.name, &constructor.ty),
        };
        check_declaration(self, metas, &constructor.name, &draft)?;
        // Семейство с индексом-универсумом обобщается позже, вместе со своими
        // конструкторами (§10 вопрос 53): здесь их дырки обязаны дожить
        // открытыми, иначе решать индексу уровень уже нечем.
        if deferred {
            let declaration = Definition {
                level_arity: family.level_arity,
                ..draft
            };
            check_constructor_shape(
                self,
                metas,
                &constructor.name,
                data,
                family,
                &declaration.ty,
            )?;
            return Ok(declaration);
        }
        let (declaration, _) = generalize(metas, arity, draft, None);

        // Арность уровня обязана совпасть с арностью семейства: элиминация
        // инстанцирует конструктор теми же аргументами, что и само семейство,
        // и лишний параметр заполнить было бы нечем. Проверку не заменяет
        // сверка результата - тот фиксирует лишь первые `arity` параметров.
        if declaration.level_arity != family.level_arity {
            return Err(ErrorKind::LevelArity {
                name: Rc::clone(&constructor.name),
                expected: family.level_arity,
                found: declaration.level_arity,
            }
            .into());
        }

        check_constructor_shape(
            self,
            metas,
            &constructor.name,
            data,
            family,
            &declaration.ty,
        )?;
        Ok(declaration)
    }

    /// Кладёт члена в сигнатуру насовсем - его самого и его конструкторы.
    fn seal_member(&mut self, metas: &mut Metas, member: &Member) -> Result<(), TypeError> {
        for constructor in member_names(member) {
            self.seal_definition(metas, constructor)?;
        }
        self.seal_definition(metas, member.name())
    }

    /// Зонканье сохранённого определения и проверка на остаточные дырки.
    fn seal_definition(&mut self, metas: &mut Metas, name: &Name) -> Result<(), TypeError> {
        let mut definition = self
            .definitions
            .get(name)
            .cloned()
            .unwrap_or_else(|| unreachable!("объявление вставлено фазой A или B1"));

        // Решённые по дороге дырки подставляются здесь: хранилище живёт прогон
        // элаборации, а определение - всю программу, и `Meta(k)` в нём пережила
        // бы границу, за которой память под неё освобождена. Универсум
        // семейства - такой же уровень, как в типе, и зонкается вместе с ним.
        definition.ty = zonk_term(metas, &definition.ty);
        definition.body = definition.body.map(|body| zonk_term(metas, &body));
        if let DefinitionKind::Data { sort, .. } = &mut definition.kind {
            *sort = metas.zonk(sort);
        }

        // Остаточные дырки ищутся **после** подстановки: уровень, спрятавшийся
        // в решении дырки терма, до неё не виден, и определение уезжало бы за
        // границу группы с уровнем из освобождённого хранилища.
        if let Some(meta) = unsolved_term_in_definition(metas, &definition) {
            return Err(ErrorKind::AmbiguousTerm { meta }.into());
        }
        if let Some(meta) = unsolved_in_definition(metas, &definition) {
            return Err(ErrorKind::UnsolvedDefinitionLevel {
                name: Rc::clone(name),
                meta,
            }
            .into());
        }
        // Третий сорт. Пропущенный, он давал не неверную программу, а падение:
        // дырка уезжала в сохранённый тип живой, а бралось за неё зонканье
        // следующей группы - уже после `release`, вне живого диапазона.
        if let Some(meta) = crate::check::unsolved_row_in_definition(metas, &definition) {
            return Err(ErrorKind::UnsolvedDefinitionRow {
                name: Rc::clone(name),
                meta,
            }
            .into());
        }

        self.definitions.insert(Rc::clone(name), definition);
        Ok(())
    }

    /// Перепроверяет то, что легло в сигнатуру, по нормализованному телу.
    ///
    /// Проверка до этого места смотрит на терм **с дырками**, а дырка инертна:
    /// её тип известен с рождения, использований она не порождает, и всё, что
    /// вписала элаборация - вставленный имплисит, найденный словарь, дописанное
    /// умолчание, поднятый разбор, - проходит мимо и §3.1, и правил вокруг.
    /// Стоило это одной честной дыры: `f k (len v)` при `(1 k : Nat)`
    /// принималось, а `f k (len @k v)` - тот же аргумент, написанный рукой -
    /// отвергалось, потому что первый попадал в терм через дырку и не
    /// расходовал ничего.
    ///
    /// Здесь дырок уже нет, и тело приводится к нормальной форме: решение дырки
    /// подставляется лямбдой, оставляя бета-редекс, а поднятый разбор -
    /// `Let`-ом, и в таком виде проверка спотыкается о позиции, где нужен
    /// вывод. Нормализация снимает и то, и другое разом, после чего тело
    /// проверяется как обычный терм - типы и кратности вместе.
    ///
    /// Названная цена - второй проход по каждому телу, с нормализацией.
    /// Дешевле он не бывает: единственный способ узнать, сколько расходует
    /// решение дырки, - посмотреть на решение.
    ///
    /// # Errors
    ///
    /// Всё, что не сошлось: тип, кратность, область уровня.
    fn recheck_group(&mut self, metas: &mut Metas, group: &Group) -> Result<(), TypeError> {
        for (index, name) in group_names(group).enumerate() {
            let Some(definition) = self.definitions.get(name).cloned() else {
                continue;
            };
            let Some(body) = &definition.body else {
                continue;
            };
            let normal = crate::eval::quote(0, &crate::ctx::Ctx::new(self).eval(body));
            let checked = Definition {
                body: Some(normal),
                ..definition
            };
            let report = crate::check::check_body(self, metas, name, &checked)
                .map_err(|error| error.in_frame(Frame::MemberBody(at(index))))?;
            // Дозволенные подстановки сужаются и здесь: проход идёт по
            // нормальной форме, и она бывает строже (§10 вопрос 41). Оставить
            // множество от фазы B2 значило бы обещать подстановку, при которой
            // тело на самом деле не проверяется.
            if let Some(stored) = self.definitions.get_mut(name) {
                stored.mult_allowed = report.allowed;
                stored.graded_carriers = report.graded;
            }
        }
        Ok(())
    }

    /// Для каждого члена группы - имена, с которыми он лежит на одном цикле
    /// вызовов, включая его самого.
    ///
    /// Рекурсией считается вызов **по циклу**, а не всякое упоминание соседа.
    /// Разница видна на первом же инстансе: словарь `Eqv#Nat` называет свой
    /// метод `Eqv#Nat.eq`, а метод словарь не зовёт - убывать словарю не по
    /// чему и не за чем. И она же существенна в другую сторону: `ping n = pong n`
    /// вместе с `pong n = ping n` цикл образуют, и без него проверка не видела
    /// в паре ни одного вызова, объявляя расходящуюся пару тотальной - в том
    /// числе для §4.7, то есть пропуская её в тип.
    ///
    /// Замыкание считается наивно, повторными проходами: членов в группе
    /// единицы, и заводить ради них Тарьяна не за что.
    fn call_cycles(&self, metas: &Metas, group: &Group) -> HashMap<Name, Vec<Name>> {
        let names: Vec<Name> = group_names(group).cloned().collect();
        let mut reaches: HashMap<Name, Vec<Name>> = HashMap::new();
        for name in &names {
            // По зонканному телу - тем же, по которому считается вердикт:
            // граф и проверка убывания обязаны видеть одни и те же вызовы.
            let direct = self
                .definitions
                .get(name)
                .and_then(|it| it.body.as_ref())
                .map_or_else(Vec::new, |body| {
                    crate::total::calls_within(self, &names, &crate::meta::zonk_term(metas, body))
                });
            reaches.insert(Rc::clone(name), direct);
        }
        loop {
            let mut grew = false;
            for name in &names {
                let mut grown = reaches[name].clone();
                for step in &reaches[name] {
                    for far in &reaches[step] {
                        if !grown.contains(far) {
                            grown.push(Rc::clone(far));
                            grew = true;
                        }
                    }
                }
                reaches.insert(Rc::clone(name), grown);
            }
            if !grew {
                break;
            }
        }
        names
            .iter()
            .map(|name| {
                let mut cycle = vec![Rc::clone(name)];
                for other in &reaches[name] {
                    if other != name && reaches[other].contains(name) {
                        cycle.push(Rc::clone(other));
                    }
                }
                (Rc::clone(name), cycle)
            })
            .collect()
    }

    /// Вердикт тотальности по совместному графу вызовов группы.
    ///
    /// Неподвижная точка сверху: члены входят тотальными, и проход повторяется,
    /// пока кто-то понижается. Для группы из одного члена это ровно один проход
    /// и тот же ответ, что раньше; для взаимной рекурсии - единственный
    /// корректный способ, потому что вердикт члена зависит от вердиктов
    /// соседей.
    fn settle_totality(&mut self, metas: &Metas, group: &Group) {
        let cycles = self.call_cycles(metas, group);
        // Вся группа без вердикта: редукции в проверке нельзя разворачивать
        // ни одного её члена, даже не лежащего на цикле проверяемого.
        let undecided: Vec<Name> = group_names(group).cloned().collect();
        loop {
            let mut demoted = false;
            for member in group.members() {
                let name = member.name();
                let Some(definition) = self.definitions.get(name) else {
                    continue;
                };
                if !definition.total {
                    continue;
                }
                let definition = definition.clone();
                let cycle = cycles
                    .get(name)
                    .map_or_else(|| std::slice::from_ref(name), Vec::as_slice);
                if !crate::total::is_total(self, metas, name, cycle, &undecided, &definition) {
                    if let Some(stored) = self.definitions.get_mut(name) {
                        stored.total = false;
                    }
                    demoted = true;
                }
            }
            if !demoted {
                return;
            }
        }
    }

    /// Вердикт `@noalloc` по совместному графу вызовов группы (§5.1).
    ///
    /// Неподвижная точка сверху, как у [`Signature::settle_totality`]: члены
    /// входят не аллоцирующими, и проход повторяется, пока кто-то понижается.
    /// Старт оптимистичный потому, что цикл не аллоцирующих функций не
    /// аллоцирует: рекурсия сама по себе кучи не трогает, о стеке атрибут не
    /// говорит вовсе.
    ///
    /// Понизившийся обратно не поднимается, поэтому проходов не больше, чем
    /// членов.
    fn settle_allocation(&mut self, metas: &Metas, group: &Group) {
        loop {
            let mut demoted = false;
            for name in group_names(group) {
                let Some(definition) = self.definitions.get(name) else {
                    continue;
                };
                if definition.allocates.is_some() {
                    continue;
                }
                let definition = definition.clone();
                let Some(found) = crate::alloc::source(self, metas, name, &definition) else {
                    continue;
                };
                if let Some(stored) = self.definitions.get_mut(name) {
                    stored.allocates = Some(found);
                }
                demoted = true;
            }
            if !demoted {
                return;
            }
        }
    }

    // --- обёртки над группой из одного члена ------------------------------

    /// Определение с объявленной арностью параметров уровня.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn define(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        level_arity: u32,
        ty: Term,
        body: Option<Term>,
    ) -> Result<(), TypeError> {
        let mut member = Member::definition(name, mult, ty).with_arity(level_arity, 0);
        if let Some(body) = body {
            member = member.with_body(body);
        }
        self.declare(metas, &Group::of(member))
    }

    /// Кладёт тип-формер **без проверки** - ровно то, что фаза A делает внутри
    /// группы.
    ///
    /// Нужно это элаборации: арность уровней она считает настоящим `is_type`
    /// (см. `self_levels` в `adamas-elab`), а тот смотрит в сигнатуру, и
    /// тип-формер соседа по группе обязан быть там виден. Проверку сосед
    /// пройдёт своим чередом, когда группа объявится целиком; здесь - только
    /// видимость (§10 вопрос 64).
    ///
    /// Зовётся **по копии** сигнатуры, а не по настоящей: непроверенному
    /// объявлению в ней делать нечего. Хранилище дырок при этом общее, и в
    /// этом весь смысл - `is_type` обязан решать те же дырки, что решит
    /// объявление.
    pub fn assume(&mut self, name: &str, level_arity: u32, ty: Term) {
        self.definitions.insert(
            name.into(),
            Definition {
                mult: Mult::Many,
                level_arity,
                row_arity: 0,
                mult_allowed: Rc::from([]),
                graded_carriers: Rc::from([]),
                ty,
                body: None,
                kind: DefinitionKind::Regular,
                total: true,
                opaque: false,
                carriers: Rc::from([] as [Mult; 0]),
                // Кладётся тип-формер, а не значение: аллоцировать нечему.
                allocates: None,
            },
        );
    }

    /// Постулат с объявленной арностью: тип без тела.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn postulate(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        level_arity: u32,
        ty: Term,
    ) -> Result<(), TypeError> {
        self.define(metas, name, mult, level_arity, ty, None)
    }

    /// Определение с **выведенной** арностью.
    ///
    /// Тип и тело пишутся с дырками ([`Metas::fresh_level`]), а не с
    /// параметрами: параметры - результат, а не вход. Дырки, решённые по ходу
    /// проверки, исчезают; оставшиеся становятся параметрами уровня, и их число
    /// и есть арность.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn define_inferred(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        ty: Term,
        body: Option<Term>,
    ) -> Result<(), TypeError> {
        self.define_opaque(metas, name, mult, ty, body, false)
    }

    /// То же, с выбором прозрачности: `true` запечатывает (§3.5).
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn define_opaque(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        ty: Term,
        body: Option<Term>,
        opaque: bool,
    ) -> Result<(), TypeError> {
        let mut member = Member::definition(name, mult, ty);
        if let Some(body) = body {
            member = member.with_body(body);
        }
        if opaque {
            member = member.sealed();
        }
        self.declare(metas, &Group::of(member))
    }

    /// То же с написанными параметрами кратности (§10 вопрос 41).
    ///
    /// Уровни выводятся как обычно: параметры кратности им ортогональны -
    /// стоят они в `Pi`, а не в универсуме.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn define_graded(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        ty: Term,
        body: Option<Term>,
        mults: u32,
    ) -> Result<(), TypeError> {
        let mut member = Member::definition(name, mult, ty).with_mults(mults);
        if let Some(body) = body {
            member = member.with_body(body);
        }
        self.declare(metas, &Group::of(member))
    }

    /// То же с объявленной row-арностью: уровни выводятся, row написаны.
    ///
    /// Так объявляется класс (§4.4): row-параметр стоит в **полях словаря**, а
    /// обобщение читает тип, - вывести число оттуда нечем.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn define_rowed(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        ty: Term,
        body: Option<Term>,
        rows: u32,
    ) -> Result<(), TypeError> {
        let mut member = Member::definition(name, mult, ty).with_rows(rows);
        if let Some(body) = body {
            member = member.with_body(body);
        }
        self.declare(metas, &Group::of(member))
    }

    /// Постулат с выведенной арностью.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn postulate_inferred(
        &mut self,
        metas: &mut Metas,
        name: &str,
        mult: Mult,
        ty: Term,
        mults: u32,
    ) -> Result<(), TypeError> {
        self.define_graded(metas, name, mult, ty, None, mults)
    }

    /// Индуктивное семейство вместе с конструкторами - одним вызовом.
    ///
    /// Раздельного объявления тип-формера и конструкторов нет: между ними
    /// сигнатура была бы наблюдаема с неполным списком конструкторов, а полноту
    /// ветвей `case` проверяют по этому списку один раз.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::declare`].
    pub fn declare_data(
        &mut self,
        metas: &mut Metas,
        name: &str,
        params: u32,
        ty: Term,
        constructors: &[(&str, Term)],
    ) -> Result<(), TypeError> {
        let member = constructors.iter().fold(
            Member::data(name, params, ty),
            |member, (constructor, ty)| member.with_constructor(constructor, ty.clone()),
        );
        self.declare(metas, &Group::of(member))
    }

    /// То же, но универсум семейства **выведен**, а не написан.
    ///
    /// Так объявляет элаборация: поверхностный язык уровня не пишет (§3.2),
    /// поэтому нуль в kind'е - умолчание, и семейство вправе подняться до
    /// универсумов своих полей (§10 вопрос 109). Ядро, вызванное напрямую,
    /// пишет уровень числом, и там он потолок.
    ///
    /// # Errors
    ///
    /// Те же, что у [`Signature::declare_data`].
    pub fn declare_data_inferred(
        &mut self,
        metas: &mut Metas,
        name: &str,
        params: u32,
        ty: Term,
        constructors: &[(&str, Term)],
    ) -> Result<(), TypeError> {
        let member = constructors.iter().fold(
            Member::data(name, params, ty).with_inferred_sort(),
            |member, (constructor, ty)| member.with_constructor(constructor, ty.clone()),
        );
        self.declare(metas, &Group::of(member))
    }

    /// Объявляет метку эффекта вместе с её операциями - одной группой (§3.4).
    ///
    /// # Errors
    ///
    /// Те же, что у [`Signature::declare`], плюс форма операции.
    pub fn declare_effect(
        &mut self,
        metas: &mut Metas,
        name: &str,
        params: u32,
        ty: Term,
        operations: &[(&str, Term, u32)],
        handlers: &[(&str, Term)],
    ) -> Result<(), TypeError> {
        let member = operations.iter().fold(
            Member::effect(name, params, ty),
            |member, (operation, ty, mults)| member.with_operation(operation, ty.clone(), *mults),
        );
        // Элиминаторы идут той же группой: их типы называют метку, а в
        // сигнатуре её ещё нет (§10 вопрос 50). Постулатами - развернуть их
        // нечем, пока evidence не подставлен.
        let group = handlers
            .iter()
            .fold(Group::of(member), |group, (name, ty)| {
                group.and(Member::definition(name, Mult::Many, ty.clone()))
            });
        self.declare(metas, &group)
    }
}

/// Что фаза A наработала по члену.
struct Checked {
    /// Объявление: тип с обобщённой арностью, роль, кратность.
    declaration: Definition,
    /// Отображение дырок в параметры уровня. `None` - арность объявлена, и
    /// обобщать нечего.
    generalization: Option<Generalization>,
    /// Обобщается ли семейство **после** своих конструкторов (§10 вопросы 53,
    /// 109). Решается один раз, в фазе A: дырки к фазе B1 успевают решиться,
    /// и пересчитанный там ответ разошёлся бы с принятым здесь.
    deferred: bool,
}

/// Приводит черновик к окончательной арности.
///
/// Объявленная остаётся как есть - её параметры уже стоят в терме. Выведенная
/// получается обобщением: нерешённые дырки становятся параметрами, и их число
/// и есть арность. Отображение возвращается вместе с объявлением, потому что по
/// телу обязана пройти **та же** подстановка, а не построенная заново.
fn generalize(
    metas: &mut Metas,
    arity: Arity,
    draft: Definition,
    released: Option<LevelMeta>,
) -> (Definition, Option<Generalization>) {
    if arity.is_declared() {
        return (draft, None);
    }
    let mut generalization = Generalization::default();
    if let Some(meta) = released {
        generalization.release(meta);
    }
    if arity.row_count() > 0 {
        // Row-параметры объявлены - обобщать их нечем и незачем: в терме они уже
        // стоят как `RowVar`. Дырка row, если она сюда всё же дошла,
        // отображению не подлежит - номера заняты, - и её ловит запечатывание
        // тем же отказом, что у объявленной арности.
        generalization.collect_levels(metas, &draft.ty);
    } else {
        generalization.collect_term(metas, &draft.ty);
    }
    let rows = if arity.row_count() > 0 {
        arity.row_count()
    } else {
        generalization.row_arity()
    };
    let declaration = Definition {
        level_arity: generalization.arity(),
        row_arity: rows,
        ty: generalization.apply_term(metas, &draft.ty),
        ..draft
    };
    (declaration, Some(generalization))
}

/// Дырка уровня у результата-универсума - признак алиаса типа (§10 вопрос 106).
///
/// Снимаются все связывания: `Twin : Type -> Type` кончается универсумом так
/// же, как `Number : Type`, и правило у них одно. Уже решённый уровень
/// признаком не является - там писать нечего, тело сравнится с написанным.
///
/// **Дырка, стоящая где-то ещё в том же типе, признаком не является тоже.** У
/// синонима, чей kind выведен по телу (`type Id a = a`), результат и домен -
/// одна и та же дырка, и она обязана стать параметром: `Id` полиморфен по
/// уровню, как всякое другое определение. Оставленная дыркой, она не решается
/// уже ничем. Различает эти два случая только вхождение: у написанного
/// `Type -> Type` дырки разные, потому что написаны они порознь.
fn alias_result(metas: &Metas, ty: &Term) -> Option<LevelMeta> {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    let Term::Universe(Level::Meta(meta)) = current else {
        return None;
    };
    let mut elsewhere = Generalization::default();
    let mut current = ty;
    while let Term::Pi(_, _, domain, row, codomain) = current {
        elsewhere.collect_term(metas, domain);
        elsewhere.collect_row(metas, row);
        current = codomain;
    }
    (!elsewhere.collected().contains(&Level::Meta(*meta))).then_some(*meta)
}

/// Обобщается ли семейство **после** своих конструкторов.
///
/// Два случая, и оба про одно: обобщать рано, потому что уровень семейства
/// решают конструкторы.
///
/// - **Индекс-универсум** (§10 вопрос 53): конструктор индекс инстанцирует и
///   вместе с ним заземляет уровень. `Expr Nat` требует `Nat : Type u`.
/// - **Собственный типовой параметр конструктора** (§10 вопрос 109): поднятое
///   имя приходит связыванием, чей домен - нерешённая дырка терма, и уровень
///   внутри неё обязан стать параметром **общим** с семейством. Порознь у
///   конструктора выходит на один параметр больше, чем у семейства.
///
/// Спрашивается по написанному в фазе A: к фазе B1 дырки успевают решиться, и
/// пересчитанный там ответ разошёлся бы с принятым здесь.
fn postponed(member: &Member, ty: &Term) -> bool {
    let Member::Data {
        params,
        constructors,
        ..
    } = member
    else {
        return false;
    };
    universe_indexed(ty, *params)
        || constructors
            .iter()
            .any(|constructor| lifts_a_type(&constructor.ty, *params))
}

/// Несёт ли конструктор собственный уровень сверх параметров семейства.
///
/// Три записи одного и того же, и все три измерены: поднятое имя
/// (`MkSome : a -> Some`) приходит связыванием, чей домен - **дырка терма**
/// (§4.1: решает её `is_type` уже при объявлении); написанное `(0 a : Type)` -
/// готовым универсумом; поле-семейство (`Hold : (Nat -> Type) -> Held`) несёт
/// универсум внутри своего типа, а связывания не заводит вовсе.
///
/// Поэтому ищется не форма связывания, а сам уровень: универсум либо
/// нерешённая дырка где угодно **правее** параметров. Параметры пропускаются
/// потому, что их семейство уже обобщило: `Cons : a -> List a -> List a` под
/// `data List (a : Type)` собственного уровня не несёт.
fn lifts_a_type(ty: &Term, params: u32) -> bool {
    let mut current = ty;
    let mut passed = 0;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        if passed >= params && carries_a_level(domain) {
            return true;
        }
        passed += 1;
        current = codomain;
    }
    false
}

/// Есть ли в терме универсум или нерешённая дырка.
fn carries_a_level(term: &Term) -> bool {
    match term {
        Term::Universe(_) | Term::RowKind(_) | Term::Meta(_) => true,
        Term::App(callee, argument) => carries_a_level(callee) || carries_a_level(argument),
        Term::Lam(_, _, body) => carries_a_level(body),
        Term::Pi(_, _, domain, _, codomain) => carries_a_level(domain) || carries_a_level(codomain),
        Term::Let(_, _, ty, value, body) => {
            carries_a_level(ty) || carries_a_level(value) || carries_a_level(body)
        }
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().any(|field| carries_a_level(&field.ty))
        }
        Term::Project(record, _) => carries_a_level(record),
        _ => false,
    }
}

/// Есть ли у семейства индекс, тип которого - универсум (§10 вопрос 53).
///
/// Смотрятся только индексы: параметр конструктор **повторяет**, а индекс
/// **инстанцирует**, и вместе с индексом инстанцируется его уровень.
/// Семейства с индексом-`Nat` это не касается вовсе, поэтому и путь
/// добавочный - он срабатывает ровно там, где сегодня отказ.
fn universe_indexed(ty: &Term, params: u32) -> bool {
    let mut current = ty;
    let mut passed = 0;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        if passed >= params && matches!(&**domain, Term::Universe(_)) {
            return true;
        }
        passed += 1;
        current = codomain;
    }
    false
}

/// Ставит семейству другой универсум, оставляя телескоп как есть.
fn resorted(ty: &Term, sort: &Level) -> Term {
    match ty {
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            Rc::clone(domain),
            row.clone(),
            Rc::new(resorted(codomain, sort)),
        ),
        Term::Universe(_) => Term::Universe(sort.clone()),
        other => other.clone(),
    }
}

/// Переписывает аргументы уровня у ссылок на `name`.
///
/// До обобщения они инертны: подставлять их некуда, параметров у семейства
/// ещё нет. После - обязаны быть ровно его параметрами, и число их обязано
/// сойтись с арностью, иначе ядро ответит `LevelArity` на собственной ссылке.
fn relevelled(term: &Term, name: &Name, levels: &Rc<[Level]>) -> Term {
    let recur = |inner: &Rc<Term>| Rc::new(relevelled(inner, name, levels));
    match term {
        Term::Const(found, _, args) if found == name => {
            Term::Const(Rc::clone(found), Rc::clone(levels), args.clone())
        }
        Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
        Term::Lam(mult, bound, body) => Term::Lam(*mult, Rc::clone(bound), recur(body)),
        Term::Pi(binder, bound, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(bound),
            recur(domain),
            row.map(|argument| relevelled(argument, name, levels)),
            recur(codomain),
        ),
        Term::Let(mult, bound, ty, value, body) => Term::Let(
            *mult,
            Rc::clone(bound),
            recur(ty),
            recur(value),
            recur(body),
        ),
        other => other.clone(),
    }
}

/// Все имена, которые занимает группа: члены и их конструкторы.
fn group_names(group: &Group) -> impl Iterator<Item = &Name> {
    group
        .members()
        .iter()
        .flat_map(|member| std::iter::once(member.name()).chain(member_names(member)))
}

/// Объявления внутри члена: конструкторы семейства либо операции эффекта.
fn member_decls(member: &Member) -> impl Iterator<Item = &MemberDecl> {
    let inner: &[MemberDecl] = match member {
        Member::Data { constructors, .. } => constructors,
        Member::Effect { operations, .. } => operations,
        Member::Definition { .. } => &[],
    };
    inner.iter()
}

/// Их имена.
fn member_names(member: &Member) -> impl Iterator<Item = &Name> {
    member_decls(member).map(|decl| &decl.name)
}

/// Конструкторы члена - только они: фаза C меряет позитивность, а у метки
/// аналога ей нет (§3.4). Метка не тип и полем стоять не может, поэтому
/// рекурсии по объявляемому эффекту не бывает.
fn constructor_decls(member: &Member) -> impl Iterator<Item = &MemberDecl> {
    let constructors: &[MemberDecl] = match member {
        Member::Data { constructors, .. } => constructors,
        Member::Definition { .. } | Member::Effect { .. } => &[],
    };
    constructors.iter()
}

/// Номер члена или конструктора в объявлении - для кадра маршрута.
///
/// Насыщение вместо паники: группа из 4 миллиардов членов - не тот случай,
/// ради которого проверка типов падает, а маршрут в ней всё равно нечитаем.
fn at(index: usize) -> u32 {
    u32::try_from(index).unwrap_or(u32::MAX)
}
