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
//! [`Signature::declare`] (§10 вопрос 50). Члены двух видов - определение и
//! индуктивное семейство со своими конструкторами; группа из одного члена и
//! есть обычное определение. Промежуточных наблюдаемых состояний сигнатуры
//! нет: снаружи группа либо добавлена целиком, либо не добавлена вовсе.
//!
//! Проверка идёт в четыре фазы, и порядок в них существенный:
//!
//! - **(A)** типы членов - против сигнатуры **без** группы. Здесь ловится
//!   `f : f -> Nat`: тип, ссылающийся на определяемое, цикличен. Цена правила -
//!   §10 вопрос 64: сосед в типе члена по той же причине не пишется.
//! - **(B1)** типы конструкторов - против сигнатуры **с** типами членов.
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
    check_declaration, data_sort, unsolved_in_definition, unsolved_term_in_definition,
};
use crate::error::ErrorKind;
use crate::eval::eval;
use crate::level::Level;
use crate::meta::{Generalization, Metas, zonk_term};
use crate::mult::Mult;
use crate::term::{Name, Rows, Term};
use crate::value::{Env, Value};

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
}

/// Что фаза B2 узнала о теле: сам терм и носители его параметров.
type CheckedBody = (Term, Rc<[Mult]>);

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
}

impl Definition {
    /// Тип, инстанцированный аргументами уровня.
    #[must_use]
    pub fn instantiate_type(&self, levels: &[Level]) -> Rc<Value> {
        eval(&Env::default(), &self.ty.substitute_levels(levels))
    }

    /// Тело, инстанцированное аргументами уровня. `None` у постулата.
    #[must_use]
    pub fn instantiate_body(&self, levels: &[Level]) -> Option<Rc<Value>> {
        let body = self.body.as_ref()?;
        Some(eval(&Env::default(), &body.substitute_levels(levels)))
    }

    /// Число параметров и универсум тип-формера. `None` - не семейство.
    #[must_use]
    pub fn data_shape(&self) -> Option<(u32, &Level)> {
        match &self.kind {
            DefinitionKind::Data { params, sort, .. } => Some((*params, sort)),
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    /// Нерешённые дырки становятся параметрами, и их число и есть арность.
    /// Это implicit universe polymorphism со стороны определения (§3.2).
    Inferred,
    /// Арность написана, параметры стоят в терме как [`crate::level::LevelVar`]
    /// и [`crate::row::RowVar`]. Дырка, оставшаяся при такой записи, - отказ:
    /// обобщать её некуда.
    Declared {
        /// Параметров уровня.
        levels: u32,
        /// Параметров row.
        rows: u32,
    },
}

impl Arity {
    /// Объявленная арность уровней.
    ///
    /// У выведенной она нулевая: параметров во входном терме нет вовсе, только
    /// дырки, и `check_level_scope` этим пользуется - параметр уровня там
    /// означал бы, что вызывающий смешал две записи.
    fn declared(self) -> u32 {
        match self {
            Self::Declared { levels, .. } => levels,
            Self::Inferred => 0,
        }
    }

    /// То же для row.
    fn declared_rows(self) -> u32 {
        match self {
            Self::Declared { rows, .. } => rows,
            Self::Inferred => 0,
        }
    }
}

/// Конструктор в объявлении семейства.
#[derive(Clone, Debug)]
pub struct ConstructorDecl {
    /// Имя.
    pub name: Name,
    /// Тип. Проверяется в фазе B - против сигнатуры, где тип-формер уже есть.
    pub ty: Term,
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
        constructors: Vec<ConstructorDecl>,
    },
}

impl Member {
    /// Определение с выведенной арностью.
    #[must_use]
    pub fn definition(name: &str, mult: Mult, ty: Term) -> Self {
        Self::Definition {
            name: name.into(),
            mult,
            arity: Arity::Inferred,
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
            Self::Data { .. } => debug_assert!(false, "запечатывается определение, а не семейство"),
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
            arity: Arity::Inferred,
            ty,
            constructors: Vec::new(),
        }
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
            Self::Definition { arity, .. } | Self::Data { arity, .. } => {
                *arity = Arity::Declared { levels, rows };
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
            constructors.push(ConstructorDecl {
                name: name.into(),
                ty,
            });
        }
        self
    }

    /// Имя члена.
    #[must_use]
    pub fn name(&self) -> &Name {
        match self {
            Self::Definition { name, .. } | Self::Data { name, .. } => name,
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
        let levels: Rc<[Level]> = (0..levels).map(|_| metas.fresh_level()).collect();
        let rows = Rows::new((0..rows).map(|_| metas.fresh_row()));
        Some(Term::Const(name.into(), levels, rows))
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
        let outcome = self.declare_fresh(metas, group);
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

        // (A) типы членов против сигнатуры без группы.
        let mut checked = Vec::with_capacity(members.len());
        for (index, member) in members.iter().enumerate() {
            checked.push(
                self.check_member_type(metas, member)
                    .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?,
            );
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
        let mut constructors = Vec::with_capacity(members.len());
        for (index, (member, checked)) in members.iter().zip(&checked).enumerate() {
            constructors.push(
                self.check_member_constructors(metas, member, checked)
                    .map_err(|error| error.in_frame(Frame::MemberType(at(index))))?,
            );
        }
        for (member, declarations) in members.iter().zip(&constructors) {
            for (name, declaration) in constructor_names(member).zip(declarations) {
                self.definitions
                    .insert(Rc::clone(name), declaration.clone());
            }
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
            if let (Some((term, carriers)), Some(stored)) =
                (body, self.definitions.get_mut(member.name()))
            {
                stored.body = Some(term);
                stored.carriers = carriers;
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
        for (index, ((member, family), declarations)) in
            members.iter().zip(&checked).zip(&constructors).enumerate()
        {
            for (slot, (declared, constructor)) in
                constructor_decls(member).zip(declarations).enumerate()
            {
                check_constructor_content(
                    self,
                    metas,
                    &declared.name,
                    member.name(),
                    &families,
                    &family.declaration,
                    &constructor.ty,
                )
                .map_err(|error| {
                    error
                        .in_frame(Frame::Constructor(at(slot)))
                        .in_frame(Frame::MemberType(at(index)))
                })?;
            }
        }
        // Вердикт тотальности считается **до** зонканья, и это названная
        // граница, а не выбор: после него рекурсия метода инстанса приходит
        // голым именем внутри подставленной записи-словаря, и структурная
        // проверка видит вызов без аргументов, то есть отвергает всякий
        // рекурсивный метод. До зонканья она не видит её вовсе - словарь стоит
        // дыркой, а `Meta` здесь инертна. Обе половины неверны, и выбирается
        // менее вредная; разбор - в §10 и ревью 2026-09-02.
        self.settle_totality(group);

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
            Member::Data {
                name, arity, ty, ..
            } => (name, Mult::Many, *arity, ty),
        };

        let mut draft = Definition {
            mult,
            opaque: matches!(member, Member::Definition { opaque: true, .. }),
            level_arity: arity.declared(),
            row_arity: arity.declared_rows(),
            // Носители неизвестны, пока тело не проверено; фаза B2 их уточнит,
            // а постулат так и останется с `ω` - консервативным ответом.
            carriers: crate::carrier::unknown(ty),
            ty: ty.clone(),
            body: None,
            kind: DefinitionKind::Regular,
            total: true,
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
        let (mut declaration, generalization) = generalize(metas, arity, draft);

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
        Ok(Checked {
            declaration,
            generalization,
        })
    }

    /// Фаза B1 для одного члена: типы его конструкторов. У определения их нет.
    fn check_member_constructors(
        &self,
        metas: &mut Metas,
        member: &Member,
        checked: &Checked,
    ) -> Result<Vec<Definition>, TypeError> {
        let Member::Data {
            name,
            arity,
            constructors,
            ..
        } = member
        else {
            return Ok(Vec::new());
        };
        let mut declarations = Vec::with_capacity(constructors.len());
        for (slot, constructor) in constructors.iter().enumerate() {
            declarations.push(
                self.check_constructor_type(metas, name, *arity, &checked.declaration, constructor)
                    .map_err(|error| error.in_frame(Frame::Constructor(at(slot))))?,
            );
        }
        Ok(declarations)
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
        let carriers = check_body(self, metas, name, &definition)?;
        Ok(Some((body, carriers)))
    }

    /// Фаза B1 для конструктора: тип, арность и форма.
    fn check_constructor_type(
        &self,
        metas: &mut Metas,
        data: &Name,
        arity: Arity,
        family: &Definition,
        constructor: &ConstructorDecl,
    ) -> Result<Definition, TypeError> {
        let draft = Definition {
            mult: Mult::Many,
            // Запись арности у конструктора та же, что у семейства: объявленную
            // обобщать нечем - её параметры уже стоят в типе как `LevelVar`, - и
            // обобщение свело бы её к нулю, отвергнув всякий полиморфный
            // конструктор объявленного семейства.
            level_arity: arity.declared(),
            row_arity: arity.declared_rows(),
            // Конструктор кладёт значение ровно однажды, поэтому носителю его
            // параметра ограничивать нечего; держателя ресурсного поля
            // проверяет отдельное правило (§3.3, вопрос 77).
            carriers: crate::carrier::stored(&constructor.ty),
            opaque: false,
            ty: constructor.ty.clone(),
            body: None,
            kind: DefinitionKind::Constructor {
                data: Rc::clone(data),
            },
            total: true,
        };
        check_declaration(self, metas, &constructor.name, &draft)?;
        let (declaration, _) = generalize(metas, arity, draft);

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
        for constructor in constructor_names(member) {
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

        self.definitions.insert(Rc::clone(name), definition);
        Ok(())
    }

    /// Вердикт тотальности по совместному графу вызовов группы.
    ///
    /// Неподвижная точка сверху: члены входят тотальными, и проход повторяется,
    /// пока кто-то понижается. Для группы из одного члена это ровно один проход
    /// и тот же ответ, что раньше; для взаимной рекурсии - единственный
    /// корректный способ, потому что вердикт члена зависит от вердиктов
    /// соседей.
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
            crate::check::check_body(self, metas, name, &checked)
                .map_err(|error| error.in_frame(Frame::MemberBody(at(index))))?;
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
    fn call_cycles(&self, group: &Group) -> HashMap<Name, Vec<Name>> {
        let names: Vec<Name> = group_names(group).cloned().collect();
        let mut reaches: HashMap<Name, Vec<Name>> = HashMap::new();
        for name in &names {
            let direct = self
                .definitions
                .get(name)
                .and_then(|it| it.body.as_ref())
                .map_or_else(Vec::new, |body| crate::total::calls_within(&names, body));
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

    fn settle_totality(&mut self, group: &Group) {
        let cycles = self.call_cycles(group);
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
                if !crate::total::is_total(self, name, cycle, &definition) {
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
    ) -> Result<(), TypeError> {
        self.define_inferred(metas, name, mult, ty, None)
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
}

/// Что фаза A наработала по члену.
struct Checked {
    /// Объявление: тип с обобщённой арностью, роль, кратность.
    declaration: Definition,
    /// Отображение дырок в параметры уровня. `None` - арность объявлена, и
    /// обобщать нечего.
    generalization: Option<Generalization>,
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
) -> (Definition, Option<Generalization>) {
    match arity {
        Arity::Declared { .. } => (draft, None),
        Arity::Inferred => {
            let mut generalization = Generalization::default();
            generalization.collect_term(metas, &draft.ty);
            let declaration = Definition {
                level_arity: generalization.arity(),
                row_arity: generalization.row_arity(),
                ty: generalization.apply_term(metas, &draft.ty),
                ..draft
            };
            (declaration, Some(generalization))
        }
    }
}

/// Все имена, которые занимает группа: члены и их конструкторы.
fn group_names(group: &Group) -> impl Iterator<Item = &Name> {
    group
        .members()
        .iter()
        .flat_map(|member| std::iter::once(member.name()).chain(constructor_names(member)))
}

/// Конструкторы члена; у определения их нет.
fn constructor_decls(member: &Member) -> impl Iterator<Item = &ConstructorDecl> {
    let constructors: &[ConstructorDecl] = match member {
        Member::Data { constructors, .. } => constructors,
        Member::Definition { .. } => &[],
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

/// Имена конструкторов члена.
fn constructor_names(member: &Member) -> impl Iterator<Item = &Name> {
    constructor_decls(member).map(|constructor| &constructor.name)
}
