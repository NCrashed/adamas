//! Глобальный контекст: определения верхнего уровня.
//!
//! До этого модуля ядро умело только замкнутые термы сами по себе. Определения
//! дают две вещи, без которых Фаза 1 не заканчивается: universe polymorphism
//! (параметры уровня принадлежат определению, а не терму) и место, куда лягут
//! индуктивные типы - data-декларация тоже определение.
//!
//! # Ациклично по построению
//!
//! Определение может ссылаться только на уже добавленные. Рекурсии в ядре нет,
//! и δ-разворот ([`crate::conv`]) поэтому заведомо завершается. Когда появится
//! рекурсия, это ограничение придётся снимать вместе с проверкой тотальности
//! (§9, `@total`).

use std::collections::HashMap;
use std::rc::Rc;

use crate::check::{
    TypeError, check_constructor, check_definition, data_sort, unsolved_in_definition,
};
use crate::eval::eval;
use crate::level::Level;
use crate::meta::{Generalization, Metas};
use crate::mult::Mult;
use crate::term::{Name, Term};
use crate::value::{Env, Value};

/// Чем определение является помимо "имя с типом и, может быть, телом".
///
/// Индуктивный тип и его конструкторы - это те же определения без тела, но
/// проверяются они строже и связаны друг с другом, а элиминация (следующий
/// срез) обязана уметь их различать: сводить `case` можно только по
/// конструктору, а не по произвольному постулату.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionKind {
    /// Обычное определение или постулат.
    Regular,
    /// Тип-формер индуктивного типа. Список конструкторов пополняется по мере
    /// их объявления и задаёт порядок ветвей будущего `case`.
    Data {
        /// Конструкторы в порядке объявления.
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
    /// Тип. Замкнут по локальным переменным, открыт по параметрам уровня.
    pub ty: Term,
    /// Тело. `None` - постулат: тип есть, вычислять нечего.
    pub body: Option<Term>,
    /// Индуктивная роль, если она есть.
    pub kind: DefinitionKind,
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

    /// Проверяет определение и добавляет его.
    ///
    /// Проверка идёт против сигнатуры **без** добавляемого имени, поэтому
    /// ссылаться на себя определение не может - см. заголовок модуля.
    ///
    /// # Errors
    ///
    /// Имя уже занято; кратность `1`; параметр уровня вне объявленной арности;
    /// тип не является типом; тело не соответствует типу.
    pub fn define(
        &mut self,
        name: &str,
        mult: Mult,
        level_arity: u32,
        ty: Term,
        body: Option<Term>,
    ) -> Result<(), TypeError> {
        let name: Name = name.into();
        if self.definitions.contains_key(&name) {
            return Err(TypeError::DuplicateDefinition { name });
        }
        let definition = Definition {
            mult,
            level_arity,
            ty,
            body,
            kind: DefinitionKind::Regular,
        };
        // Хранилище своё: арность объявлена, значит выводить нечего, а
        // метапеременные живут ровно на время одной проверки. Заимствование
        // `&self` заканчивается до вставки.
        let mut metas = Metas::default();
        check_definition(self, &mut metas, &name, &definition)?;
        if let Some(meta) = unsolved_in_definition(&metas, &definition) {
            return Err(TypeError::UnsolvedDefinitionLevel { name, meta });
        }
        self.definitions.insert(name, definition);
        Ok(())
    }

    /// Проверяет определение и добавляет его, **выводя арность** из того, что
    /// осталось нерешённым.
    ///
    /// Тип и тело пишутся с дырками ([`Metas::fresh_level`]), а не с
    /// параметрами: параметры - результат, а не вход. Дырки, решённые по ходу
    /// проверки, исчезают; оставшиеся становятся параметрами уровня, и их число
    /// и есть арность.
    ///
    /// Это вторая половина implicit universe polymorphism: первая - вывод
    /// аргументов в местах использования ([`Signature::instantiate`]).
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::define`], плюс дырка, оставшаяся **только в
    /// теле**: параметром она стать не может, потому что в месте использования
    /// аргументы уровня подставляются по типу, и заполнить её нечем.
    pub fn define_inferred(
        &mut self,
        name: &str,
        mult: Mult,
        metas: &mut Metas,
        ty: Term,
        body: Option<Term>,
    ) -> Result<(), TypeError> {
        let name: Name = name.into();
        if self.definitions.contains_key(&name) {
            return Err(TypeError::DuplicateDefinition { name });
        }

        // Арность нулевая: на входе параметров нет вовсе, только дырки.
        // `check_level_scope` этим и пользуется - параметр уровня во входном
        // типе означал бы, что вызывающий смешал две записи.
        let draft = Definition {
            mult,
            level_arity: 0,
            ty,
            body,
            kind: DefinitionKind::Regular,
        };
        check_definition(self, metas, &name, &draft)?;

        let definition = generalize(metas, &name, &draft)?;
        self.definitions.insert(name, definition);
        Ok(())
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
        let arity = self.lookup(name)?.level_arity;
        let levels: Rc<[Level]> = (0..arity).map(|_| metas.fresh_level()).collect();
        Some(Term::Const(name.into(), levels))
    }

    /// Объявляет индуктивный тип - тип-формер без конструкторов.
    ///
    /// Конструкторы добавляются потом, по одному
    /// ([`Signature::declare_constructor`]): каждый проверяется против уже
    /// объявленного типа, и до объявления самого типа проверять было бы не
    /// против чего. Арность уровня выводится, как у
    /// [`Signature::define_inferred`].
    ///
    /// Кратность у тип-формера `ω`: он живёт и в позиции типа (там `σ = 0`, и
    /// `ω` это допускает), и как обычное значение - §3.2 разрешает `List Type`.
    ///
    /// `params` - сколько первых связываний считать параметрами. Разделение
    /// нужно уже здесь, а не в элаборации: параметры выведены из-под
    /// универсумной проверки конструкторов, иначе `List : Type u -> Type u` не
    /// объявить - его параметр живёт в `Type (u+1)`, то есть заведомо выше
    /// самого `List`.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::define_inferred`], плюс: связываний меньше,
    /// чем параметров; тип-формер не заканчивается универсумом.
    pub fn declare_data(
        &mut self,
        name: &str,
        params: u32,
        metas: &mut Metas,
        ty: Term,
    ) -> Result<(), TypeError> {
        let name: Name = name.into();
        let mut draft = self.checked_draft(&name, metas, ty)?;
        // Универсум берётся из уже обобщённого типа: до обобщения на его месте
        // стоит дырка, а конструкторы будут сравниваться с параметром уровня.
        let sort = data_sort(&name, params, &draft.ty)?;
        draft.kind = DefinitionKind::Data {
            constructors: Vec::new(),
            params,
            sort,
        };
        self.definitions.insert(name, draft);
        Ok(())
    }

    /// Объявляет конструктор уже существующего индуктивного типа.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::define_inferred`], плюс: имя не индуктивный
    /// тип; результат не тот тип; нарушена строгая позитивность; поле живёт
    /// выше универсума типа.
    pub fn declare_constructor(
        &mut self,
        data: &str,
        name: &str,
        metas: &mut Metas,
        ty: Term,
    ) -> Result<(), TypeError> {
        let data: Name = data.into();
        let name: Name = name.into();
        let mut draft = self.checked_draft(&name, metas, ty)?;

        // Обычная машинерия проверила тип и вывела арность; сверх неё - только
        // то, что отличает конструктор от постулата похожей формы.
        let mut fresh = Metas::default();
        check_constructor(self, &mut fresh, &name, &data, &draft.ty)?;

        draft.kind = DefinitionKind::Constructor {
            data: Rc::clone(&data),
        };
        self.definitions.insert(Rc::clone(&name), draft);

        // Порядок объявления задаёт порядок ветвей будущего `case`.
        if let Some(DefinitionKind::Data { constructors, .. }) =
            self.definitions.get_mut(&data).map(|entry| &mut entry.kind)
        {
            constructors.push(name);
        }
        Ok(())
    }

    /// Конструкторы индуктивного типа в порядке объявления.
    #[must_use]
    pub fn constructors(&self, data: &str) -> Option<&[Name]> {
        match &self.lookup(data)?.kind {
            DefinitionKind::Data { constructors, .. } => Some(constructors),
            _ => None,
        }
    }

    /// Проверяет постулат и возвращает его, **не** добавляя в сигнатуру.
    ///
    /// Общая часть объявления типа и конструктора: и то и другое - постулат с
    /// выведенной арностью, к которому потом приписывается роль.
    fn checked_draft(
        &mut self,
        name: &Name,
        metas: &mut Metas,
        ty: Term,
    ) -> Result<Definition, TypeError> {
        if self.definitions.contains_key(name) {
            return Err(TypeError::DuplicateDefinition {
                name: Rc::clone(name),
            });
        }
        self.postulate_inferred(name, Mult::Many, metas, ty)?;
        Ok(self
            .definitions
            .remove(name)
            .unwrap_or_else(|| unreachable!("постулат только что добавлен")))
    }

    /// Постулат с выведенной арностью - [`Signature::define_inferred`] без тела.
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::define_inferred`].
    pub fn postulate_inferred(
        &mut self,
        name: &str,
        mult: Mult,
        metas: &mut Metas,
        ty: Term,
    ) -> Result<(), TypeError> {
        self.define_inferred(name, mult, metas, ty, None)
    }

    /// Постулат: тип без тела. Удобная обёртка над [`Signature::define`].
    ///
    /// # Errors
    ///
    /// То же, что у [`Signature::define`].
    pub fn postulate(
        &mut self,
        name: &str,
        mult: Mult,
        level_arity: u32,
        ty: Term,
    ) -> Result<(), TypeError> {
        self.define(name, mult, level_arity, ty, None)
    }
}

/// Превращает нерешённые дырки определения в параметры уровня.
///
/// Собирает дырки **из типа** - именно он определяет, что подставится в месте
/// использования. Тело перенумеровывается той же таблицей, и если в нём
/// осталась дырка, которой в типе не было, это отказ: аргументы уровня
/// подставляются по типу, и заполнить её было бы нечем.
fn generalize(metas: &Metas, name: &Name, draft: &Definition) -> Result<Definition, TypeError> {
    let mut generalization = Generalization::default();
    generalization.collect_term(metas, &draft.ty);

    let definition = Definition {
        mult: draft.mult,
        level_arity: generalization.arity(),
        ty: generalization.apply_term(metas, &draft.ty),
        body: draft
            .body
            .as_ref()
            .map(|body| generalization.apply_term(metas, body)),
        kind: draft.kind.clone(),
    };

    match unsolved_in_definition(metas, &definition) {
        Some(meta) => Err(TypeError::UnsolvedDefinitionLevel {
            name: Rc::clone(name),
            meta,
        }),
        None => Ok(definition),
    }
}
