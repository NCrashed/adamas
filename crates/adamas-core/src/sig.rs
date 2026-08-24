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

use crate::check::{TypeError, check_definition, unsolved_in_definition};
use crate::eval::eval;
use crate::level::Level;
use crate::meta::{Generalization, Metas};
use crate::mult::Mult;
use crate::term::{Name, Term};
use crate::value::{Env, Value};

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
    };

    match unsolved_in_definition(metas, &definition) {
        Some(meta) => Err(TypeError::UnsolvedDefinitionLevel {
            name: Rc::clone(name),
            meta,
        }),
        None => Ok(definition),
    }
}
