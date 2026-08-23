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

use crate::check::{TypeError, check_definition};
use crate::eval::eval;
use crate::level::Level;
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
        // Заимствование `&self` заканчивается здесь, до вставки.
        let definition = check_definition(self, &name, mult, level_arity, ty, body)?;
        self.definitions.insert(name, definition);
        Ok(())
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
