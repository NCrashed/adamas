//! Типы, объявленные `unique data` и `resource` (§3.3).
//!
//! # Почему таблица здесь, а не в сигнатуре
//!
//! §3.3 говорит прямо: `unique` и `resource` - поверхностные конструкции, а не
//! расширение ядра QTT. Ядро не знает о них ничего и знать не обязано: всё,
//! что они делают, - назначают связыванию кратность, которую программист мог
//! бы написать сам. Положи мы маркер в `Signature`, ядро начало бы носить
//! surface-сведения, которыми само не пользуется.
//!
//! Хранилище поэтому идёт рядом с [`Metas`](adamas_core::meta::Metas) - тем же
//! способом, что и оно: заводит его вызывающий, а прогон элаборации принимает.
//! Когда появится prelude, таблица приедет вместе с сигнатурой, а не будет
//! собрана заново.
//!
//! # Что распознаётся
//!
//! Голова написанного типа - и только она. `(h : File)` узнаётся, `(h : Maybe
//! File)` нет: `Maybe File` - обычный тип, чьё поле ресурсно, и отвечает за
//! него рекурсия `drop` по полям (§3.3), а не кратность связывания.
//!
//! **Названная цена: определение, разворачивающееся в ресурс, не узнаётся.**
//! `Handle : Type` с телом `File` даёт связыванию `ω`, потому что голова
//! написанного - `Handle`. Смотреть сквозь δ элаборация не может: она не
//! типонаправленная и значений не вычисляет. Закроется это тем же, чем
//! закроются остальные такие места, - Фазой 3, где у элаборации появится
//! доступ к типам.

use std::collections::HashMap;

use adamas_parser::ast::{Expr, ExprKind, Symbol};

/// Чем тип объявлен.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ownership {
    /// `unique data T`: связывания линейны, деструктора нет, память
    /// освобождается статически.
    Unique,
    /// `resource T`: то же плюс `drop`, вызываемый на выходе из scope.
    Resource,
}

impl Ownership {
    /// Как это называется в сообщении.
    fn face(self) -> &'static str {
        match self {
            Self::Unique => "unique",
            Self::Resource => "resource",
        }
    }
}

impl std::fmt::Display for Ownership {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.face())
    }
}

/// Таблица типов с владением.
#[derive(Clone, Debug, Default)]
pub struct Owned(HashMap<Symbol, Ownership>);

impl Owned {
    /// Объявляет тип уникальным или ресурсным.
    pub fn declare(&mut self, name: &Symbol, how: Ownership) {
        self.0.insert(name.clone(), how);
    }

    /// Как объявлен тип, стоящий головой написанного.
    #[must_use]
    pub fn of(&self, ty: &Expr) -> Option<Ownership> {
        self.0.get(head(ty)?).copied()
    }

    /// Сколько типов с владением объявлено.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Пуста ли таблица.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Имя в голове применения: `Array n a` - это `Array`.
fn head(expr: &Expr) -> Option<&Symbol> {
    match &expr.kind {
        ExprKind::Name(name) => Some(&name.text),
        ExprKind::App(callee, _) => head(callee),
        _ => None,
    }
}
