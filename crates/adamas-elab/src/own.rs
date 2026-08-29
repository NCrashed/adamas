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

    /// Чем это объявляется в исходнике.
    #[must_use]
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Unique => "unique data",
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
pub struct Owned {
    types: HashMap<Symbol, Ownership>,
    /// Имя деструктора ресурсного типа. У `unique` его нет по определению.
    drops: HashMap<Symbol, Symbol>,
}

impl Owned {
    /// Объявляет тип уникальным или ресурсным.
    pub fn declare(&mut self, name: &Symbol, how: Ownership) {
        self.types.insert(name.clone(), how);
    }

    /// Называет деструктор ресурсного типа.
    pub fn destroys(&mut self, name: &Symbol, drop: &Symbol) {
        self.drops.insert(name.clone(), drop.clone());
    }

    /// Как объявлен тип, стоящий головой написанного.
    #[must_use]
    pub fn of(&self, ty: &Expr) -> Option<Ownership> {
        self.types.get(head(ty)?).copied()
    }

    /// Ресурс, деструктор которого уже назван так.
    ///
    /// Имя деструктора одно на модуль: пространств имён ещё нет (§4.8), и
    /// второй `drop` столкнулся бы с первым.
    #[must_use]
    pub fn named(&self, drop: &str) -> Option<&Symbol> {
        self.drops
            .iter()
            .find(|(_, it)| &***it == drop)
            .map(|(data, _)| data)
    }

    /// Объявлен ли тип с этим именем владеемым.
    #[must_use]
    pub fn owns(&self, name: &str) -> bool {
        self.types.contains_key(name)
    }

    /// Чем объявлен тип с этим именем.
    ///
    /// Отвечает и во время объявления самого типа: маркер ставится до
    /// элаборации конструкторов, потому что поле собственного типа получает
    /// кратность тем же правилом, что и всякое другое связывание.
    #[must_use]
    pub fn how(&self, name: &str) -> Option<Ownership> {
        self.types.get(name).copied()
    }

    /// Деструктор типа, стоящего головой написанного.
    #[must_use]
    pub fn destructor(&self, ty: &Expr) -> Option<&Symbol> {
        self.drops.get(head(ty)?)
    }

    /// То же по имени типа - для домена, снятого с уже собранного терма.
    #[must_use]
    pub fn destructor_of(&self, data: &str) -> Option<&Symbol> {
        self.drops.get(data)
    }

    /// Сколько типов с владением объявлено.
    #[must_use]
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Пуста ли таблица.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
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
