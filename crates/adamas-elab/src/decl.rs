//! Объявления модуля в группы сигнатуры.
//!
//! # Сборка
//!
//! Сигнатура и клаузы приходят из парсера отдельными членами блока: дерево -
//! образ исходника, а не полуэлаборированная форма. Здесь они соединяются.
//! Сигнатура без клауз - постулат: §4.1 пишет так примитивы (`openFile : …`).
//! Клаузы без сигнатуры - отказ: тип нужен раньше тела, по нему снимается
//! телескоп аргументов, а из него - арность и типы колонок разбора.
//!
//! # Единица - группа из одного члена
//!
//! `mutual` - Фаза 3, поэтому каждое объявление объявляется своей группой.
//! Механизм при этом тот же (§10 вопрос 50): группа из одного члена и есть
//! обычное определение.

use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::meta::{Generalization, Metas};
use adamas_core::mult::Mult;
use adamas_core::pattern::compile;
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::Term;
use adamas_parser::ast::{self, DeclKind, Module, Symbol};

use crate::error::{ElabError, Missing};
use crate::expr::Elaborator;

/// Сигнатура, ожидающая клауз.
struct Pending {
    name: Symbol,
    ty: Term,
    span: Span,
}

/// Элаборирует модуль в новую сигнатуру.
///
/// Хранилище дырок заводится здесь: прогон элаборации - это модуль целиком
/// (§10 вопрос 51).
///
/// # Errors
///
/// Любой отказ элаборации, сборки клауз или проверки типов.
pub fn elaborate(module: &Module) -> Result<Signature, ElabError> {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    elaborate_into(module, &mut signature, &mut metas)?;
    Ok(signature)
}

/// То же, но поверх уже собранной сигнатуры - так к модулю приставляется
/// prelude, когда он появится.
///
/// # Errors
///
/// То же, что у [`elaborate`].
pub fn elaborate_into(
    module: &Module,
    signature: &mut Signature,
    metas: &mut Metas,
) -> Result<(), ElabError> {
    let mut pending: Option<Pending> = None;
    for decl in &module.decls {
        match &decl.kind {
            DeclKind::Signature { name, ty } => {
                postulate(signature, metas, pending.take())?;
                let ty = Elaborator::new(signature, metas).expr(ty, Mult::Many)?;
                pending = Some(Pending {
                    name: Rc::clone(&name.text),
                    ty,
                    span: decl.span,
                });
            }
            DeclKind::Clauses { name, clauses } => {
                let Some(declared) = pending.take().filter(|it| it.name == name.text) else {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&name.text),
                        span: decl.span,
                    });
                };
                define(signature, metas, &declared, clauses, decl.span)?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take())?;
                declare_data(signature, metas, data, decl.span)?;
            }
            DeclKind::Resource(_) => {
                return Err(ElabError::Missing {
                    what: Missing::Resource,
                    span: decl.span,
                });
            }
        }
    }
    postulate(signature, metas, pending)
}

/// Сигнатура, за которой не последовало клауз, - постулат.
fn postulate(
    signature: &mut Signature,
    metas: &mut Metas,
    pending: Option<Pending>,
) -> Result<(), ElabError> {
    let Some(pending) = pending else {
        return Ok(());
    };
    signature
        .postulate_inferred(metas, &pending.name, Mult::Many, pending.ty)
        .map_err(|error| ElabError::Core {
            error: Box::new(error),
            span: pending.span,
        })
}

/// Определение: клаузы собираются в дерево разбора, дерево уходит в сигнатуру.
fn define(
    signature: &mut Signature,
    metas: &mut Metas,
    declared: &Pending,
    clauses: &[ast::Clause],
    span: Span,
) -> Result<(), ElabError> {
    // Рекурсивная ссылка обязана найти себя: в сигнатуре определения ещё нет,
    // а его арность уже известна - это арность обобщения по типу, ровно та,
    // которую выведет ядро (§10 вопрос 63).
    let group = vec![(Rc::clone(&declared.name), self_levels(metas, &declared.ty))];
    let compiled = {
        let mut elaborator = Elaborator::with_group(signature, metas, group);
        clauses
            .iter()
            .map(|clause| elaborator.clause(clause))
            .collect::<Result<Vec<_>, _>>()?
    };

    // Тип идёт в сборку тем же, каким пойдёт в сигнатуру, - с дырками уровня.
    // Одно хранилище на прогон это и позволяет: решение, найденное сборкой,
    // доживает до объявления.
    let body =
        compile(signature, metas, &declared.ty, &compiled).map_err(|error| ElabError::Clauses {
            error: Box::new(error),
            span,
        })?;

    signature
        .define_inferred(
            metas,
            &declared.name,
            Mult::Many,
            declared.ty.clone(),
            Some(body),
        )
        .map_err(|error| ElabError::Core {
            error: Box::new(error),
            span,
        })
}

/// Индуктивное семейство вместе с конструкторами - одной группой.
fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    let kind = match &data.kind {
        Some(kind) => Elaborator::new(signature, metas).expr(kind, Mult::Many)?,
        // Тип-формер не написан - семейство живёт в нулевом универсуме.
        //
        // **Не дырка.** Дырка здесь осталась бы нерешённой (её ограничивают
        // только неравенства `leq` от полей, а их §10 вопрос 39 не решает),
        // обобщилась бы в параметр - и `data Nat where` стало бы
        // полиморфным по уровню. Тогда `f : Nat -> Nat` читается как
        // `∀u v. Nat{u} -> Nat{v}` и тождеством не населяется. Ничего не
        // написано - значит и выводить не из чего; наименьший универсум -
        // единственный выбор, не придумывающий полиморфизма за автора.
        // Полиморфное семейство пишется явно: `data D : Type where`.
        None => Term::universe(0),
    };
    let kind = parameters(signature, metas, &data.params, kind)?;

    // Конструктор называет своё семейство, а в сигнатуре его ещё нет: группа
    // объявляется целиком. Арность берётся обобщением по тип-формеру - это та
    // же арность, которую выведет ядро, а не догадка (§10 вопрос 63).
    let levels = self_levels(metas, &kind);

    // §4.1 назначает полю конструктора кратность `1` по умолчанию, и здесь
    // стоит `ω` - **сознательное расхождение с документом**, заведённое §10
    // вопросом 65.
    //
    // Причина: §4.1 обещает, что «обычный код изменения не замечает», и это
    // обещание против сегодняшнего ядра неверно. Поле, полученное разбором,
    // приходит с кратностью конструктора и **не масштабируется** тем, как
    // расходуется само разбираемое значение. Поэтому `plus (Succ k) m =
    // Succ (plus k m)` отвергается: `k` линейно, а параметр `plus` по
    // умолчанию `ω`, и передача туда даёт «использована ω». Проверено
    // поимённо: вернуть поле можно, положить в другой конструктор можно,
    // передать в `1`-параметр можно, в `ω`-параметр - нет.
    //
    // До ответа на вопрос 65 поля неограниченные: это ровно то, с чем ядро
    // проверялось всю Фазу 1, и на unique-типы оно пока не влияет - их в
    // элаборации нет вовсе.
    let constructors = data
        .constructors
        .iter()
        .map(|constructor| {
            let group = vec![(Rc::clone(&data.name.text), Rc::clone(&levels))];
            let ty = Elaborator::with_group(signature, metas, group)
                .expr(&constructor.ty, Mult::Many)?;
            Ok((&*constructor.name.text, ty))
        })
        .collect::<Result<Vec<_>, ElabError>>()?;

    let params = u32::try_from(data.params.len()).unwrap_or(u32::MAX);
    signature
        .declare_data(metas, &data.name.text, params, kind, &constructors)
        .map_err(|error| ElabError::Core {
            error: Box::new(error),
            span,
        })
}

/// Аргументы уровня, с которыми член группы называет сам себя.
///
/// Их число - арность, которую выведет ядро: обобщение считает нерешённые
/// дырки, и ровно их `define_inferred` превращает в параметры. Не догадка;
/// разойдись оно с ядром - ядро ответит `LevelArity`, а не примет неверное.
///
/// Дырки **общие на весь тип**, а не свежие на каждое вхождение: `Succ : Nat
/// -> Nat` называет одно и то же семейство дважды, и разные дырки сделали бы
/// его полиморфным по двум независимым уровням (§10 вопрос 63).
fn self_levels(metas: &mut Metas, ty: &Term) -> Rc<[Level]> {
    let mut generalization = Generalization::default();
    generalization.collect_term(metas, ty);
    (0..generalization.arity())
        .map(|_| metas.fresh_level())
        .collect()
}

/// Параметры семейства, написанные до `where`, дописываются к тип-формеру.
///
/// Кратность у них `0`: параметр - это тип, а типы живут в стёртом фрагменте.
fn parameters(
    signature: &Signature,
    metas: &mut Metas,
    params: &[ast::Binder],
    kind: Term,
) -> Result<Term, ElabError> {
    let mut result = kind;
    for param in params.iter().rev() {
        let Some(name) = param.names.first() else {
            continue;
        };
        let ty = match &param.ty {
            Some(ty) => Elaborator::new(signature, metas).expr(ty, Mult::Zero)?,
            None => Term::Universe(metas.fresh_level()),
        };
        result = Term::Pi(
            Mult::Zero,
            adamas_core::term::Name::from(&*name.text),
            Rc::new(ty),
            Rc::new(result),
        );
    }
    Ok(result)
}
