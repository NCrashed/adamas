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

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::check::{TypeError, is_type};
use adamas_core::ctx::Ctx;
use adamas_core::level::Level;
use adamas_core::meta::{Generalization, Metas};
use adamas_core::mult::Mult;
use adamas_core::pattern::{PatternError, compile_traced};
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::Term;
use adamas_parser::ast::{self, DeclKind, Module, Symbol};

use crate::error::{ElabError, Missing};
use crate::expr::Elaborator;
use crate::route::{self, Declared};

/// Сигнатура, ожидающая клауз.
///
/// Написанный тип хранится вместе с собранным: маршрут отказа пойдёт по нему
/// обратно, чтобы стать спаном (§10 вопрос 49б).
struct Pending<'a> {
    name: Symbol,
    ty: Term,
    source: &'a ast::Expr,
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
    // Сигнатуры, ставшие постулатами по ходу прогона: клаузы, пришедшие за
    // ними, - не «нет сигнатуры», а сигнатура не рядом.
    let mut postulated: HashMap<Symbol, Span> = HashMap::new();
    let mut pending: Option<Pending<'_>> = None;
    for decl in &module.decls {
        match &decl.kind {
            DeclKind::Signature { name, ty } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                let elaborated =
                    Elaborator::new(signature, metas).typing(|it| it.expr(ty, Mult::Many))?;
                pending = Some(Pending {
                    name: Rc::clone(&name.text),
                    ty: elaborated,
                    source: ty,
                    span: decl.span,
                });
            }
            DeclKind::Clauses { name, clauses } => {
                let Some(declared) = pending.take().filter(|it| it.name == name.text) else {
                    return Err(match postulated.get(&name.text) {
                        Some(signature) => ElabError::DetachedSignature {
                            name: Rc::clone(&name.text),
                            signature: *signature,
                            span: decl.span,
                        },
                        None => ElabError::MissingSignature {
                            name: Rc::clone(&name.text),
                            span: decl.span,
                        },
                    });
                };
                define(signature, metas, &declared, clauses, decl.span)?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
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
    postulate(signature, metas, pending, &mut postulated)
}

/// Сигнатура, за которой не последовало клауз, - постулат.
fn postulate(
    signature: &mut Signature,
    metas: &mut Metas,
    pending: Option<Pending<'_>>,
    postulated: &mut HashMap<Symbol, Span>,
) -> Result<(), ElabError> {
    let Some(pending) = pending else {
        return Ok(());
    };
    postulated.insert(Rc::clone(&pending.name), pending.span);
    let source = pending.source;
    signature
        .postulate_inferred(metas, &pending.name, Mult::Many, pending.ty)
        .map_err(|error| {
            let span = route::locate(&Declared::Postulate(source), &error, pending.span);
            ElabError::Core {
                error: Box::new(error),
                span,
            }
        })
}

/// Определение: клаузы собираются в дерево разбора, дерево уходит в сигнатуру.
fn define(
    signature: &mut Signature,
    metas: &mut Metas,
    declared: &Pending<'_>,
    clauses: &[ast::Clause],
    span: Span,
) -> Result<(), ElabError> {
    // Рекурсивная ссылка обязана найти себя: в сигнатуре определения ещё нет,
    // а его арность считает элаборация - §10 вопрос 63, вариант (а).
    let levels = self_levels(signature, metas, &declared.ty).map_err(|error| ElabError::Core {
        span: route::locate(&Declared::Bare(declared.source), &error, declared.span),
        error: Box::new(error),
    })?;
    let group = vec![(Rc::clone(&declared.name), levels)];
    let compiled = {
        let mut elaborator =
            Elaborator::with_group(signature, metas, group).declaring(&declared.ty);
        clauses
            .iter()
            .map(|clause| elaborator.clause(clause))
            .collect::<Result<Vec<_>, _>>()?
    };

    // Тип идёт в сборку тем же, каким пойдёт в сигнатуру, - с дырками уровня.
    // Одно хранилище на прогон это и позволяет: решение, найденное сборкой,
    // доживает до объявления.
    let tree = compile_traced(signature, metas, &declared.ty, &compiled).map_err(|error| {
        ElabError::Clauses {
            span: clause_span(&error, declared, clauses, span),
            error: Box::new(error),
        }
    })?;

    signature
        .define_inferred(
            metas,
            &declared.name,
            Mult::Many,
            declared.ty.clone(),
            Some(tree.term.clone()),
        )
        .map_err(|error| {
            let declared = Declared::Definition {
                ty: declared.source,
                clauses,
                compiled: &tree,
            };
            ElabError::Core {
                span: route::locate(&declared, &error, span),
                error: Box::new(error),
            }
        })
}

/// Где в исходнике то, на чём споткнулась сборка клауз.
///
/// Отказы сборки делятся на два вида, и указывают они в разные места: тип
/// написан в сигнатуре, а всё остальное - в конкретной клаузе, номер которой
/// сборка и носит.
fn clause_span(
    error: &PatternError,
    declared: &Pending<'_>,
    clauses: &[ast::Clause],
    fallback: Span,
) -> Span {
    let clause = match error {
        PatternError::IllTypedType { error } => {
            return route::locate(&Declared::Bare(declared.source), error, declared.span);
        }
        PatternError::ClauseArity { clause, .. }
        | PatternError::UnboundInBody { clause }
        | PatternError::ImpossiblePattern { clause, .. }
        | PatternError::UnreachableClause { clause } => *clause,
        _ => return fallback,
    };
    clauses.get(clause).map_or(fallback, |clause| clause.span)
}

/// Индуктивное семейство вместе с конструкторами - одной группой.
fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    // Параметры семейства - форма, которой элаборация не владеет, и половина
    // её хуже отказа: телескоп, построенный по шапке, не связывает имена в
    // типах конструкторов и не отражается в их телескопах.
    if let (Some(first), Some(last)) = (data.params.first(), data.params.last()) {
        return Err(ElabError::Missing {
            what: Missing::FamilyParameters,
            span: first.span.merge(last.span),
        });
    }
    let kind = match &data.kind {
        Some(kind) => Elaborator::new(signature, metas).typing(|it| it.expr(kind, Mult::Many))?,
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
    // Конструктор называет своё семейство, а в сигнатуре его ещё нет: группа
    // объявляется целиком, и арность тип-формера считает элаборация.
    let levels = self_levels(signature, metas, &kind).map_err(|error| ElabError::Core {
        span: data.kind.as_ref().map_or(span, |kind| {
            route::locate(&Declared::Bare(kind), &error, span)
        }),
        error: Box::new(error),
    })?;

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
                .typing(|it| it.expr(&constructor.ty, Mult::Many))?;
            Ok((&*constructor.name.text, ty))
        })
        .collect::<Result<Vec<_>, ElabError>>()?;

    signature
        .declare_data(metas, &data.name.text, 0, kind, &constructors)
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Data(data), &error, span),
            error: Box::new(error),
        })
}

/// Аргументы уровня, с которыми член группы называет сам себя.
///
/// Их число - арность, которую выведет ядро: обобщение считает нерешённые
/// дырки, и ровно их фаза A превращает в параметры. Разойдись счёт с ядром -
/// ядро ответит `LevelArity`, а не примет неверное.
///
/// **Считать можно только по проверенному типу.** Фаза A обобщает после
/// `check_declaration`, а тот решает часть дырок унификацией: в `f : Id Nat ->
/// Id Nat` аргумент уровня у `Id` навязан её собственным объявлением. Поэтому
/// здесь идёт тот же `is_type`, что и в ядре, - без него самоссылка получает
/// больше аргументов уровня, чем у члена окажется параметров, и корректная
/// рекурсия отвергается.
///
/// Дырки **общие на весь тип**, а не свежие на каждое вхождение: `Succ : Nat
/// -> Nat` называет одно и то же семейство дважды, и разные дырки сделали бы
/// его полиморфным по двум независимым уровням (§10 вопрос 63).
fn self_levels(
    signature: &Signature,
    metas: &mut Metas,
    ty: &Term,
) -> Result<Rc<[Level]>, TypeError> {
    is_type(&Ctx::new(signature), metas, ty)?;
    let mut generalization = Generalization::default();
    generalization.collect_term(metas, ty);
    Ok((0..generalization.arity())
        .map(|_| metas.fresh_level())
        .collect())
}
