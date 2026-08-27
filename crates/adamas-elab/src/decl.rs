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
use crate::own::{Owned, Ownership};
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
    let mut owned = Owned::default();
    elaborate_into(module, &mut signature, &mut metas, &mut owned)?;
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
    owned: &mut Owned,
) -> Result<(), ElabError> {
    // Сигнатуры, ставшие постулатами по ходу прогона: клаузы, пришедшие за
    // ними, - не «нет сигнатуры», а сигнатура не рядом.
    let mut postulated: HashMap<Symbol, Span> = HashMap::new();
    let mut pending: Option<Pending<'_>> = None;
    for decl in &module.decls {
        match &decl.kind {
            DeclKind::Signature { name, ty } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                let elaborated = Elaborator::new(signature, metas, owned)
                    .typing(|it| it.expr(ty, Mult::Many))?;
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
                define(signature, metas, owned, &declared, clauses, decl.span)?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // Маркер ставится **до** элаборации конструкторов: поле
                // собственного типа получит `1` тем же правилом, что и всякое
                // другое связывание, а не отдельным случаем.
                if data.unique {
                    owned.declare(&data.name.text, Ownership::Unique);
                }
                declare_data(signature, metas, owned, data, decl.span)?;
            }
            DeclKind::Resource(resource) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                owned.declare(&resource.name.text, Ownership::Resource);
                declare_resource(signature, metas, owned, resource, decl.span)?;
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
    owned: &Owned,
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
            Elaborator::with_group(signature, metas, owned, group).declaring(&declared.ty);
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

/// Ресурсный тип: семейство плюс обязательный `drop` (§3.3).
///
/// **Тело держит два жанра объявлений**, и различаются они формой записи:
/// голая сигнатура - конструктор (`Open : String -> File`), сигнатура с
/// клаузами - определение. Определяется здесь только `drop`: пусти мы сюда
/// произвольные определения, пришлось бы отвечать, видно ли снаружи имя,
/// написанное внутри, - то есть заводить пространства имён, а они §4.8 и
/// Фаза 3.
///
/// **Названное ограничение:** `drop` объявляется под своим написанным именем,
/// поэтому двух ресурсных типов в одном модуле не бывает - второй `drop`
/// столкнётся с первым. Имя менять нельзя, пока `drop` рекурсивен по
/// написанному имени; развяжется это тогда же, когда компилятор начнёт искать
/// `drop` сам, - вместе со вставкой в exit-points.
fn declare_resource(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    resource: &ast::Resource,
    span: Span,
) -> Result<(), ElabError> {
    let mut constructors: Vec<ast::Constructor> = Vec::new();
    let mut destructor: Option<(&ast::Expr, &[ast::Clause], Span)> = None;
    // Сигнатура, о которой ещё не известно, конструктор она или заголовок
    // определения: решают следующие за ней клаузы.
    let mut pending: Option<(&ast::Name, &ast::Expr, Span)> = None;
    let constructor = |(name, ty, span): (&ast::Name, &ast::Expr, Span)| ast::Constructor {
        name: name.clone(),
        ty: ty.clone(),
        span,
    };

    for member in &resource.members {
        match &member.kind {
            ast::DeclKind::Signature { name, ty } => {
                constructors.extend(pending.take().map(constructor));
                pending = Some((name, ty, member.span));
            }
            ast::DeclKind::Clauses { name, clauses } => {
                let Some((_, ty, _)) = pending.take().filter(|(it, ..)| it.text == name.text)
                else {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&name.text),
                        span: member.span,
                    });
                };
                if &*name.text != "drop" {
                    return Err(ElabError::ResourceMember {
                        data: Rc::clone(&resource.name.text),
                        name: Rc::clone(&name.text),
                        span: member.span,
                    });
                }
                destructor = Some((ty, clauses, member.span));
            }
            ast::DeclKind::Data(inner) => {
                return Err(ElabError::ResourceMember {
                    data: Rc::clone(&resource.name.text),
                    name: Rc::clone(&inner.name.text),
                    span: member.span,
                });
            }
            ast::DeclKind::Resource(inner) => {
                return Err(ElabError::ResourceMember {
                    data: Rc::clone(&resource.name.text),
                    name: Rc::clone(&inner.name.text),
                    span: member.span,
                });
            }
        }
    }
    constructors.extend(pending.take().map(constructor));

    let Some((drop_ty, clauses, drop_span)) = destructor else {
        return Err(ElabError::ResourceWithoutDrop {
            name: Rc::clone(&resource.name.text),
            span,
        });
    };

    let data = ast::Data {
        unique: true,
        name: resource.name.clone(),
        params: resource.params.clone(),
        kind: None,
        constructors,
    };
    declare_data(signature, metas, owned, &data, span)?;

    // `drop` объявляется после семейства: его тип называет ресурс, а в
    // сигнатуре тот появляется только сейчас. Домен получает `1` тем же
    // правилом, что и всякое связывание ресурсного типа, - писать `(1 h : …)`
    // руками не нужно и не требуется §3.3.
    let elaborated =
        Elaborator::new(signature, metas, owned).typing(|it| it.expr(drop_ty, Mult::Many))?;
    let declared = Pending {
        name: Rc::from("drop"),
        ty: elaborated,
        source: drop_ty,
        span: drop_span,
    };
    define(signature, metas, owned, &declared, clauses, drop_span)
}

/// Индуктивное семейство вместе с конструкторами - одной группой.
fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
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
        Some(kind) => {
            Elaborator::new(signature, metas, owned).typing(|it| it.expr(kind, Mult::Many))?
        }
        // Тип-формер не написан - семейство живёт в нулевом универсуме.
        //
        // **Не дырка.** Дырку здесь ограничивают только неравенства `leq` от
        // полей, а их §10 вопрос 39 не решает: обобщённая в параметр, она
        // упирается в укладку полей - `data Even : Nat -> Type` с полем
        // `Even n` отвечает «поле живёт в `Type u0`, а тип - в `Type u1`».
        // Проверено подстановкой дырки вместо нуля. Ничего не написано -
        // значит и выводить не из чего; полиморфное по уровню семейство
        // пишется явно: `data D : Type where`.
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

    // Поле конструктора получает `1` (§4.1): конструктор кладёт аргумент
    // однажды. Обычный код этого не замечает, потому что при разборе поле
    // приходит в ветвь при `q · r`, а `r` - кратность потребления
    // разбираемого; у ω-связывания `1 · ω = ω` (§3.3, вопрос 65).
    let constructors = data
        .constructors
        .iter()
        .map(|constructor| {
            let group = vec![(Rc::clone(&data.name.text), Rc::clone(&levels))];
            let ty = Elaborator::with_group(signature, metas, owned, group)
                .typing(|it| it.expr(&constructor.ty, Mult::One))?;
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
