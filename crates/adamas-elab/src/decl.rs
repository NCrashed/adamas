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

use adamas_core::check::{TypeError, check_closed_with, infer, is_type};
use adamas_core::ctx::Ctx;
use adamas_core::eval::quote;
use adamas_core::level::Level;
use adamas_core::meta::{Generalization, Metas, zonk_term};
use adamas_core::mult::Mult;
use adamas_core::pattern::{PatternError, compile_traced};
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::{Binder, Fields, Name as CoreName, Term};
use adamas_parser::ast::{self, DeclKind, Module, Symbol};

use crate::carrier;
use crate::error::{ElabError, Names};
use crate::expr::{Elaborator, Member, Param};
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
    members_into(&module.decls, None, signature, metas, owned)
}

/// Квалифицирует имя членом модуля: `T` внутри `IntOrd` объявляется как
/// `IntOrd.T` (§4.8, решение 2026-08-30).
///
/// Точка в имени - то, чего поверхностный лексер не порождает, поэтому
/// столкнуться с написанным именем квалифицированное не может, а написать его
/// автор не в состоянии: снаружи модуль читается проекцией.
fn qualify(within: Option<&Symbol>, name: &str) -> Symbol {
    match within {
        Some(outer) => Rc::from(format!("{outer}.{name}").as_str()),
        None => Rc::from(name),
    }
}

/// Объявления одного уровня: верхнего либо тела модуля.
fn members_into(
    decls: &[ast::Decl],
    within: Option<&Symbol>,
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
) -> Result<(), ElabError> {
    // Сигнатуры, ставшие постулатами по ходу прогона: клаузы, пришедшие за
    // ними, - не «нет сигнатуры», а сигнатура не рядом.
    let mut postulated: HashMap<Symbol, Span> = HashMap::new();
    let mut pending: Option<Pending<'_>> = None;
    for decl in decls {
        match &decl.kind {
            DeclKind::Signature { name, ty } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // Владение верхнего уровня не выражается: определение всегда
                // `ω` (`sig.rs`: линейность на всю программу не считается), а
                // §3.3 требует `1`. Без этого отказа постулат ресурсного типа
                // - обычное ω-имя, и `drop` по нему зовётся сколько угодно раз.
                if let Some(how) = owned.of(ty) {
                    return Err(ElabError::OwnedTopLevel {
                        owned: how,
                        name: Rc::clone(&name.text),
                        span: ty.span,
                    });
                }
                let elaborated = Elaborator::new(signature, metas, owned)
                    .within(within)
                    .declaration(ty, Mult::Many)?;
                pending = Some(Pending {
                    name: qualify(within, &name.text),
                    ty: elaborated,
                    source: ty,
                    span: decl.span,
                });
            }
            DeclKind::Clauses { name, clauses } => {
                let qualified = qualify(within, &name.text);
                let Some(declared) = pending.take().filter(|it| it.name == qualified) else {
                    return Err(match postulated.get(&qualified) {
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
                define(
                    signature, metas, owned, within, &declared, clauses, decl.span,
                )?;
            }
            // Алиас: `Point : Type` не годится - `Type` обобщается в `∀u`, а
            // тело живёт в конкретном универсуме. Тип поэтому не пишется, а
            // считается по телу.
            DeclKind::Alias { name, body } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // `type T` без уравнения объявляет абстрактный типовой член, и
                // законно это только в сигнатуре модуля: снаружи её тип брать
                // неоткуда, а постулировать `T : Type` можно и сигнатурой.
                let Some(body) = body else {
                    return Err(ElabError::AbstractType {
                        name: Rc::clone(&name.text),
                        span: decl.span,
                    });
                };
                alias(signature, metas, owned, within, name, body, decl.span)?;
            }
            DeclKind::Module(declared) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_module(signature, metas, owned, within, declared, decl.span)?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // Семейство в теле модуля - названная граница среза: имя
                // квалифицируется, а имена конструкторов нет, и разбор по ним
                // писать было бы нечем. Заводится вместе с путём в паттерне.
                if within.is_some() {
                    return Err(ElabError::ModuleMember {
                        name: Rc::clone(&data.name.text),
                        what: "модуле",
                        why: "конструкторы квалифицированного имени пока не носят, \
                              и разобрать их в паттерне нечем",
                        span: decl.span,
                    });
                }
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
                if within.is_some() {
                    return Err(ElabError::ModuleMember {
                        name: Rc::clone(&resource.name.text),
                        what: "модуле",
                        why: "ресурс объявляет конструкторы, а они пока \
                              квалифицированного имени не носят",
                        span: decl.span,
                    });
                }
                owned.declare(&resource.name.text, Ownership::Resource);
                declare_resource(signature, metas, owned, resource, decl.span)?;
            }
        }
    }
    postulate(signature, metas, pending, &mut postulated)
}

/// Алиас типа: `type Point = { x : Nat }` (§4.2).
///
/// Собственной сигнатуры у него нет и быть не может: `Point : Type` обобщает
/// универсум в параметр, а тело живёт в конкретном. Универсум поэтому берётся
/// у тела - тем же `is_type`, которым его и проверяют.
fn alias(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    within: Option<&Symbol>,
    name: &ast::Name,
    body: &ast::Expr,
    span: Span,
) -> Result<(), ElabError> {
    let term = Elaborator::new(signature, metas, owned)
        .within(within)
        .typing(|it| it.expr(body, Mult::Many))?;
    let declared = qualify(within, &name.text);
    let names = Names::of(&declared, Vec::new());
    let level = is_type(&Ctx::new(signature), metas, &term).map_err(|error| ElabError::Core {
        span: route::locate(&Declared::Bare(body), &error, span),
        error: Box::new(error),
        names: names.clone(),
    })?;
    signature
        .define_inferred(
            metas,
            &declared,
            Mult::Many,
            Term::Universe(metas.zonk(&level)),
            Some(term),
        )
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Bare(body), &error, span),
            error: Box::new(error),
            names,
        })
}

/// Модуль или его сигнатура (§4.8).
///
/// **Члены поднимаются на верхний уровень** под квалифицированными именами
/// (`IntOrd.compare`), а сам модуль объявляется записью из них. Решение от
/// 2026-08-30: так рекурсивный член, `data` в теле, проверка тотальности и
/// позитивность работают тем же кодом, что и снаружи, - модулю не нужно
/// заводить второй механизм определений. Семантика §3.5 при этом сохраняется:
/// модуль остаётся значением-записью, доступ к члену - проекцией.
///
/// Сигнатура модуля объявляется не записью, а **типом** записи: члены её -
/// телескоп, поэтому `compare : T -> T -> Ordering` видит `T`.
fn declare_module(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    within: Option<&Symbol>,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    let declared = qualify(within, &module.name.text);
    if module.signature {
        return declare_module_type(signature, metas, owned, &declared, module, span);
    }
    members_into(&module.members, Some(&declared), signature, metas, owned)?;

    // Поле на каждого объявленного члена, в порядке написания. Клаузы своего
    // поля не заводят: его завела сигнатура, за которой они идут.
    let mut written = Vec::new();
    for member in &module.members {
        let Some(name) = member_name(member) else {
            continue;
        };
        let full = qualify(Some(&declared), name);
        let Some(term) = signature.instantiate(&full, metas) else {
            continue;
        };
        written.push((CoreName::from(&**name), Rc::new(term)));
    }
    let object = Term::Object(written.into());
    let names = Names::of(&declared, Vec::new());
    // Аннотация - тип объявления; проверяет соответствие ей `declare`, тем же
    // правилом, что и всякое тело. Без аннотации тип **структурный**: он
    // синтезируется по собранной записи, как и обещает §4.8.
    let ty = if let Some(ascription) = &module.ascription {
        let written = Elaborator::new(signature, metas, owned)
            .within(within)
            .typing(|it| it.expr(ascription, Mult::Many))?;
        // Проверка **до** объявления, и это не дубль той, что сделает
        // `declare`. Аннотация написана именем, а у имени есть аргументы
        // уровня - дырки; не решив их сравнением с телом, обобщение примет их
        // за параметры самого модуля, и `Nat : Type 0` перестанет подходить
        // под `T : Type u0`, ставшую жёсткой.
        check_closed_with(signature, metas, &object, &written).map_err(|error| {
            ElabError::Core {
                span,
                error: Box::new(error),
                names: names.clone(),
            }
        })?;
        zonk_term(metas, &written)
    } else {
        let (ty, _) = infer(&Ctx::new(signature), metas, Mult::Many, &object).map_err(|error| {
            ElabError::Core {
                span,
                error: Box::new(error),
                names: names.clone(),
            }
        })?;
        quote(0, &ty)
    };
    signature
        .define_inferred(metas, &declared, Mult::Many, ty, Some(object))
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })
}

/// Имя, под которым член становится полем модуля.
///
/// `None` - член поля не заводит: клаузы объявлены своей сигнатурой.
fn member_name(member: &ast::Decl) -> Option<&Symbol> {
    match &member.kind {
        DeclKind::Signature { name, .. } | DeclKind::Alias { name, .. } => Some(&name.text),
        DeclKind::Module(inner) => Some(&inner.name.text),
        DeclKind::Data(data) => Some(&data.name.text),
        DeclKind::Resource(resource) => Some(&resource.name.text),
        DeclKind::Clauses { .. } => None,
    }
}

/// `module type S where …` - тип записи, собранный телескопом.
fn declare_module_type(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    declared: &Symbol,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    let mut members = Vec::with_capacity(module.members.len());
    for member in &module.members {
        match &member.kind {
            DeclKind::Signature { name, ty } => members.push((name.clone(), Some(ty))),
            // Абстрактный типовой член. Уравнение здесь - полупрозрачная
            // сигнатура (§10 вопрос 46), и её в языке пока нет.
            DeclKind::Alias { name, body: None } => members.push((name.clone(), None)),
            DeclKind::Alias { name, .. } => {
                return Err(ElabError::ModuleMember {
                    name: Rc::clone(&name.text),
                    what: "сигнатуре модуля",
                    why: "уравнение у типового члена делает сигнатуру полупрозрачной, \
                          а таких пока нет (§10 вопрос 46)",
                    span: member.span,
                });
            }
            _ => {
                let name = match &member.kind {
                    DeclKind::Clauses { name, .. } => Rc::clone(&name.text),
                    _ => member_name(member)
                        .cloned()
                        .unwrap_or_else(|| Rc::from("_")),
                };
                return Err(ElabError::ModuleMember {
                    name,
                    what: "сигнатуре модуля",
                    why: "сигнатура несёт объявления без реализаций",
                    span: member.span,
                });
            }
        }
    }
    let borrowed: Vec<(ast::Name, Option<&ast::Expr>)> = members;
    let fields =
        Elaborator::new(signature, metas, owned).typing(|it| it.module_members(&borrowed))?;
    let record = Term::Record(Fields::closed(fields.into()));
    let names = Names::of(declared, Vec::new());
    let level = is_type(&Ctx::new(signature), metas, &record).map_err(|error| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    })?;
    signature
        .define_inferred(
            metas,
            declared,
            Mult::Many,
            Term::Universe(metas.zonk(&level)),
            Some(record),
        )
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })
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
                names: Names::of(&pending.name, Vec::new()),
            }
        })
}

/// Определение: клаузы собираются в дерево разбора, дерево уходит в сигнатуру.
fn define(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    within: Option<&Symbol>,
    declared: &Pending<'_>,
    clauses: &[ast::Clause],
    span: Span,
) -> Result<(), ElabError> {
    // Рекурсивная ссылка обязана найти себя: в сигнатуре определения ещё нет,
    // а его арность считает элаборация - §10 вопрос 63, вариант (а).
    let levels = self_levels(signature, metas, &declared.ty).map_err(|error| ElabError::Core {
        span: route::locate(&Declared::Bare(declared.source), &error, declared.span),
        error: Box::new(error),
        names: Names::of(&declared.name, Vec::new()),
    })?;
    let group = vec![Member {
        name: Rc::clone(&declared.name),
        levels,
        ty: Rc::new(declared.ty.clone()),
    }];
    let compiled = {
        let mut elaborator = Elaborator::with_group(signature, metas, owned, group)
            .within(within)
            .declaring(&declared.ty);
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
            let names = Names::of(&declared.name, Vec::new());
            let source = Declared::Definition {
                ty: declared.source,
                clauses,
                compiled: &tree,
            };
            ElabError::Core {
                span: route::locate(&source, &error, span),
                error: Box::new(error),
                names,
            }
        })?;

    // После объявления, а не до: дырки решены и подставлены, поэтому видно,
    // чем на самом деле стал каждый выводимый аргумент (§10 вопрос 76).
    carrier::check(signature, owned, &declared.name, span)
}

/// Поднимает универсум семейства до уровней его параметров.
fn raised(kind: Term, params: &[Param]) -> Term {
    match kind {
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            binder,
            name,
            domain,
            row,
            Rc::new(raised(codomain.as_ref().clone(), params)),
        ),
        Term::Universe(level) | Term::RowKind(level) => {
            Term::Universe(Elaborator::sort(params, level))
        }
        other => other,
    }
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

/// Члены тела: конструкторы и деструктор.
///
/// Жанр читается формой записи (§4.1): голая сигнатура - конструктор
/// (`Open : String -> File`), сигнатура с клаузами - определение. Определение
/// в теле одно, и оно и есть деструктор - **под любым именем**: пространство
/// имён плоское (§4.8, Фаза 3), и `drop` на каждый ресурс не хватило бы (§10
/// вопрос 77). Второе определение - то, чему в теле не место: пусти мы его
/// туда, пришлось бы отвечать, видно ли снаружи написанное внутри имя, то есть
/// заводить пространства имён.
fn resource_members(
    resource: &ast::Resource,
) -> Result<(Vec<ast::Constructor>, Option<Destructor<'_>>), ElabError> {
    let mut constructors: Vec<ast::Constructor> = Vec::new();
    let mut destructor: Option<Destructor<'_>> = None;
    // Сигнатура, о которой ещё не известно, конструктор она или заголовок
    // определения: решают следующие за ней клаузы.
    let mut pending: Option<(&ast::Name, &ast::Expr, Span)> = None;
    let constructor = |(name, ty, span): (&ast::Name, &ast::Expr, Span)| ast::Constructor {
        name: name.clone(),
        ty: ty.clone(),
        span,
    };
    let refuse = |name: &Symbol, span| ElabError::ResourceMember {
        data: Rc::clone(&resource.name.text),
        name: Rc::clone(name),
        span,
    };

    for member in &resource.members {
        match &member.kind {
            ast::DeclKind::Signature { name, ty } => {
                constructors.extend(pending.take().map(constructor));
                pending = Some((name, ty, member.span));
            }
            // Ни алиас, ни модуль телом ресурса не бывают: layout их туда
            // пускает, а смысла у них там нет - конструктор либо деструктор.
            ast::DeclKind::Module(ast::ModuleDecl { name, .. })
            | ast::DeclKind::Alias { name, .. } => {
                return Err(ElabError::ResourceMember {
                    data: Rc::clone(&resource.name.text),
                    name: Rc::clone(&name.text),
                    span: member.span,
                });
            }
            ast::DeclKind::Clauses { name, clauses } => {
                let Some((_, ty, _)) = pending.take().filter(|(it, ..)| it.text == name.text)
                else {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&name.text),
                        span: member.span,
                    });
                };
                if let Some(first) = &destructor {
                    return Err(refuse(&first.name.text, member.span));
                }
                destructor = Some(Destructor {
                    name,
                    ty,
                    clauses,
                    span: member.span,
                });
            }
            ast::DeclKind::Data(inner) => return Err(refuse(&inner.name.text, member.span)),
            ast::DeclKind::Resource(inner) => return Err(refuse(&inner.name.text, member.span)),
        }
    }
    constructors.extend(pending.take().map(constructor));
    Ok((constructors, destructor))
}

/// Деструктор, снятый с тела ресурса.
struct Destructor<'a> {
    name: &'a ast::Name,
    ty: &'a ast::Expr,
    clauses: &'a [ast::Clause],
    span: Span,
}

/// Ресурсный тип: семейство плюс обязательный деструктор (§3.3).
///
/// Семейство объявляется `unique`, деструктор - обычным определением следом за
/// ним, и только после этого тип получает имя своего деструктора. Порядок
/// существен во всех трёх шагах, и каждый отмечен по месту.
fn declare_resource(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    resource: &ast::Resource,
    span: Span,
) -> Result<(), ElabError> {
    let (constructors, destructor) = resource_members(resource)?;

    // Голая сигнатура - конструктор, а конструктор пишется заглавной (§4.1).
    // Строчное имя без клауз - деструктор, у которого забыли тело, и сказать
    // об этом надо здесь: иначе отказ придёт позже и не про то - «деструктора
    // нет» вместо «у него нет тела».
    if let Some(bare) = constructors
        .iter()
        .find(|it| !crate::is_reference(&it.name.text))
    {
        return Err(ElabError::DestructorWithoutBody {
            data: Rc::clone(&resource.name.text),
            name: Rc::clone(&bare.name.text),
            span: bare.span,
        });
    }

    let Some(Destructor {
        name: drop_name,
        ty: drop_ty,
        clauses,
        span: drop_span,
    }) = destructor
    else {
        return Err(ElabError::ResourceWithoutDrop {
            name: Rc::clone(&resource.name.text),
            span,
        });
    };

    // Имя деструктора свободно, но пространство имён плоское: два ресурса,
    // назвавшие деструктор одинаково, столкнутся (§4.8, Фаза 3). Отказ говорит
    // об этом прямо - `DuplicateDefinition` от ядра назвал бы столкновение
    // имён, не называя причины.
    if let Some(first) = owned
        .named(&drop_name.text)
        .filter(|it| ***it != *resource.name.text)
    {
        return Err(ElabError::SharedDestructor {
            data: Rc::clone(&resource.name.text),
            name: Rc::clone(&drop_name.text),
            first: Rc::clone(first),
            span: drop_span,
        });
    }

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
    let elaborated = Elaborator::new(signature, metas, owned).declaration(drop_ty, Mult::Many)?;
    // Форма проверяется здесь, один раз, а не в каждой точке вставки: вызов
    // `drop` подставляется компилятором, и тип его результата обязан быть
    // написан в области видимости, где ресурса уже нет.
    destructor_shape(
        &elaborated,
        &resource.name.text,
        &drop_name.text,
        owned,
        drop_ty.span,
    )?;
    let declared = Pending {
        name: Rc::clone(&drop_name.text),
        ty: elaborated,
        source: drop_ty,
        span: drop_span,
    };
    define(signature, metas, owned, None, &declared, clauses, drop_span)?;
    // Имя деструктора связывается с типом **после** того, как собрано его
    // тело, и это не порядок ради порядка. Связав раньше, мы получили бы
    // вставку `drop` внутрь самого `drop`: параметр там ресурсного типа, и
    // тело `closeFile h = True` его не упоминает. Вставка полезла бы за типом
    // деструктора в сигнатуру, где его ещё нет, - то есть в `unreachable!`
    // (см. `destructor` в [`crate::expr`], чей инвариант это и есть).
    owned.destroys(&resource.name.text, &declared.name);
    Ok(())
}

/// Деструктор берёт свой ресурс и отдаёт что-то, от него не зависящее.
///
/// Зависимость запрещена не из осторожности: вставка ставит `drop h` в
/// `let`-связывание, тип которого пишется **рядом** с вызовом, а зависимый
/// результат пришлось бы инстанцировать самим ресурсом - тем самым, которого
/// после вызова уже нет.
fn destructor_shape(
    ty: &Term,
    data: &Symbol,
    name: &Symbol,
    owned: &Owned,
    span: Span,
) -> Result<(), ElabError> {
    let refuse = || ElabError::DestructorShape {
        data: Rc::clone(data),
        name: Rc::clone(name),
        span,
    };
    let Term::Pi(Binder { mult, .. }, _, domain, _, result) = ty else {
        return Err(refuse());
    };
    // Кратность домена `1`: при `0` тело деструктора не вправе тронуть ресурс
    // (ядро отвергнет его же), то есть объявлен заведомо пустой `drop`.
    if *mult != Mult::One || name_head(domain).is_none_or(|name| **name != **data) {
        return Err(refuse());
    }
    // Ровно один аргумент: вызов подставляет вставка, и лишний параметр
    // превратил бы её в частичное применение - тело `drop` не выполнилось бы
    // никогда. Результат не владеемый: иначе каждое закрытие заводило бы новый
    // ресурс, которого никто не держит.
    let returns_owned = name_head(result).is_some_and(|name| owned.owns(name));
    if matches!(result.as_ref(), Term::Pi(..)) || returns_owned || mentions_local(result) {
        return Err(refuse());
    }
    Ok(())
}

/// Поле с владением требует владения от типа, который его держит.
///
/// Правило в одну фразу, обе половины которой - закрытые вопросы §10.
///
/// **Владеемое поле требует владеемого типа** (вопрос 70). Обёртка из обычного
/// `data` отмывала бы владение: связывания её `ω`, разбор идёт при `r = ω`, и
/// поле кратности `1` приходит в ветвь как `ω` - ресурс оказывается снаружи
/// без линейности и закрывается дважды.
///
/// **Ресурсное поле требует ресурсного типа** (вопрос 77). Уничтожение
/// значения влечёт уничтожение полей (§3.3), но у `unique` деструктора нет, и
/// влечь ему нечем: `let w : Wrap = …` с забытым `w` не закрывает ничего.
/// Рекурсия `drop` по полям идёт по разбору, а забытое значение не
/// разбирается.
///
/// Смотрит на голову написанного, как и всё правило владения, поэтому ресурс
/// под переменной типа сюда не попадает - вопрос 76.
fn owned_field(
    ty: &Term,
    owned: &Owned,
    data: &ast::Data,
    constructor: &ast::Constructor,
) -> Result<(), ElabError> {
    let holder = owned.how(&data.name.text);
    let mut current = ty;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        let field = name_head(domain).and_then(|name| owned.how(name).map(|how| (name, how)));
        if let Some((name, field)) = field {
            let refuse = |needed| {
                Err(ElabError::OwnedField {
                    data: Rc::clone(&data.name.text),
                    constructor: Rc::clone(&constructor.name.text),
                    field: Rc::from(&**name),
                    owned: field,
                    needed,
                    span: constructor.ty.span,
                })
            };
            match (field, holder) {
                (_, None) => return refuse(Ownership::Unique),
                (Ownership::Resource, Some(Ownership::Unique)) => {
                    return refuse(Ownership::Resource);
                }
                _ => {}
            }
        }
        current = codomain;
    }
    Ok(())
}

/// Имя в голове спайна применения, если она константа.
fn name_head(term: &Term) -> Option<&adamas_core::term::Name> {
    let mut head = term;
    while let Term::App(callee, _) = head {
        head = callee;
    }
    match head {
        Term::Const(name, _) => Some(name),
        _ => None,
    }
}

/// Ссылается ли терм хоть на одно локальное связывание.
fn mentions_local(term: &Term) -> bool {
    match term {
        Term::Var(_) => true,
        // Дырка замкнута: локальных связываний в ней нет по построению.
        Term::Universe(_) | Term::RowKind(_) | Term::Const(..) | Term::Meta(_) => false,
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().any(|field| mentions_local(&field.ty))
                || fields
                    .tail
                    .as_ref()
                    .is_some_and(|tail| mentions_local(tail))
        }
        Term::Object(fields) => fields.iter().any(|(_, value)| mentions_local(value)),
        Term::With(base, fields) => {
            mentions_local(base) || fields.iter().any(|(_, value)| mentions_local(value))
        }
        Term::Project(record, _) => mentions_local(record),
        Term::Lam(_, _, body) => mentions_local(body),
        Term::App(callee, argument) => mentions_local(callee) || mentions_local(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            mentions_local(domain)
                || mentions_local(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(mentions_local)
        }
        Term::Let(_, _, ty, value, body) => {
            mentions_local(ty) || mentions_local(value) || mentions_local(body)
        }
        Term::Case(case) => {
            mentions_local(&case.scrutinee)
                || mentions_local(&case.motive)
                || case
                    .branches
                    .iter()
                    .any(|branch| mentions_local(&branch.body))
        }
    }
}

/// Индуктивное семейство вместе с конструкторами - одной группой.
fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    // Телескоп параметров элаборируется один раз и переиспользуется: kind и
    // каждый конструктор обязаны нести **один и тот же** телескоп, иначе
    // `List` в результате и `List` в объявлении - два разных семейства.
    let mut elaborator = Elaborator::new(signature, metas, owned);
    let params = elaborator.telescope(&data.params)?;
    let kind = match &data.kind {
        // Параметры пишутся, поэтому в kind они явные: `Vect a n`.
        Some(kind) => elaborator.wrapped(&params, false, |it| {
            it.typing(|it| it.expr(kind, Mult::Many))
        })?,
        // Тип-формер не написан - семейство живёт в нулевом универсуме.
        //
        // **Не дырка.** Дырку здесь ограничивают только неравенства `leq` от
        // полей, а их §10 вопрос 39 не решает: обобщённая в параметр, она
        // упирается в укладку полей - `data Even : Nat -> Type` с полем
        // `Even n` отвечает «поле живёт в `Type u0`, а тип - в `Type u1`».
        // Проверено подстановкой дырки вместо нуля. Ничего не написано -
        // значит и выводить не из чего; полиморфное по уровню семейство
        // пишется явно: `data D : Type where`.
        None => elaborator.wrapped(&params, false, |_| Ok(Term::universe(0)))?,
    };
    // Семейство обязано вместить универсумы своих параметров: поле типа `a`
    // живёт там же, где `a`. Написанный `Type` даёт дырку, и поднять её до
    // максимума - наименьшее, что подходит.
    let kind = raised(kind, &params);
    // Маршрут внутрь семейства называет конструктор номером, а имена у него
    // здесь: собираются один раз на оба возможных отказа.
    let names = Names::of(
        &data.name.text,
        data.constructors
            .iter()
            .map(|constructor| Rc::clone(&constructor.name.text))
            .collect(),
    );
    // Конструктор называет своё семейство, а в сигнатуре его ещё нет: группа
    // объявляется целиком, и арность тип-формера считает элаборация.
    let levels = self_levels(signature, metas, &kind).map_err(|error| ElabError::Core {
        span: data.kind.as_ref().map_or(span, |kind| {
            route::locate(&Declared::Bare(kind), &error, span)
        }),
        error: Box::new(error),
        names: names.clone(),
    })?;

    // Поле конструктора получает `1` (§4.1): конструктор кладёт аргумент
    // однажды. Обычный код этого не замечает, потому что при разборе поле
    // приходит в ветвь при `q · r`, а `r` - кратность потребления
    // разбираемого; у ω-связывания `1 · ω = ω` (§3.3, вопрос 65).
    let constructors = data
        .constructors
        .iter()
        .map(|constructor| {
            let group = vec![Member {
                name: Rc::clone(&data.name.text),
                levels: Rc::clone(&levels),
                ty: Rc::new(kind.clone()),
            }];
            // У конструктора те же параметры, но выводимые: пишут `MkPair x y`,
            // а не `MkPair A B x y`. Свободные имена, оставшиеся сверх них,
            // поднимаются уже под ними - и потому стоят после, как того и ждёт
            // ядро от телескопа с параметрами.
            let ty = Elaborator::with_group(signature, metas, owned, group).wrapped(
                &params,
                true,
                |it| it.declaration(&constructor.ty, Mult::One),
            )?;
            owned_field(&ty, owned, data, constructor)?;
            Ok((&*constructor.name.text, ty))
        })
        .collect::<Result<Vec<_>, ElabError>>()?;

    let parameters = u32::try_from(params.len()).unwrap_or(u32::MAX);
    signature
        .declare_data(metas, &data.name.text, parameters, kind, &constructors)
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Data(data), &error, span),
            error: Box::new(error),
            names,
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
    // Считать по зонканному: уровень, спрятавшийся в решении дырки терма,
    // иначе не виден, и арность вышла бы меньше настоящей - той, которую
    // посчитает объявление.
    let ty = zonk_term(metas, ty);
    let mut generalization = Generalization::default();
    generalization.collect_term(metas, &ty);
    Ok((0..generalization.arity())
        .map(|_| metas.fresh_level())
        .collect())
}
