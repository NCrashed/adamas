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

use adamas_core::alloc;
use adamas_core::check::{TypeError, check_within, infer, is_type};
use adamas_core::conv::{convertible, whnf};
use adamas_core::ctx::Ctx;
use adamas_core::error::Frame;
use adamas_core::eval::{eval, quote};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::{Generalization, Metas, zonk_term};
use adamas_core::mult::{Mult, MultVar};
use adamas_core::pattern::{Compiled, PatternError, compile_traced};
use adamas_core::prim::{PrimOp, PrimTy};
use adamas_core::row::{Label, Row, RowVar, Tail};
use adamas_core::sig::{DefinitionKind, Group, Member as SigMember, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Args, Binder, Fields, Name as CoreName, Term};
use adamas_parser::ast::{self, DeclKind, Module, Symbol};

use crate::carrier;
use crate::error::{ElabError, Names};
use adamas_core::value::{Env, Lvl, Value};

use crate::class::{self, Class, Declaring, Instances, Offence};
use crate::expr::{Elaborator, Enclosing, Member, Param, UNIT, Unwritten, WrittenField};
use crate::fixity::Fixities;
use crate::own::{Owned, Ownership};
use crate::route::{self, Declared};
use crate::warn::{Warning, Warnings};

/// Сигнатура, ожидающая клауз.
///
/// Написанный тип хранится вместе с собранным: маршрут отказа пойдёт по нему
/// обратно, чтобы стать спаном (§10 вопрос 49б).
struct Pending<'a> {
    /// Каких вердиктов требуют написанные атрибуты (§4.7, §5.1).
    required: Required,
    name: Symbol,
    ty: Term,
    /// Сколько параметров кратности написано (§10 вопрос 41).
    grades: u32,
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
pub fn elaborate(module: &Module) -> Result<(Signature, Warnings), ElabError> {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut instances = Instances::default();
    let mut fixities = Fixities::default();
    let mut warnings = Warnings::new();
    elaborate_into(
        module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )?;
    Ok((signature, warnings))
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
    fixities: &mut Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
) -> Result<(), ElabError> {
    // Есть ли в модуле ресурсы, спрашивается **до** объявлений: иначе тот же
    // `handleMulti` принимался бы или отвергался в зависимости от того, выше
    // или ниже него написан `resource`, - а гарантия §3.4 от порядка записи не
    // зависит. Само владение по-прежнему объявляется по ходу: ordered scoping
    // §4.8 - решение, и трогать его тут незачем.
    if declares_resource(&module.decls) {
        owned.expect_resources();
    }
    members_into(
        &module.decls,
        None,
        signature,
        metas,
        owned,
        fixities,
        instances,
        warnings,
    )
}

/// Объявлен ли в модуле ресурсный тип - на любой глубине вложенности.
fn declares_resource(decls: &[ast::Decl]) -> bool {
    decls.iter().any(|decl| match &decl.kind {
        DeclKind::Resource(_) => true,
        DeclKind::Module(written) => declares_resource(&written.members),
        _ => false,
    })
}

/// Квалифицирует имя членом модуля: `T` внутри `IntOrd` объявляется как
/// `IntOrd.T` (§4.8, решение 2026-08-30).
///
/// Точка в имени - то, чего поверхностный лексер не порождает, поэтому
/// столкнуться с написанным именем квалифицированное не может, а написать его
/// автор не в состоянии: снаружи модуль читается проекцией.
fn qualify(within: Option<&Enclosing>, name: &str) -> Symbol {
    match within {
        Some(outer) => Rc::from(format!("{}.{name}", outer.name).as_str()),
        None => Rc::from(name),
    }
}

/// Что объявление читает, но не меняет.
///
/// Одной ссылкой, а не двумя: список параметров у каждого помощника и без того
/// длинный, а эти две всегда ходят вместе.
#[derive(Clone, Copy)]
struct Known<'a> {
    /// Владеемые типы (§3.3).
    owned: &'a Owned,
    /// Объявленные фикситеты (§4.4).
    fixities: &'a Fixities,
    /// Классы и их инстансы (§3.5).
    instances: &'a Instances,
}

/// Клаузы, которым не нашлось сигнатуры рядом.
///
/// Сигнатура, ставшая постулатом, - не «её нет», а «она не рядом», и сказать
/// об этом полагается по-разному.
fn detached(
    name: &Symbol,
    postulated: &HashMap<Symbol, Span>,
    qualified: &Symbol,
    span: Span,
) -> ElabError {
    match postulated.get(qualified) {
        Some(signature) => ElabError::DetachedSignature {
            name: Rc::clone(name),
            signature: *signature,
            span,
        },
        None => ElabError::MissingSignature {
            name: Rc::clone(name),
            span,
        },
    }
}

/// `type T = …` на своём месте.
///
/// `type T` без уравнения объявляет абстрактный типовой член, и законно это
/// только в сигнатуре модуля: снаружи её тип брать неоткуда, а постулировать
/// `T : Type` можно и сигнатурой.
#[allow(clippy::too_many_arguments)]
fn written_alias(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    instances: &Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    written: &WrittenAlias<'_>,
    span: Span,
) -> Result<(), ElabError> {
    let Some(body) = written.body else {
        return Err(ElabError::AbstractType {
            name: Rc::clone(&written.name.text),
            span,
        });
    };
    alias(
        signature,
        metas,
        known(owned, fixities, instances),
        warnings,
        within,
        &Aliased {
            name: written.name,
            params: written.params,
            body,
        },
        span,
    )
}

/// Написанный алиас: имя, параметры и тело.
///
/// `body` - `None` у абстрактного типового члена, и законна такая форма
/// только в сигнатуре модуля.
#[derive(Clone, Copy)]
struct WrittenAlias<'a> {
    /// Имя.
    name: &'a ast::Name,
    /// Параметры: `type Twice a = …`.
    params: &'a [ast::Binder],
    /// Что алиас называет.
    body: Option<&'a ast::Expr>,
}

/// То же с телом, которое уже есть: алиас, а не абстрактный член.
#[derive(Clone, Copy)]
struct Aliased<'a> {
    /// Имя.
    name: &'a ast::Name,
    /// Параметры.
    params: &'a [ast::Binder],
    /// Что алиас называет.
    body: &'a ast::Expr,
}

/// Что атрибуты сигнатуры требуют от вердиктов ядра (§4.7, §5.1).
#[derive(Clone, Copy, Default)]
struct Required {
    /// `@total` (§4.7).
    total: bool,
    /// `@noalloc` (§5.1).
    noalloc: bool,
    /// `@fbip` (§5.1).
    fbip: bool,
}

/// Разбирает атрибуты сигнатуры: что из них требует проверки (§4.7, §5.1).
///
/// Все три вердикта считает ядро ([`adamas_core::total`],
/// [`adamas_core::alloc`], [`adamas_core::fbip`]), а атрибут превращается в
/// требование к ответу: «да» у `@total` и `@fbip`, «не аллоцирует» у
/// `@noalloc`. Спрашивает их всех [`verdicts`].
fn required(attributes: &[ast::Name]) -> Result<Required, ElabError> {
    let mut found = Required::default();
    for attribute in attributes {
        match &*attribute.text {
            "total" => found.total = true,
            "fbip" => found.fbip = true,
            "noalloc" => found.noalloc = true,
            _ => {
                return Err(ElabError::Attribute {
                    name: Rc::clone(&attribute.text),
                    why: "такого атрибута в языке нет",
                    span: attribute.span,
                });
            }
        }
    }
    Ok(found)
}

/// Написанная сигнатура - объявление, ждущее своих клауз.
#[allow(clippy::too_many_arguments)]
fn declared_signature<'a>(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    name: &ast::Name,
    ty: &'a ast::Expr,
    attributes: &[ast::Name],
    span: Span,
) -> Result<Pending<'a>, ElabError> {
    let demanded = required(attributes)?;
    // Владение верхнего уровня не выражается: определение всегда `ω`
    // (`sig.rs`: линейность на всю программу не считается), а §3.3 требует
    // `1`. Без этого отказа постулат ресурсного типа - обычное ω-имя, и `drop`
    // по нему зовётся сколько угодно раз.
    if let Some(how) = owned_head(signature, owned, within, ty) {
        return Err(ElabError::OwnedTopLevel {
            owned: how,
            name: Rc::clone(&name.text),
            span: ty.span,
        });
    }
    // Параметры функтора стоят у члена implicit-связываниями: компилятор
    // клауз связывает такие сам, а ссылка изнутри применяется к ним явно
    // (`Elaborator::specialized`).
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    let params = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    // Row-параметр функтора и подъём члена - одна переменная (§10 вопрос 107).
    // Порознь обобщение заводит две, а тело требует их равенства.
    let lift = elaborator.shared_lift(&params);
    let elaborated = elaborator.wrapped(&params, true, |it| {
        it.declaration_lifted(ty, Mult::Many, lift)
    })?;
    let grades = elaborator.grade_arity();
    Ok(Pending {
        required: demanded,
        name: qualify(within, &name.text),
        ty: elaborated,
        grades,
        source: ty,
        span,
    })
}

/// Имена implicit-групп, не встречающиеся в остатке типа (§10 вопросы 79, 81).
///
/// Спрашивается по **написанному**, а не по элаборированному: у поднятого
/// связывания имя тоже implicit, но оно поднято именно потому, что встречается,
/// - а спан у написанного точный, и указать есть на что.
///
/// Форма `{ x : Nat }` в домене читается связыванием, тогда как записана могла
/// быть записью (§4.2, вопрос 79). Оба прочтения дают корректный тип, поэтому
/// отказом это не ловится; различает их ровно то, что имя больше нигде не
/// стоит.
fn unused_implicits(ty: &ast::Expr, into: &mut Warnings) {
    let ast::ExprKind::Pi { binders, codomain } = &ty.kind else {
        return;
    };
    for (at, binder) in binders.iter().enumerate() {
        if binder.visibility != ast::Visibility::Implicit {
            continue;
        }
        for name in &binder.names {
            // `_` не используется намеренно - о нём и предупреждать нечего.
            if &*name.text == "_" {
                continue;
            }
            // Имя, стоящее в позиции кратности, - это первое имя группы, а не
            // выражение (§10 вопрос 41), и обход типов его не находит.
            let graded = binders[at + 1..]
                .iter()
                .filter_map(|it| it.names.first())
                .any(|it| it.text == name.text)
                || grades(codomain, &name.text);
            let later = binders[at + 1..]
                .iter()
                .filter_map(|it| it.ty.as_ref())
                .any(|it| crate::expr::names_any(it, &[&name.text]));
            if graded || later || crate::expr::names_any(codomain, &[&name.text]) {
                continue;
            }
            into.push(Warning::UnusedImplicit {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        }
    }
    unused_implicits(codomain, into);
}

/// Стоит ли имя в позиции кратности где-нибудь в типе (§10 вопрос 41).
///
/// Спрашивается по написанному, а в написанном кратность-параметр - это первое
/// имя группы, а не выражение: `(q x : a)` разбирается двумя именами. Обход
/// типов его поэтому не находит, и без этой проверки предупреждение о
/// неиспользованном имплисите срабатывало бы на всякий `{q : Mult}`.
fn grades(ty: &ast::Expr, name: &str) -> bool {
    let ast::ExprKind::Pi { binders, codomain } = &ty.kind else {
        // Стрелка без имени параметра кратности не пишет, но нести его в своих
        // сторонах вправе: `(q x : a) -> b` стоит доменом у `->`.
        return matches!(&ty.kind, ast::ExprKind::Arrow(left, right)
            if grades(left, name) || grades(right, name));
    };
    let written = |binder: &ast::Binder| {
        binder.names.len() > 1
            && binder
                .names
                .first()
                .into_iter()
                .chain(&binder.factors)
                .any(|it| &*it.text == name)
    };
    // Тип связывания смотрится тоже: `(ω f : (q x : a) -> b)` пишет `q` в
    // домене, а не в кодомене, и у второго порядка это обычное место. Без
    // этого предупреждение о неиспользованном имплисите срабатывало на всякий
    // комбинатор, чей параметр кратности стоит только у аргумента-функции.
    binders
        .iter()
        .any(|binder| written(binder) || binder.ty.as_ref().is_some_and(|it| grades(it, name)))
        || grades(codomain, name)
}

/// Собирает read-only половину состояния.
fn known<'a>(owned: &'a Owned, fixities: &'a Fixities, instances: &'a Instances) -> Known<'a> {
    Known {
        owned,
        fixities,
        instances,
    }
}

/// Почему класс и инстанс не пишутся в теле модуля - причины у них разные.
///
/// У класса своя: методы его - имена верхнего уровня, а модуль их
/// квалифицирует, и разрешение искало бы не то имя. У инстанса - записанная
/// правилом (§3.5, пункт 4): тело функтора инстанциируется на каждое
/// применение, и уникальности там нет по построению.
fn outside_a_module(instance: bool) -> (&'static str, &'static str) {
    if instance {
        (
            "instance",
            "тело функтора инстанциируется на каждое применение, \
             и уникальности инстанса там нет (§3.5)",
        )
    } else {
        (
            "class",
            "методы класса - имена верхнего уровня, а модуль их квалифицирует",
        )
    }
}

/// Отвергает форму, законную только на верхнем уровне.
fn only_at_top(
    within: Option<&Enclosing>,
    name: &Symbol,
    why: &'static str,
    span: Span,
) -> Result<(), ElabError> {
    if within.is_none() {
        return Ok(());
    }
    Err(ElabError::ModuleMember {
        name: Rc::clone(name),
        what: "модуле",
        why,
        span,
    })
}

/// Как объявлен тип, стоящий головой написанного (§3.3).
///
/// Лестница та же, какой разрешается сам тип: владение объявлено под
/// квалифицированным именем, и спрашивать его написанным коротким значило бы
/// принять за своё одноимённое из соседнего модуля.
fn owned_head(
    signature: &Signature,
    owned: &Owned,
    within: Option<&Enclosing>,
    ty: &ast::Expr,
) -> Option<Ownership> {
    let head = crate::own::head_path(ty)?;
    let name =
        crate::expr::qualified_in(signature, within.map(|it| &*it.name), &head).unwrap_or(head);
    owned.how(&name)
}

/// Параметры функтора, под которыми объявляется член. Пусто вне функтора.
///
/// У вложенного модуля это склейка: объемлющие параметры идут первыми, свои
/// вторыми, и член поднимается под всеми сразу.
fn params_of(within: Option<&Enclosing>) -> &[ast::Binder] {
    within.map_or(&[][..], |it| &it.params)
}

/// Оборачивает тело члена лямбдами по параметрам функтора.
///
/// Клаузы делают это сами - параметры стоят у них implicit-связываниями, и
/// компилятор разбора абстрагирует по всем аргументам, - а алиасу и объекту
/// модуля обёртку строит этот помощник.
fn abstracted(params: &[Param], body: Term) -> Term {
    params.iter().rev().fold(body, |inner, param| {
        Term::Lam(param.mult, CoreName::from(&*param.name), Rc::new(inner))
    })
}

/// Объявления одного уровня: верхнего либо тела модуля.
#[allow(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    reason = "прогон элаборации несёт своё состояние; складывать его в структуру значило бы прятать, что именно меняется"
)]
fn members_into(
    decls: &[ast::Decl],
    within: Option<&Enclosing>,
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &mut Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
) -> Result<(), ElabError> {
    // Сигнатуры, ставшие постулатами по ходу прогона: клаузы, пришедшие за
    // ними, - не «нет сигнатуры», а сигнатура не рядом.
    let mut postulated: HashMap<Symbol, Span> = HashMap::new();
    let mut pending: Option<Pending<'_>> = None;
    for decl in decls {
        reserved(decl)?;
        match &decl.kind {
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                unused_implicits(ty, warnings);
                pending = Some(declared_signature(
                    signature, metas, owned, fixities, warnings, within, name, ty, attributes,
                    decl.span,
                )?);
            }
            DeclKind::Clauses { name, clauses } => {
                let qualified = qualify(within, &name.text);
                let Some(declared) = pending.take().filter(|it| it.name == qualified) else {
                    return Err(detached(&name.text, &postulated, &qualified, decl.span));
                };
                define(
                    signature,
                    metas,
                    known(owned, fixities, instances),
                    warnings,
                    within,
                    &declared,
                    clauses,
                    decl.span,
                )?;
            }
            // Алиас: `Point : Type` не годится - `Type` обобщается в `∀u`, а
            // тело живёт в конкретном универсуме. Тип поэтому не пишется, а
            // считается по телу.
            DeclKind::Alias { name, params, body } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                written_alias(
                    signature,
                    metas,
                    owned,
                    fixities,
                    instances,
                    warnings,
                    within,
                    &WrittenAlias {
                        name,
                        params,
                        body: body.as_ref(),
                    },
                    decl.span,
                )?;
            }
            DeclKind::Module(declared) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_module(
                    signature, metas, owned, fixities, instances, warnings, within, declared,
                    decl.span,
                )?;
            }
            DeclKind::Mutual(members) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                only_at_top(
                    within,
                    &Rc::from("mutual"),
                    "члены группы объявляются одним вызовом, а модуль их квалифицирует",
                    decl.span,
                )?;
                declare_mutual(
                    signature, metas, owned, fixities, instances, warnings, members, decl.span,
                )?;
            }
            DeclKind::Class(class) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                let (what, why) = outside_a_module(class.instance);
                only_at_top(within, &Rc::from(what), why, decl.span)?;
                declare_class(
                    signature, metas, owned, fixities, instances, warnings, class, decl.span,
                )?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_family(
                    signature, metas, owned, fixities, warnings, within, data, decl.span,
                )?;
            }
            DeclKind::Resource(resource) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_owned(
                    signature, metas, owned, fixities, instances, warnings, within, resource,
                    decl.span,
                )?;
            }
            // Фикситет ничего не объявляет: он говорит, как читать цепочку, и
            // действует на всё, что написано ниже (§4.8).
            DeclKind::Fixity(decl) => fixities.declare(decl)?,
            DeclKind::Effect(effect) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_effect(
                    signature, metas, owned, fixities, warnings, within, effect, decl.span,
                )?;
            }
        }
    }
    postulate(signature, metas, pending, &mut postulated)
}

/// Ресурсный тип вместе с тем, что решается до его объявления.
#[allow(clippy::too_many_arguments)]
fn declare_owned(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    resource: &ast::Resource,
    span: Span,
) -> Result<(), ElabError> {
    owned.declare(&qualify(within, &resource.name.text), Ownership::Resource);
    declare_resource(
        signature, metas, owned, fixities, instances, warnings, within, resource, span,
    )
}

/// Алиас типа: `type Point = { x : Nat }` (§4.2).
///
/// Собственной сигнатуры у него нет и быть не может: `Point : Type` обобщает
/// универсум в параметр, а тело живёт в конкретном. Универсум поэтому берётся
/// у тела - тем же `is_type`, которым его и проверяют.
fn alias(
    signature: &mut Signature,
    metas: &mut Metas,
    known: Known<'_>,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    written: &Aliased<'_>,
    span: Span,
) -> Result<(), ElabError> {
    let (name, body) = (written.name, written.body);
    let declared = qualify(within, &name.text);
    let names = Names::of(&declared, Vec::new());
    let mut elaborator =
        Elaborator::new(signature, metas, known.owned, known.fixities, warnings).within(within);
    // Связывания двух родов и в одном телескопе: сперва параметры функтора,
    // потом свои. Написанный параметр живёт под функторными - его тип вправе
    // их упоминать, - поэтому и элаборируются они одной последовательностью.
    let outer = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let owned_params = elaborator.beneath(&outer, |it| {
        it.telescope(written.params, false, Mult::Many, Unwritten::Sort)
    })?;
    let params: Vec<Param> = outer.iter().chain(owned_params.iter()).cloned().collect();
    // Тело и его сорт считаются **под параметрами**: тип члена функтора живёт
    // под ними, и в пустом контексте считать его нечем.
    let (term, level) = elaborator.beneath(&params, |it| {
        let term = it.typing(|inner| inner.expr(body, Mult::Many))?;
        let level = it.sort_of(&term).map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Bare(body), &error, span),
            error: Box::new(error),
            names: names.clone(),
        })?;
        Ok((term, level))
    })?;
    let sort = Term::Universe(metas.zonk(&level));
    // Функторные связывания implicit - их подставляет вставка, - а свои
    // explicit: `Twice Nat` автор пишет сам.
    let ty = Elaborator::new(signature, metas, known.owned, known.fixities, warnings)
        .within(within)
        .wrapped(&outer, true, |it| {
            it.wrapped(&owned_params, false, |_| Ok(sort))
        })?;
    let wrapped_body = abstracted(&params, term);
    class::resolve(
        signature,
        metas,
        known.instances,
        known.owned,
        None,
        &wrapped_body,
        &ty,
        span,
    )?;
    signature
        .define_inferred(metas, &declared, Mult::Many, ty, Some(wrapped_body))
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Bare(body), &error, span),
            error: Box::new(error),
            names,
        })?;
    // Умолчание у члена функтора не объявляется: дописывается оно по
    // написанной арности, а член несёт ещё и параметры функтора - написанного
    // и дописанного там разное число.
    if !outer.is_empty() && written.params.iter().any(|it| it.default.is_some()) {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&name.text),
            what: "функторе",
            why: "умолчание дописывается по написанной арности, а член функтора \
                  несёт ещё и его параметры",
            span,
        });
    }
    declare_defaults(
        signature,
        metas,
        known.owned,
        known.fixities,
        warnings,
        &declared,
        written.params,
        Unwritten::Sort,
    )
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
#[allow(clippy::too_many_arguments)]
fn declare_module(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &mut Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    let declared = qualify(within, &module.name.text);
    writable(within, module, span)?;
    sealable(instances, within, module, span)?;
    if module.signature {
        return declare_module_type(
            signature, metas, owned, fixities, instances, warnings, within, &declared, module, span,
        );
    }
    let names = Names::of(&declared, Vec::new());
    if let Some(body) = &module.body {
        return declare_module_value(
            signature, metas, owned, fixities, instances, warnings, within, module, body,
            &declared, span,
        );
    }
    let inner = Enclosing::nested(within, Rc::clone(&declared), &module.params);
    members_into(
        &module.members,
        Some(&inner),
        signature,
        metas,
        owned,
        fixities,
        instances,
        warnings,
    )?;
    // Запечатываются **поднятые члены**, и ставится флаг до проверки
    // аннотации (§10 вопрос 148): соответствие сигнатуре обязано мерить
    // абстракцию тем же зрением, каким её увидит внешний код, - иначе
    // развёрнутый синоним в собственной сигнатуре члена (`eq : Nat -> Nat ->
    // Bool` при `type T = Nat`) проходил проверку по прозрачности и уносил
    // представление наружу написанным типом. Члены друг друга уже видели:
    // их тела элаборированы строкой выше. Снаружи `M.f` есть ссылка на
    // поднятое имя, а не проекция из записи, и одной непрозрачной записи для
    // сокрытия было бы мало.
    if module.sealed {
        seal_members(signature, &inner, &module.members);
    }
    // Телескоп для самой записи считается **после** членов: граница объявления
    // освобождает дырки, и посчитанный заранее умер бы на первом же члене.
    //
    // Связывания двух родов, как у всякого члена: объемлющие параметры, потом
    // свои. У вложенного модуля первые есть, и без них его запись не собрать -
    // члены подняты под ними.
    let mut telescopes =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    let outer = telescopes.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let own = telescopes.beneath(&outer, |it| {
        it.telescope(&module.params, true, Mult::Many, Unwritten::Sort)
    })?;
    let params: Vec<Param> = outer.iter().chain(own.iter()).cloned().collect();

    let object = module_object(signature, metas, &inner, &module.members, &params);
    // Контекст параметров: тип записи считается под ними, а `Pi` над ним
    // строится тем же телескопом.
    let ctx = beneath_params(signature, &params);
    // Аннотация - тип объявления; проверяет соответствие ей `declare`, тем же
    // правилом, что и всякое тело. Без аннотации тип **структурный**: он
    // Аннотация - тип объявления; проверяет соответствие ей `declare`, тем же
    // правилом, что и всякое тело. Без аннотации тип **структурный**: он
    // синтезируется по собранной записи, как и обещает §4.8. У функтора
    // аннотация относится к результату - к записи под параметрами.
    let inner_ty = if let Some(ascription) = &module.ascription {
        let written = Elaborator::new(signature, metas, owned, fixities, warnings)
            .within(within)
            .beneath(&params, |it| {
                it.typing(|inner| inner.expr(ascription, Mult::Many))
            })?;
        // Сигнатура с эффектом-членом инстанцируется меткой модуля (§4.8,
        // §10 вопрос 146): написанное имя разворачивается до записи, и
        // поднятая метка сигнатуры переименовывается в одноимённую метку
        // модуля. Без переименования проверка сравнила бы `{Counting.Tick}`
        // с `{Counter.Tick}` и отвергла всякий модуль под такой сигнатурой:
        // конвертируемость меток именная.
        let written =
            instantiated_ascription(signature, metas, instances, &ctx, &inner, &written, span)?;
        // Проверка **до** объявления, и это не дубль той, что сделает
        // `declare`. Аннотация написана именем, а у имени есть аргументы
        // уровня - дырки; не решив их сравнением с телом, обобщение примет их
        // за параметры самого модуля, и `Nat : Type 0` перестанет подходить
        // под `T : Type u0`, ставшую жёсткой.
        check_within(&ctx, metas, &object, &written).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        zonk_term(metas, &written)
    } else {
        let (ty, _) = infer(&ctx, metas, Mult::Many, &object).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        quote(ctx.size(), &ty)
    };
    // Тип модуля-функтора - `Pi` по параметрам, тело - лямбда по ним же.
    // Видимость у своих **явная**: `OrderedMap IntOrd` пишется, в отличие от
    // параметров у членов, которые автор не пишет никогда. У объемлющих
    // обратное, и по той же причине: `Outer.Inner` изнутри `Outer` пишется без
    // `Key`, потому что писать эту позицию некому - её подставляет вставка.
    let piled = |inner: Term, params: &[Param], implicit: bool| {
        params.iter().rev().fold(inner, |codomain, param| {
            let binder = if implicit {
                Binder::implicit(param.mult)
            } else {
                Binder::explicit(param.mult)
            };
            Term::Pi(
                binder,
                CoreName::from(&*param.name),
                Rc::clone(&param.ty),
                adamas_core::row::Row::empty(),
                Rc::new(codomain),
            )
        })
    };
    let ty = piled(piled(inner_ty, &own, false), &outer, true);
    let body = abstracted(&params, object);
    // Запечатывание - свойство определения, а не значения (§3.5): тело
    // остаётся, а сравнение перестаёт его разворачивать. Без аннотации
    // запечатывать нечего - скрывать было бы от чего, но нечем.
    signature
        .define_opaque(metas, &declared, Mult::Many, ty, Some(body), module.sealed)
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })?;
    // Модуль, аннотированный сигнатурой, становится кандидатом для
    // implicit-параметра функтора (§4.8): тот апплицируется без явного
    // аргумента «через тот же механизм резолвинга, что и class-инстансы».
    //
    // Запечатанный не идёт: снаружи его представление скрыто, и подставлять
    // такой неявно значило бы решать за автора, какая абстракция ему нужна.
    // Функтор тоже не идёт - он сам ждёт аргумента, и реализацией сигнатуры
    // является не он, а его применение.
    // Вложенный в функтор не идёт по тому же доводу: параметр он несёт, пусть и
    // не свой, поэтому реализацией сигнатуры является не он, а его применение.
    //
    // Цепочкой `&&` с `let` это не пишется: та требует Rust 2024, а MSRV
    // проекта 1.85 (джоба `msrv` его и ловит).
    let ascribed = module
        .ascription
        .as_ref()
        .filter(|_| !module.sealed && params.is_empty())
        .and_then(ascription_name);
    if let Some(written) = ascribed {
        instances.implements(&written, &declared);
    }
    Ok(())
}

/// Контекст, в котором стоят параметры: под ними живут и запись, и её тип.
fn beneath_params<'a>(signature: &'a Signature, params: &[Param]) -> Ctx<'a> {
    params.iter().fold(Ctx::new(signature), |ctx, param| {
        let bound = ctx.eval(&param.ty);
        ctx.bind(CoreName::from(&*param.name), param.mult, bound)
    })
}

/// Запись модуля: поле на каждого объявленного члена, в порядке написания.
///
/// Клаузы своего поля не заводят - его завела сигнатура, за которой они идут.
/// Член функтора поднят вместе с параметрами, поэтому здесь он применяется к
/// ним: запись собирается уже специализированной.
fn module_object(
    signature: &Signature,
    metas: &mut Metas,
    within: &Enclosing,
    members: &[ast::Decl],
    params: &[Param],
) -> Term {
    let mut written = Vec::new();
    for member in members {
        // Метка эффекта полем не становится: поле записи типизируется типом, а
        // метка - не тип (§3.4), и `module type` объявить её нечем. Снаружи она
        // видна поднятым именем наравне с прочими членами - `Store.Ask`, - а в
        // самой записи её места нет. Оставь поле, и всякий модуль с эффектом
        // перестал бы подходить под свою сигнатуру числом полей, то есть
        // запечатать эффект стало бы нечем.
        if matches!(member.kind, DeclKind::Effect(_)) {
            continue;
        }
        let Some(name) = member_name(member) else {
            continue;
        };
        let full = qualify(Some(within), name);
        let Some(mut term) = signature.instantiate(&full, metas) else {
            continue;
        };
        // Row-арность члена-значения инстанцируется пустой row, а не дыркой
        // (§10 вопрос 147). Носит её только `module type`: поле хранит саму
        // сигнатуру - её члены с написанными метками, - а не место её
        // использования, поэтому дырку в теле записи объемлющего не решало бы
        // ничто, и граница объявления отвергала бы модуль нерешённым хвостом.
        if let Term::Const(name, levels, args) = &term {
            if !args.row_args().is_empty() {
                term = Term::Const(
                    Rc::clone(name),
                    Rc::clone(levels),
                    Args::new(
                        args.row_args().iter().map(|_| Row::empty()),
                        args.mult_args().iter().copied(),
                    ),
                );
            }
        }
        for position in 0..params.len() {
            let index = u32::try_from(params.len() - 1 - position).unwrap_or(u32::MAX);
            term = Term::App(Rc::new(term), Rc::new(Term::var(index)));
        }
        written.push((CoreName::from(&**name), Rc::new(term)));
    }
    Term::Object(written.into())
}

/// Ставит непрозрачность поднятым членам - **включая вложенные модули**.
///
/// Вложенный модуль поднимает свои члены под своей квалификацией, и в
/// `module.members` объемлющего их нет: запечатав только непосредственных,
/// `Outer.Inner.Flag` оставляли прозрачным, и `:>` на двух уровнях не держал
/// того, что держал на одном. Спуск здесь тот же, что и у подъёма, - иначе два
/// обхода разъезжаются.
fn seal_members(signature: &mut Signature, within: &Enclosing, members: &[ast::Decl]) {
    for member in members {
        if let Some(name) = member_name(member) {
            signature.seal(&qualify(Some(within), name));
        }
        if let DeclKind::Module(inner) = &member.kind {
            // Спуску нужно только имя: запечатывается имя члена, а телескоп в
            // квалификации не участвует.
            let deeper = Enclosing {
                name: qualify(Some(within), &inner.name.text),
                params: Rc::clone(&within.params),
            };
            seal_members(signature, &deeper, &inner.members);
        }
    }
}

/// Заключение написанной головы: `{Eqv a} => Eqv (List a)` даёт `Eqv (List a)`.
fn conclusion_of(head: &ast::Expr) -> &ast::Expr {
    let mut current = head;
    while let ast::ExprKind::Pi { codomain, .. } = &current.kind {
        current = codomain;
    }
    current
}

/// Имя в голове объявления и её аргументы: `Eqv Nat` даёт `(Eqv, [Nat])`.
fn spine_of(head: &ast::Expr) -> Option<(&ast::Name, Vec<&ast::Expr>)> {
    let mut arguments = Vec::new();
    let mut current = head;
    while let ast::ExprKind::App(callee, argument) = &current.kind {
        arguments.push(&**argument);
        current = callee;
    }
    arguments.reverse();
    match &current.kind {
        ast::ExprKind::Name(name) => Some((name, arguments)),
        _ => None,
    }
}

/// Класс либо его инстанс (§3.5, §4.1).
///
/// **Класс - это тип записи, параметризованный своими аргументами**, плюс по
/// определению верхнего уровня на каждый метод: `eq` объявляется как
/// `{0 a : Type} -> {ω d : Eqv a} -> a -> a -> Bool` с телом `\a d -> d.eq`.
/// Словарь стоит implicit-связыванием, поэтому в месте вызова он вставляется
/// дыркой, а заполняется поиском - см. [`crate::class`].
///
/// **Инстанс - это запись**, объявленная под невыразимым именем `Eqv#Nat` и
/// проверенная против `Eqv Nat`. Тип метода в нём не пишется: он **выводится**
/// из класса проекцией словаря, иначе автор переписывал бы сигнатуру, уже
/// написанную в классе.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_class(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    class: &ast::ClassDecl,
    span: Span,
) -> Result<(), ElabError> {
    // У инстанса с контекстом голова написана `Pi`: имя класса живёт в её
    // заключении, а связывания перед ним - словари контекста.
    let written = if class.instance {
        conclusion_of(&class.head)
    } else {
        &class.head
    };
    let Some((name, _)) = spine_of(written) else {
        return Err(ElabError::ClassHead { span });
    };
    if class.instance {
        return declare_instance(
            signature, metas, owned, fixities, instances, warnings, class, name, span,
        );
    }
    // Параметры класса разбирает парсер теми же формами, что у семейства.
    // Ненаписанная кратность здесь **нулевая**: параметр класса - это тип, и в
    // рантайме его нет. Тем же нулём он стоит у метода:
    // `{0 a : Type} -> {ω d : C a} -> …`.
    let params: Vec<ast::Binder> = class
        .params
        .iter()
        .map(|binder| ast::Binder {
            mult: binder.mult.or(Some(ast::MultAnn {
                mult: ast::Mult::Zero,
                span: binder.span,
            })),
            ..binder.clone()
        })
        .collect();
    if params.is_empty() {
        return Err(ElabError::ClassHead { span });
    }
    // Поля суперклассов идут **первыми**: разряжает их объявление инстанса, а
    // не автор, и имя у них невыразимое - написать его нечем (§3.5).
    let mut members = Vec::with_capacity(class.superclasses.len() + class.members.len());
    let mut info = Class {
        coherent: class.coherent,
        superclasses: class.superclasses.len(),
        ..Class::default()
    };
    for (index, superclass) in class.superclasses.iter().enumerate() {
        members.push(WrittenField {
            name: ast::Name {
                text: Rc::from(format!("#super{index}").as_str()),
                span: superclass.span,
            },
            params: &[],
            ty: Some(superclass),
        });
    }
    class_members(class, &mut info, &mut members)?;
    flat_shape(&name.text, class, &params, &mut info)?;
    let names = Names::of(&name.text, Vec::new());
    // Класс - **функция** от своих параметров в тип записи, а не сам тип:
    // `Eqv Nat` есть применение. Отсюда тело лямбдой, а тип - `Pi` над
    // универсумом, в котором живёт запись.
    let kinds = superclass_kinds(signature, metas, class);
    // Row-параметр у класса один на все члены и заводится, только если метки
    // написаны хоть у одного (§10 вопрос 102). Он **не дырка**: обобщение
    // читает тип определения, а поля словаря живут в теле, и вывести число
    // оттуда нечем - параметр пишется сразу и объявляется арностью.
    let rowed = members
        .iter()
        .filter_map(|it| it.ty)
        .any(crate::expr::writes_effects)
        .then(|| Row::closing([], Some(Tail::Var(RowVar(0)))));
    let mut elaborator = Elaborator::new(signature, metas, owned, fixities, warnings);
    let telescope = elaborator.telescope(&params, false, Mult::Zero, Unwritten::Given(&kinds))?;
    let (record, level) = elaborator.beneath(&telescope, |it| {
        let fields = it.module_members(&members, rowed.as_ref())?;
        let record = Term::Record(Fields::closed(fields.into()));
        let level = it.sort_of(&record).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        // Через значение, а не зонканьем: домен поднятого связывания есть
        // дырка терма, решается она универсумом, и решение подставляется как
        // записано - `?m #0` даёт бета-редекс `(\m -> Type u) a` вместо
        // `Type u`. Обратное чтение из значения его сводит, и тогда уровень
        // виден и типу словаря, и обобщению (тот же приём, что у головы
        // инстанса, лог 2026-08-31).
        let zonked = zonk_term(it.metas, &record);
        let value = it.valued(&zonked);
        Ok((quote(it.depth(), &value), level))
    })?;
    let sort = Term::Universe(metas.zonk(&level));
    let ty = Elaborator::new(signature, metas, owned, fixities, warnings).wrapped(
        &telescope,
        false,
        |_| Ok(sort),
    )?;
    let body = abstracted(&telescope, record);
    signature
        .define_rowed(
            metas,
            &name.text,
            Mult::Many,
            ty,
            Some(body),
            u32::from(rowed.is_some()),
        )
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })?;
    declare_defaults(
        signature,
        metas,
        owned,
        fixities,
        warnings,
        &name.text,
        &params,
        Unwritten::Sort,
    )?;
    // Имя верхнего уровня получает **метод**, а не поле суперкласса: его
    // разряжает разрешение, и писать его автору незачем.
    for method in &info.methods {
        declare_method(signature, metas, &name.text, method, span)?;
    }
    instances.declare(&name.text, info);
    Ok(())
}

/// Класс `Flat` объявляется так, как написан в §4.11, - и когерентен.
///
/// Форма спрашивается потому, что компилятор знает это имя и **выводит** по
/// нему инстансы: класс с тем же именем и другим содержимым сломал бы вывод
/// молча. Когерентность же не объявляется автором, а следует из вывода: инстанс
/// вычисляется по представлению, выбирать нечего. Отсюда и §4.8 - запрет на
/// class-констрейнты в запечатывающей сигнатуре охраняет от осадки выбора и
/// когерентные классы пропускает, а `Flat T` в сигнатуре модуля есть
/// обязательство о представлении.
fn flat_shape(
    name: &Symbol,
    class: &ast::ClassDecl,
    params: &[ast::Binder],
    info: &mut Class,
) -> Result<(), ElabError> {
    if &**name != crate::flat::FLAT {
        return Ok(());
    }
    let written = params.iter().map(|it| it.names.len()).sum::<usize>();
    let shaped = written == 1
        && class.superclasses.is_empty()
        && info.defaults.is_empty()
        && info.methods.len() == 1
        && &*info.methods[0] == crate::flat::LAYOUT;
    if !shaped {
        return Err(ElabError::FlatShape {
            why: "класс `Flat` объявляется одним параметром и единственным методом \
                  `layout : Layout` (§4.11)",
            span: class.head.span,
        });
    }
    info.coherent = true;
    Ok(())
}

/// `instance Eqv Nat where …` - запись, проверенная против `Eqv Nat`.
#[allow(clippy::too_many_arguments)]
fn declare_instance(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    class: &ast::ClassDecl,
    name: &ast::Name,
    span: Span,
) -> Result<(), ElabError> {
    if !instances.is_class(&name.text) {
        return Err(ElabError::UnknownName {
            name: Rc::clone(&name.text),
            span: name.span,
        });
    }
    // Инстанс `Flat` не пишется: его порождает компилятор структурно (§4.11).
    // Отказ стоит здесь, а не в разрешении, потому что написанный инстанс
    // молча заслонил бы выведенный - и объявил бы представление, которого у
    // типа нет.
    if &*name.text == crate::flat::FLAT {
        return Err(ElabError::FlatShape {
            why: "инстанс `Flat` руками не пишется: компилятор выводит его \
                  структурно по представлению типа (§4.11)",
            span,
        });
    }
    let names = Names::of(&name.text, Vec::new());
    let fail = |error: TypeError| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    };
    // Голова элаборируется **один раз на всю группу**: члены инстанса
    // объявляются вместе, поэтому граница объявления одна, и дырки уровня
    // доживают до неё.
    let written = written_head(
        signature, metas, owned, fixities, warnings, class, span, &names,
    )?;
    let prefix = leading(&written);
    let Some((_, arguments)) = applied_head(signature, under_prefix(&written), span)? else {
        return Err(ElabError::ClassHead { span });
    };
    coherence(signature, instances, name, &arguments, &prefix, span)?;
    sealed_abstraction(signature, instances, &prefix, &written, span)?;
    // Именованный объявляется под своим именем: сослаться на него через
    // `using` и `@` можно только так (§4.3). Анонимный - под невыразимым.
    let declared: Symbol = match &class.name {
        Some(written) => Rc::clone(&written.text),
        None => Rc::from(mangled(&name.text, &arguments).as_str()),
    };
    // Кандидат запоминается **до** членов: иначе о дубликате скажет ядро,
    // назвав `Eqv#Nat.eq` - имя, которого автор не писал.
    if class.name.is_some() {
        instances.add_named(&name.text, &arguments, Rc::clone(&declared));
    } else if !instances.add(&name.text, &arguments, Rc::clone(&declared)) {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&name.text),
            what: "программе",
            why: "анонимный инстанс для этого типа уже объявлен; несколько на один тип \
                  пишутся именованными",
            span,
        });
    }
    let (superclasses, members) = instance_members(class, instances, &name.text, span)?;
    let qualified: Vec<Symbol> = members
        .iter()
        .map(|(method, ..)| Rc::from(format!("{declared}.{method}").as_str()))
        .collect();

    declare_members(
        signature,
        metas,
        owned,
        fixities,
        instances,
        warnings,
        name,
        &arguments,
        &prefix,
        &written,
        superclasses,
        &members,
        &qualified,
        span,
        &names,
    )?;

    // Словарь - запись из членов, применённых к своим же связываниям.
    // Заголовок считается заново: объявление группы освободило дырки, и
    // прежний уже не жив.
    let written = written_head(
        signature, metas, owned, fixities, warnings, class, span, &names,
    )?;
    let prefix = leading(&written);
    let mut object = Vec::with_capacity(superclasses + members.len());
    // Поле суперкласса - дырка: разряжает его **разрешение**, а не автор
    // (§3.5). Стоит она в контексте префикса, поэтому и тип у неё - тот же
    // телескоп, оканчивающийся типом поля.
    for index in 0..superclasses {
        let field: Symbol = Rc::from(format!("#super{index}").as_str());
        let (ty, _) = instance_method(signature, metas, &prefix, &written, &field, span, &names)?;
        let size = u32::try_from(prefix.len()).unwrap_or(u32::MAX);
        let hole = metas.fresh_term(Ctx::new(signature).eval(&ty), size);
        object.push((CoreName::from(&*field), Rc::new(hole)));
    }
    // Row-аргументы члена берутся у **заголовка**, а не свежими дырками. Член
    // обобщён по тем же дыркам, что стоят в голове класса, поэтому
    // инстанцирование его заголовком тождественно. Свежие годились, пока
    // row-параметров у класса не было; с ними член, чей тип row не называет
    // (`zero : a` рядом с эффектным `run`), получал дырку, которую не
    // определяет ничто, и она доживала до границы объявления (§10 вопрос 102).
    let carried = head_rows(under_prefix(&written));
    for (at, (method, ..)) in members.iter().enumerate() {
        let Some(term) = instantiate_carrying(signature, metas, &qualified[at], &carried) else {
            continue;
        };
        let applied = (0..prefix.len()).fold(term, |callee, position| {
            let index = u32::try_from(prefix.len() - 1 - position).unwrap_or(u32::MAX);
            Term::App(Rc::new(callee), Rc::new(Term::var(index)))
        });
        object.push((CoreName::from(&**method), Rc::new(applied)));
    }
    let object = abstracted(&prefix, Term::Object(object.into()));
    // Поля суперклассов заполняются поиском - до проверки, которой дырка
    // уже мешала бы.
    class::resolve(
        signature, metas, instances, owned, None, &object, &written, span,
    )?;
    // `check_within`, а не `check_closed_with`: нерешённая дырка уровня здесь -
    // будущий параметр самого словаря, и запрет отвергал бы всякий
    // полиморфный инстанс. Окончательный запрет ставит объявление.
    check_within(&Ctx::new(signature), metas, &object, &written).map_err(fail)?;
    let written = zonk_term(metas, &written);
    signature
        .define_inferred(metas, &declared, Mult::Many, written, Some(object))
        .map_err(fail)
}

/// Члены класса: сигнатуры методов в поля, умолчания - в реестр.
///
/// Поля суперклассов уже сложены вызывающим, поэтому список приходит
/// непустым, а не собирается здесь с нуля.
fn class_members<'a>(
    class: &'a ast::ClassDecl,
    info: &mut Class,
    members: &mut Vec<WrittenField<'a>>,
) -> Result<(), ElabError> {
    for member in &class.members {
        match &member.kind {
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                // Атрибуты у метода не выбрасываются молча: все три были бы
                // обещанием про **каждый** инстанс, а вердикт считается у
                // определения, и определение это - член инстанса.
                let demanded = required(attributes)?;
                if demanded.total || demanded.noalloc || demanded.fbip {
                    return Err(ElabError::ModuleMember {
                        name: Rc::clone(&name.text),
                        what: "классе",
                        why: "`@total`, `@noalloc` и `@fbip` у метода обещали бы вердикт \
                              за каждый инстанс, а считается он у определения - пишите \
                              атрибут у члена инстанса",
                        span: member.span,
                    });
                }
                members.push(WrittenField {
                    name: name.clone(),
                    params: &[],
                    ty: Some(ty),
                });
                info.methods.push(Rc::clone(&name.text));
            }
            // Умолчание хранится написанным: тело его зовёт другие методы того
            // же класса, а словарь для них объявляет инстанс. Раскрывается оно
            // поэтому там, где этот словарь и собирается.
            DeclKind::Clauses { name, clauses } => {
                if !info.methods.contains(&name.text) {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&name.text),
                        span: member.span,
                    });
                }
                info.defaults.insert(Rc::clone(&name.text), clauses.clone());
            }
            _ => {
                return Err(ElabError::ModuleMember {
                    name: member_name(member)
                        .cloned()
                        .unwrap_or_else(|| Rc::from("_")),
                    what: "классе",
                    why: "класс несёт сигнатуры методов и умолчания к ним",
                    span: member.span,
                });
            }
        }
    }
    Ok(())
}

/// Условия пригодности `coherent` (§3.5), проверяемые на объявлении инстанса.
///
/// Пункты 2 и 4 - orphan-правило и «только верхний уровень» - предмета
/// сегодня не имеют: инстанс объявляется единственной единицей компиляции и
/// только на верхнем уровне (`only_at_top`), поэтому чужого модуля, где его
/// можно было бы написать, просто нет.
///
/// Пункт 3 - глобальная непересекаемость - проверяется реестром, а не обходом
/// программы: ключ кандидата есть головы всех аргументов после δ, значит две
/// декларации с унифицирующимися головами дают один ключ, а с разными -
/// заведомо не унифицируются.
fn coherence(
    signature: &Signature,
    instances: &Instances,
    class: &ast::Name,
    arguments: &Rc<[Symbol]>,
    prefix: &[Param],
    span: Span,
) -> Result<(), ElabError> {
    if !instances.is_coherent(&class.text) {
        return Ok(());
    }
    if instances.declared(&class.text, arguments) {
        return Err(ElabError::CoherentDuplicate {
            class: Rc::clone(&class.text),
            written: class::written(&class.text, arguments),
            span,
        });
    }
    // Пункт 1: контекст состоит только из когерентных классов. Связывания
    // префикса - это и типовые параметры, и словари контекста; первые головы
    // класса не имеют, поэтому отсеиваются сами.
    for param in prefix {
        let Some((context, _)) = class::applied(signature, &param.ty) else {
            continue;
        };
        if instances.is_class(&context) && !instances.is_coherent(&context) {
            return Err(ElabError::CoherentContext {
                class: Rc::clone(&class.text),
                context,
                span,
            });
        }
    }
    Ok(())
}

/// Написанная голова инстанса как тип словаря.
///
/// Считается заново на каждое объявление: граница объявления освобождает
/// дырки, а у полиморфного инстанса уровень как раз и остаётся нерешённым до
/// обобщения. Тот же порядок у функтора (лог 2026-08-31).
#[allow(clippy::too_many_arguments)]
fn written_head(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    class: &ast::ClassDecl,
    span: Span,
    names: &Names,
) -> Result<Term, ElabError> {
    let written = Elaborator::new(signature, metas, owned, fixities, warnings)
        .declaration(&class.head, Mult::Many)?;
    is_type(&Ctx::new(signature), metas, &written).map_err(|error| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    })?;
    // Зонк подставляет решение дырки целиком и оставляет бета-редекс:
    // домен второго связывания заголовка - дырка над первым, и её решение
    // приезжает лямбдой, применённой к нему. Инференс такого домена спотыкается
    // (лямбде нужна аннотация), поэтому заголовок читается обратно из значения.
    // Константы при этом остаются свёрнутыми - класс в голове переживает
    // нормализацию.
    let written = zonk_term(metas, &written);
    Ok(pure_spine(&quote(0, &Ctx::new(signature).eval(&written))))
}

/// Стрелки заголовка инстанса - с пустой row: они словарные, применение чистое.
///
/// Обычная элаборация даёт стрелке auto-lift (§3.4), и открытая row уезжала
/// row-параметром словаря: применение кандидата к контексту «производило»
/// её, а на месте использования дырку этого параметра не определяло ничто -
/// «остался неразрешённый хвост row» у всякого инстанса с контекстом и
/// эффектным методом (§10 вопрос 138). Домены не трогаются: row там - часть
/// написанного типа, а не контракта словарной стрелки.
fn pure_spine(written: &Term) -> Term {
    match written {
        Term::Pi(binder, name, domain, _, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            Rc::clone(domain),
            Row::empty(),
            Rc::new(pure_spine(codomain)),
        ),
        other => other.clone(),
    }
}

/// Член инстанса: имя метода, клаузы и место, откуда они взяты.
type Written = (Symbol, Vec<ast::Clause>, Span);

/// Члены инстанса: методы класса вместе с клаузами, которые их определяют.
///
/// Порядок - **классовый**, а не написанный: поля словаря обязаны идти так,
/// как объявлены. Ненаписанный метод берёт умолчание, а его нет - отказ.
fn instance_members(
    class: &ast::ClassDecl,
    instances: &Instances,
    name: &Symbol,
    span: Span,
) -> Result<(usize, Vec<Written>), ElabError> {
    let mut written = Vec::with_capacity(class.members.len());
    for member in &class.members {
        let DeclKind::Clauses { name, clauses } = &member.kind else {
            return Err(ElabError::ModuleMember {
                name: member_name(member)
                    .cloned()
                    .unwrap_or_else(|| Rc::from("_")),
                what: "инстансе",
                why: "тип метода написан в классе, поэтому инстанс несёт только клаузы",
                span: member.span,
            });
        };
        written.push((name, clauses, member.span));
    }
    let Some(info) = instances.class(name) else {
        return Err(ElabError::UnknownName {
            name: Rc::clone(name),
            span,
        });
    };
    for (method, _, at) in &written {
        if !info.methods.contains(&method.text) {
            return Err(ElabError::ModuleMember {
                name: Rc::clone(&method.text),
                what: "инстансе",
                why: "у класса нет такого метода",
                span: *at,
            });
        }
    }
    let mut found = Vec::with_capacity(info.methods.len());
    for method in &info.methods {
        let (clauses, at) = match written.iter().find(|(it, ..)| it.text == *method) {
            Some((_, clauses, at)) => ((*clauses).clone(), *at),
            None => match info.defaults.get(method) {
                Some(clauses) => (clauses.clone(), span),
                None => {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(method),
                        span,
                    });
                }
            },
        };
        found.push((Rc::clone(method), clauses, at));
    }
    Ok((info.superclasses, found))
}

/// Тип одного метода инстанса - выведенный из класса проекцией словаря.
///
/// Тип читается дважды: под словарём - чтобы проверить, что он на него не
/// ссылается, - и без него, потому что члену словарь не связывает. Индексы у
/// двух чтений различаются ровно на это связывание.
#[allow(clippy::too_many_arguments)]
fn instance_method(
    signature: &Signature,
    metas: &mut Metas,
    prefix: &[Param],
    written: &Term,
    method: &str,
    span: Span,
    names: &Names,
) -> Result<(Term, u32), ElabError> {
    let fail = |error: TypeError| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    };
    let mut ctx = Ctx::new(signature);
    for param in prefix {
        let bound = ctx.eval(&param.ty);
        ctx = ctx.bind(CoreName::from(&*param.name), param.mult, bound);
    }
    let value = ctx.eval(under_prefix(written));
    let bound = ctx.bind(CoreName::from("d"), Mult::Many, value);
    // Параметры поля переходят в параметры **члена инстанса**: у поля своё
    // пространство индексов, и граница с определением - здесь (§10 вопрос 115).
    let (found, shape) =
        adamas_core::check::projected(&bound, metas, &Term::var(0), &CoreName::from(method))
            .map_err(fail)?;
    if mentions_depth(&quote(bound.size(), &found), 0) {
        return Err(ElabError::ModuleMember {
            name: Rc::from(method),
            what: "классе",
            why: "тип метода зависит от значения другого метода, и вывести его \
                  в инстансе нечем",
            span,
        });
    }
    let depth = u32::try_from(prefix.len()).unwrap_or(u32::MAX);
    let ty = zonk_term(metas, &quote(depth, &found));
    let ty = prefix.iter().rev().fold(ty, |inner, param| {
        Term::Pi(
            Binder::implicit(param.mult),
            CoreName::from(&*param.name),
            Rc::clone(&param.ty),
            adamas_core::row::Row::empty(),
            Rc::new(inner),
        )
    });
    Ok((ty, u32::from(shape.mults)))
}

/// Ведущие связывания типа - те, под которыми живут и словарь, и его члены.
fn leading(ty: &Term) -> Vec<Param> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, name, domain, _, codomain) = current {
        found.push(Param {
            mult: binder.mult,
            name: Rc::from(&**name),
            ty: Rc::clone(domain),
        });
        current = codomain;
    }
    found
}

/// Что под ними написано.
fn under_prefix(ty: &Term) -> &Term {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    current
}

/// Row-аргументы головы применения. Пусто, если голова не ссылка.
fn head_rows(ty: &Term) -> Vec<Row<Term>> {
    let mut current = ty;
    while let Term::App(callee, _) = current {
        current = callee;
    }
    match current {
        Term::Const(_, _, args) => args.row_args().to_vec(),
        _ => Vec::new(),
    }
}

/// Ссылка на определение со **своими** row-аргументами и свежими уровнями.
///
/// От [`Signature::instantiate`] отличается только row: уровни там и здесь
/// свежие. Недостающие берутся дырками - член вправе нести row-параметров
/// больше, чем голова, если его тип назвал свой хвост.
fn instantiate_carrying(
    signature: &Signature,
    metas: &mut Metas,
    name: &str,
    carried: &[Row<Term>],
) -> Option<Term> {
    let definition = signature.lookup(name)?;
    let levels: Rc<[Level]> = (0..definition.level_arity)
        .map(|_| metas.fresh_level())
        .collect();
    let rows = (0..definition.row_arity as usize).map(|index| {
        carried
            .get(index)
            .cloned()
            .unwrap_or_else(|| metas.fresh_row())
    });
    Some(Term::Const(CoreName::from(name), levels, Args::rows(rows)))
}

/// Невыразимое имя анонимного инстанса: `Eqv#Nat`, `Conv#Nat#Bool`.
fn mangled(class: &str, heads: &[Symbol]) -> String {
    let mut out = String::from(class);
    for head in heads {
        out.push('#');
        out.push_str(head);
    }
    out
}

/// Имя класса и головы всех его аргументов - ключ кандидата.
type AppliedHead = (Symbol, Rc<[Symbol]>);

/// Имя класса и головы всех его аргументов - по элаборированному типу.
///
/// Головы **всех**: у многопараметрического класса первая ничего не решает
/// (§4.1), и ключ кандидата составляется из них целиком.
fn applied_head(
    signature: &Signature,
    ty: &Term,
    span: Span,
) -> Result<Option<AppliedHead>, ElabError> {
    let Some((class, head)) = class::applied(signature, ty) else {
        return Ok(None);
    };
    match head {
        class::Head::Named(heads) => Ok(Some((class, heads))),
        // Ключа у такой головы нет, и «голова пишется именем с аргументами»
        // здесь неправда: написана она именно так, просто имя разворачивается
        // в собственный параметр.
        class::Head::Projecting => Err(ElabError::ProjectingHead { class, span }),
        _ => Ok(None),
    }
}

/// Метод класса - определение верхнего уровня, проецирующее словарь.
///
/// Тип его собирается не переписыванием написанного, а **проекцией**: под
/// связываниями `{0 a} {ω d : C a}` тип `d.eq` считает та же проверка, что
/// считает всякую проекцию, и телескоп класса с его зависимостями учитывается
/// сам собой.
fn declare_method(
    signature: &mut Signature,
    metas: &mut Metas,
    class: &Symbol,
    method: &Symbol,
    span: Span,
) -> Result<(), ElabError> {
    let names = Names::of(method, Vec::new());
    let fail = |error: TypeError| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    };
    let Some(applied) = signature.instantiate(class, metas) else {
        return Ok(());
    };
    let (mut kind, _) = infer(&Ctx::new(signature), metas, Mult::Zero, &applied).map_err(fail)?;
    // Параметров у класса бывает несколько (§4.1), поэтому связывания
    // собираются циклом: у двухпараметрического `Conv a b` метод получает оба,
    // и словарь стоит за ними.
    let mut ctx = Ctx::new(signature);
    let mut sorts = Vec::new();
    while let Value::Pi(_, _, domain, _, codomain) = &*kind.clone() {
        sorts.push(quote(ctx.size(), domain));
        let name = CoreName::from(format!("a{}", sorts.len() - 1).as_str());
        ctx = ctx.bind(name, Mult::Zero, Rc::clone(domain));
        kind = codomain.clone().apply(ctx.eval(&Term::var(0)));
    }
    if sorts.is_empty() {
        return Ok(());
    }
    let arity = u32::try_from(sorts.len()).unwrap_or(u32::MAX);
    let dictionary = (0..arity).fold(applied.clone(), |callee, at| {
        Term::App(Rc::new(callee), Rc::new(Term::var(arity - 1 - at)))
    });
    let bound = ctx.eval(&dictionary);
    let inner = ctx.bind(CoreName::from("d"), Mult::Many, bound);
    let projection = Term::Project(Rc::new(Term::var(0)), CoreName::from(&**method));
    // Параметры поля становятся **параметрами метода**: у поля своё
    // пространство индексов, и на границе с определением оно переходит в его
    // собственное (§10 вопрос 115). Дырка тут не годится - она решилась бы
    // один раз на всё определение.
    let (ty, shape) =
        adamas_core::check::projected(&inner, metas, &Term::var(0), &CoreName::from(&**method))
            .map_err(fail)?;
    // Row-параметр класса достаётся методу, **только если его называет поле**.
    // Иначе он не определяется в месте вызова ничем: погашение решает хвост по
    // стрелке типа метода, а у `zero : a` стрелки нет вовсе, и дырка доживала
    // бы до границы объявления вызывающего (§10 вопрос 102). Незваный решается
    // пустой row - «метод не производит ничего сверх написанного», - и тогда
    // словарь ему нужен при пустом аргументе, каким его и даст разрешение.
    let quoted = quote(inner.size(), &ty);
    let mut mentioned = Generalization::default();
    mentioned.collect_term(metas, &quoted);
    for row in head_rows(&applied) {
        if let Some(Tail::Meta(meta)) = row.tail() {
            if !mentioned.rows().contains(&meta) {
                metas.solve_row(meta, Row::empty());
            }
        }
    }
    let ty = Term::Pi(
        Binder::implicit(Mult::Many),
        CoreName::from("d"),
        Rc::new(dictionary),
        adamas_core::row::Row::empty(),
        Rc::new(quoted),
    );
    let ty = sorts.iter().enumerate().rev().fold(ty, |body, (at, sort)| {
        Term::Pi(
            Binder::implicit(Mult::Zero),
            CoreName::from(format!("a{at}").as_str()),
            Rc::new(sort.clone()),
            adamas_core::row::Row::empty(),
            Rc::new(body),
        )
    });
    let body = Term::Lam(Mult::Many, CoreName::from("d"), Rc::new(projection));
    let body = (0..sorts.len()).rev().fold(body, |inner, at| {
        Term::Lam(
            Mult::Zero,
            CoreName::from(format!("a{at}").as_str()),
            Rc::new(inner),
        )
    });
    signature
        .define_graded(
            metas,
            method,
            Mult::Many,
            ty,
            Some(body),
            u32::from(shape.mults),
        )
        .map_err(fail)
}

/// Члены инстанса - **одной группой**.
///
/// Группа нужна затем, что словарь для собственной цели собирается записью из
/// всех членов сразу: объявляй их по одному, и первый не смог бы пользоваться
/// собственным инстансом - включая простую саморекурсию. Арность параметров
/// уровня при этом известна **до** проверки тел: тип члена выводится из класса
/// и головы, а не из тела, - поэтому она объявляется явно, и предмет §10
/// вопроса 54 здесь не возникает.
/// Чем член инстанса разряжает цель, указывающую на его же инстанс.
///
/// Сослаться на инстанс именем член не может - в сигнатуре его ещё нет, -
/// поэтому словарь для собственной цели собирается записью: поля суперклассов
/// дырками, члены именами, которые объявятся вместе с ним.
///
/// Заголовок и типы полей суперкласса кладутся **лямбдами по префиксу**.
/// Написаны они в контексте префикса, а спрашивают их в контексте цели, и
/// глубины эти не совпадают: цель живёт под связываниями клаузы. Применение к
/// ведущим связываниям цели переименовывает их бета-редукцией, и отдельного
/// сдвига индексов не нужно.
///
/// # Errors
///
/// Если тип поля суперкласса не читается из заголовка.
#[allow(clippy::too_many_arguments)]
fn self_dictionary(
    signature: &Signature,
    metas: &mut Metas,
    name: &ast::Name,
    arguments: &Rc<[Symbol]>,
    prefix: &[Param],
    written: &Term,
    superclasses: usize,
    members: &[Written],
    qualified: &[Symbol],
    levels: &Rc<[Level]>,
    span: Span,
    names: &Names,
) -> Result<Declaring, ElabError> {
    let over_prefix = |body: Term| -> Term {
        prefix
            .iter()
            .rev()
            .fold(body, |inner: Term, param: &Param| {
                Term::Lam(param.mult, CoreName::from(&*param.name), Rc::new(inner))
            })
    };
    let mut super_types = Vec::with_capacity(superclasses);
    for index in 0..superclasses {
        let field = format!("#super{index}");
        let (ty, _) = instance_method(signature, metas, prefix, written, &field, span, names)?;
        super_types.push(over_prefix(ty));
    }
    Ok(Declaring {
        class: Rc::clone(&name.text),
        heads: Rc::clone(arguments),
        prefix: prefix.len(),
        super_types,
        header: over_prefix(class::goal_of(written).clone()),
        members: members
            .iter()
            .zip(qualified)
            .map(|((method, ..), full)| {
                (
                    Rc::clone(method),
                    Term::Const(CoreName::from(&**full), Rc::clone(levels), Args::none()),
                )
            })
            .collect(),
    })
}

#[allow(clippy::too_many_arguments)]
#[allow(
    clippy::too_many_lines,
    reason = "объявление группы идёт одной последовательностью: типы членов, общее обобщение, тела, группа"
)]
fn declare_members(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &Instances,
    warnings: &mut Warnings,
    name: &ast::Name,
    arguments: &Rc<[Symbol]>,
    prefix: &[Param],
    written: &Term,
    superclasses: usize,
    members: &[Written],
    qualified: &[Symbol],
    span: Span,
    names: &Names,
) -> Result<(), ElabError> {
    let fail = |error: TypeError| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    };
    // Типы всех членов - из одного заголовка, значит с общими дырками уровня.
    let mut types = Vec::with_capacity(members.len());
    // Арность кратностей у каждого члена **своя**: она приходит от поля, а поле
    // связывает свои параметры само (§10 вопрос 115).
    let mut grades = Vec::with_capacity(members.len());
    for (method, ..) in members {
        let (ty, mults) = instance_method(signature, metas, prefix, written, method, span, names)?;
        types.push(ty);
        grades.push(mults);
    }
    // Обобщение **общее на группу**: члены живут под одним заголовком, и
    // параметры уровня у них одни и те же. Арность поэтому известна до
    // проверки тел - в отличие от `mutual`, где она зависит от них (§10
    // вопрос 54), - и объявляется явно.
    let mut generalization = Generalization::default();
    for ty in &types {
        let zonked = zonk_term(metas, ty);
        generalization.collect_term(metas, &zonked);
    }
    let arity = generalization.arity();
    // Арность-пара: вторая компонента считается тем же обобщением по тому же
    // написанному типу (§10 вопрос 73).
    let row_arity = generalization.row_arity();
    let types: Vec<Term> = types
        .iter()
        .map(|ty| {
            let zonked = zonk_term(metas, ty);
            generalization.apply_term(metas, &zonked)
        })
        .collect();
    let levels: Rc<[Level]> = (0..arity)
        .map(|index| Level::Var(LevelVar(index)))
        .collect();

    // Члены видят друг друга: группа - единица объявления (§10 вопрос 50), и
    // ссылка на соседа законна ещё до того, как он попал в сигнатуру.
    let visible: Vec<Member> = qualified
        .iter()
        .zip(&types)
        .map(|(name, ty)| Member {
            name: Rc::clone(name),
            levels: Rc::clone(&levels),
            // Обобщение здесь общее на группу, поэтому `RowVar(k)` у членов
            // общий, и подстановка тождественна. Полный список аргументов
            // ждёт сверки row-арности (§10, ревью 2026-09-03).
            args: Args::none(),
            ty: Rc::new(ty.clone()),
        })
        .collect();
    let declaring = self_dictionary(
        signature,
        metas,
        name,
        arguments,
        prefix,
        written,
        superclasses,
        members,
        qualified,
        &levels,
        span,
        names,
    )?;

    let mut trees = Vec::with_capacity(members.len());
    for (at, (_, clauses, at_span)) in members.iter().enumerate() {
        let compiled = {
            let mut elaborator = Elaborator::with_group(
                signature,
                metas,
                owned,
                fixities,
                warnings,
                visible.clone(),
            )
            .declaring(&types[at]);
            clauses
                .iter()
                .map(|clause| elaborator.clause(clause))
                .collect::<Result<Vec<_>, _>>()?
        };
        let tree = compile_traced(signature, metas, &types[at], &compiled).map_err(|error| {
            ElabError::Clauses {
                span: *at_span,
                error: Box::new(error),
            }
        })?;
        class::resolve(
            signature,
            metas,
            instances,
            owned,
            Some(&declaring),
            &tree.term,
            &types[at],
            *at_span,
        )?;
        trees.push(tree);
    }

    let mut group: Option<Group> = None;
    for (at, ty) in types.iter().enumerate() {
        let member = SigMember::definition(&qualified[at], Mult::Many, ty.clone())
            .with_body(trees[at].term.clone())
            .with_arity(arity, row_arity)
            .with_mults(grades[at]);
        group = Some(match group {
            None => Group::of(member),
            Some(group) => group.and(member),
        });
    }
    if let Some(group) = group {
        signature.declare(metas, &group).map_err(fail)?;
    }
    kept_promise(signature, members, qualified, span)?;
    for method in qualified {
        carrier::check(signature, owned, method, span)?;
    }

    Ok(())
}

/// Группа взаимной рекурсии (§4.8).
///
/// Члены объявляются **одним вызовом** - той же группой §10 вопроса 50, на
/// которой стоят `data` и члены инстанса: имена и типы известны до проверки
/// любого тела, поэтому ссылка на соседа законна.
///
/// # Уровни: своя арность у каждого члена (§10 вопрос 54)
///
/// Обобщение идёт по **написанному типу** члена и до проверки всех тел - то
/// же правило, что у одиночного определения, только применённое ко всем
/// сразу. Отсюда и ссылки: на себя - своими параметрами, на соседа - свежими
/// дырками, как всякая ссылка на объявленное. Общая арность на группу дала бы
/// фантомные параметры члену, которому уровни не нужны, и решать их в месте
/// использования было бы нечем. Решение от 2026-08-31.
#[allow(clippy::too_many_arguments)]
fn declare_mutual(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &Instances,
    warnings: &mut Warnings,
    members: &[ast::Decl],
    span: Span,
) -> Result<(), ElabError> {
    let planned = mutual_members(members, span)?;
    // Семейства объявляются **первыми и своей группой**. Разбор в теле
    // определения берёт у конструктора тип, а элаборация читает его из
    // сигнатуры: значит конструкторы обязаны быть там раньше, чем компилируется
    // первая клауза. Взаимная рекурсия семейств от этого не страдает - она
    // внутри их группы, - а названная цена в том, что тип конструктора не
    // вправе назвать определение того же блока.
    declare_families(signature, metas, owned, fixities, warnings, &planned, span)?;
    let planned: Vec<&Mutual<'_>> = planned
        .iter()
        .filter_map(|member| match member {
            Planned::Definition(it) => Some(it),
            Planned::Family(..) => None,
        })
        .collect();
    if planned.is_empty() {
        return Ok(());
    }
    // Типы элаборируются до всякого объявления: граница объявления одна на
    // группу, и дырки уровня доживают до неё.
    //
    // **Тип члена не вправе назвать соседа** (§10 вопрос 64), и отказ здесь
    // явный. Элаборация группы не видит: `Elaborator::new` строится без неё, и
    // строчное имя соседа попадало в свободные, а §4.1 поднимала его в
    // implicit-параметр. Получалось хуже, чем ограничение: обёртка в `mutual`
    // не добавляла типу видимости, а отнимала - программа, законная снаружи
    // блока, внутри него меняла смысл молча, и ошибка всплывала в месте
    // использования, «аргумент не выведен». Заглавное имя тем же путём даёт
    // честный `UnknownConstant`; здесь выравнивается строчное.
    unnamed_siblings(&planned)?;
    let mut types = Vec::with_capacity(planned.len());
    for member in &planned {
        // Владение верхнего уровня не выражается и внутри группы (§3.3). Путь
        // сюда идёт мимо `definition`, где этот отказ и стоит, поэтому его
        // приходится повторить: `mutual` меняет **видимость**, и только её
        // (§4.8), а без этой строки `leaked : File` внутри блока принималось,
        // тогда как то же объявление снаружи отвергалось (ревью 2026-09-07).
        if let Some(how) = owned_head(signature, owned, None, member.ty) {
            return Err(ElabError::OwnedTopLevel {
                owned: how,
                name: Rc::clone(&member.name.text),
                span: member.ty.span,
            });
        }
        types.push(
            Elaborator::new(signature, metas, owned, fixities, warnings)
                .declaration(member.ty, Mult::Many)?,
        );
    }
    let mut arities = Vec::with_capacity(planned.len());
    let mut generalized = Vec::with_capacity(planned.len());
    for (member, ty) in planned.iter().zip(&types) {
        // Тип проверяется **до** обобщения: `is_type` решает дырки уровня, и
        // без него применённое семейство приезжает сюда нерешённым - `List
        // Nat` заводил параметр `u0`, которого в самом типе нет, и объявление
        // отвергалось «ожидался `Type u0`, получен `Type 0`». Соседняя ветка
        // (`self_levels`) делает ровно это и тем же комментарием объясняет
        // (§10 вопрос 126, измерено 2026-09-07).
        is_type(&Ctx::new(signature), metas, ty).map_err(|error| ElabError::Core {
            span: member.span,
            error: Box::new(error),
            names: Names::of(&member.name.text, Vec::new()),
        })?;
        let zonked = zonk_term(metas, ty);
        let mut generalization = Generalization::default();
        generalization.collect_term(metas, &zonked);
        arities.push((generalization.arity(), generalization.row_arity()));
        generalized.push(generalization.apply_term(metas, &zonked));
    }

    let mut trees = Vec::with_capacity(planned.len());
    for (at, member) in planned.iter().enumerate() {
        let visible = siblings_of(metas, &planned, &arities, &generalized, at);
        let compiled = {
            let mut elaborator =
                Elaborator::with_group(signature, metas, owned, fixities, warnings, visible)
                    .declaring(&generalized[at])
                    .suspending(suspends(member.ty));
            member
                .clauses
                .iter()
                .map(|clause| elaborator.clause(clause))
                .collect::<Result<Vec<_>, _>>()?
        };
        let tree =
            compile_traced(signature, metas, &generalized[at], &compiled).map_err(|error| {
                ElabError::Clauses {
                    span: member.span,
                    error: Box::new(error),
                }
            })?;
        class::resolve(
            signature,
            metas,
            instances,
            owned,
            None,
            &tree.term,
            &generalized[at],
            member.span,
        )?;
        trees.push(tree);
    }

    declare_definitions(
        signature,
        metas,
        &planned,
        &generalized,
        &arities,
        &trees,
        span,
    )?;
    required_verdicts(signature, &planned, &trees)?;
    for member in &planned {
        carrier::check(signature, owned, &member.name.text, member.span)?;
    }
    Ok(())
}

/// Объявляет определения группы одним вызовом - и называет отказ по месту.
///
/// Маршрут группы начинается **номером члена**, и по нему ищутся оба: текст для
/// каретки и имя для пути. Без них отказ вставал на слово `mutual`, каким бы
/// длинным блок ни был, и звал члена как «член группы #1».
fn declare_definitions(
    signature: &mut Signature,
    metas: &mut Metas,
    planned: &[&Mutual<'_>],
    generalized: &[Term],
    arities: &[(u32, u32)],
    trees: &[Compiled],
    span: Span,
) -> Result<(), ElabError> {
    let mut group: Option<Group> = None;
    for (at, member) in planned.iter().enumerate() {
        let declared =
            SigMember::definition(&member.name.text, Mult::Many, generalized[at].clone())
                .with_body(trees[at].term.clone())
                .with_arity(arities[at].0, arities[at].1);
        group = Some(match group {
            None => Group::of(declared),
            Some(group) => group.and(declared),
        });
    }
    let Some(group) = group else {
        return Ok(());
    };
    let routed: Vec<route::Member<'_>> = planned
        .iter()
        .zip(trees)
        .map(|(member, tree)| route::Member {
            ty: member.ty,
            clauses: member.clauses,
            compiled: tree,
        })
        .collect();
    let declared = Declared::Group(&routed);
    signature
        .declare(metas, &group)
        .map_err(|error| ElabError::Core {
            span: route::locate(&declared, &error, span),
            error: Box::new(error),
            names: Names::group(
                planned
                    .iter()
                    .map(|it| (Rc::clone(&it.name.text), Vec::new())),
            ),
        })
}

/// Чем члены группы видят друг друга при проверке тела `at`-го.
///
/// Свой параметр приходит переменной, чужой - дыркой: сосед объявляется рядом,
/// но инстанцируется в каждом месте использования заново. Правило одно на оба
/// сорта - уровни и row (§10 вопросы 54 и 73), - и для row оно соблюдалось
/// только на словах: список аргументов был пуст, то есть подстановка
/// тождественна, а ядро её не ловит. Параметры соседа читались после этого как
/// свои, и `mutual` над двумя эффектными сигнатурами отвергался сообщением про
/// переменную, которой в области видимости нет.
fn siblings_of(
    metas: &mut Metas,
    planned: &[&Mutual<'_>],
    arities: &[(u32, u32)],
    generalized: &[Term],
    at: usize,
) -> Vec<Member> {
    let mut visible = Vec::with_capacity(planned.len());
    for (other, sibling) in planned.iter().enumerate() {
        let levels: Rc<[Level]> = if other == at {
            (0..arities[at].0)
                .map(|index| Level::Var(LevelVar(index)))
                .collect()
        } else {
            (0..arities[other].0).map(|_| metas.fresh_level()).collect()
        };
        let rows: Vec<Row<Term>> = if other == at {
            (0..arities[at].1)
                .map(|index| Row::closing([], Some(Tail::Var(RowVar(index)))))
                .collect()
        } else {
            (0..arities[other].1).map(|_| metas.fresh_row()).collect()
        };
        let ty = generalized[other]
            .substitute_levels(&levels)
            .substitute_rows(&rows);
        visible.push(Member {
            name: Rc::clone(&sibling.name.text),
            ty: Rc::new(ty),
            args: Args::rows(rows),
            levels,
        });
    }
    visible
}

/// Отвергает тип члена группы, назвавший соседа (§10 вопрос 64).
///
/// Типы всех членов проверяются **до** объявления группы, поэтому соседа тип
/// назвать не вправе. Элаборация группы при этом не видит, и строчное имя
/// соседа уходило в свободные, а §4.1 поднимала его в implicit-параметр:
/// получалось хуже ограничения. Обёртка в `mutual` не добавляла типу
/// видимости, а отнимала - программа, законная снаружи блока, внутри меняла
/// смысл молча, и отказ всплывал далеко от причины, в месте использования.
/// Заглавное имя тем же путём даёт честный `UnknownConstant`; здесь
/// выравнивается строчное.
///
/// Семейство той же группы назвать можно и нужно: объявляется оно первым, и
/// `mutual` над `data` только ради этого и пишут.
///
/// **Выразительности ограничение не отнимает, и это измерено.** Тип, назвавший
/// соседа, зависит от его **значения**; такая зависимость либо обоснована - и
/// тогда пара пишется по порядку до блока, ordered scoping это даёт, - либо не
/// обоснована, и тогда программа отвергается по существу. Член, чей тип назвал
/// соседа, в самой рекурсии участвовать не может: иначе круг замыкается через
/// тип. Поэтому вынести его наружу можно всегда, и сообщение это говорит.
/// То же для типов конструкторов: назвать определение того же блока нельзя.
///
/// Цена названа там, где заведён порядок (`declare_families`): семейства
/// объявляются первыми, значит определений блока в сигнатуре ещё нет. Пока
/// отказа не было, строчное имя соседа уходило в свободные и §4.1 поднимала
/// его в implicit-параметр **конструктора** - `One : Vec Nat count -> Held`
/// объявлялось как `{count : Nat} -> Vec Nat count -> Held`, и обёртка в
/// `mutual` принимала программу, отвергаемую вне блока (ревью 2026-09-05).
///
/// Семейства блока при этом называть можно: их конструкторы видят всю группу,
/// и на этом стоит `Tree`/`Forest`.
fn unnamed_in_constructors(planned: &[Planned<'_>]) -> Result<(), ElabError> {
    let definitions: Vec<&Symbol> = planned
        .iter()
        .filter_map(|member| match member {
            Planned::Definition(it) => Some(&it.name.text),
            Planned::Family(..) => None,
        })
        .collect();
    if definitions.is_empty() {
        return Ok(());
    }
    for member in planned {
        let Planned::Family(data, _) = member else {
            continue;
        };
        for constructor in &data.constructors {
            if crate::expr::names_any(&constructor.ty, &definitions) {
                return Err(ElabError::ModuleMember {
                    name: Rc::clone(&constructor.name.text),
                    what: "группе `mutual`",
                    why: "тип конструктора не вправе назвать определение блока - \
                          семейства объявляются раньше определений, и в сигнатуре \
                          их ещё нет; вынесите его отдельным объявлением перед \
                          блоком, ordered scoping это позволяет. Семейство группы \
                          назвать можно",
                    span: constructor.span,
                });
            }
        }
    }
    Ok(())
}

fn unnamed_siblings(planned: &[&Mutual<'_>]) -> Result<(), ElabError> {
    for member in planned {
        let siblings: Vec<&Symbol> = planned
            .iter()
            .map(|it| &it.name.text)
            .filter(|it| **it != member.name.text)
            .collect();
        if crate::expr::names_any(member.ty, &siblings) {
            return Err(ElabError::ModuleMember {
                name: Rc::clone(&member.name.text),
                what: "группе `mutual`",
                why: "тип члена не вправе назвать соседа - типы всех членов проверяются \
                      до объявления группы; вынесите его отдельным объявлением \
                      перед блоком, ordered scoping это позволяет. Семейство \
                      группы назвать можно",
                span: member.span,
            });
        }
    }
    Ok(())
}

/// Собранное тело вместе с тем, чем перевести место отказа в спан.
///
/// Нужно `@fbip`: его вердикт считается по телу и указывает **внутрь** него, а
/// не на сигнатуру. У постулата тела нет, и передавать нечего.
#[derive(Clone, Copy)]
struct Assembled<'a> {
    /// Дерево разбора, собранное из клауз.
    term: &'a Term,
    /// Объявление, по которому маршрут отказа станет спаном.
    declared: &'a Declared<'a>,
    /// Номер члена в группе; у одиночного определения нуль.
    member: u32,
}

/// Требует от вердиктов ядра того, что обещано атрибутами (§4.7, §5.1).
///
/// Спрашивается **после** объявления: вердикты считает ядро, а атрибут только
/// требует нужного ответа. У члена группы вердикт зависит от соседей -
/// неподвижная точка понижает их вместе, - и спросить раньше значило бы
/// спросить не тот.
///
/// Место у трёх атрибутов одно, и это существенно: путей тоже три -
/// определение, член `mutual`, постулат, - и разойдись они, атрибут значил бы
/// разное в зависимости от того, где написан. Ровно так он и терялся внутри
/// `mutual`, пока проверка стояла в одном пути из трёх.
fn verdicts(
    signature: &Signature,
    name: &Symbol,
    demanded: Required,
    written: Option<Assembled<'_>>,
    span: Span,
) -> Result<(), ElabError> {
    if demanded.total && !signature.lookup(name).is_some_and(|it| it.total) {
        return Err(ElabError::NotTotal {
            name: Rc::clone(name),
            span,
        });
    }
    if demanded.noalloc {
        if let Some(blame) = alloc::blame(signature, name) {
            return Err(ElabError::Allocates {
                name: Rc::clone(name),
                blame,
                span,
            });
        }
    }
    // Совместимость с FBIP - свойство тела, и у постулата спрашивать её не у
    // чего: ветвей, которым не совпасть формой, там нет.
    if demanded.fbip {
        if let Some(written) = written {
            fbip_verdict(
                signature,
                written.term,
                written.declared,
                written.member,
                name,
                span,
            )?;
        }
    }
    Ok(())
}

/// То же по каждому члену группы.
///
/// Спрашивается **после** объявления группы: до этой проверки атрибут внутри
/// `mutual` выбрасывался вместе с заголовком, то есть не значил ничего.
fn required_verdicts(
    signature: &Signature,
    planned: &[&Mutual<'_>],
    trees: &[Compiled],
) -> Result<(), ElabError> {
    let routed: Vec<route::Member<'_>> = planned
        .iter()
        .zip(trees)
        .map(|(member, tree)| route::Member {
            ty: member.ty,
            clauses: member.clauses,
            compiled: tree,
        })
        .collect();
    let declared = Declared::Group(&routed);
    for (at, member) in planned.iter().enumerate() {
        let written = trees.get(at).map(|tree| Assembled {
            term: &tree.term,
            declared: &declared,
            member: u32::try_from(at).unwrap_or(u32::MAX),
        });
        verdicts(
            signature,
            &member.name.text,
            member.required,
            written,
            member.span,
        )?;
    }
    Ok(())
}

/// Требует совместимости с FBIP там, где написан `@fbip` (§5.1).
///
/// Вердикт считает ядро по телу, а место отказа переводится в спан тем же
/// маршрутом, каким переводится отказ проверки типов (§10 вопрос 49б): кадры
/// ложатся на дерево разбора, дерево - на клаузу, клауза - на её текст.
fn fbip_verdict(
    signature: &Signature,
    body: &Term,
    declared: &Declared<'_>,
    member: u32,
    name: &Symbol,
    span: Span,
) -> Result<(), ElabError> {
    let Err(refusal) = adamas_core::fbip::compatible(signature, body) else {
        return Ok(());
    };
    let mut route = vec![Frame::MemberBody(member)];
    route.extend(refusal.route);
    Err(ElabError::NotFbip {
        name: Rc::clone(name),
        fault: Box::new(refusal.fault),
        span: route::at(declared, &route, span),
    })
}

/// Семейства блока - одной группой, конструкторы под нею целиком.
///
/// `Tree` и `Forest` друг без друга не объявляются, и единица объявления у них
/// поэтому общая: ядро принимает членов двух видов по построению (§10
/// вопрос 50), а фаза B1 кладёт типы конструкторов раньше тел.
fn declare_families(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    planned: &[Planned<'_>],
    span: Span,
) -> Result<(), ElabError> {
    // Тип-формер видит семейства, объявленные **раньше него** в той же группе
    // (§10 вопрос 64): `data Held : Tag -> Type` рядом с `data Tag` пишется.
    //
    // Порядок здесь не компромисс, а верное правило: kind'ы взаимно
    // рекурсивными быть не могут - `data A : B -> Type` вместе с `data B : A ->
    // Type` не обосновано, - и симметрии, которую порядок мог бы нарушить, у
    // них нет. Конструкторы по-прежнему видят **всю** группу: у них взаимная
    // рекурсия настоящая, и на ней стоит `Tree`/`Forest`.
    // Названная цена того же порядка: тип **конструктора** не вправе назвать
    // определение того же блока - определения объявляются после семейств, и в
    // сигнатуре их ещё нет. Отказ здесь явный по той же причине, по какой он
    // явный у типа определения: строчное имя соседа иначе уходит в свободные,
    // §4.1 поднимает его в implicit-параметр конструктора, и обёртка в
    // `mutual` принимает программу, отвергаемую вне блока, молча меняя тип
    // конструктора против написанного (ревью 2026-09-05). Заплатка вопроса 64
    // закрыла тип определения и этот случай не тронула.
    unnamed_in_constructors(planned)?;
    let mut families: Vec<Family<'_>> = Vec::new();
    // Черновая копия сигнатуры, куда по ходу кладутся тип-формеры уже
    // разобранных семейств. Нужна она потому, что арность уровней считается
    // **настоящим** `is_type` (см. `self_levels`), а тот смотрит в сигнатуру, и
    // соседа там иначе нет. Копия заводится только со второго семейства -
    // одиночному объявлению она не стоит ничего.
    let mut scratch: Option<Signature> = None;
    for member in planned {
        let Planned::Family(data, at) = member else {
            continue;
        };
        if let Some(previous) = families.last() {
            scratch.get_or_insert_with(|| signature.clone()).assume(
                &previous.data.name.text,
                u32::try_from(previous.levels.len()).unwrap_or(u32::MAX),
                previous.kind.clone(),
            );
        }
        let known = scratch.as_ref().unwrap_or(signature);
        families.push(family_header(
            known, metas, owned, fixities, warnings, None, data, *at,
        )?);
    }
    if families.is_empty() {
        return Ok(());
    }
    // Имена **всей** группы: маршрут несёт номер члена, и `Tree` рядом с
    // `Forest` печатались бы как «член группы #0» и «#1».
    let names = Names::group(families.iter().map(|family| {
        (
            Rc::clone(&family.declared),
            family
                .data
                .constructors
                .iter()
                .map(|it| Rc::clone(&it.name.text))
                .collect(),
        )
    }));
    // Семейства видны **все** сразу: на этом стоит `Tree`/`Forest`, где
    // конструктор одного называет другое. Конструкторы же дописываются по
    // ходу - тот же порядок, что у тип-формеров, и по тому же доводу: взаимная
    // ссылка конструкторов друг на друга не обоснована.
    let mut seen: Vec<Member> = families.iter().map(Family::visible).collect();
    let mut group: Option<Group> = None;
    for family in &families {
        let constructors = family_constructors(
            signature, metas, owned, fixities, warnings, None, family, &seen,
        )?;
        seen.extend(constructors.iter().map(|(name, ty)| Member {
            name: Rc::clone(name),
            levels: Rc::clone(&family.levels),
            args: Args::none(),
            ty: Rc::new(ty.clone()),
        }));
        let declared = family_member(family, &constructors);
        group = Some(match group {
            None => Group::of(declared),
            Some(group) => group.and(declared),
        });
    }
    let Some(group) = group else {
        return Ok(());
    };
    signature
        .declare(metas, &group)
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })?;
    for family in &families {
        declare_defaults(
            signature,
            metas,
            owned,
            fixities,
            warnings,
            &family.data.name.text,
            &family.data.params,
            Unwritten::Sort,
        )?;
    }
    Ok(())
}

/// Член группы: имя, написанный тип и клаузы.
struct Mutual<'a> {
    name: &'a ast::Name,
    ty: &'a ast::Expr,
    clauses: &'a [ast::Clause],
    span: Span,
    /// Каких вердиктов требуют написанные атрибуты (§4.7, §5.1).
    required: Required,
}

/// Что написано членом группы.
enum Planned<'a> {
    /// Определение с сигнатурой.
    Definition(Mutual<'a>),
    /// Семейство.
    Family(&'a ast::Data, Span),
}
/// Разбирает блок `mutual` на членов.
///
/// Постулата в группе не бывает: члены её объявляются вместе, а постулат -
/// это отсутствие тела, и объявлять его группой незачем.
fn mutual_members(members: &[ast::Decl], span: Span) -> Result<Vec<Planned<'_>>, ElabError> {
    let mut found = Vec::with_capacity(members.len() / 2);
    let mut pending: Option<(&ast::Name, &ast::Expr, Span, Required)> = None;
    for member in members {
        match &member.kind {
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                if let Some((waiting, ..)) = pending {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&waiting.text),
                        span: member.span,
                    });
                }
                // Атрибуты читаются здесь же, а не выбрасываются вместе с
                // остальным заголовком: обещание, принятое молча, - обещание,
                // которого никто не давал. `@fbip` внутри группы принимался,
                // а `@total` внутри неё не значил ничего.
                pending = Some((name, ty, member.span, required(attributes)?));
            }
            DeclKind::Clauses { name, clauses } => {
                let Some((declared, ty, at, demanded)) =
                    pending.take().filter(|(it, ..)| it.text == name.text)
                else {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&name.text),
                        span: member.span,
                    });
                };
                found.push(Planned::Definition(Mutual {
                    name: declared,
                    ty,
                    clauses,
                    span: at.merge(member.span),
                    required: demanded,
                }));
            }
            // Семейство в группе - тот самый случай, ради которого `mutual` и
            // пишут: `Tree` и `Forest` друг без друга не объявляются.
            DeclKind::Data(data) => {
                if let Some((waiting, ..)) = pending {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&waiting.text),
                        span: member.span,
                    });
                }
                found.push(Planned::Family(data, member.span));
            }
            _ => {
                return Err(ElabError::ModuleMember {
                    name: member_name(member)
                        .cloned()
                        .unwrap_or_else(|| Rc::from("_")),
                    what: "группе `mutual`",
                    why: "группа несёт определения с сигнатурами и семейства; \
                          модули и классы объявляются отдельно",
                    span: member.span,
                });
            }
        }
    }
    if let Some((waiting, ..)) = pending {
        return Err(ElabError::MissingSignature {
            name: Rc::clone(&waiting.text),
            span,
        });
    }
    if found.is_empty() {
        return Err(ElabError::ModuleMember {
            name: Rc::from("mutual"),
            what: "группе `mutual`",
            why: "группа без членов ничего не объявляет",
            span,
        });
    }
    Ok(found)
}
/// Формы объявления, которых язык не несёт, - названные границы среза.
fn writable(
    within: Option<&Enclosing>,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    let refuse = |what, why| {
        Err(ElabError::ModuleMember {
            name: Rc::clone(&module.name.text),
            what,
            why,
            span,
        })
    };
    if module.signature {
        if !module.params.is_empty() {
            return refuse(
                "сигнатуре модуля",
                "параметр делает функцию от интерфейса, а сигнатура интерфейсом и является",
            );
        }
        // Аннотация у сигнатуры бессмысленна: она сама и есть интерфейс,
        // проверять её против другого - отдельная операция (уточнение
        // сигнатуры), и её в языке пока нет.
        if module.ascription.is_some() {
            return refuse(
                "сигнатуре модуля",
                "аннотация проверяет модуль против интерфейса, а сигнатура интерфейсом \
                 и является",
            );
        }
        return Ok(());
    }
    // Параметр вложенного функтора, названный как у объемлющего, отвергается.
    // Подстановка параметров у ссылки на соседа ищет их **по имени** (`insert`
    // изнутри есть `F.insert Key`), и затенённый внешний ей не найти: оба слота
    // получают внутренний. При одинаковых сигнатурах это молча меняет значение,
    // при разных приезжает несовпадением типов в чужом месте - измерено зондом.
    // Написать внешний параметр внутри всё равно нечем, поэтому отказ ничего не
    // отнимает.
    let outer = params_of(within);
    let shadows = names_of(&module.params).any(|own| names_of(outer).any(|it| it == own));
    if shadows {
        return refuse(
            "теле функтора",
            "параметр назван так же, как у объемлющего, а подстановка ищет их \
             по имени, и внешний стал бы недостижим",
        );
    }
    Ok(())
}

/// Имена связываний телескопа в порядке написания.
fn names_of(params: &[ast::Binder]) -> impl Iterator<Item = &Symbol> {
    params
        .iter()
        .flat_map(|binder| binder.names.iter().map(|name| &name.text))
}

/// `module IntMap = OrderedMap IntOrd` - тело написано выражением.
///
/// Членов оно не поднимает: их поднял тот функтор, к которому применились.
/// Само объявление - обычное определение, и путь к члену читается проекцией
/// сквозь него.
#[allow(clippy::too_many_arguments)]
fn declare_module_value(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    module: &ast::ModuleDecl,
    body: &ast::Expr,
    declared: &Symbol,
    span: Span,
) -> Result<(), ElabError> {
    if !module.params.is_empty() {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&module.name.text),
            what: "модуле с телом-выражением",
            why: "параметр объявляется у модуля с блоком членов",
            span,
        });
    }
    let names = Names::of(declared, Vec::new());
    // Внутри функтора выражение живёт **под его параметрами**: `Twice Key`
    // называет `Key`, а он связывание, а не имя. Телескоп поэтому тот же, что у
    // всякого члена, и вне функтора он пуст - тогда остаётся ровно прежнее.
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    let params = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let term = elaborator.beneath(&params, |it| it.typing(|it| it.expr(body, Mult::Many)))?;
    let ctx = beneath_params(signature, &params);
    let inner_ty = if let Some(ascription) = &module.ascription {
        let written = Elaborator::new(signature, metas, owned, fixities, warnings)
            .within(within)
            .beneath(&params, |it| {
                it.typing(|it| it.expr(ascription, Mult::Many))
            })?;
        // Названная граница: сигнатура с эффектом-членом требует блока -
        // переименовывать её метку (§10 вопрос 146) в теле-выражении не во
        // что, эффект там не объявляется.
        if ascription_head(&written)
            .is_some_and(|head| !instances.signature_effects(head).is_empty())
        {
            return Err(ElabError::ModuleMember {
                name: Rc::clone(&module.name.text),
                what: "модуле с телом-выражением",
                why: "сигнатура с эффектом-членом требует блока членов: эффект в теле-выражении не объявляется",
                span,
            });
        }
        check_within(&ctx, metas, &term, &written).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        zonk_term(metas, &written)
    } else {
        let (ty, _) = infer(&ctx, metas, Mult::Many, &term).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        quote(ctx.size(), &ty)
    };
    let ty = Elaborator::new(signature, metas, owned, fixities, warnings)
        .within(within)
        .wrapped(&params, true, |_| Ok(inner_ty))?;
    let term = abstracted(&params, term);
    class::resolve(signature, metas, instances, owned, None, &term, &ty, span)?;
    signature
        .define_opaque(metas, declared, Mult::Many, ty, Some(term), module.sealed)
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })
}

/// Отвергает объявление, чьё имя занято примитивом (§4.11).
///
/// Заслонить примитив объявление не может: имя разрешается тем же правилом, что
/// `Type` и `Effect`. Без этого отказа `data Int64` доезжало до ядра, и то
/// сообщало «конструктор обязан возвращать `Int64`, а возвращает `Int64`» -
/// имя одно, типа два.
///
/// Конструкторы и операции проверяются наравне с головой: имя `addInt64`
/// заслонялось бы так же молча.
fn reserved(decl: &ast::Decl) -> Result<(), ElabError> {
    let refuse = |name: &Symbol, span: Span| {
        let what = if PrimTy::named(name).is_some() {
            "это примитивный тип"
        } else {
            "это примитивная операция"
        };
        Err(ElabError::ReservedName {
            name: Rc::clone(name),
            what,
            span,
        })
    };
    let taken = |name: &Symbol| PrimTy::named(name).is_some() || PrimOp::named(name).is_some();
    if let DeclKind::Mutual(members) = &decl.kind {
        for member in members {
            reserved(member)?;
        }
        return Ok(());
    }
    if let Some(name) = member_name(decl).filter(|it| taken(it)) {
        return refuse(name, decl.span);
    }
    if let DeclKind::Data(data) = &decl.kind {
        for constructor in &data.constructors {
            if taken(&constructor.name.text) {
                return refuse(&constructor.name.text, constructor.name.span);
            }
        }
    }
    if let DeclKind::Effect(effect) = &decl.kind {
        for operation in &effect.operations {
            if taken(&operation.name.text) {
                return refuse(&operation.name.text, operation.name.span);
            }
        }
    }
    Ok(())
}

/// Имя, под которым член становится полем модуля.
///
/// `None` - член поля не заводит: клаузы объявлены своей сигнатурой.
fn member_name(member: &ast::Decl) -> Option<&Symbol> {
    match &member.kind {
        DeclKind::Signature { name, .. } | DeclKind::Alias { name, .. } => Some(&name.text),
        DeclKind::Module(inner) => Some(&inner.name.text),
        DeclKind::Data(data) => Some(&data.name.text),
        DeclKind::Effect(effect) => Some(&effect.name.text),
        DeclKind::Resource(resource) => Some(&resource.name.text),
        // Фикситет имени не заводит: он говорит про уже написанное.
        DeclKind::Clauses { .. }
        | DeclKind::Class(_)
        | DeclKind::Mutual(_)
        | DeclKind::Fixity(_) => None,
    }
}

/// Правило запечатанной абстракции у инстанса (§3.5).
///
/// Контексты инстансов включены в правило намеренно: `instance {Ord k} =>
/// Functor (Map k)` даёт запрещённую форму в обход сигнатур - словарь `Ord k`
/// осаждается в значении, чей тип о нём молчит, ровно как у операции.
///
/// Названная граница обхода: запечатанный тип ищется в спайне заключения.
/// Спрятанный под `Pi` внутри аргумента не находится - в голове инстанса
/// такого не пишут.
fn sealed_abstraction(
    signature: &Signature,
    instances: &Instances,
    prefix: &[Param],
    written: &Term,
    span: Span,
) -> Result<(), ElabError> {
    let depth = u32::try_from(prefix.len()).unwrap_or(u32::MAX);
    let mut beneath = Vec::new();
    sealed_arguments(signature, under_prefix(written), depth, &mut beneath);
    if beneath.is_empty() {
        return Ok(());
    }
    for (at, param) in prefix.iter().enumerate() {
        let position = u32::try_from(at).unwrap_or(u32::MAX);
        let Some((class, arguments)) = spine(&param.ty) else {
            continue;
        };
        if !instances.is_class(&class) || instances.is_coherent(&class) {
            continue;
        }
        for argument in arguments {
            let Term::Var(index) = argument else {
                continue;
            };
            let Some(bound) = position
                .checked_sub(1)
                .and_then(|it| it.checked_sub(index.0))
            else {
                continue;
            };
            let Some((_, sealed)) = beneath.iter().find(|(it, _)| *it == bound) else {
                continue;
            };
            return Err(ElabError::SealedInstance {
                class,
                param: Rc::clone(&prefix[bound as usize].name),
                sealed: Rc::clone(sealed),
                span,
            });
        }
    }
    Ok(())
}

/// Переменные префикса, стоящие аргументами запечатанного типа.
fn sealed_arguments(signature: &Signature, ty: &Term, depth: u32, found: &mut Vec<(u32, Symbol)>) {
    let Some((name, arguments)) = spine(ty) else {
        return;
    };
    if signature.lookup(&name).is_some_and(|it| it.opaque) {
        for argument in &arguments {
            let Term::Var(index) = argument else {
                continue;
            };
            if let Some(bound) = depth.checked_sub(1).and_then(|it| it.checked_sub(index.0)) {
                found.push((bound, Rc::clone(&name)));
            }
        }
    }
    for argument in arguments {
        sealed_arguments(signature, argument, depth, found);
    }
}

/// Спайн применения константы: её имя и аргументы.
fn spine(ty: &Term) -> Option<(Symbol, Vec<&Term>)> {
    let mut arguments = Vec::new();
    let mut current = ty;
    while let Term::App(callee, argument) = current {
        arguments.push(&**argument);
        current = callee;
    }
    arguments.reverse();
    match current {
        Term::Const(name, _, _) => Some((Rc::clone(name), arguments)),
        _ => None,
    }
}

/// Отвергает `:>` по сигнатуре, которой запечатывать нельзя (§3.5).
///
/// Аннотация `:` при том же тексте законна: правило охраняет **осадок**, а он
/// заводится только там, где представление скрыто.
fn sealable(
    instances: &Instances,
    within: Option<&Enclosing>,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    if !module.sealed {
        return Ok(());
    }
    let Some(written) = module.ascription.as_ref().and_then(ascription_name) else {
        return Ok(());
    };
    // Нарушение записано под **квалифицированным** именем сигнатуры, а
    // написать её автор вправе двумя способами: коротким именем изнутри того
    // же модуля и квалифицированным откуда угодно. Спрашивались обе формы по
    // написанному тексту, поэтому `module type` внутри модуля правило обходил:
    // клалось `Outer.BagSig`, искалось `BagSig`.
    let (short, qualified) = (Rc::clone(&written), qualify(within, &written));
    let Some(offence) = instances
        .offence(&short)
        .or_else(|| instances.offence(&qualified))
    else {
        return Ok(());
    };
    Err(ElabError::SealedConstraint {
        signature: written,
        member: Rc::clone(&offence.member),
        class: Rc::clone(&offence.class),
        param: Rc::clone(&offence.param),
        sealed: Rc::clone(&offence.sealed),
        span,
    })
}

/// Голова элаборированной аннотации - имя определения, если оно там стоит.
fn ascription_head(written: &Term) -> Option<&CoreName> {
    let mut current = written;
    loop {
        match current {
            Term::Const(name, ..) => return Some(name),
            Term::App(callee, _) => current = callee,
            _ => return None,
        }
    }
}

/// Называет ли написанный тип метку с таким коротким именем.
///
/// Обход тот же, что у [`crate::expr::writes_effects`], и по той же причине:
/// row живёт в стрелках и группах связываний, глубже в сигнатурах её не пишут.
fn names_label(written: &ast::Expr, label: &str) -> bool {
    match &written.kind {
        ast::ExprKind::Effectful { labels, body, .. } => {
            labels.iter().any(|it| &*it.name.text == label) || names_label(body, label)
        }
        ast::ExprKind::Arrow(left, right) => names_label(left, label) || names_label(right, label),
        ast::ExprKind::Pi { binders, codomain } => {
            binders
                .iter()
                .filter_map(|it| it.ty.as_ref())
                .any(|ty| names_label(ty, label))
                || names_label(codomain, label)
        }
        _ => false,
    }
}

/// Сигнатура с эффектом-членом, инстанцированная метками модуля (§4.8, §10
/// вопрос 146).
///
/// Написанное имя разворачивается до записи, и каждая поднятая метка
/// сигнатуры переименовывается в одноимённую метку модуля. Без переименования
/// проверка сравнила бы `{Counting.Tick}` с `{Counter.Tick}` и отвергла бы
/// всякий модуль под такой сигнатурой: конвертируемость меток именная.
/// Сигнатура без эффектов возвращается как написана и не разворачивается -
/// имя короче записи.
fn instantiated_ascription(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    ctx: &Ctx<'_>,
    inner: &Enclosing,
    written: &Term,
    span: Span,
) -> Result<Term, ElabError> {
    let Some(head) = ascription_head(written) else {
        return Ok(written.clone());
    };
    let effects = instances.signature_effects(head);
    if effects.is_empty() {
        return Ok(written.clone());
    }
    let mut renames = Vec::with_capacity(effects.len());
    for (short, full) in effects {
        let owned_label = qualify(Some(inner), short);
        let is_effect = signature
            .lookup(&owned_label)
            .is_some_and(|it| matches!(it.kind, DefinitionKind::Effect { .. }));
        if !is_effect {
            return Err(ElabError::ModuleMember {
                name: Rc::clone(short),
                what: "модуле",
                why: "сигнатура объявляет эффект, и одноимённый эффект обязан быть членом модуля",
                span,
            });
        }
        // Формеры обязаны совпасть: телескоп метки - её интерфейс, а
        // представление (операции) сигнатура не называет. Сравниваются типы
        // формеров; параметры уровня инстанцируются дырками, как во всяком
        // месте использования.
        let former = |metas: &mut Metas, name: &str| -> Option<Term> {
            let definition = signature.lookup(name)?;
            let levels: Vec<Level> = (0..definition.level_arity)
                .map(|_| metas.fresh_level())
                .collect();
            Some(definition.ty.substitute_levels(&levels))
        };
        let wanted = former(metas, full);
        let found = former(metas, &owned_label);
        let same = match (wanted, found) {
            (Some(wanted), Some(found)) => {
                let empty = Ctx::new(signature);
                let wanted = empty.eval(&wanted);
                let found = empty.eval(&found);
                convertible(signature, metas, 0, &found, &wanted)
            }
            _ => false,
        };
        if !same {
            return Err(ElabError::ModuleMember {
                name: Rc::clone(short),
                what: "модуле",
                why: "телескоп метки расходится с объявленным в сигнатуре",
                span,
            });
        }
        renames.push((Rc::clone(full), owned_label));
    }
    // δ написанного имени руками: переименовывать метки в имени негде - они
    // в записи, которую имя называет.
    let unfolded = quote(ctx.size(), &whnf(signature, &ctx.eval(written)));
    Ok(unfolded.rename_labels(&renames))
}

/// Имя сигнатуры, написанное аннотацией.
///
/// Формы две: короткое имя и квалифицированное - `Outer.BagSig` есть проекция,
/// а не имя. Всё прочее правилу не подлежит: разворачивать выражение оно не
/// берётся, тем и локально.
fn ascription_name(ascription: &ast::Expr) -> Option<Symbol> {
    match &ascription.kind {
        ast::ExprKind::Name(name) => Some(Rc::clone(&name.text)),
        ast::ExprKind::Project(base, field) => {
            let outer = ascription_name(base)?;
            Some(Rc::from(format!("{outer}.{}", field.text).as_str()))
        }
        _ => None,
    }
}

/// Правило запечатанной абстракции (§3.5), посчитанное по тексту сигнатуры.
///
/// Констрейнт `C τ` у операции, где `τ` стоит аргументом абстрактного типового
/// члена, означает, что инстанс участвовал в построении значения, чей тип о нём
/// молчит. Проверяется локально, без разворачивания представлений: сигнатура и
/// есть то, что автор написал.
///
/// Названная граница обхода: констрейнт ищется в написанных стрелках и группах
/// связываний. Спрятанный внутрь поля записи или блока не находится - в
/// сигнатуре такого не пишут, а обход, честный ко всякой форме, стоил бы
/// второго `free_in`.
fn sealing_offence(module: &ast::ModuleDecl, instances: &Instances) -> Option<Offence> {
    let sealed: Vec<&Symbol> = module
        .members
        .iter()
        .filter_map(|member| match &member.kind {
            DeclKind::Alias {
                name, body: None, ..
            } => Some(&name.text),
            _ => None,
        })
        .collect();
    if sealed.is_empty() {
        return None;
    }
    for member in &module.members {
        let DeclKind::Signature { name, ty, .. } = &member.kind else {
            continue;
        };
        let mut written = Vec::new();
        constraints(ty, instances, &mut written);
        for (class, param) in written {
            if let Some(found) = argument_of(ty, &sealed, param) {
                return Some(Offence {
                    member: Rc::clone(&name.text),
                    class: Rc::clone(class),
                    param: Rc::clone(param),
                    sealed: Rc::clone(found),
                });
            }
        }
    }
    None
}

/// Констрейнты написанного типа: класс и переменная, на которую он написан.
///
/// Некогерентные только: у когерентного класса словарь на программу один, и
/// осадка он не оставляет (§3.5).
fn constraints<'a>(
    ty: &'a ast::Expr,
    instances: &Instances,
    found: &mut Vec<(&'a Symbol, &'a Symbol)>,
) {
    match &ty.kind {
        ast::ExprKind::Pi { binders, codomain } => {
            for binder in binders {
                let Some(domain) = &binder.ty else {
                    continue;
                };
                let Some((class, arguments)) = spine_of(domain) else {
                    continue;
                };
                if !instances.is_class(&class.text) || instances.is_coherent(&class.text) {
                    continue;
                }
                for argument in arguments {
                    if let ast::ExprKind::Name(param) = &argument.kind {
                        found.push((&class.text, &param.text));
                    }
                }
            }
            constraints(codomain, instances, found);
        }
        ast::ExprKind::Arrow(domain, codomain) => {
            constraints(domain, instances, found);
            constraints(codomain, instances, found);
        }
        _ => {}
    }
}

/// Запечатываемый тип, чьим аргументом стоит переменная.
fn argument_of<'a>(ty: &'a ast::Expr, sealed: &[&'a Symbol], param: &Symbol) -> Option<&'a Symbol> {
    match &ty.kind {
        ast::ExprKind::Pi { binders, codomain } => binders
            .iter()
            .filter_map(|binder| binder.ty.as_ref())
            .find_map(|domain| argument_of(domain, sealed, param))
            .or_else(|| argument_of(codomain, sealed, param)),
        ast::ExprKind::Arrow(domain, codomain) => {
            argument_of(domain, sealed, param).or_else(|| argument_of(codomain, sealed, param))
        }
        ast::ExprKind::App(..) => {
            let (head, arguments) = spine_of(ty)?;
            let found = *sealed.iter().find(|it| **it == &head.text)?;
            let takes = arguments.iter().any(
                |argument| matches!(&argument.kind, ast::ExprKind::Name(it) if it.text == *param),
            );
            takes.then_some(found)
        }
        _ => None,
    }
}

/// Эффект-член сигнатуры: абстрактная метка, поднятая под её именем (§4.8).
///
/// Представление эффекта - его операции, ровно как представление семейства -
/// конструкторы, и семейство в сигнатуре тоже пишется абстрактным членом, без
/// них. Ordered scoping проверяется по тексту: метка видна с места объявления,
/// а поднятое имя видно элаборации членов целиком.
#[allow(clippy::too_many_arguments)]
fn declare_signature_effect(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    inner: &Enclosing,
    declared: &Symbol,
    members: &[WrittenField<'_>],
    effect: &ast::EffectDecl,
    span: Span,
) -> Result<(), ElabError> {
    if let Some(operation) = effect.operations.first() {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&operation.name.text),
            what: "сигнатуре модуля",
            why: "операции - представление эффекта, и сигнатура объявляет метку без них",
            span,
        });
    }
    if let Some(early) = members
        .iter()
        .filter_map(|it| it.ty)
        .find(|ty| names_label(ty, &effect.name.text))
    {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&effect.name.text),
            what: "сигнатуре модуля",
            why: "метка написана выше своего объявления (ordered scoping, §4.8)",
            span: early.span,
        });
    }
    declare_effect(
        signature,
        metas,
        owned,
        fixities,
        warnings,
        Some(inner),
        effect,
        span,
    )?;
    instances.declares_effect(
        declared,
        &effect.name.text,
        &qualify(Some(inner), &effect.name.text),
    );
    Ok(())
}

/// `module type S where …` - тип записи, собранный телескопом.
#[allow(clippy::too_many_arguments)]
fn declare_module_type(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    instances: &mut Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    declared: &Symbol,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    // Правило запечатанной абстракции считается здесь - тут ещё есть текст
    // сигнатуры, - а спрашивается на `:>`: с аннотацией `:` та же сигнатура
    // законна, потому что представление остаётся видимым.
    if let Some(offence) = sealing_offence(module, instances) {
        instances.forbid_sealing(declared, offence);
    }
    // Эффект-член поднимается под именем сигнатуры, как у модуля (§4.8):
    // полем записи метка не становится - она не тип (§3.4), - а членам ниже
    // нужно её короткое имя в row. На `:>` поднятая метка переименуется в
    // метку модуля.
    let inner = Enclosing::nested(within, Rc::clone(declared), &[]);
    let mut members = Vec::with_capacity(module.members.len());
    for member in &module.members {
        match &member.kind {
            DeclKind::Effect(effect) => declare_signature_effect(
                signature,
                metas,
                owned,
                fixities,
                instances,
                warnings,
                &inner,
                declared,
                &members,
                effect,
                member.span,
            )?,
            DeclKind::Signature { name, ty, .. } => members.push(WrittenField {
                name: name.clone(),
                params: &[],
                ty: Some(ty),
            }),
            // Абстрактный типовой член. Уравнение здесь - полупрозрачная
            // сигнатура (§10 вопрос 46), и её в языке пока нет.
            DeclKind::Alias {
                name,
                params,
                body: None,
            } => members.push(WrittenField {
                name: name.clone(),
                params,
                ty: None,
            }),
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
    // Row-параметр у сигнатуры модуля - тот же, что у класса (§10 вопрос 102):
    // один на все члены и только при написанных метках. Причина та же: поля
    // живут в теле, а обобщение читает тип, - и вывести число оттуда нечем.
    let rowed = members
        .iter()
        .filter_map(|it| it.ty)
        .any(crate::expr::writes_effects)
        .then(|| Row::closing([], Some(Tail::Var(RowVar(0)))));
    // Сигнатура внутри функтора поднимается тем же телескопом, что и всякий
    // член: `Local` объемлющего `Outer (Key : Eqv)` есть `{Key : Eqv} -> Type`,
    // а её члены вправе называть `Key`. Вне функтора телескоп пуст, и остаётся
    // ровно прежнее - тип записи без параметров.
    //
    // Члены элаборируются под собственным объемлющим: короткое имя
    // эффекта-члена - лестница §4.8 к поднятой метке. Телескоп при этом тот
    // же: своих параметров у сигнатуры нет, и `params_of` обоих совпадает.
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(Some(&inner));
    let params = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let fields = elaborator.beneath(&params, |it| {
        it.typing(|it| it.module_members(&members, rowed.as_ref()))
    })?;
    let record = Term::Record(Fields::closed(fields.into()));
    let names = Names::of(declared, Vec::new());
    // Сорт считается **под параметрами**: члены живут под ними, и в пустом
    // контексте считать запись нечем.
    let ctx = beneath_params(signature, &params);
    let level = is_type(&ctx, metas, &record).map_err(|error| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    })?;
    let sort = Term::Universe(metas.zonk(&level));
    let ty = Elaborator::new(signature, metas, owned, fixities, warnings)
        .within(within)
        .wrapped(&params, true, |_| Ok(sort))?;
    signature
        .define_rowed(
            metas,
            declared,
            Mult::Many,
            ty,
            Some(abstracted(&params, record)),
            u32::from(rowed.is_some()),
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
        .postulate_inferred(metas, &pending.name, Mult::Many, pending.ty, pending.grades)
        .map_err(|error| {
            let span = route::locate(&Declared::Postulate(source), &error, pending.span);
            ElabError::Core {
                error: Box::new(error),
                span,
                names: Names::of(&pending.name, Vec::new()),
            }
        })?;
    // `@noalloc` на постулате - объявление обязательства, а не требование к
    // вердикту: через границу его объявляют, потому что тела за ней нет (§5.1).
    // Вердикты спрашиваются следом, как у всякого другого пути.
    if pending.required.noalloc {
        signature.promise_noalloc(&pending.name);
    }
    verdicts(
        signature,
        &pending.name,
        pending.required,
        None,
        pending.span,
    )
}

/// Определение: клаузы собираются в дерево разбора, дерево уходит в сигнатуру.
#[allow(clippy::too_many_arguments)]
fn define(
    signature: &mut Signature,
    metas: &mut Metas,
    known: Known<'_>,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
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
        // Одиночное определение: своя row-переменная приходит из типа как
        // есть, подставлять нечего.
        //
        // С кратностями так нельзя, и в этом их отличие от уровней и row.
        // Тождественная подстановка у тех работает, потому что окружающий тип
        // подставляется той же тождественной; кратности же перебираются
        // **значениями** (§10 вопрос 41), и тип рекурсивной ссылки, взятый из
        // сигнатуры, остался бы при `q0`, когда всё вокруг уже конкретно.
        // Поэтому свой параметр приходит переменной явно: подстановка тела
        // перепишет её вместе со всем остальным.
        args: Args::mults(
            (0..declared.grades)
                .map(|index| Mult::Var(MultVar(u16::try_from(index).unwrap_or(u16::MAX)))),
        ),
        ty: Rc::new(declared.ty.clone()),
    }];
    let compiled = {
        let mut elaborator = Elaborator::with_group(
            signature,
            metas,
            known.owned,
            known.fixities,
            warnings,
            group,
        )
        .within(within)
        .declaring(&declared.ty)
        .suspending(suspends(declared.source));
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

    // Словари, вставленные дырками, заполняются поиском - до объявления,
    // которому нерешённая дырка запрещена (§3.5, `crate::class`).
    class::resolve(
        signature,
        metas,
        known.instances,
        known.owned,
        // Не объявляемый инстанс: сюда приходит обычное определение, а член
        // инстанса объявляется своим путём и `Declaring` получает там.
        None,
        &tree.term,
        &declared.ty,
        span,
    )?;

    signature
        .define_graded(
            metas,
            &declared.name,
            Mult::Many,
            declared.ty.clone(),
            Some(tree.term.clone()),
            declared.grades,
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

    // Вердикты читаются после объявления: считает их ядро, а атрибут только
    // требует нужного ответа (§4.7, §5.1).
    let source = Declared::Definition {
        ty: declared.source,
        clauses,
        compiled: &tree,
    };
    verdicts(
        signature,
        &declared.name,
        declared.required,
        Some(Assembled {
            term: &tree.term,
            declared: &source,
            member: 0,
        }),
        declared.span,
    )?;

    // После объявления, а не до: дырки решены и подставлены, поэтому видно,
    // чем на самом деле стал каждый выводимый аргумент (§10 вопрос 76).
    carrier::check(signature, known.owned, &declared.name, span)
}

/// Подлежит ли связывание заземлению.
///
/// Различие измерено, и оно существенно. **Написанный `Type`** приезжает
/// готовым универсумом с дыркой уровня - тут сомнений нет: связывание типовое.
/// **Поднятое имя** приезжает дыркой терма, и чем она окажется, к этому моменту
/// известно не всегда: у операции `throw : e -> a` домен `a` так и остаётся
/// нерешённым - его ничто не ограничивает, кроме употребления в позиции типа, -
/// а у конструктора `VCons : a -> Vec a n -> Vec a (Succ n)` домен поднятого
/// `n` решается в `Nat` соседним полем. Заземлять поднятое поэтому вправе
/// только implicit-связывание: явное `(0 a : Type)` пишет автор, и там уже
/// стоит универсум.
fn grounds(domain: &Term, lifted: bool) -> bool {
    match peeled_head(domain) {
        Term::Universe(Level::Meta(_)) => true,
        Term::Meta(_) => lifted,
        _ => false,
    }
}

/// Голова спайна, из-под лямбд решения дырки.
///
/// Развёрнутое решение дырки терма стоит **бета-редексом**: `?m` заведена над
/// контекстом, и решение её - цепочка лямбд по нему, применённая к спайну.
/// Второе поднятое имя конструктора приезжает именно так - `(\(0 m0) -> Type
/// ?0) a`, - и по одной голове спайна универсум в нём не виден (§10 вопрос
/// 109).
///
/// Считать саму бету не нужно: тело лямбды - `Type ?0`, и от аргумента оно не
/// зависит вовсе. Уровень внутри терма зависеть от него и не может: уровни
/// термовых переменных не называют.
fn peeled_head(term: &Term) -> &Term {
    let mut head = spine_head(term);
    while let Term::Lam(_, _, body) = head {
        head = spine_head(body);
    }
    head
}

/// Голова спайна применения.
fn spine_head(term: &Term) -> &Term {
    let mut head = term;
    while let Term::App(callee, _) = head {
        head = callee;
    }
    head
}

/// Заземляет универсумы собственных параметров операции (§10 вопрос 83).
///
/// Параметры метки операция **повторяет**, и уровни у них общие с формером -
/// их трогать нечем. Свои же она поднимает сама из свободных имён (`throw : e
/// -> a`), и вот их уровень связать в точке `handle` нечем: метка о нём не
/// несёт ничего, тип вычисления его не называет.
///
/// Тип ветки хендлера строится по типу операции и берёт этот универсум как
/// есть, а место вызова инстанцирует **свою** копию. Обе стёрты, поэтому
/// расхождения никто не увидит: `throw` при `a := Type` проходил, тогда как
/// ветка ждала нулевой универсум. Заземление сводит обе копии к одной, и
/// вызов в высшем универсуме отвергается там, где написан.
///
/// Названная цена - операция не бывает полиморфной по `Type`. Правильный
/// ответ - сделать ветку полиморфной и по уровню, но уровневых `Pi` в ядре
/// нет (вариант «б» вопроса 83).
fn grounded(ty: &Term, params: usize, lifted: bool) -> Term {
    let Term::Pi(binder, name, domain, row, codomain) = ty else {
        return ty.clone();
    };
    // Универсум поднятого имени приезжает сюда **дыркой терма**, а не готовым
    // `Type` (§4.1): решает её `is_type` уже при объявлении группы, то есть
    // после того, как тип ветки с неё снят. Поэтому заземляется она здесь
    // подстановкой, а не решением - решать нечего, дырка ещё пуста.
    let own = params == 0 && binder.mult == Mult::Zero && grounds(domain, lifted);
    let domain = if own {
        Rc::new(Term::Universe(Level::Zero))
    } else {
        Rc::clone(domain)
    };
    Term::Pi(
        *binder,
        Rc::clone(name),
        domain,
        row.clone(),
        Rc::new(grounded(codomain, params.saturating_sub(1), lifted)),
    )
}

/// Поднимает универсум семейства до уровней его параметров.
fn raised(kind: &Term, params: &[Param]) -> Term {
    match kind {
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            name.clone(),
            Rc::clone(domain),
            row.clone(),
            Rc::new(raised(codomain, params)),
        ),
        // Написанный `Type` даёт дырку, и здесь она **заземляется нулём** - тем
        // же, чем ветка без написанного kind, и по той же причине. Ограничивают
        // её только неравенства `leq` от полей, а их вопрос 39 не решает;
        // обобщённая в параметр, она уезжает в тело и остаётся там свободной:
        // `Eqv` получал два уровня вместо одного, и `subst`, чьё доказательство
        // построено в теле, отвергался «остался неразрешённый уровень» (§10
        // вопрос 88).
        //
        // Ноль здесь не догадка, а наименьшее: `sort` поднимет его до
        // универсумов параметров, и семейство окажется ровно там, где обязано
        // быть.
        Term::Universe(level) | Term::RowKind(level) => {
            let written = if matches!(level, Level::Meta(_)) {
                Level::Zero
            } else {
                level.clone()
            };
            Term::Universe(Elaborator::sort(params, written))
        }
        other => other.clone(),
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
            ast::DeclKind::Signature { name, ty, .. } => {
                constructors.extend(pending.take().map(constructor));
                pending = Some((name, ty, member.span));
            }
            // Ни алиас, ни модуль телом ресурса не бывают: layout их туда
            // пускает, а смысла у них там нет - конструктор либо деструктор.
            ast::DeclKind::Class(_) | ast::DeclKind::Mutual(_) => {
                return Err(ElabError::ResourceMember {
                    data: Rc::clone(&resource.name.text),
                    name: Rc::from("группа"),
                    span: member.span,
                });
            }
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
            ast::DeclKind::Effect(inner) => return Err(refuse(&inner.name.text, member.span)),
            ast::DeclKind::Fixity(_) => {
                return Err(refuse(&Rc::from("фикситет"), member.span));
            }
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
#[allow(
    clippy::too_many_arguments,
    reason = "прогон элаборации несёт своё состояние; складывать его в структуру значило бы прятать, что именно меняется"
)]
fn declare_resource(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    instances: &Instances,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    resource: &ast::Resource,
    span: Span,
) -> Result<(), ElabError> {
    let declared = qualify(within, &resource.name.text);
    // Элиминатор scope объявляется вместе с первым же ресурсом: раньше он
    // предмета не имеет, а позже его было бы негде взять - вставка идёт при
    // элаборации тел, когда объявления уже закончились.
    declare_closing(signature, metas, span)?;
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

    // Имя деструктора свободно, но столкнуться два ресурса всё же могут -
    // теперь лишь внутри одного модуля: квалификация развела `A.close` и
    // `B.close`, и пространство имён плоским быть перестало. Отказ говорит об
    // этом прямо - `DuplicateDefinition` от ядра назвал бы столкновение имён,
    // не называя причины.
    let drop_declared = qualify(within, &drop_name.text);
    if let Some(first) = owned.named(&drop_declared).filter(|it| ***it != *declared) {
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
    declare_data(
        signature, metas, owned, fixities, warnings, within, &data, span,
    )?;

    // `drop` объявляется после семейства: его тип называет ресурс, а в
    // сигнатуре тот появляется только сейчас. Домен получает `1` тем же
    // правилом, что и всякое связывание ресурсного типа, - писать `(1 h : …)`
    // руками не нужно и не требуется §3.3. Параметры функтора стоят у него
    // implicit-связываниями, как у всякого члена.
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    let params = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let elaborated = elaborator.wrapped(&params, true, |it| it.declaration(drop_ty, Mult::Many))?;
    // Форма проверяется здесь, один раз, а не в каждой точке вставки: вызов
    // `drop` подставляется компилятором, и тип его результата обязан быть
    // написан в области видимости, где ресурса уже нет. Параметры функтора
    // стоят впереди домена и к форме отношения не имеют - их пропускают.
    destructor_shape(
        &elaborated,
        params.len(),
        &declared,
        &drop_name.text,
        owned,
        drop_ty.span,
    )?;
    let pending = Pending {
        // Деструктор пишет компилятор: атрибутов на нём нет.
        required: Required::default(),
        name: drop_declared,
        ty: elaborated,
        // Деструктор ресурса кратностями не полиморфен: его домен - `1` по
        // правилу §3.3, а не по выбору автора.
        grades: 0,
        source: drop_ty,
        span: drop_span,
    };
    define(
        signature,
        metas,
        known(owned, fixities, instances),
        warnings,
        within,
        &pending,
        clauses,
        drop_span,
    )?;
    // Имя деструктора связывается с типом **после** того, как собрано его
    // тело, и это не порядок ради порядка. Связав раньше, мы получили бы
    // вставку `drop` внутрь самого `drop`: параметр там ресурсного типа, и
    // тело `closeFile h = True` его не упоминает. Вставка полезла бы за типом
    // деструктора в сигнатуру, где его ещё нет, - то есть в `unreachable!`
    // (см. `destructor` в [`crate::expr`], чей инвариант это и есть).
    owned.destroys(&declared, &pending.name);
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
    leading: usize,
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
    // Параметры функтора стоят впереди написанного домена: их подставляет
    // вставка, и к форме деструктора они отношения не имеют.
    let mut ty = ty;
    for _ in 0..leading {
        let Term::Pi(_, _, _, _, codomain) = ty else {
            return Err(refuse());
        };
        ty = codomain;
    }
    // Дальше идут имплиситы подъёма - параметры семейства ресурса в
    // `cancelTask : (1 t : Task a) -> …`. Их тоже подставляет вставка, дырками,
    // как всякое употребление имени; написанного домена они не касаются.
    //
    // Цепочка `&&` с `let` тут не пишется: она требует Rust 2024, а MSRV
    // проекта 1.85 (джоба `msrv` его и ловит).
    while let Term::Pi(binder, _, _, _, codomain) = ty {
        if !binder.visibility.is_implicit() || binder.mult != Mult::Zero {
            break;
        }
        ty = codomain;
    }
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
///
/// **Стёртое связывание полем не бывает** (вопрос 122). Телескоп конструктора
/// начинается параметрами семейства, и `data Ref (0 r : Region) (a : Type)` с
/// `MkRef : Ref r a` не берёт ни одного поля - но `r` стоит в телескопе, и
/// правило читало его как поле типа `Region`. Кратность написана в сигнатуре, и
/// правилу хватает того же взгляда на неё, каким на кратности параметров
/// научили смотреть вставку `drop` (лог 2026-08-29): при `0` значения в
/// рантайме не возникает, держать нечего, уничтожать нечего. Нестёртый параметр
/// семейства ресурсного типа под правило по-прежнему попадает: он приходит
/// конструктору настоящим аргументом и лежит в значении.
fn owned_field(
    ty: &Term,
    owned: &Owned,
    declared: &Symbol,
    data: &ast::Data,
    constructor: &ast::Constructor,
) -> Result<(), ElabError> {
    // Держателя спрашивают под объявленным именем, а поля - под тем, что стоит
    // головой их типа в **ядре**: оба квалифицированы, и разъехаться им негде.
    let holder = owned.how(declared);
    let mut current = ty;
    while let Term::Pi(binder, _, domain, _, codomain) = current {
        let field = name_head(domain)
            .filter(|_| binder.mult != Mult::Zero)
            .and_then(|name| owned.how(name).map(|how| (name, how)));
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
                // Советуется то, чем объявлено **поле**, а не `unique` всегда.
                // Половины правила стоят лестницей, и `unique data` для
                // ресурсного поля - ступенька в никуда: следующая же половина
                // потребует `resource`. Совет обязан вести к проходящему
                // файлу за один шаг.
                (_, None) => return refuse(field),
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
        Term::Const(name, _, _) => Some(name),
        _ => None,
    }
}

/// Ссылается ли терм хоть на одно локальное связывание.
/// Ссылается ли терм на связывание глубины `depth`.
///
/// Нужно типу метода инстанса: считается он под связыванием словаря, и
/// ссылка на него означала бы, что тип метода зависит от значения соседа.
/// Такой тип под префикс не вынести - индекс уехал бы на чужое связывание.
fn mentions_depth(term: &Term, depth: u32) -> bool {
    let recur = |inner| mentions_depth(inner, depth);
    let under = |inner| mentions_depth(inner, depth + 1);
    match term {
        Term::Var(index) => index.0 == depth,
        Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Const(..)
        | Term::Prim(_)
        | Term::Meta(_) => false,
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().enumerate().any(|(at, field)| {
                mentions_depth(&field.ty, depth + u32::try_from(at).unwrap_or(0))
            }) || fields.tail.as_ref().is_some_and(|tail| recur(tail))
        }
        Term::Object(fields) => fields.iter().any(|(_, value)| recur(value)),
        Term::With(base, fields) => recur(base) || fields.iter().any(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Lam(_, _, body) => under(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || under(codomain)
                // Row стоит под связыванием стрелки наравне с кодоменом.
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(under)
        }
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || under(body),
        Term::Case(case) => {
            recur(&case.scrutinee)
                || recur(&case.motive)
                || case.branches.iter().any(|branch| recur(&branch.body))
        }
    }
}

fn mentions_local(term: &Term) -> bool {
    match term {
        Term::Var(_) => true,
        // Дырка замкнута: локальных связываний в ней нет по построению.
        Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Const(..)
        | Term::Prim(_)
        | Term::Meta(_) => false,
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
/// Объявляет умолчания хвостовых параметров невыразимыми именами (§4.1).
///
/// Умолчание - синтаксический сахар: при неполном применении элаборация
/// дописывает его аргументом, до всякого резолвинга (правило 1). Хранится оно
/// **определением** - `Mul#default1` - потому что спрашивают его в местах
/// использования, а сигнатура и есть то, что там доступно; отдельного реестра
/// для этого не нужно, и точку в имени автор не напишет.
///
/// Тело умолчания живёт под предшествующими параметрами: `(b = a)` есть
/// `\a -> a`. Отсюда и правило 2 - упоминать оно вправе только их.
#[allow(clippy::too_many_arguments)]
fn declare_defaults(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    declared: &Symbol,
    written: &[ast::Binder],
    unwritten: Unwritten<'_>,
) -> Result<(), ElabError> {
    let mut at = 0;
    let mut trailing = false;
    for (position, binder) in written.iter().enumerate() {
        let Some(default) = &binder.default else {
            if trailing {
                return Err(ElabError::TrailingDefault {
                    name: Rc::clone(&binder.names[0].text),
                    span: binder.span,
                });
            }
            at += binder.names.len();
            continue;
        };
        trailing = true;
        // Телескоп считается заново на каждое умолчание: объявление
        // предыдущего освободило дырки уровня, и посчитанный один раз умер бы
        // на втором.
        let mut elaborator = Elaborator::new(signature, metas, owned, fixities, warnings);
        let params = elaborator.telescope(&written[..=position], false, Mult::Zero, unwritten)?;
        let Some(param) = params.get(at) else {
            return Err(ElabError::TrailingDefault {
                name: Rc::clone(&binder.names[0].text),
                span: binder.span,
            });
        };
        let domain = Rc::clone(&param.ty);
        let leading: Vec<Param> = params[..at].to_vec();
        let (body, inferred) = elaborator.beneath(&leading, |it| {
            let body = it.typing(|inner| inner.expr(default, Mult::Many))?;
            let inferred = it.inferred(&body);
            Ok((body, inferred))
        })?;
        // Тип - **выведенный по телу**, а не написанный домен параметра: у
        // ненаписанного домена свой уровень, независимый от уровня тела, и
        // `(b = a)` при `b : Type u1` и `a : Type u0` не сошлось бы. Подходит
        // ли умолчание параметру, скажет место использования: дописанный
        // аргумент проверяется там наравне с написанным.
        let ty = elaborator.wrapped(&leading, false, |_| {
            Ok(inferred.unwrap_or_else(|| (*domain).clone()))
        })?;
        let term = abstracted(&leading, body);
        let name: Symbol = Rc::from(format!("{declared}#default{at}").as_str());
        // Кратность нулевая: умолчание живёт только на этапе проверки типов -
        // в результат элаборации попадает не оно, а то, во что оно
        // развернулось. Параметр класса при этом стёрт, и тело `\a -> a` при
        // ω-суждении было бы его употреблением.
        signature
            .define_inferred(metas, &name, Mult::Zero, ty, Some(term))
            .map_err(|error| ElabError::Core {
                span: binder.span,
                error: Box::new(error),
                names: Names::of(&name, Vec::new()),
            })?;
        at += binder.names.len();
    }
    Ok(())
}

/// Заголовок семейства: всё, что известно о нём **до** конструкторов.
///
/// Отдельно от конструкторов потому, что в группе конструктор одного семейства
/// называет другое: заголовки обязаны быть готовы все, прежде чем
/// элаборируется первый конструктор. Одиночное объявление проходит тем же
/// путём - группа из одного члена.
struct Family<'a> {
    /// Написанное.
    data: &'a ast::Data,
    /// Имя, под которым семейство объявляется: квалифицированное в теле модуля.
    declared: Symbol,
    /// Телескоп параметров - один на kind и на все конструкторы.
    params: Vec<Param>,
    /// Тип-формер.
    kind: Term,
    /// Аргументы уровня, которыми семейство называют внутри группы.
    ///
    /// Общие на всю группу, а не свежие на вхождение: семейство одно, и
    /// независимые дырки сделали бы его полиморфным по нескольким уровням
    /// сразу (§10 вопрос 63).
    levels: Rc<[Level]>,
    /// Имена для маршрута.
    names: Names,
}

impl Family<'_> {
    /// Каким его видят соседи по группе.
    fn visible(&self) -> Member {
        Member {
            name: Rc::clone(&self.declared),
            levels: Rc::clone(&self.levels),
            // Тип-формер семейства row не носит: метка не тип.
            args: Args::none(),
            ty: Rc::new(self.kind.clone()),
        }
    }
}

/// Телескоп, kind и арность уровней семейства.
#[allow(clippy::too_many_arguments)]
fn family_header<'a>(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    data: &'a ast::Data,
    span: Span,
) -> Result<Family<'a>, ElabError> {
    // Телескоп параметров элаборируется один раз и переиспользуется: kind и
    // каждый конструктор обязаны нести **один и тот же** телескоп, иначе
    // `List` в результате и `List` в объявлении - два разных семейства.
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    // Связывания двух родов в одном телескопе, как у алиаса: сперва параметры
    // функтора, потом свои. Написанный параметр живёт под функторными - его тип
    // вправе их упоминать.
    let outer = elaborator.telescope(params_of(within), true, Mult::Many, Unwritten::Sort)?;
    let own = elaborator.beneath(&outer, |it| {
        it.telescope(&data.params, false, Mult::Zero, Unwritten::Sort)
    })?;
    // Параметр сортом `Effect` - `Task eff a` из §5.2 - форма следующего
    // среза: формер по row-аргументу не применяется, спайн значения row не
    // несёт. Отказ здесь, при объявлении, - дальше падал сам компилятор.
    if let Some(param) = own.iter().find(|it| matches!(&*it.ty, Term::EffectKind)) {
        let at = data
            .params
            .iter()
            .find(|binder| binder.names.iter().any(|name| name.text == param.name))
            .map_or(span, |binder| binder.span);
        return Err(ElabError::RowParameter {
            name: Rc::clone(&param.name),
            span: at,
        });
    }
    let params: Vec<Param> = outer.iter().chain(own.iter()).cloned().collect();
    let kind = match &data.kind {
        // Параметры пишутся, поэтому в kind они явные: `Vect a n`. Функторные -
        // наоборот: писать их некому, их подставляет вставка.
        Some(kind) => elaborator.wrapped(&outer, true, |it| {
            it.wrapped(&own, false, |it| it.typing(|it| it.expr(kind, Mult::Many)))
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
        None => elaborator.wrapped(&outer, true, |it| {
            it.wrapped(&own, false, |_| Ok(Term::universe(0)))
        })?,
    };
    // Семейство обязано вместить универсумы своих параметров: поле типа `a`
    // живёт там же, где `a`. Написанный `Type` даёт дырку, и поднять её до
    // максимума - наименьшее, что подходит.
    let kind = raised(&kind, &params);
    // Маршрут внутрь семейства называет конструктор номером, а имена у него
    // здесь: собираются один раз на оба возможных отказа.
    let declared = qualify(within, &data.name.text);
    let names = Names::of(
        &declared,
        data.constructors
            .iter()
            .map(|constructor| qualify(within, &constructor.name.text))
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
    Ok(Family {
        data,
        declared,
        params,
        kind,
        levels,
        names,
    })
}

/// Типы конструкторов - под группой, в которой семейство объявляется.
#[allow(clippy::too_many_arguments)]
fn family_constructors(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    family: &Family<'_>,
    visible: &[Member],
) -> Result<Vec<(Symbol, Term)>, ElabError> {
    // Поле конструктора получает `1` (§4.1): конструктор кладёт аргумент
    // однажды. Обычный код этого не замечает, потому что при разборе поле
    // приходит в ветвь при `q · r`, а `r` - кратность потребления
    // разбираемого; у ω-связывания `1 · ω = ω` (§3.3, вопрос 65).
    family
        .data
        .constructors
        .iter()
        .map(|constructor| {
            // У конструктора те же параметры, но выводимые: пишут `MkPair x y`,
            // а не `MkPair A B x y`. Свободные имена, оставшиеся сверх них,
            // поднимаются уже под ними - и потому стоят после, как того и ждёт
            // ядро от телескопа с параметрами.
            let ty = Elaborator::with_group(
                signature,
                metas,
                owned,
                fixities,
                warnings,
                visible.to_vec(),
            )
            .within(within)
            .wrapped(&family.params, true, |it| {
                it.constructor_type(&constructor.ty, Mult::One)
            })?;
            // Собственный типовой параметр конструктора живёт в нулевом
            // универсуме (§10 вопрос 109) - тем же доводом, что у операции
            // (вопрос 83): полиморфный по уровню он делает и само семейство
            // полиморфным, а запинить уровень в месте использования нечем -
            // уровни не пишутся (§3.2). Семейство встаёт над ним само: сорт
            // поднимается до полей.
            let ty = grounded(&zonk_term(metas, &ty), family.params.len(), false);
            owned_field(&ty, owned, &family.declared, family.data, constructor)?;
            Ok((qualify(within, &constructor.name.text), ty))
        })
        .collect()
}

/// Член ядра, собранный из семейства и типов его конструкторов.
fn family_member(family: &Family<'_>, constructors: &[(Symbol, Term)]) -> SigMember {
    let parameters = u32::try_from(family.params.len()).unwrap_or(u32::MAX);
    constructors.iter().fold(
        SigMember::data(&family.declared, parameters, family.kind.clone()),
        |member, (constructor, ty)| member.with_constructor(constructor, ty.clone()),
    )
}

/// Семейство вместе с тем, что решается до его объявления.
#[allow(clippy::too_many_arguments)]
fn declare_family(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    // Маркер ставится **до** элаборации конструкторов: поле собственного типа
    // получит `1` тем же правилом, что и всякое другое связывание, а не
    // отдельным случаем. Имя - квалифицированное: под ним семейство объявлено,
    // и под ним же его найдут по голове ядерного типа.
    if data.unique {
        owned.declare(&qualify(within, &data.name.text), Ownership::Unique);
    }
    declare_data(
        signature, metas, owned, fixities, warnings, within, data, span,
    )
}

/// Объявление эффекта: формер метки плюс её операции (§3.4).
///
/// Устроено как семейство и объявляется той же группой: операция называет свою
/// метку, а в сигнатуре её ещё нет. Отличий два. Формер не пишется - результат
/// метки всегда `Effect`, - и укладывать метку некуда: она не тип, полем стоять
/// не может, поэтому ни универсума, ни позитивности у неё нет.
///
/// В теле модуля квалифицируются и метка, и каждая операция - подъём тот же,
/// что у семейства (§4.8). Полем записи метка при этом не становится, и
/// [`module_object`] её пропускает: поле типизируется типом, а метка им не
/// является.
#[allow(
    clippy::too_many_arguments,
    reason = "объявление несёт своё окружение; складывать его в структуру значило бы прятать, что именно читается"
)]
fn declare_effect(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    effect: &ast::EffectDecl,
    span: Span,
) -> Result<(), ElabError> {
    // `return` занято формой хендлера: так называется ветка **значения**
    // вычисления (§3.4, §4.1), и разрешение операции с тем же именем сделало
    // бы одну написанную ветку двумя. У элиминатора это разные связывания, и
    // расходились они молча: при операции-вычислении слоты получают
    // структурно один тип, хендлер проходит проверку, а ветка исполняет две
    // роли - линейное имя, написанное в ней раз, становится ω.
    if let Some(clash) = effect
        .operations
        .iter()
        .find(|operation| &*operation.name.text == crate::expr::RETURN)
    {
        return Err(ElabError::ReservedOperation {
            name: Rc::clone(&clash.name.text),
            span: clash.name.span,
        });
    }
    // Имя, под которым эффект объявляется, - квалифицированное в теле модуля,
    // и квалифицируются **и метка, и операции**: представление эффекта есть
    // его операции ровно так же, как представление семейства есть его
    // конструкторы (§4.8). Оставь операции на верхнем уровне - и два модуля с
    // одноимённым `Ask` столкнулись бы, а запечатывать было бы нечего.
    let declared = qualify(within, &effect.name.text);
    // Названная граница: в теле функтора эффект не объявляется. Член функтора
    // поднимается под его параметрами, а метка их не несёт - формер её
    // оканчивается `Effect`, и телескопа перед ним элаборация не строит.
    // Отказ здесь затем, что без него та же форма падала «имя `Key` не
    // найдено» на типе операции - сообщение о параметре, написанном строкой
    // выше.
    if !params_of(within).is_empty() {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&effect.name.text),
            what: "функторе",
            why: "член функтора поднимается под его параметрами, а метка их не несёт",
            span,
        });
    }
    let mut elaborator =
        Elaborator::new(signature, metas, owned, fixities, warnings).within(within);
    let params = elaborator.telescope(&effect.params, false, Mult::Zero, Unwritten::Sort)?;
    let kind = elaborator.wrapped(&params, false, |_| Ok(Term::EffectKind))?;
    let names = Names::of_effect(
        &declared,
        effect
            .operations
            .iter()
            .map(|operation| qualify(within, &operation.name.text))
            .collect(),
    );
    let levels = self_levels(signature, metas, &kind).map_err(|error| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    })?;
    let visible = Member {
        name: Rc::clone(&declared),
        levels,
        // Формер метки оканчивается `Effect`, своей row у него нет.
        args: Args::none(),
        ty: Rc::new(kind.clone()),
    };

    let label = own_label(effect, &declared);
    // Подъём у операций и у элиминаторов - **одна** переменная (§10 вопрос 120).
    //
    // Собственный row-параметр операции есть окружающая места вызова, а под
    // хендлером она равна `{L | ρ}`: правило погашения §3.4 связывает хвост
    // вызываемого с хвостом окружающей. Заведи операция свою переменную, тип
    // ветки унёс бы её в элиминатор, обобщение сделало бы её лишним параметром,
    // и место применения не решало бы её ничем - всякий `handle` над операцией
    // с **функциональным** аргументом отвергался «остался неразрешённый хвост
    // row». Видно это только там, потому что аргумент без стрелки row не носит.
    let rho = metas.fresh_row();
    let mut operations = Vec::with_capacity(effect.operations.len());
    for operation in &effect.operations {
        let written = performed(&operation.ty, &label);
        let suspended = suspends(&written);
        // Параметры кратности, написанные операцией, - её собственные: она
        // инстанцируется местом вызова, как всякое определение (§10 вопрос
        // 116). Считаются они тем же элаборатором, что строит тип.
        let mut it = Elaborator::with_group(
            signature,
            metas,
            owned,
            fixities,
            warnings,
            vec![visible.clone()],
        )
        .within(within);
        let lift = rho.clone();
        let ty = it.wrapped(&params, true, |it| {
            it.declaration_lifted(&written, Mult::Many, lift)
        })?;
        let grades = it.grade_arity();
        let ty = grounded(&zonk_term(metas, &ty), params.len(), true);
        operations.push((qualify(within, &operation.name.text), ty, suspended, grades));
    }

    let handlers = eliminator_types(signature, metas, &kind, &declared, &operations, &rho, span)?;
    let handlers: Vec<(&str, Term)> = handlers
        .iter()
        .map(|(name, ty)| (name.as_str(), ty.clone()))
        .collect();

    let written: Vec<(&str, Term, u32)> = operations
        .iter()
        .map(|(name, ty, _, grades)| (&**name, ty.clone(), *grades))
        .collect();
    let parameters = u32::try_from(params.len()).unwrap_or(u32::MAX);
    signature
        .declare_effect(metas, &declared, parameters, kind, &written, &handlers)
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Effect(effect), &error, span),
            error: Box::new(error),
            names,
        })?;
    declare_defaults(
        signature,
        metas,
        owned,
        fixities,
        warnings,
        &declared,
        &effect.params,
        Unwritten::Sort,
    )
}

/// Переменная контекста по её уровню.
fn at(level: u32, depth: u32) -> Term {
    Term::Var(Lvl(level).to_index(depth))
}

/// Складывает связывания в `Pi`, надевая на каждую стрелку одну и ту же row.
fn arrows(binders: Vec<(Binder, CoreName, Term)>, row: &Row<Term>, result: Term) -> Term {
    binders
        .into_iter()
        .rev()
        .fold(result, |codomain, (binder, name, domain)| {
            Term::Pi(
                binder,
                name,
                Rc::new(domain),
                row.clone(),
                Rc::new(codomain),
            )
        })
}

/// Невыразимое имя элиминатора маски (§3.4, §10 вопрос 72).
pub(crate) const MASK: &str = "#mask";

/// Невыразимое имя элиминатора scope (§3.3).
pub(crate) const CLOSING: &str = "#closing";

/// Имя постулата питомника (§5.2). Питомником его делает отсутствие тела -
/// то же условие, каким машина решает давать тело сама.
pub(crate) const NURSERY: &str = "withNursery";

/// Объявляет `#closing` - элиминатор scope, держащего ресурс.
///
/// Он один на программу, а не по ресурсу на штуку: ресурса в типе он не
/// называет вовсе - оба его аргумента приостановленные вычисления, а какой
/// именно деструктор зовётся, решено в том, что подставлено вторым.
///
/// Зачем он нужен, если `let held = тело in let _ = drop h in held` считает то
/// же самое: `let` невидим машине. Продолжение - цепочка замыканий, и `drop`,
/// оставшийся внутри неё, уходит вместе с ней, когда ветка хендлера не зовёт
/// `resume`. Элиминатор делает scope **наблюдаемым**: машина видит, что вошла
/// в него, и знает, что при обрыве отсюда надо запустить отложенное.
///
/// # Errors
///
/// Те же, что у [`Signature::declare`], плюс отсутствие `Unit` в сигнатуре.
fn declare_closing(
    signature: &mut Signature,
    metas: &mut Metas,
    span: Span,
) -> Result<(), ElabError> {
    if signature.lookup(CLOSING).is_some() {
        return Ok(());
    }
    // Единицы в программе может не быть, и это не отказ: приостановленное
    // вычисление `{ε} A` есть функция от неё, значит без неё нет ни эффектов,
    // ни обрыва через них - раскручивать нечего. Вставка тогда идёт прежней
    // формой, тоже в точку выхода, только машине она невидима.
    //
    // Спрашивается при этом **единственный конструктор**, а не объявленность
    // имени: значение единицы машина строит по нему, и «`Unit` объявлен» её не
    // устраивает. Пока здесь стояла объявленность, `data Unit` с двумя
    // конструкторами вместе с любым ресурсом давал принятую проверкой
    // программу, которая роняла исполнение на `unreachable!` в раскрутке.
    let Some([_]) = signature.constructors(UNIT) else {
        return Ok(());
    };
    let Some(unit) = signature.instantiate(UNIT, metas) else {
        return Ok(());
    };
    let rho = metas.fresh_row();
    // Приостановленное вычисление: `{ρ} t` есть нульместная функция от единицы.
    let suspended = |result: u32| {
        Term::Pi(
            Binder::explicit(Mult::Many),
            CoreName::from("_"),
            Rc::new(unit.clone()),
            rho.clone(),
            Rc::new(Term::var(result)),
        )
    };
    let binders = vec![
        (
            Binder::implicit(Mult::Zero),
            CoreName::from("a"),
            Term::Universe(metas.fresh_level()),
        ),
        (
            Binder::implicit(Mult::Zero),
            CoreName::from("b"),
            Term::Universe(metas.fresh_level()),
        ),
        // Тело и деструктор - оба по разу: деструктор зовётся либо на выходе,
        // либо при раскрутке, но не дважды. Кратность `1` это и говорит, а
        // заодно пропускает захват ресурса замыканием: `ω` умножил бы его
        // расход и отверг бы то, что §3.3 разрешает.
        (Binder::explicit(Mult::One), CoreName::from("body"), {
            suspended(2)
        }),
        (Binder::explicit(Mult::One), CoreName::from("close"), {
            suspended(2)
        }),
    ];
    let ty = arrows(binders, &rho, Term::var(3));
    signature
        .declare(
            metas,
            &Group::of(SigMember::definition(CLOSING, Mult::Many, ty)),
        )
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: Names::of(&Rc::from(CLOSING), Vec::new()),
        })
}

/// Тип элиминатора эффекта (§3.4).
///
/// `handle e with …` есть применение этой константы, а не узел ядра. Правило
/// хендлера выражается обычной стрелкой: строка `{L p⃗ | ρ}` в домене и `ρ` в
/// результате и есть «снимает первое вхождение метки», а row-полиморфизм для
/// того и заведён. Отсюда даром полнота веток (по арности), тип каждой ветки,
/// кратность резумпции и `@`-выбор вхождения; и отсюда же то, что тотальность,
/// носители и живость видят обычное применение с лямбдами.
///
/// `resumed` - кратность самой резумпции: `1` у `handle`, `ω` у
/// `handleMulti`. Аффинность `1` и означает «вызывается не более одного раза»,
/// а забыть её законно: ветка, не зовущая её, обрывает вычисление.
///
/// **Row-параметров два, и они разные.** `ρ` - остаток вычисления после снятия
/// метки: её несёт `resume`, потому что резумпция продолжает именно вычисление.
/// `λ` - окружающая **применения** `handle`: её несут стрелки спайна и тела
/// веток, потому что ветка выполняется там, где написан сам хендлер.
///
/// Совпадать они не обязаны, и в этом всё дело. Ветка вправе производить
/// эффект, которого у вычисления нет вовсе, - на этом стоит хендлер-трансформер
/// `mapS` из §3.4, приведённый мотивом самого правила погашения. Пока обе роли
/// играла `ρ`, ветка могла производить только то, что осталось в вычислении, и
/// `mapS` не типизировался.
///
/// `λ ⊒ ρ` отдельным правилом не требуется и не проверяется: нужна эта связь
/// ровно там, где ветка зовёт `resume`, а там её обеспечивает обычное
/// погашение - `resume` объявлена в `ρ`, зовут её под `λ`. Ветка, не зовущая
/// резумпцию, обрывает вычисление, и остаток ему уже не понадобится.
///
/// **Порядок параметров.** Обобщение собирает дырки в порядке появления в
/// терме, а обход идёт «домен, кодомен, своя row». Первым встречается домен
/// вычисления - там стоит `{L p⃗ | ρ}`, - и только потом домен ветки `return`,
/// где стоит `λ`. Отсюда `ρ` нулевой, `λ` первый, и на это опирается
/// `Elaborator::handled`, подставляя их позиционно.
/// Тип `#mask.L` - элиминатора, пропускающего ближайший одноимённый хендлер.
///
/// ```text
/// #mask.L : {0 p⃗} -> {0 a} -> (ω c : {ρ} a) -> {L p⃗ | ρ} a
/// ```
///
/// Читается так: вычисление умеет `ρ`, а место применения обязано уметь `L p⃗`
/// **сверх** того. Лишняя метка впереди - фантом: её снимет ближайший хендлер,
/// и настоящие операции вычисления, если они той же метки, останутся в row и
/// достанутся следующему наружу (§3.4, §10 вопрос 72).
///
/// Row у элиминатора одна, а не две, как у хендлера: окружающая из неё
/// выводится дописыванием метки, а не задаётся отдельно.
fn mask_type(
    signature: &Signature,
    metas: &mut Metas,
    kind: &Term,
    label: &str,
    span: Span,
) -> Result<Term, ElabError> {
    let unit = signature
        .instantiate(UNIT, metas)
        .ok_or_else(|| ElabError::UnknownName {
            name: Rc::from(UNIT),
            span,
        })?;
    let rho = metas.fresh_row();

    // Параметры метки - те же implicit-связывания, что у хендлера.
    let mut binders: Vec<(Binder, CoreName, Term)> = Vec::new();
    let mut level = 0;
    let mut former = eval(&Env::default(), kind);
    while let Some(next) = peeled(&former, level, &mut binders) {
        former = next;
        level += 1;
    }
    let params = level;

    // Глубина под всеми связываниями: параметры метки, `a`, вычисление.
    let depth = params + 2;
    let answer = at(params, depth);
    let computation = Term::Pi(
        Binder::explicit(Mult::Many),
        CoreName::from("_"),
        Rc::new(unit),
        rho.clone(),
        Rc::new(answer.clone()),
    );
    // Окружающая стоит на стрелке вычисления и читается **под** её
    // связыванием - на той же глубине, что и кодомен.
    let ambient = Row::closing(
        [Label {
            name: CoreName::from(label),
            arguments: (0..params).map(|param| at(param, depth)).collect(),
        }],
        rho.tail(),
    );
    // Кратность вычисления - `1`: маска резумпции не имеет вовсе, поэтому
    // вычисление под ней проходится ровно однажды (§10 вопрос 95). Пока стояло
    // `ω`, элиминатор масштабировал расход, и `mask (logged h)` при
    // `(1 h : File)` отвергалось там, где `logged h` без маски проходило.
    let mut ty = Term::Pi(
        Binder::explicit(Mult::One),
        CoreName::from("computation"),
        Rc::new(computation),
        ambient,
        Rc::new(answer),
    );
    ty = Term::Pi(
        Binder::implicit(Mult::Zero),
        CoreName::from("a"),
        Rc::new(Term::Universe(metas.fresh_level())),
        Row::empty(),
        Rc::new(ty),
    );
    Ok(binders
        .into_iter()
        .rev()
        .fold(ty, |codomain, (binder, name, domain)| {
            Term::Pi(
                binder,
                name,
                Rc::new(domain),
                Row::empty(),
                Rc::new(codomain),
            )
        }))
}

/// Объявляемая метка глазами её элиминатора.
/// Типы элиминаторов эффекта - той же группой, что метка: они её называют, а
/// в сигнатуре её ещё нет.
///
/// Форм `handle` три. Мультишот отличается кратностью резумпции (§3.4);
/// параметризованный - только именем: оно доводит до машины признак, по
/// которому решение «резумпцию не позвали» откладывается до применения
/// ответа к состоянию (§10 вопрос 129), а ответ `S -> B` и двухаргументный
/// `resume` строит элаборация формы, не объявление. Маска - четвёртый
/// элиминатор той же группы и по той же причине (§10 вопрос 72).
fn eliminator_types(
    signature: &mut Signature,
    metas: &mut Metas,
    kind: &Term,
    declared: &Symbol,
    operations: &[(Symbol, Term, bool, u32)],
    rho: &Row<Term>,
    span: Span,
) -> Result<Vec<(String, Term)>, ElabError> {
    let forms = [
        ("#handle", Mult::One),
        ("#handleMulti", Mult::Many),
        ("#handleState", Mult::One),
    ];
    let mut handlers = Vec::with_capacity(forms.len() + 1);
    for (prefix, resumed) in forms {
        let ty = handler_type(
            signature,
            metas,
            &Handled {
                kind,
                label: declared,
                operations,
                resumed,
                rho: rho.clone(),
            },
            span,
        )?;
        handlers.push((format!("{prefix}.{declared}"), ty));
    }
    handlers.push((
        format!("{MASK}.{declared}"),
        mask_type(signature, metas, kind, declared, span)?,
    ));
    Ok(handlers)
}

struct Handled<'a> {
    /// Сорт формера метки: по нему снимаются её параметры.
    kind: &'a Term,
    /// Имя метки.
    label: &'a str,
    /// Операции: имя, тип, синтезирован ли триггер сахаром, арность кратностей.
    operations: &'a [(Symbol, Term, bool, u32)],
    /// Кратность резумпции - ею и различаются два элиминатора.
    resumed: Mult,
    /// Подъём, общий у элиминатора с операциями (§10 вопрос 120).
    rho: Row<Term>,
}

fn handler_type(
    signature: &Signature,
    metas: &mut Metas,
    handled: &Handled<'_>,
    span: Span,
) -> Result<Term, ElabError> {
    let Handled {
        kind,
        label,
        operations,
        resumed,
        rho,
    } = handled;
    let (kind, label, operations) = (*kind, *label, *operations);
    let (resumed, rho) = (*resumed, rho.clone());
    let missing = || ElabError::UnknownName {
        name: Rc::from(UNIT),
        span,
    };
    let unit = signature.instantiate(UNIT, metas).ok_or_else(missing)?;
    let [only] = signature.constructors(UNIT).ok_or_else(missing)? else {
        return Err(missing());
    };
    let only = Rc::clone(only);
    let trivial = signature.instantiate(&only, metas).ok_or_else(missing)?;
    let lambda = metas.fresh_row();

    // Параметры метки повторяются у элиминатора implicit-связываниями: писать
    // их в месте вызова незачем, они читаются из типа вычисления.
    let mut binders: Vec<(Binder, CoreName, Term)> = Vec::new();
    let mut level = 0;
    let mut former = eval(&Env::default(), kind);
    while let Some(next) = peeled(&former, level, &mut binders) {
        former = next;
        level += 1;
    }
    let params = level;

    // `a` - результат вычисления, `b` - ответ хендлера. Оба стёрты: они типы.
    let (answer, result) = (level + 1, level);
    for name in ["a", "b"] {
        let sort = Term::Universe(metas.fresh_level());
        binders.push((Binder::implicit(Mult::Zero), CoreName::from(name), sort));
        level += 1;
    }

    // Вычисление: `{L p⃗ | ρ} a`, то есть нульместная функция от единицы. Row
    // стоит под связыванием-единицей, поэтому её аргументы адресуются с той же
    // глубины, что и кодомен.
    let performed = Row::closing(
        [Label {
            name: CoreName::from(label),
            arguments: (0..params).map(|param| at(param, level + 1)).collect(),
        }],
        rho.tail(),
    );
    // Кратность вычисления - **кратность резумпции**, а не `ω` (§10 вопрос 95).
    // Одношотный хендлер проходит вычисление один раз, поэтому `1`-связывание
    // под ним расходуется однажды, и `ω` отвергало законное. Мультишот проходит
    // его столько раз, сколько ветка позвала `resume`: резумпция есть **участок
    // вычисления**, а не что-то рядом с ним, и захваченное замыканием
    // расходуется заново на каждом возобновлении. Измерено: при `1` у обоих
    // `handleMulti` над `\u -> pick n toss` при `(1 n : Nat)` проверку проходит,
    // а прогон отдаёт `n + n`.
    binders.push((
        Binder::explicit(resumed),
        CoreName::from("computation"),
        Term::Pi(
            Binder::explicit(Mult::Many),
            CoreName::from("_"),
            Rc::new(unit),
            performed,
            Rc::new(at(result, level + 1)),
        ),
    ));
    level += 1;

    // Ветка `return`: значение вычисления в ответ хендлера. Тело её работает в
    // окружающей применения, как и всякая другая ветка.
    binders.push((
        Binder::explicit(Mult::Many),
        CoreName::from("return"),
        Term::Pi(
            Binder::explicit(Mult::Many),
            CoreName::from("_"),
            Rc::new(at(result, level)),
            lambda.clone(),
            Rc::new(at(answer, level + 1)),
        ),
    ));
    level += 1;

    for (name, ty, suspended, _) in operations {
        let branch = branch_type(Branch {
            operation: ty,
            params,
            suspended: *suspended,
            depth: level,
            resumption: &rho,
            ambient: &lambda,
            answer,
            trivial: &trivial,
            resumed,
        });
        binders.push((
            Binder::explicit(Mult::Many),
            CoreName::from(&**name),
            branch,
        ));
        level += 1;
    }

    // Стрелки спайна несут **ρ**, а не λ: применение элиминатора исполняет
    // вычисление, и его остаток производится независимо от того, резюмирует
    // ветка или обрывает - до первой операции вычисление успевает сделать
    // своё. Понеси спайн λ, остаток перестал бы всплывать у хендлера, ни одна
    // ветка которого не зовёт `resume`.
    //
    // λ при этом не остаётся необеспеченной: подставляет её место применения
    // собственной окружающей, а окружающая разрешает сама себя. Написать
    // элиминатор частично применённым автор не может - имя его невыразимо.
    let body = at(answer, level);
    Ok(arrows(binders, &rho, body))
}

/// Снимает одно связывание типа, дописывая его в телескоп.
///
/// Связывание implicit и стёртое: параметры метки у элиминатора не пишут - они
/// читаются из типа вычисления.
fn peeled(
    ty: &Rc<Value>,
    level: u32,
    into: &mut Vec<(Binder, CoreName, Term)>,
) -> Option<Rc<Value>> {
    let Value::Pi(_, name, domain, _, codomain) = &**ty else {
        return None;
    };
    into.push((
        Binder::implicit(Mult::Zero),
        Rc::clone(name),
        quote(level, domain),
    ));
    Some(codomain.clone().apply(Value::var(Lvl(level))))
}

/// Тип ветки одной операции: её аргументы, резумпция, ответ.
///
/// Аргументы - те, что **написаны**: связывание-единицу, вставленную сахаром
/// `{ε} A`, ветка не связывает. Различить их по типу нечем - `get : s` и
/// `put : Unit -> Unit` после сахара одинаковы, - поэтому знание приходит от
/// объявления, где сахар и разворачивался.
#[derive(Clone, Copy)]
struct Branch<'a> {
    /// Тип операции, как его собрало объявление.
    operation: &'a Term,
    /// Сколько ведущих связываний - параметры метки.
    params: u32,
    /// Синтезирован ли триггер сахаром `{ε} A`.
    suspended: bool,
    /// Глубина, на которой стоит домен ветки.
    depth: u32,
    /// Остаток вычисления: его несёт `resume` - резумпция продолжает
    /// вычисление, а метка с него уже снята.
    resumption: &'a Row<Term>,
    /// Окружающая применения `handle`: в ней работает тело ветки.
    ambient: &'a Row<Term>,
    /// Уровень связывания ответа `b`.
    answer: u32,
    /// Значение единицы - им подставляется синтезированный триггер.
    trivial: &'a Term,
    /// Кратность резумпции.
    resumed: Mult,
}

fn branch_type(branch: Branch<'_>) -> Term {
    let Branch {
        operation,
        params,
        suspended,
        depth,
        resumption,
        ambient,
        answer,
        trivial,
        resumed,
    } = branch;
    // Параметры метки у операции - те же связывания и в том же порядке, что у
    // элиминатора, поэтому снимаются они своими же переменными.
    let mut current = eval(&Env::default(), operation);
    for param in 0..params {
        let Value::Pi(_, _, _, _, codomain) = &*current else {
            break;
        };
        let codomain = codomain.clone();
        current = codomain.apply(Value::var(Lvl(param)));
    }
    let mut binders: Vec<(Binder, CoreName, Term)> = Vec::new();
    let mut level = depth;
    let result = loop {
        let Value::Pi(binder, name, domain, labels, codomain) = &*current else {
            // Row обязана где-то стоять - это проверило объявление, - так что
            // сюда приходят только стрелки; ответ на всякий случай тот же.
            break quote(level, &current);
        };
        // Метки, а не row целиком: хвост есть у всякой стрелки, а производит
        // операция там, где написана метка.
        let performing = !labels.written().labels().is_empty();
        let (binder, name, domain) = (*binder, Rc::clone(name), quote(level, domain));
        let codomain = codomain.clone();
        let argument = if performing && suspended {
            // Триггер синтезирован сахаром: аргументом операции он не является,
            // а кодомен от него не зависит - связывание безымянное.
            eval(&Env::default(), trivial)
        } else {
            binders.push((binder, name, domain));
            level += 1;
            Value::var(Lvl(level - 1))
        };
        let next = codomain.apply(argument);
        if performing {
            break quote(level, &next);
        }
        current = next;
    };

    binders.push((
        Binder::explicit(resumed),
        CoreName::from("resume"),
        Term::Pi(
            Binder::explicit(Mult::Many),
            CoreName::from("_"),
            Rc::new(result),
            resumption.clone(),
            Rc::new(at(answer, level + 1)),
        ),
    ));
    level += 1;
    arrows(binders, ambient, at(answer, level))
}

/// Метка, применённая к собственным параметрам: `State s`.
///
/// Имя берётся объявленное, а не написанное: в теле модуля метка объявлена
/// квалифицированной, и собственная row операции обязана назвать её так же -
/// иначе операция ссылалась бы на несуществующее верхнеуровневое имя.
fn own_label(effect: &ast::EffectDecl, declared: &Symbol) -> ast::EffectLabel {
    ast::EffectLabel {
        name: ast::Name {
            text: Rc::clone(declared),
            span: effect.name.span,
        },
        arguments: effect
            .params
            .iter()
            .flat_map(|binder| &binder.names)
            .map(|name| ast::Expr {
                kind: ast::ExprKind::Name(name.clone()),
                span: name.span,
            })
            .collect(),
        span: effect.name.span,
    }
}

/// Тип операции с дописанной row: `yield : a -> ()` есть `a -> {Yield a} ()`.
///
/// Обе записи законны, и обе стоят в дизайне: §3.4 пишет `yield : a -> ()`,
/// §3.6 пишет `allocIn : … -> {Alloc r} (Ref r a)`. Дописывается метка в
/// **последний** кодомен - операция производится, когда применена целиком, - а
/// написанную не трогаем: её проверит ядро, и оно же скажет, если написана не
/// та.
///
/// Операция без стрелок вовсе (`get : s`) становится `{State s} s`, то есть
/// приостановленным вычислением (§3.4). Отдельного случая для неё нет: это та
/// же дописанная row, просто дописывать её некуда, кроме как в сам тип.
fn performed(ty: &ast::Expr, label: &ast::EffectLabel) -> ast::Expr {
    let kind = match &ty.kind {
        ast::ExprKind::Arrow(domain, codomain) => {
            ast::ExprKind::Arrow(domain.clone(), Box::new(performed(codomain, label)))
        }
        ast::ExprKind::Pi { binders, codomain } => ast::ExprKind::Pi {
            binders: binders.clone(),
            codomain: Box::new(performed(codomain, label)),
        },
        ast::ExprKind::Effectful { .. } => return ty.clone(),
        _ => ast::ExprKind::Effectful {
            labels: vec![label.clone()],
            tail: None,
            body: Box::new(ty.clone()),
        },
    };
    ast::Expr {
        kind,
        span: ty.span,
    }
}

/// Синтезировано ли связывание, на котором стоит row операции.
///
/// Row, легшая на **сам тип**, а не на кодомен стрелки, разворачивается сахаром
/// `{ε} A` в нульместную функцию, и связывание-единица в ней - не аргумент
/// операции: ветка хендлера его не связывает. Различить это по ядерному типу
/// нечем (`get : s` и `put : Unit -> Unit` после сахара одинаковы), а по
/// написанному - видно сразу, и видно одинаково у обеих форм записи row.
fn suspends(written: &ast::Expr) -> bool {
    matches!(written.kind, ast::ExprKind::Effectful { .. })
}

#[allow(clippy::too_many_arguments)]
fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    fixities: &Fixities,
    warnings: &mut Warnings,
    within: Option<&Enclosing>,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    let family = family_header(
        signature, metas, owned, fixities, warnings, within, data, span,
    )?;
    let constructors = family_constructors(
        signature,
        metas,
        owned,
        fixities,
        warnings,
        within,
        &family,
        &[family.visible()],
    )?;
    let parameters = u32::try_from(family.params.len()).unwrap_or(u32::MAX);
    let written: Vec<(&str, Term)> = constructors
        .iter()
        .map(|(name, ty)| (&**name, ty.clone()))
        .collect();
    signature
        .declare_data_inferred(
            metas,
            &family.declared,
            parameters,
            family.kind.clone(),
            &written,
        )
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Data(data), &error, span),
            error: Box::new(error),
            names: family.names.clone(),
        })?;
    // Умолчания - **после** объявления: они обычные определения, и семейство
    // им доступно как всякое другое имя.
    declare_defaults(
        signature,
        metas,
        owned,
        fixities,
        warnings,
        &family.declared,
        &data.params,
        Unwritten::Sort,
    )
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

/// Кайнды параметров класса, названные его суперклассами.
///
/// `class Applicative f when Functor f` кайнда `f` не пишет, а `Functor`
/// объявлен `(f : Type -> Type)` и, значит, уже его назвал. Читается кайнд по
/// позиции: аргумент констрейнта, написанный голым именем параметра, получает
/// домен суперкласса, стоящий на том же месте.
///
/// Общий вывод кайнда сюда не годится, и это измерено: дырка вместо `Type`
/// потребовала бы изобретать функциональный тип при применении `f a`, чего
/// элаборация не делает, и вдобавок ломала бы умолчание параметра. §4.4 при
/// этом пишет высококайндовый параметр без аннотации ровно там, где есть
/// суперкласс, - `Functor` объявлен с аннотацией, `Applicative` и
/// `Traversable` без неё.
fn superclass_kinds(
    signature: &Signature,
    metas: &mut Metas,
    class: &ast::ClassDecl,
) -> HashMap<Symbol, Term> {
    let named: Vec<&Symbol> = class
        .params
        .iter()
        .filter(|binder| binder.ty.is_none())
        .flat_map(|binder| &binder.names)
        .map(|name| &name.text)
        .collect();
    let mut found = HashMap::new();
    for superclass in &class.superclasses {
        let Some((head, arguments)) = spine_of(superclass) else {
            continue;
        };
        let Some(definition) = signature.lookup(&head.text) else {
            continue;
        };
        // Параметры уровня у суперкласса свои, и в новом классе их нет:
        // домен берётся инстанцированным свежими, как всякая ссылка на
        // объявленное.
        let levels: Vec<Level> = (0..definition.level_arity)
            .map(|_| metas.fresh_level())
            .collect();
        let rows: Vec<Row<Term>> = (0..definition.row_arity)
            .map(|_| metas.fresh_row())
            .collect();
        let mut domains = Vec::new();
        let mut current = &definition.ty;
        while let Term::Pi(_, _, domain, _, codomain) = current {
            domains.push(domain.substitute_levels(&levels).substitute_rows(&rows));
            current = codomain;
        }
        for (at, argument) in arguments.iter().enumerate() {
            let ast::ExprKind::Name(name) = &argument.kind else {
                continue;
            };
            let Some(domain) = domains.get(at) else {
                continue;
            };
            if named.contains(&&name.text) {
                found.insert(Symbol::clone(&name.text), Term::clone(domain));
            }
        }
    }
    found
}

/// Выполняет ли каждый член обещание своего поля целиком (§10 вопрос 115).
///
/// Поле, объявленное `{q : Mult}`, обещает **все** кратности, и место вызова
/// инстанцирует `q` по этому обещанию. Член же проверяется перебором
/// подстановок, как всякое определение, и множество прошедших бывает у́же:
/// `idy x = x` при `q = 0` не проверяется вовсе - стёртое связывание стоит в
/// рантайм-позиции.
///
/// Перебор объявление уже сделало; сравнить его итог с обещанием поля больше
/// некому. Разница наружу не уезжала: член ссылается на своё определение с
/// `Args::none()`, а место вызова идёт по **методу-проекции**, чьё множество
/// полное, - и нерешённая дырка оседала в наименьшее `0`, отчего линейный
/// аргумент переставал считаться израсходованным (ревью 2026-09-07).
///
/// Замерено: `Idy#File.idy` сужается до `[1, ω]`, тогда как `Functor#List.map`
/// и `Functor#Maybe.map` остаются полными - правило бьёт по тому, что и правда
/// невыполнимо.
///
/// # Errors
///
/// Член проверяется не при всех кратностях, обещанных полем.
fn kept_promise(
    signature: &Signature,
    members: &[Written],
    qualified: &[Symbol],
    span: Span,
) -> Result<(), ElabError> {
    for ((method, ..), full) in members.iter().zip(qualified) {
        let (Some(promised), Some(passing)) = (
            signature.lookup(method).map(|it| &it.mult_allowed),
            signature.lookup(full).map(|it| &it.mult_allowed),
        ) else {
            continue;
        };
        let narrower = promised
            .iter()
            .zip(passing.iter())
            .any(|(want, have)| want.iter().any(|value| !have.contains(value)));
        if narrower {
            return Err(ElabError::MemberMultiplicity {
                method: Rc::clone(method),
                passing: shown_mults(passing),
                promised: shown_mults(promised),
                span,
            });
        }
    }
    Ok(())
}

/// Множества кратностей в сообщении: по параметру, через запятую.
fn shown_mults(allowed: &[Rc<[adamas_core::mult::Mult]>]) -> String {
    allowed
        .iter()
        .map(|values| {
            let inner: Vec<String> = values.iter().map(ToString::to_string).collect();
            format!("{{{}}}", inner.join(", "))
        })
        .collect::<Vec<_>>()
        .join(", ")
}
