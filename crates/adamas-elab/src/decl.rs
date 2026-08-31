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

use adamas_core::check::{TypeError, check_closed_with, check_within, infer, is_type};
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
use adamas_core::value::Value;

use crate::class::{self, Declaring, Instances};
use crate::expr::{Elaborator, Enclosing, Member, Param};
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
    let mut instances = Instances::default();
    elaborate_into(
        module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut instances,
    )?;
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
    instances: &mut Instances,
) -> Result<(), ElabError> {
    members_into(&module.decls, None, signature, metas, owned, instances)
}

/// Квалифицирует имя членом модуля: `T` внутри `IntOrd` объявляется как
/// `IntOrd.T` (§4.8, решение 2026-08-30).
///
/// Точка в имени - то, чего поверхностный лексер не порождает, поэтому
/// столкнуться с написанным именем квалифицированное не может, а написать его
/// автор не в состоянии: снаружи модуль читается проекцией.
fn qualify(within: Option<&Enclosing<'_>>, name: &str) -> Symbol {
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
    /// Классы и их инстансы (§3.5).
    instances: &'a Instances,
    /// Инстанс, который объявляется прямо сейчас: сослаться на него именем
    /// нельзя, и словарь для него собирается записью из членов.
    declaring: Option<&'a Declaring<'a>>,
}

/// Написанная сигнатура - объявление, ждущее своих клауз.
#[allow(clippy::too_many_arguments)]
fn declared_signature<'a>(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    within: Option<&Enclosing<'_>>,
    name: &ast::Name,
    ty: &'a ast::Expr,
    span: Span,
) -> Result<Pending<'a>, ElabError> {
    // Владение верхнего уровня не выражается: определение всегда `ω`
    // (`sig.rs`: линейность на всю программу не считается), а §3.3 требует
    // `1`. Без этого отказа постулат ресурсного типа - обычное ω-имя, и `drop`
    // по нему зовётся сколько угодно раз.
    if let Some(how) = owned.of(ty) {
        return Err(ElabError::OwnedTopLevel {
            owned: how,
            name: Rc::clone(&name.text),
            span: ty.span,
        });
    }
    // Параметры функтора стоят у члена implicit-связываниями: компилятор
    // клауз связывает такие сам, а ссылка изнутри применяется к ним явно
    // (`Elaborator::specialized`).
    let mut elaborator = Elaborator::new(signature, metas, owned).within(within);
    let params = elaborator.telescope(params_of(within), true)?;
    let elaborated = elaborator.wrapped(&params, true, |it| it.declaration(ty, Mult::Many))?;
    Ok(Pending {
        name: qualify(within, &name.text),
        ty: elaborated,
        source: ty,
        span,
    })
}

/// Собирает read-only половину состояния.
fn known<'a>(owned: &'a Owned, instances: &'a Instances) -> Known<'a> {
    Known {
        owned,
        instances,
        declaring: None,
    }
}

/// Отвергает форму, законную только на верхнем уровне.
fn only_at_top(
    within: Option<&Enclosing<'_>>,
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

/// Параметры функтора, под которыми объявляется член. Пусто вне функтора.
fn params_of<'a>(within: Option<&Enclosing<'a>>) -> &'a [ast::Binder] {
    within.map_or(&[], |it| it.params)
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
fn members_into(
    decls: &[ast::Decl],
    within: Option<&Enclosing<'_>>,
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    instances: &mut Instances,
) -> Result<(), ElabError> {
    // Сигнатуры, ставшие постулатами по ходу прогона: клаузы, пришедшие за
    // ними, - не «нет сигнатуры», а сигнатура не рядом.
    let mut postulated: HashMap<Symbol, Span> = HashMap::new();
    let mut pending: Option<Pending<'_>> = None;
    for decl in decls {
        match &decl.kind {
            DeclKind::Signature { name, ty } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                pending = Some(declared_signature(
                    signature, metas, owned, within, name, ty, decl.span,
                )?);
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
                    signature,
                    metas,
                    known(owned, instances),
                    within,
                    &declared,
                    clauses,
                    decl.span,
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
                alias(
                    signature,
                    metas,
                    known(owned, instances),
                    within,
                    name,
                    body,
                    decl.span,
                )?;
            }
            DeclKind::Module(declared) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                declare_module(
                    signature, metas, owned, instances, within, declared, decl.span,
                )?;
            }
            DeclKind::Class(class) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // Класс в теле модуля не объявляется: методы его - имена
                // верхнего уровня, а модуль их квалифицирует, и разрешение
                // искало бы не то имя.
                only_at_top(
                    within,
                    &Rc::from("класс"),
                    "методы класса - имена верхнего уровня, а модуль их квалифицирует",
                    decl.span,
                )?;
                declare_class(signature, metas, owned, instances, class, decl.span)?;
            }
            DeclKind::Data(data) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                // Семейство в теле модуля - названная граница среза: имя
                // квалифицируется, а имена конструкторов нет, и разбор по ним
                // писать было бы нечем. Заводится вместе с путём в паттерне.
                only_at_top(
                    within,
                    &data.name.text,
                    "конструкторы квалифицированного имени пока не носят, \
                     и разобрать их в паттерне нечем",
                    decl.span,
                )?;
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
                only_at_top(
                    within,
                    &resource.name.text,
                    "ресурс объявляет конструкторы, а они пока квалифицированного \
                     имени не носят",
                    decl.span,
                )?;
                owned.declare(&resource.name.text, Ownership::Resource);
                declare_resource(signature, metas, owned, instances, resource, decl.span)?;
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
    known: Known<'_>,
    within: Option<&Enclosing<'_>>,
    name: &ast::Name,
    body: &ast::Expr,
    span: Span,
) -> Result<(), ElabError> {
    let declared = qualify(within, &name.text);
    let names = Names::of(&declared, Vec::new());
    let mut elaborator = Elaborator::new(signature, metas, known.owned).within(within);
    let params = elaborator.telescope(params_of(within), true)?;
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
    let ty = Elaborator::new(signature, metas, known.owned)
        .within(within)
        .wrapped(&params, true, |_| Ok(sort))?;
    let wrapped_body = abstracted(&params, term);
    class::resolve(
        signature,
        metas,
        known.instances,
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
    instances: &mut Instances,
    within: Option<&Enclosing<'_>>,
    module: &ast::ModuleDecl,
    span: Span,
) -> Result<(), ElabError> {
    let declared = qualify(within, &module.name.text);
    writable(within, module, span)?;
    if module.signature {
        return declare_module_type(signature, metas, owned, &declared, module, span);
    }
    let names = Names::of(&declared, Vec::new());
    if let Some(body) = &module.body {
        return declare_module_value(
            signature, metas, owned, instances, within, module, body, &declared, span,
        );
    }
    let inner = Enclosing {
        name: Rc::clone(&declared),
        params: &module.params,
    };
    members_into(
        &module.members,
        Some(&inner),
        signature,
        metas,
        owned,
        instances,
    )?;
    // Телескоп для самой записи считается **после** членов: граница объявления
    // освобождает дырки, и посчитанный заранее умер бы на первом же члене.
    let params = Elaborator::new(signature, metas, owned)
        .within(within)
        .telescope(&module.params, true)?;

    // Поле на каждого объявленного члена, в порядке написания. Клаузы своего
    // поля не заводят: его завела сигнатура, за которой они идут. Член
    // функтора поднят вместе с параметрами, поэтому здесь он применяется к
    // ним - запись собирается уже специализированной.
    let mut written = Vec::new();
    for member in &module.members {
        let Some(name) = member_name(member) else {
            continue;
        };
        let full = qualify(Some(&inner), name);
        let Some(mut term) = signature.instantiate(&full, metas) else {
            continue;
        };
        for position in 0..params.len() {
            let index = u32::try_from(params.len() - 1 - position).unwrap_or(u32::MAX);
            term = Term::App(Rc::new(term), Rc::new(Term::var(index)));
        }
        written.push((CoreName::from(&**name), Rc::new(term)));
    }
    let object = Term::Object(written.into());
    // Контекст параметров: тип записи считается под ними, а `Pi` над ним
    // строится тем же телескопом.
    let mut ctx = Ctx::new(signature);
    for param in &params {
        let bound = ctx.eval(&param.ty);
        ctx = ctx.bind(CoreName::from(&*param.name), param.mult, bound);
    }
    // Аннотация - тип объявления; проверяет соответствие ей `declare`, тем же
    // правилом, что и всякое тело. Без аннотации тип **структурный**: он
    // синтезируется по собранной записи, как и обещает §4.8.
    // Аннотация - тип объявления; проверяет соответствие ей `declare`, тем же
    // правилом, что и всякое тело. Без аннотации тип **структурный**: он
    // синтезируется по собранной записи, как и обещает §4.8. У функтора
    // аннотация относится к результату - к записи под параметрами.
    let inner_ty = if let Some(ascription) = &module.ascription {
        let written = Elaborator::new(signature, metas, owned)
            .within(within)
            .beneath(&params, |it| {
                it.typing(|inner| inner.expr(ascription, Mult::Many))
            })?;
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
    // Видимость здесь **явная**: `OrderedMap IntOrd` пишется, в отличие от
    // параметров у членов, которые автор не пишет никогда.
    let ty = params.iter().rev().fold(inner_ty, |codomain, param| {
        Term::Pi(
            Binder::explicit(param.mult),
            CoreName::from(&*param.name),
            Rc::clone(&param.ty),
            adamas_core::row::Row::empty(),
            Rc::new(codomain),
        )
    });
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
        })
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
fn declare_class(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    instances: &mut Instances,
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
    let Some((name, arguments)) = spine_of(written) else {
        return Err(ElabError::ClassHead { span });
    };
    if class.instance {
        return declare_instance(signature, metas, owned, instances, class, name, span);
    }
    // Параметр класса пишется именем: `class Eqv a where`. Тип у него не
    // написан, и умолчание то же, что у параметра семейства, - `Type`.
    let mut params = Vec::with_capacity(arguments.len());
    for argument in arguments {
        let ast::ExprKind::Name(bound) = &argument.kind else {
            return Err(ElabError::ClassHead {
                span: argument.span,
            });
        };
        params.push(ast::Binder {
            visibility: ast::Visibility::Explicit,
            // Параметр класса стёрт: это тип, и в рантайме его нет. Тем же
            // нулём он стоит у метода - `{0 a : Type} -> {ω d : C a} -> …`.
            mult: Some(ast::MultAnn {
                mult: ast::Mult::Zero,
                span: argument.span,
            }),
            names: vec![bound.clone()],
            ty: None,
            span: argument.span,
        });
    }
    let mut members = Vec::with_capacity(class.members.len());
    for member in &class.members {
        let DeclKind::Signature { name, ty } = &member.kind else {
            return Err(ElabError::ModuleMember {
                name: member_name(member)
                    .cloned()
                    .unwrap_or_else(|| Rc::from("_")),
                what: "классе",
                why: "класс несёт сигнатуры методов; умолчания и суперклассы пока не \
                      объявляются",
                span: member.span,
            });
        };
        members.push((name.clone(), Some(ty)));
    }
    let names = Names::of(&name.text, Vec::new());
    // Класс - **функция** от своих параметров в тип записи, а не сам тип:
    // `Eqv Nat` есть применение. Отсюда тело лямбдой, а тип - `Pi` над
    // универсумом, в котором живёт запись.
    let mut elaborator = Elaborator::new(signature, metas, owned);
    let telescope = elaborator.telescope(&params, false)?;
    let (record, level) = elaborator.beneath(&telescope, |it| {
        let fields = it.module_members(&members)?;
        let record = Term::Record(Fields::closed(fields.into()));
        let level = it.sort_of(&record).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        Ok((record, level))
    })?;
    let sort = Term::Universe(metas.zonk(&level));
    let ty = Elaborator::new(signature, metas, owned).wrapped(&telescope, false, |_| Ok(sort))?;
    let body = abstracted(&telescope, record);
    signature
        .define_inferred(metas, &name.text, Mult::Many, ty, Some(body))
        .map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names,
        })?;
    instances.declare(&name.text);
    for (method, _) in &members {
        declare_method(signature, metas, &name.text, &method.text, span)?;
    }
    Ok(())
}

/// `instance Eqv Nat where …` - запись, проверенная против `Eqv Nat`.
#[allow(clippy::too_many_arguments)]
fn declare_instance(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    instances: &mut Instances,
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
    let names = Names::of(&name.text, Vec::new());
    let fail = |error: TypeError| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    };
    // Голова элаборируется заново на каждое объявление: граница объявления
    // освобождает дырки уровня, а у полиморфного инстанса они как раз и
    // остаются нерешёнными - тот же порядок, что у функтора.
    let written = written_head(signature, metas, owned, class, span, &names)?;
    let Some((_, argument)) = applied_head(under_prefix(&written)) else {
        return Err(ElabError::ClassHead { span });
    };
    let declared: Symbol = Rc::from(format!("{}#{argument}", name.text).as_str());
    // Кандидат запоминается **до** членов: иначе о дубликате скажет ядро,
    // назвав `Eqv#Nat.eq` - имя, которого автор не писал.
    if !instances.add(&name.text, &argument, Rc::clone(&declared)) {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&name.text),
            what: "программе",
            why: "инстанс для этого типа уже объявлен, а именованных инстансов пока нет",
            span,
        });
    }
    let members = instance_members(class)?;
    let qualified: Vec<Symbol> = members
        .iter()
        .map(|(method, _)| Rc::from(format!("{declared}.{}", method.text).as_str()))
        .collect();
    for (at, (method, clauses)) in members.iter().enumerate() {
        let written = written_head(signature, metas, owned, class, span, &names)?;
        let prefix = leading(&written);
        let ty = instance_method(signature, metas, &prefix, &written, method, span, &names)?;
        // Словарь для **собственной** цели собирается записью из членов:
        // сослаться на объявляемый инстанс именем нельзя, в сигнатуре его ещё
        // нет. Член, объявленный ниже, сюда не попадает - тогда рекурсия по
        // нему и отвергается (решение 2026-08-31).
        let mut fields = Vec::with_capacity(members.len());
        for (other, full) in qualified.iter().enumerate() {
            let term = if other == at {
                Term::Const(
                    CoreName::from(&**full),
                    self_levels(signature, metas, &ty).map_err(fail)?,
                )
            } else if let Some(term) = signature.instantiate(full, metas) {
                term
            } else {
                continue;
            };
            fields.push((Rc::clone(&members[other].0.text), term));
        }
        let declaring = Declaring {
            class: Rc::clone(&name.text),
            head: Rc::clone(&argument),
            prefix: prefix.len(),
            members: &fields,
        };
        let complete = fields.len() == members.len();
        let pending = Pending {
            name: Rc::clone(&qualified[at]),
            ty,
            source: &class.head,
            span: span_of(clauses, span),
        };
        let mut known = known(owned, instances);
        if complete {
            known.declaring = Some(&declaring);
        }
        define(signature, metas, known, None, &pending, clauses, span)?;
    }
    // Словарь - запись из членов, применённых к своим же связываниям.
    let written = written_head(signature, metas, owned, class, span, &names)?;
    let prefix = leading(&written);
    let mut object = Vec::with_capacity(members.len());
    for (at, (method, _)) in members.iter().enumerate() {
        let Some(term) = signature.instantiate(&qualified[at], metas) else {
            continue;
        };
        let applied = (0..prefix.len()).fold(term, |callee, position| {
            let index = u32::try_from(prefix.len() - 1 - position).unwrap_or(u32::MAX);
            Term::App(Rc::new(callee), Rc::new(Term::var(index)))
        });
        object.push((CoreName::from(&*method.text), Rc::new(applied)));
    }
    let object = abstracted(&prefix, Term::Object(object.into()));
    // `check_within`, а не `check_closed_with`: нерешённая дырка уровня здесь -
    // будущий параметр самого словаря, и запрет отвергал бы всякий
    // полиморфный инстанс. Окончательный запрет ставит объявление.
    check_within(&Ctx::new(signature), metas, &object, &written).map_err(fail)?;
    let written = zonk_term(metas, &written);
    signature
        .define_inferred(metas, &declared, Mult::Many, written, Some(object))
        .map_err(fail)
}

/// Место клауз - для маршрута ошибки.
fn span_of(clauses: &[ast::Clause], span: Span) -> Span {
    clauses.first().map_or(span, |clause| clause.span)
}

/// Написанная голова инстанса как тип словаря.
///
/// Считается заново на каждое объявление: граница объявления освобождает
/// дырки, а у полиморфного инстанса уровень как раз и остаётся нерешённым до
/// обобщения. Тот же порядок у функтора (лог 2026-08-31).
fn written_head(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    class: &ast::ClassDecl,
    span: Span,
    names: &Names,
) -> Result<Term, ElabError> {
    let written = Elaborator::new(signature, metas, owned).declaration(&class.head, Mult::Many)?;
    is_type(&Ctx::new(signature), metas, &written).map_err(|error| ElabError::Core {
        span,
        error: Box::new(error),
        names: names.clone(),
    })?;
    Ok(zonk_term(metas, &written))
}

/// Члены инстанса: только клаузы, и тип каждого пишет класс.
fn instance_members(
    class: &ast::ClassDecl,
) -> Result<Vec<(&ast::Name, &[ast::Clause])>, ElabError> {
    let mut found = Vec::with_capacity(class.members.len());
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
        found.push((name, clauses.as_slice()));
    }
    Ok(found)
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
    method: &ast::Name,
    span: Span,
    names: &Names,
) -> Result<Term, ElabError> {
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
    let projection = Term::Project(Rc::new(Term::var(0)), CoreName::from(&*method.text));
    let (found, _) = infer(&bound, metas, Mult::Zero, &projection).map_err(fail)?;
    if mentions_depth(&quote(bound.size(), &found), 0) {
        return Err(ElabError::ModuleMember {
            name: Rc::clone(&method.text),
            what: "классе",
            why: "тип метода зависит от значения другого метода, и вывести его \
                  в инстансе нечем",
            span,
        });
    }
    let depth = u32::try_from(prefix.len()).unwrap_or(u32::MAX);
    let ty = zonk_term(metas, &quote(depth, &found));
    Ok(prefix.iter().rev().fold(ty, |inner, param| {
        Term::Pi(
            Binder::implicit(param.mult),
            CoreName::from(&*param.name),
            Rc::clone(&param.ty),
            adamas_core::row::Row::empty(),
            Rc::new(inner),
        )
    }))
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

/// Голова применения и голова её аргумента - по элаборированному типу.
fn applied_head(ty: &Term) -> Option<(Symbol, Symbol)> {
    let Term::App(callee, argument) = ty else {
        return None;
    };
    let Term::Const(class, _) = &**callee else {
        return None;
    };
    let mut head = &**argument;
    while let Term::App(inner, _) = head {
        head = inner;
    }
    let Term::Const(name, _) = head else {
        return None;
    };
    Some((Rc::clone(class), Rc::clone(name)))
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
    let (kind, _) = infer(&Ctx::new(signature), metas, Mult::Zero, &applied).map_err(fail)?;
    let Value::Pi(_, _, domain, _, _) = &*kind else {
        return Ok(());
    };
    let sort = quote(0, domain);
    let ctx = Ctx::new(signature);
    let inner = ctx.bind(CoreName::from("a"), Mult::Zero, Rc::clone(domain));
    let dictionary = Term::App(Rc::new(applied.clone()), Rc::new(Term::var(0)));
    let bound = inner.eval(&dictionary);
    let inner = inner.bind(CoreName::from("d"), Mult::Many, bound);
    let projection = Term::Project(Rc::new(Term::var(0)), CoreName::from(&**method));
    let (ty, _) = infer(&inner, metas, Mult::Zero, &projection).map_err(fail)?;
    let ty = Term::Pi(
        Binder::implicit(Mult::Zero),
        CoreName::from("a"),
        Rc::new(sort),
        adamas_core::row::Row::empty(),
        Rc::new(Term::Pi(
            Binder::implicit(Mult::Many),
            CoreName::from("d"),
            Rc::new(dictionary),
            adamas_core::row::Row::empty(),
            Rc::new(quote(inner.size(), &ty)),
        )),
    );
    let body = Term::Lam(
        Mult::Zero,
        CoreName::from("a"),
        Rc::new(Term::Lam(
            Mult::Many,
            CoreName::from("d"),
            Rc::new(projection),
        )),
    );
    signature
        .define_inferred(metas, method, Mult::Many, ty, Some(body))
        .map_err(fail)
}

/// Формы объявления, которых язык не несёт, - названные границы среза.
fn writable(
    within: Option<&Enclosing<'_>>,
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
    // Вложенность внутри функтора не поддержана: члены внутреннего модуля
    // подняты со **своими** параметрами, а внешние им тоже нужны, и склеивать
    // два телескопа этот срез не берётся.
    if within.is_some_and(|it| !it.params.is_empty()) {
        return refuse(
            "теле функтора",
            "члены вложенного модуля поднимаются со своими параметрами, \
             а внешние им тоже нужны",
        );
    }
    Ok(())
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
    instances: &Instances,
    within: Option<&Enclosing<'_>>,
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
    let term = Elaborator::new(signature, metas, owned)
        .within(within)
        .typing(|it| it.expr(body, Mult::Many))?;
    let ty = if let Some(ascription) = &module.ascription {
        let written = Elaborator::new(signature, metas, owned)
            .within(within)
            .typing(|it| it.expr(ascription, Mult::Many))?;
        check_closed_with(signature, metas, &term, &written).map_err(|error| ElabError::Core {
            span,
            error: Box::new(error),
            names: names.clone(),
        })?;
        zonk_term(metas, &written)
    } else {
        let (ty, _) = infer(&Ctx::new(signature), metas, Mult::Many, &term).map_err(|error| {
            ElabError::Core {
                span,
                error: Box::new(error),
                names: names.clone(),
            }
        })?;
        quote(0, &ty)
    };
    class::resolve(signature, metas, instances, None, &term, &ty, span)?;
    signature
        .define_opaque(metas, declared, Mult::Many, ty, Some(term), module.sealed)
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
        DeclKind::Clauses { .. } | DeclKind::Class(_) => None,
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
    known: Known<'_>,
    within: Option<&Enclosing<'_>>,
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
        let mut elaborator = Elaborator::with_group(signature, metas, known.owned, group)
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

    // Словари, вставленные дырками, заполняются поиском - до объявления,
    // которому нерешённая дырка запрещена (§3.5, `crate::class`).
    class::resolve(
        signature,
        metas,
        known.instances,
        known.declaring,
        &tree.term,
        &declared.ty,
        span,
    )?;

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
    carrier::check(signature, known.owned, &declared.name, span)
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
            ast::DeclKind::Class(_) => {
                return Err(ElabError::ResourceMember {
                    data: Rc::clone(&resource.name.text),
                    name: Rc::from("класс"),
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
    instances: &Instances,
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
    define(
        signature,
        metas,
        known(owned, instances),
        None,
        &declared,
        clauses,
        drop_span,
    )?;
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
        Term::Universe(_) | Term::RowKind(_) | Term::Const(..) | Term::Meta(_) => false,
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
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(recur)
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
    let params = elaborator.telescope(&data.params, false)?;
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
