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
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::{Generalization, Metas, zonk_term};
use adamas_core::mult::Mult;
use adamas_core::pattern::{PatternError, compile_traced};
use adamas_core::sig::{Group, Member as SigMember, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Binder, Fields, Name as CoreName, Term};
use adamas_parser::ast::{self, DeclKind, Module, Symbol};

use crate::carrier;
use crate::error::{ElabError, Names};
use adamas_core::value::Value;

use crate::class::{self, Class, Declaring, Instances, Offence};
use crate::expr::{Elaborator, Enclosing, Member, Param, WrittenField};
use crate::own::{Owned, Ownership};
use crate::route::{self, Declared};

/// Сигнатура, ожидающая клауз.
///
/// Написанный тип хранится вместе с собранным: маршрут отказа пойдёт по нему
/// обратно, чтобы стать спаном (§10 вопрос 49б).
struct Pending<'a> {
    /// Требует ли `@total` положительного вердикта (§4.7).
    total: bool,
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
    declaring: Option<&'a Declaring>,
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
    instances: &Instances,
    within: Option<&Enclosing<'_>>,
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
        known(owned, instances),
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

/// Разбирает атрибуты сигнатуры: что из них требует проверки (§4.7).
///
/// `@total` - единственный, который компилятор сегодня проверяет: вердикт
/// ядро считает всегда, и атрибут превращается в требование «ответ обязан
/// быть да». `@fbip` и `@noalloc` - обязательства перед backend'ом, а его нет;
/// принять их молча значило бы обещать проверку, которой не будет.
fn required(attributes: &[ast::Name]) -> Result<bool, ElabError> {
    let mut total = false;
    for attribute in attributes {
        match &*attribute.text {
            "total" => total = true,
            "fbip" => {
                return Err(ElabError::Attribute {
                    name: Rc::clone(&attribute.text),
                    why: "совместимость с FBIP проверяется по коду backend'а (§5.1), \
                          а его ещё нет",
                    span: attribute.span,
                });
            }
            "noalloc" => {
                return Err(ElabError::Attribute {
                    name: Rc::clone(&attribute.text),
                    why: "источники аллокации перечисляет backend (§5.1), а его ещё нет",
                    span: attribute.span,
                });
            }
            _ => {
                return Err(ElabError::Attribute {
                    name: Rc::clone(&attribute.text),
                    why: "такого атрибута в языке нет",
                    span: attribute.span,
                });
            }
        }
    }
    Ok(total)
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
    attributes: &[ast::Name],
    span: Span,
) -> Result<Pending<'a>, ElabError> {
    let total = required(attributes)?;
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
    let params = elaborator.telescope(params_of(within), true, Mult::Many)?;
    let elaborated = elaborator.wrapped(&params, true, |it| it.declaration(ty, Mult::Many))?;
    Ok(Pending {
        total,
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
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                pending = Some(declared_signature(
                    signature, metas, owned, within, name, ty, attributes, decl.span,
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
            DeclKind::Alias { name, params, body } => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                written_alias(
                    signature,
                    metas,
                    owned,
                    instances,
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
                    signature, metas, owned, instances, within, declared, decl.span,
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
                declare_mutual(signature, metas, owned, instances, members, decl.span)?;
            }
            DeclKind::Class(class) => {
                postulate(signature, metas, pending.take(), &mut postulated)?;
                let (what, why) = outside_a_module(class.instance);
                only_at_top(within, &Rc::from(what), why, decl.span)?;
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
    written: &Aliased<'_>,
    span: Span,
) -> Result<(), ElabError> {
    let (name, body) = (written.name, written.body);
    let declared = qualify(within, &name.text);
    let names = Names::of(&declared, Vec::new());
    let mut elaborator = Elaborator::new(signature, metas, known.owned).within(within);
    // Связывания двух родов и в одном телескопе: сперва параметры функтора,
    // потом свои. Написанный параметр живёт под функторными - его тип вправе
    // их упоминать, - поэтому и элаборируются они одной последовательностью.
    let outer = elaborator.telescope(params_of(within), true, Mult::Many)?;
    let owned_params =
        elaborator.beneath(&outer, |it| it.telescope(written.params, false, Mult::Zero))?;
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
    let ty = Elaborator::new(signature, metas, known.owned)
        .within(within)
        .wrapped(&outer, true, |it| {
            it.wrapped(&owned_params, false, |_| Ok(sort))
        })?;
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
    declare_defaults(signature, metas, known.owned, &declared, written.params)
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
    sealable(instances, module, span)?;
    if module.signature {
        return declare_module_type(signature, metas, owned, instances, &declared, module, span);
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
        .telescope(&module.params, true, Mult::Many)?;

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
        })?;
    // Запечатываются и **поднятые члены**: снаружи `M.f` есть ссылка на них, а
    // не проекция из записи, и одной непрозрачной записи для сокрытия уже мало.
    // Ставится флаг после проверки всего модуля: члены видят друг друга, и
    // непрозрачность, поставленная сразу, запретила бы δ соседу.
    if module.sealed {
        for member in &module.members {
            if let Some(name) = member_name(member) {
                signature.seal(&qualify(Some(&inner), name));
            }
        }
    }
    Ok(())
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
    let Some((name, _)) = spine_of(written) else {
        return Err(ElabError::ClassHead { span });
    };
    if class.instance {
        return declare_instance(signature, metas, owned, instances, class, name, span);
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
    let names = Names::of(&name.text, Vec::new());
    // Класс - **функция** от своих параметров в тип записи, а не сам тип:
    // `Eqv Nat` есть применение. Отсюда тело лямбдой, а тип - `Pi` над
    // универсумом, в котором живёт запись.
    let mut elaborator = Elaborator::new(signature, metas, owned);
    let telescope = elaborator.telescope(&params, false, Mult::Zero)?;
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
    declare_defaults(signature, metas, owned, &name.text, &params)?;
    // Имя верхнего уровня получает **метод**, а не поле суперкласса: его
    // разряжает разрешение, и писать его автору незачем.
    for method in &info.methods {
        declare_method(signature, metas, &name.text, method, span)?;
    }
    instances.declare(&name.text, info);
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
    // Голова элаборируется **один раз на всю группу**: члены инстанса
    // объявляются вместе, поэтому граница объявления одна, и дырки уровня
    // доживают до неё.
    let written = written_head(signature, metas, owned, class, span, &names)?;
    let prefix = leading(&written);
    let Some((_, arguments)) = applied_head(signature, under_prefix(&written)) else {
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
        instances,
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
    let written = written_head(signature, metas, owned, class, span, &names)?;
    let prefix = leading(&written);
    let mut object = Vec::with_capacity(superclasses + members.len());
    // Поле суперкласса - дырка: разряжает его **разрешение**, а не автор
    // (§3.5). Стоит она в контексте префикса, поэтому и тип у неё - тот же
    // телескоп, оканчивающийся типом поля.
    for index in 0..superclasses {
        let field: Symbol = Rc::from(format!("#super{index}").as_str());
        let ty = instance_method(signature, metas, &prefix, &written, &field, span, &names)?;
        let size = u32::try_from(prefix.len()).unwrap_or(u32::MAX);
        let hole = metas.fresh_term(Ctx::new(signature).eval(&ty), size);
        object.push((CoreName::from(&*field), Rc::new(hole)));
    }
    for (at, (method, ..)) in members.iter().enumerate() {
        let Some(term) = signature.instantiate(&qualified[at], metas) else {
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
    class::resolve(signature, metas, instances, None, &object, &written, span)?;
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
            DeclKind::Signature { name, ty, .. } => {
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
    // Зонк подставляет решение дырки целиком и оставляет бета-редекс:
    // домен второго связывания заголовка - дырка над первым, и её решение
    // приезжает лямбдой, применённой к нему. Инференс такого домена спотыкается
    // (лямбде нужна аннотация), поэтому заголовок читается обратно из значения.
    // Константы при этом остаются свёрнутыми - класс в голове переживает
    // нормализацию.
    let written = zonk_term(metas, &written);
    Ok(quote(0, &Ctx::new(signature).eval(&written)))
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
    let projection = Term::Project(Rc::new(Term::var(0)), CoreName::from(method));
    let (found, _) = infer(&bound, metas, Mult::Zero, &projection).map_err(fail)?;
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

/// Невыразимое имя анонимного инстанса: `Eqv#Nat`, `Conv#Nat#Bool`.
fn mangled(class: &str, heads: &[Symbol]) -> String {
    let mut out = String::from(class);
    for head in heads {
        out.push('#');
        out.push_str(head);
    }
    out
}

/// Имя класса и головы всех его аргументов - по элаборированному типу.
///
/// Головы **всех**: у многопараметрического класса первая ничего не решает
/// (§4.1), и ключ кандидата составляется из них целиком.
fn applied_head(signature: &Signature, ty: &Term) -> Option<(Symbol, Rc<[Symbol]>)> {
    let (class, head) = class::applied(signature, ty)?;
    match head {
        class::Head::Named(heads) => Some((class, heads)),
        _ => None,
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
    let (ty, _) = infer(&inner, metas, Mult::Zero, &projection).map_err(fail)?;
    let ty = Term::Pi(
        Binder::implicit(Mult::Many),
        CoreName::from("d"),
        Rc::new(dictionary),
        adamas_core::row::Row::empty(),
        Rc::new(quote(inner.size(), &ty)),
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
        .define_inferred(metas, method, Mult::Many, ty, Some(body))
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
        let ty = instance_method(signature, metas, prefix, written, &field, span, names)?;
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
                    Term::Const(CoreName::from(&**full), Rc::clone(levels)),
                )
            })
            .collect(),
    })
}

#[allow(clippy::too_many_arguments)]
fn declare_members(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    instances: &Instances,
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
    for (method, ..) in members {
        types.push(instance_method(
            signature, metas, prefix, written, method, span, names,
        )?);
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
            let mut elaborator = Elaborator::with_group(signature, metas, owned, visible.clone())
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
            .with_arity(arity);
        group = Some(match group {
            None => Group::of(member),
            Some(group) => group.and(member),
        });
    }
    if let Some(group) = group {
        signature.declare(metas, &group).map_err(fail)?;
    }
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
fn declare_mutual(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &mut Owned,
    instances: &Instances,
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
    declare_families(signature, metas, owned, &planned, span)?;
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
    let mut types = Vec::with_capacity(planned.len());
    for member in &planned {
        types.push(Elaborator::new(signature, metas, owned).declaration(member.ty, Mult::Many)?);
    }
    let mut arities = Vec::with_capacity(planned.len());
    let mut generalized = Vec::with_capacity(planned.len());
    for ty in &types {
        let zonked = zonk_term(metas, ty);
        let mut generalization = Generalization::default();
        generalization.collect_term(metas, &zonked);
        arities.push(generalization.arity());
        generalized.push(generalization.apply_term(metas, &zonked));
    }

    let mut trees = Vec::with_capacity(planned.len());
    for (at, member) in planned.iter().enumerate() {
        let mut visible = Vec::with_capacity(planned.len());
        for (other, sibling) in planned.iter().enumerate() {
            // Свой параметр - `Var`, чужой - дырка: сосед объявляется рядом,
            // но инстанцируется в каждом месте использования заново.
            let levels: Rc<[Level]> = if other == at {
                (0..arities[at])
                    .map(|index| Level::Var(LevelVar(index)))
                    .collect()
            } else {
                (0..arities[other]).map(|_| metas.fresh_level()).collect()
            };
            visible.push(Member {
                name: Rc::clone(&sibling.name.text),
                ty: Rc::new(generalized[other].substitute_levels(&levels)),
                levels,
            });
        }
        let compiled = {
            let mut elaborator = Elaborator::with_group(signature, metas, owned, visible)
                .declaring(&generalized[at]);
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
            None,
            &tree.term,
            &generalized[at],
            member.span,
        )?;
        trees.push(tree);
    }

    let mut group: Option<Group> = None;
    for (at, member) in planned.iter().enumerate() {
        let declared =
            SigMember::definition(&member.name.text, Mult::Many, generalized[at].clone())
                .with_body(trees[at].term.clone())
                .with_arity(arities[at]);
        group = Some(match group {
            None => Group::of(declared),
            Some(group) => group.and(declared),
        });
    }
    if let Some(group) = group {
        signature
            .declare(metas, &group)
            .map_err(|error| ElabError::Core {
                span,
                error: Box::new(error),
                names: Names::of(&planned[0].name.text, Vec::new()),
            })?;
    }
    for member in &planned {
        carrier::check(signature, owned, &member.name.text, member.span)?;
    }
    Ok(())
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
    planned: &[Planned<'_>],
    span: Span,
) -> Result<(), ElabError> {
    let mut families = Vec::new();
    for member in planned {
        if let Planned::Family(data, at) = member {
            families.push(family_header(signature, metas, owned, data, *at)?);
        }
    }
    let Some(first) = families.first() else {
        return Ok(());
    };
    let names = first.names.clone();
    let seen: Vec<Member> = families.iter().map(Family::visible).collect();
    let mut group: Option<Group> = None;
    for family in &families {
        let constructors = family_constructors(signature, metas, owned, family, &seen)?;
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
            &family.data.name.text,
            &family.data.params,
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
    let mut pending: Option<(&ast::Name, &ast::Expr, Span)> = None;
    for member in members {
        match &member.kind {
            DeclKind::Signature { name, ty, .. } => {
                if let Some((waiting, ..)) = pending {
                    return Err(ElabError::MissingSignature {
                        name: Rc::clone(&waiting.text),
                        span: member.span,
                    });
                }
                pending = Some((name, ty, member.span));
            }
            DeclKind::Clauses { name, clauses } => {
                let Some((declared, ty, at)) =
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
        DeclKind::Clauses { .. } | DeclKind::Class(_) | DeclKind::Mutual(_) => None,
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
        Term::Const(name, _) => Some((Rc::clone(name), arguments)),
        _ => None,
    }
}

/// Отвергает `:>` по сигнатуре, которой запечатывать нельзя (§3.5).
///
/// Аннотация `:` при том же тексте законна: правило охраняет **осадок**, а он
/// заводится только там, где представление скрыто.
fn sealable(instances: &Instances, module: &ast::ModuleDecl, span: Span) -> Result<(), ElabError> {
    if !module.sealed {
        return Ok(());
    }
    // Аннотация выражением, а не именем, сюда не проходит: искать нарушение
    // негде, а разворачивать выражение правило не берётся - оно локально.
    let Some(ast::ExprKind::Name(name)) = module.ascription.as_ref().map(|it| &it.kind) else {
        return Ok(());
    };
    let Some(offence) = instances.offence(&name.text) else {
        return Ok(());
    };
    Err(ElabError::SealedConstraint {
        signature: Rc::clone(&name.text),
        member: Rc::clone(&offence.member),
        class: Rc::clone(&offence.class),
        param: Rc::clone(&offence.param),
        sealed: Rc::clone(&offence.sealed),
        span,
    })
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

/// `module type S where …` - тип записи, собранный телескопом.
fn declare_module_type(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    instances: &mut Instances,
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
    let mut members = Vec::with_capacity(module.members.len());
    for member in &module.members {
        match &member.kind {
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
    let fields =
        Elaborator::new(signature, metas, owned).typing(|it| it.module_members(&members))?;
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

    // Вердикт читается после объявления: считает его ядро, а атрибут только
    // требует, чтобы ответ был «да» (§4.7).
    if declared.total && !signature.lookup(&declared.name).is_some_and(|it| it.total) {
        return Err(ElabError::NotTotal {
            name: Rc::clone(&declared.name),
            span: declared.span,
        });
    }

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
        total: false,
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
fn declare_defaults(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    declared: &Symbol,
    written: &[ast::Binder],
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
        let mut elaborator = Elaborator::new(signature, metas, owned);
        let params = elaborator.telescope(&written[..=position], false, Mult::Zero)?;
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
            name: Rc::clone(&self.data.name.text),
            levels: Rc::clone(&self.levels),
            ty: Rc::new(self.kind.clone()),
        }
    }
}

/// Телескоп, kind и арность уровней семейства.
fn family_header<'a>(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    data: &'a ast::Data,
    span: Span,
) -> Result<Family<'a>, ElabError> {
    // Телескоп параметров элаборируется один раз и переиспользуется: kind и
    // каждый конструктор обязаны нести **один и тот же** телескоп, иначе
    // `List` в результате и `List` в объявлении - два разных семейства.
    let mut elaborator = Elaborator::new(signature, metas, owned);
    let params = elaborator.telescope(&data.params, false, Mult::Zero)?;
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
    Ok(Family {
        data,
        params,
        kind,
        levels,
        names,
    })
}

/// Типы конструкторов - под группой, в которой семейство объявляется.
fn family_constructors<'a>(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    family: &Family<'a>,
    visible: &[Member],
) -> Result<Vec<(&'a str, Term)>, ElabError> {
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
            let ty = Elaborator::with_group(signature, metas, owned, visible.to_vec()).wrapped(
                &family.params,
                true,
                |it| it.declaration(&constructor.ty, Mult::One),
            )?;
            owned_field(&ty, owned, family.data, constructor)?;
            Ok((&*constructor.name.text, ty))
        })
        .collect()
}

/// Член ядра, собранный из семейства и типов его конструкторов.
fn family_member(family: &Family<'_>, constructors: &[(&str, Term)]) -> SigMember {
    let parameters = u32::try_from(family.params.len()).unwrap_or(u32::MAX);
    constructors.iter().fold(
        SigMember::data(&family.data.name.text, parameters, family.kind.clone()),
        |member, (constructor, ty)| member.with_constructor(constructor, ty.clone()),
    )
}

fn declare_data(
    signature: &mut Signature,
    metas: &mut Metas,
    owned: &Owned,
    data: &ast::Data,
    span: Span,
) -> Result<(), ElabError> {
    let family = family_header(signature, metas, owned, data, span)?;
    let constructors = family_constructors(signature, metas, owned, &family, &[family.visible()])?;
    let parameters = u32::try_from(family.params.len()).unwrap_or(u32::MAX);
    signature
        .declare_data(
            metas,
            &data.name.text,
            parameters,
            family.kind.clone(),
            &constructors,
        )
        .map_err(|error| ElabError::Core {
            span: route::locate(&Declared::Data(data), &error, span),
            error: Box::new(error),
            names: family.names,
        })?;
    // Умолчания - **после** объявления: они обычные определения, и семейство
    // им доступно как всякое другое имя.
    declare_defaults(signature, metas, owned, &data.name.text, &data.params)
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
