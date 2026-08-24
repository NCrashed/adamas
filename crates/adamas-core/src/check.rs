//! Bidirectional-проверка типов с учётом использований QTT (§3.2, §9 Фаза 1).
//!
//! Два режима, как в warm-up'е: [`infer`] синтезирует тип, [`check`] сверяет
//! терм с уже известным. С зависимыми типами это не удобство, а необходимость -
//! у лямбды нет аннотации домена, синтезировать её тип не из чего.
//!
//! # Кратность суждения
//!
//! Каждая проверка идёт при кратности `σ` - сколько раз используется сам
//! проверяемый терм. Снаружи ядро вызывают при `σ = 1` (терм присутствует в
//! рантайме) или `σ = 0` (терм стёрт; в этом фрагменте живут **все типы** -
//! домен и кодомен `Pi`, аннотация `let`, проверяемый тип целиком).
//!
//! Правило переменной выдаёт использование `σ`, применение проверяет аргумент
//! при `q · σ`, где `q` - кратность связывания. Отсюда сразу два ключевых
//! свойства §3.3: аргумент под `0`-связыванием не стоит ничего в рантайме, а
//! стёртая переменная, использованная в рантайм-позиции, даёт `1` там, где
//! разрешён только `0`, и проверка падает.
//!
//! **Внутри рекурсии `σ` пробегает всё полукольцо, включая `ω`** - именно
//! потому, что масштабирование на `q` вплавлено в неё, а не применено к
//! вектору использований. У Аткея правило применения выглядит иначе: `σ`
//! ограничена `{0, 1}`, а вектор складывается как `Γ + q · Δ`. Формы
//! эквивалентны, потому что полукольцо коммутативно, а умножение дистрибутивно
//! над сложением: масштабировать результат обхода и обходить в масштабе - одно
//! и то же на каждом правиле. Вплавленная форма выбрана за то, что вектор
//! использований остаётся неизменяемым - его только складывают и снимают с
//! него верхний слой.
//!
//! Ошибки спанов не несут: термы ядра их не хранят. "Где" знает элаборатор
//! (Фаза 2) - он держит спан того, что элаборирует в момент отказа.

use std::rc::Rc;

use crate::conv::convertible;
use crate::ctx::{Ctx, Usage};
use crate::level::{Level, LevelMeta};
use crate::meta::{Metas, unsolved_level_meta};
use crate::mult::Mult;
use crate::sig::{Definition, Signature};
use crate::term::{Index, Name, Term};
use crate::value::Value;

/// Ошибка проверки типов.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum TypeError {
    /// Индекс не адресует ни одно связывание - терм незамкнут.
    #[error("переменная #{} вне контекста", index.0)]
    UnboundIndex {
        /// Сам индекс.
        index: Index,
    },

    /// В позиции типа оказался терм, тип которого не универсум.
    #[error("ожидался тип, получено `{term}` типа `{ty}`")]
    NotAType {
        /// Терм в позиции типа.
        term: String,
        /// Его тип.
        ty: String,
    },

    /// Применение чего-то, что не является функцией.
    #[error("ожидалась функция, получено значение типа `{ty}`")]
    NotAFunction {
        /// Тип того, что применяли.
        ty: String,
    },

    /// Тип не совпал с ожидаемым.
    #[error("несовпадение типов: ожидался `{expected}`, получен `{found}`")]
    Mismatch {
        /// Тип, которого требовал контекст.
        expected: String,
        /// Тип, который получился.
        found: String,
    },

    /// Кратность лямбды разошлась с кратностью `Pi`, под который её проверяют.
    #[error("кратность лямбды {found}, а тип требует {expected}")]
    LambdaMultiplicity {
        /// Кратность из типа.
        expected: Mult,
        /// Кратность, написанная на лямбде.
        found: Mult,
    },

    /// Переменная использована чаще, чем разрешает её кратность.
    #[error("`{name}` объявлена с кратностью {declared}, а использована {actual}")]
    UsageViolation {
        /// Имя связывания.
        name: Name,
        /// Разрешённая кратность (уже с учётом кратности суждения).
        declared: Mult,
        /// Фактическое использование.
        actual: Mult,
    },

    /// Тип терма нельзя синтезировать - нужна проверка против известного.
    #[error("тип `{term}` невозможно синтезировать, нужна аннотация")]
    CannotInfer {
        /// Проблемный терм.
        term: String,
    },

    /// Ссылка на определение, которого нет в сигнатуре.
    #[error("определение `{name}` не найдено")]
    UnknownConstant {
        /// Имя.
        name: Name,
    },

    /// Число аргументов уровня не совпало с арностью определения.
    #[error("`{name}` принимает {expected} параметров уровня, передано {found}")]
    LevelArity {
        /// Имя определения.
        name: Name,
        /// Объявленная арность.
        expected: u32,
        /// Сколько аргументов передано.
        found: u32,
    },

    /// Стёртое определение использовано в рантайм-позиции.
    #[error("`{name}` объявлено с кратностью 0 и недоступно в рантайме")]
    ErasedConstant {
        /// Имя определения.
        name: Name,
    },

    /// Имя уже занято.
    #[error("определение `{name}` уже существует")]
    DuplicateDefinition {
        /// Имя.
        name: Name,
    },

    /// Кратность `1` у определения верхнего уровня.
    #[error("определение `{name}` не может быть линейным: учёта на всю программу нет")]
    LinearDefinition {
        /// Имя.
        name: Name,
    },

    /// После проверки остался неразрешённый уровень.
    #[error("уровень ?{} не определён: добавьте аннотацию", meta.0)]
    AmbiguousLevel {
        /// Метапеременная, оставшаяся без решения.
        meta: crate::level::LevelMeta,
    },

    /// В определении, уходящем в сигнатуру, осталась дырка уровня.
    #[error("в определении `{name}` остался неразрешённый уровень ?{}", meta.0)]
    UnsolvedDefinitionLevel {
        /// Имя определения.
        name: Name,
        /// Метапеременная, оставшаяся без решения.
        meta: crate::level::LevelMeta,
    },

    /// Определение ссылается на параметр уровня, которого у него нет.
    #[error("`{name}` использует параметр уровня u{var} при арности {arity}")]
    LevelVarOutOfScope {
        /// Имя определения.
        name: Name,
        /// Индекс переменной.
        var: u32,
        /// Объявленная арность.
        arity: u32,
    },
}

/// Синтезирует тип терма и считает использования.
///
/// # Errors
///
/// Любое нарушение типизации или учёта кратностей.
pub fn infer(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    term: &Term,
) -> Result<(Rc<Value>, Usage), TypeError> {
    match term {
        Term::Var(index) => {
            let binding = ctx
                .lookup(*index)
                .ok_or(TypeError::UnboundIndex { index: *index })?;
            let level = index
                .to_level(ctx.size())
                .ok_or(TypeError::UnboundIndex { index: *index })?;
            Ok((
                Rc::clone(&binding.ty),
                Usage::single(ctx.size(), level, sigma),
            ))
        }

        // `Type n : Type (n+1)`. Предикативно (§3.2): импредикативный `Type`
        // дал бы парадокс Жирара.
        Term::Universe(level) => Ok((
            Rc::new(Value::Universe(level.clone().succ())),
            Usage::zero(ctx.size()),
        )),

        // `Pi` сам является типом, поэтому и домен, и кодомен проверяются в
        // стёртом фрагменте, а использований он не порождает вовсе.
        //
        // Уровень - `max`: предикативность (§3.2) в одну строку. Правило Lean
        // `imax` вернуло бы `Type 0`, когда там живёт кодомен, то есть сделало
        // бы нижний универсум импредикативным; см. заголовок
        // [`crate::level`], почему это несовместимо с §3.2.
        Term::Pi(mult, name, domain, codomain) => {
            let domain_level = is_type(ctx, metas, domain)?;
            let inner = ctx.bind(Rc::clone(name), *mult, ctx.eval(domain));
            let codomain_level = is_type(&inner, metas, codomain)?;
            Ok((
                Rc::new(Value::Universe(domain_level.max(codomain_level))),
                Usage::zero(ctx.size()),
            ))
        }

        Term::App(callee, argument) => {
            let (callee_ty, callee_usage) = infer(ctx, metas, sigma, callee)?;
            let Value::Pi(mult, _, domain, codomain) = &*callee_ty else {
                return Err(TypeError::NotAFunction {
                    ty: ctx.quote(&callee_ty).to_string(),
                });
            };
            // Аргумент используется столько раз, сколько требует связывание.
            // При `q = 0` внутри аргумента ничего не расходуется - это и есть
            // "доказательства ничего не стоят".
            let argument_usage = check(ctx, metas, *mult * sigma, argument, domain)?;
            let result = codomain.apply(ctx.eval(argument));
            Ok((result, callee_usage + &argument_usage))
        }

        Term::Let(mult, name, ty, value, body) => {
            let described = LetBinding {
                mult: *mult,
                name,
                ty,
                value,
            };
            binding(ctx, metas, sigma, described, |inner, metas| {
                infer(inner, metas, sigma, body)
            })
        }

        // Определение не занимает места в контексте, поэтому вектор
        // использований нулевой. Ограничение на кратность при этом есть, но
        // проверяется локально: `0`-определение (доказательство, тип) в
        // рантайм-позиции - ошибка.
        Term::Const(name, levels) => {
            let definition =
                ctx.signature()
                    .lookup(name)
                    .ok_or_else(|| TypeError::UnknownConstant {
                        name: Rc::clone(name),
                    })?;
            // Насыщение здесь дало бы несовпадение арности, то есть ошибку, а
            // не тихо неверный результат. Но правило одно на весь крейт:
            // счётчик, не помещающийся в u32, - поломка, а не вход.
            let found = u32::try_from(levels.len())
                .unwrap_or_else(|_| unreachable!("аргументов уровня больше, чем помещается в u32"));
            if found != definition.level_arity {
                return Err(TypeError::LevelArity {
                    name: Rc::clone(name),
                    expected: definition.level_arity,
                    found,
                });
            }
            if !definition.mult.admits(sigma) {
                return Err(TypeError::ErasedConstant {
                    name: Rc::clone(name),
                });
            }
            Ok((definition.instantiate_type(levels), Usage::zero(ctx.size())))
        }

        // Домена у лямбды в терме нет, синтезировать не из чего.
        Term::Lam(..) => Err(TypeError::CannotInfer {
            term: term.to_string(),
        }),
    }
}

/// Сверяет терм с известным типом и считает использования.
///
/// # Errors
///
/// Любое нарушение типизации или учёта кратностей.
pub fn check(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    term: &Term,
    expected: &Rc<Value>,
) -> Result<Usage, TypeError> {
    match (term, &**expected) {
        (Term::Lam(mult, name, body), Value::Pi(pi_mult, _, domain, codomain)) => {
            // Кратность лямбды обязана совпасть с кратностью типа. Проверка
            // конвертируемости её сознательно игнорирует (иначе ломается
            // транзитивность через η), поэтому единственное место, где
            // аннотация на лямбде что-то значит, - здесь.
            if mult != pi_mult {
                return Err(TypeError::LambdaMultiplicity {
                    expected: *pi_mult,
                    found: *mult,
                });
            }
            let inner = ctx.bind(Rc::clone(name), *mult, Rc::clone(domain));
            let body_ty = codomain.apply(ctx.fresh());
            let usage = check(&inner, metas, sigma, body, &body_ty)?;
            let (used, rest) = usage.pop();
            spend(name, *mult * sigma, used)?;
            Ok(rest)
        }

        (Term::Lam(..), _) => Err(TypeError::NotAFunction {
            ty: ctx.quote(expected).to_string(),
        }),

        (Term::Let(mult, name, ty, value, body), _) => {
            let described = LetBinding {
                mult: *mult,
                name,
                ty,
                value,
            };
            let ((), usage) = binding(ctx, metas, sigma, described, |inner, metas| {
                check(inner, metas, sigma, body, expected).map(|usage| ((), usage))
            })?;
            Ok(usage)
        }

        _ => {
            let (found, usage) = infer(ctx, metas, sigma, term)?;
            if convertible(ctx.signature(), metas, ctx.size(), expected, &found) {
                Ok(usage)
            } else {
                Err(TypeError::Mismatch {
                    expected: ctx.quote(expected).to_string(),
                    found: ctx.quote(&found).to_string(),
                })
            }
        }
    }
}

/// Проверяет, что терм - тип, и возвращает уровень его универсума.
///
/// # Errors
///
/// Если терм не типизируется или его тип не универсум.
pub fn is_type(ctx: &Ctx<'_>, metas: &mut Metas, term: &Term) -> Result<Level, TypeError> {
    // Стёртый фрагмент: внутри типа ничто не расходуется, поэтому вектор
    // использований заведомо нулевой и отбрасывается.
    let (ty, _) = infer(ctx, metas, Mult::Zero, term)?;
    match &*ty {
        Value::Universe(level) => Ok(level.clone()),
        _ => Err(TypeError::NotAType {
            term: term.to_string(),
            ty: ctx.quote(&ty).to_string(),
        }),
    }
}

/// Проверяет замкнутый терм против замкнутого типа.
///
/// Терм считается присутствующим в рантайме, то есть проверяется при
/// кратности `1`.
///
/// # Errors
///
/// Если тип не является типом или терм ему не соответствует.
pub fn check_closed(signature: &Signature, term: &Term, ty: &Term) -> Result<(), TypeError> {
    let mut metas = Metas::default();
    check_closed_with(signature, &mut metas, term, ty)
}

/// То же, но с внешним хранилищем метапеременных - когда терм построен через
/// [`Signature::instantiate`] и содержит дырки в аргументах уровня.
///
/// # Errors
///
/// То же, что у [`check_closed`], плюс нерешённая метапеременная уровня.
pub fn check_closed_with(
    signature: &Signature,
    metas: &mut Metas,
    term: &Term,
    ty: &Term,
) -> Result<(), TypeError> {
    let ctx = Ctx::new(signature);
    is_type(&ctx, metas, ty)?;
    let ty_value = ctx.eval(ty);
    check(&ctx, metas, Mult::One, term, &ty_value)?;
    no_unsolved_levels(metas, term)
}

/// Синтезирует тип замкнутого терма и читает его обратно в терм.
///
/// # Errors
///
/// Если терм не типизируется.
pub fn infer_closed(signature: &Signature, term: &Term) -> Result<Term, TypeError> {
    let mut metas = Metas::default();
    infer_closed_with(signature, &mut metas, term)
}

/// То же, но с внешним хранилищем метапеременных. Результат зонкается: в
/// возвращённом типе решённые дырки уже заменены решениями.
///
/// **Нерешённые дырки не отвергаются**, в отличие от [`check_closed_with`]. Это
/// не послабление, а разные вопросы: проверка обязана закончиться без дырок,
/// потому что её ответ - "терм годится", а синтез отвечает "вот тип", и у
/// полиморфного терма этот тип законно содержит `?N`. Синтезировать тип
/// `Id{?l}`, ничем её не ограничив, - осмысленный запрос, а не ошибка.
///
/// # Errors
///
/// То же, что у [`infer_closed`].
pub fn infer_closed_with(
    signature: &Signature,
    metas: &mut Metas,
    term: &Term,
) -> Result<Term, TypeError> {
    let ctx = Ctx::new(signature);
    let (ty, _) = infer(&ctx, metas, Mult::One, term)?;
    Ok(crate::meta::zonk_term(metas, &ctx.quote(&ty)))
}

/// Отвергает терм, в котором после проверки остались нерешённые уровни.
fn no_unsolved_levels(metas: &Metas, term: &Term) -> Result<(), TypeError> {
    match unsolved_level_meta(metas, term) {
        Some(meta) => Err(TypeError::AmbiguousLevel { meta }),
        None => Ok(()),
    }
}

/// Первая дырка, оставшаяся в определении после проверки.
///
/// Дырка в том, что сохраняется навсегда, - это тип, зависящий от хранилища,
/// которого уже нет: определение подхватывало бы значение метапеременной из
/// любой следующей проверки, то есть жило бы сразу во всех универсумах.
/// `check_level_scope` этого не ловит - он смотрит параметры уровня, а
/// метапеременная не параметр.
#[must_use]
pub fn unsolved_in_definition(metas: &Metas, definition: &Definition) -> Option<LevelMeta> {
    unsolved_level_meta(metas, &definition.ty).or_else(|| {
        definition
            .body
            .as_ref()
            .and_then(|body| unsolved_level_meta(metas, body))
    })
}

/// Проверяет определение верхнего уровня перед добавлением в сигнатуру.
///
/// Тип проверяется в стёртом фрагменте (он и есть тип), тело - при кратности
/// самого определения. Для `0`-определения это означает `σ = 0`: доказательство
/// проверяется, но ничего не расходует.
///
/// # Errors
///
/// Линейная кратность; параметр уровня вне арности; тип не является типом;
/// тело не соответствует типу.
pub fn check_definition(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    definition: &Definition,
) -> Result<(), TypeError> {
    let Definition {
        mult,
        level_arity,
        ty,
        body,
    } = definition;
    let (mult, level_arity) = (*mult, *level_arity);

    if mult == Mult::One {
        return Err(TypeError::LinearDefinition {
            name: Rc::clone(name),
        });
    }
    check_level_scope(name, level_arity, ty)?;
    if let Some(body) = body {
        check_level_scope(name, level_arity, body)?;
    }

    let ctx = Ctx::new(signature);
    is_type(&ctx, metas, ty)?;
    if let Some(body) = body {
        let ty_value = ctx.eval(ty);
        // `0`-определение проверяется при σ = 0, `ω` - при σ = 1: тело
        // присутствует в рантайме один раз, а сколько раз его позовут,
        // определение не решает.
        let sigma = if mult == Mult::Zero {
            Mult::Zero
        } else {
            Mult::One
        };
        check(&ctx, metas, sigma, body, &ty_value)?;
    }

    // Остаточные дырки здесь не проверяются: что с ними делать, решает
    // вызывающий. `Signature::define` их отвергает, `define_inferred`
    // обобщает в параметры.
    Ok(())
}

fn check_level_scope(name: &Name, arity: u32, term: &Term) -> Result<(), TypeError> {
    match term.max_level_var() {
        Some(var) if var >= arity => Err(TypeError::LevelVarOutOfScope {
            name: Rc::clone(name),
            var,
            arity,
        }),
        _ => Ok(()),
    }
}

/// Связывание `let` одним аргументом - иначе у [`binding`] их восемь.
struct LetBinding<'a> {
    mult: Mult,
    name: &'a Name,
    ty: &'a Term,
    value: &'a Term,
}

/// Общая часть `let` для обоих режимов: проверить аннотацию и значение, ввести
/// связывание, обработать тело, снять и проверить использование.
fn binding<T>(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    LetBinding {
        mult,
        name,
        ty,
        value,
    }: LetBinding<'_>,
    body: impl FnOnce(&Ctx<'_>, &mut Metas) -> Result<(T, Usage), TypeError>,
) -> Result<(T, Usage), TypeError> {
    is_type(ctx, metas, ty)?;
    let ty_value = ctx.eval(ty);
    let allowed = mult * sigma;
    let value_usage = check(ctx, metas, allowed, value, &ty_value)?;

    // Именно `define`, а не `bind`: значение известно, и тип тела не должен
    // оказаться зависящим от связывания, которого снаружи уже нет.
    let inner = ctx.define(Rc::clone(name), mult, ty_value, ctx.eval(value));
    let (result, body_usage) = body(&inner, metas)?;

    let (used, rest) = body_usage.pop();
    spend(name, allowed, used)?;
    Ok((result, value_usage + &rest))
}

/// Проверяет, что фактическое использование укладывается в разрешённое.
fn spend(name: &Name, allowed: Mult, actual: Mult) -> Result<(), TypeError> {
    if allowed.admits(actual) {
        Ok(())
    } else {
        Err(TypeError::UsageViolation {
            name: Rc::clone(name),
            declared: allowed,
            actual,
        })
    }
}
