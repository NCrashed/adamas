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
use crate::level::Level;
use crate::mult::Mult;
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
}

/// Синтезирует тип терма и считает использования.
///
/// # Errors
///
/// Любое нарушение типизации или учёта кратностей.
pub fn infer(ctx: &Ctx, sigma: Mult, term: &Term) -> Result<(Rc<Value>, Usage), TypeError> {
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
            let domain_level = is_type(ctx, domain)?;
            let inner = ctx.bind(Rc::clone(name), *mult, ctx.eval(domain));
            let codomain_level = is_type(&inner, codomain)?;
            Ok((
                Rc::new(Value::Universe(domain_level.max(codomain_level))),
                Usage::zero(ctx.size()),
            ))
        }

        Term::App(callee, argument) => {
            let (callee_ty, callee_usage) = infer(ctx, sigma, callee)?;
            let Value::Pi(mult, _, domain, codomain) = &*callee_ty else {
                return Err(TypeError::NotAFunction {
                    ty: ctx.quote(&callee_ty).to_string(),
                });
            };
            // Аргумент используется столько раз, сколько требует связывание.
            // При `q = 0` внутри аргумента ничего не расходуется - это и есть
            // "доказательства ничего не стоят".
            let argument_usage = check(ctx, *mult * sigma, argument, domain)?;
            let result = codomain.apply(ctx.eval(argument));
            Ok((result, callee_usage + &argument_usage))
        }

        Term::Let(mult, name, ty, value, body) => {
            binding(ctx, sigma, *mult, name, ty, value, |inner| {
                infer(inner, sigma, body)
            })
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
    ctx: &Ctx,
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
            let usage = check(&inner, sigma, body, &body_ty)?;
            let (used, rest) = usage.pop();
            spend(name, *mult * sigma, used)?;
            Ok(rest)
        }

        (Term::Lam(..), _) => Err(TypeError::NotAFunction {
            ty: ctx.quote(expected).to_string(),
        }),

        (Term::Let(mult, name, ty, value, body), _) => {
            let ((), usage) = binding(ctx, sigma, *mult, name, ty, value, |inner| {
                check(inner, sigma, body, expected).map(|usage| ((), usage))
            })?;
            Ok(usage)
        }

        _ => {
            let (found, usage) = infer(ctx, sigma, term)?;
            if convertible(ctx.size(), expected, &found) {
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
pub fn is_type(ctx: &Ctx, term: &Term) -> Result<Level, TypeError> {
    // Стёртый фрагмент: внутри типа ничто не расходуется, поэтому вектор
    // использований заведомо нулевой и отбрасывается.
    let (ty, _) = infer(ctx, Mult::Zero, term)?;
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
pub fn check_closed(term: &Term, ty: &Term) -> Result<(), TypeError> {
    let ctx = Ctx::default();
    is_type(&ctx, ty)?;
    let ty_value = ctx.eval(ty);
    check(&ctx, Mult::One, term, &ty_value)?;
    Ok(())
}

/// Синтезирует тип замкнутого терма и читает его обратно в терм.
///
/// # Errors
///
/// Если терм не типизируется.
pub fn infer_closed(term: &Term) -> Result<Term, TypeError> {
    let ctx = Ctx::default();
    let (ty, _) = infer(&ctx, Mult::One, term)?;
    Ok(ctx.quote(&ty))
}

/// Общая часть `let` для обоих режимов: проверить аннотацию и значение, ввести
/// связывание, обработать тело, снять и проверить использование.
fn binding<T>(
    ctx: &Ctx,
    sigma: Mult,
    mult: Mult,
    name: &Name,
    ty: &Term,
    value: &Term,
    body: impl FnOnce(&Ctx) -> Result<(T, Usage), TypeError>,
) -> Result<(T, Usage), TypeError> {
    is_type(ctx, ty)?;
    let ty_value = ctx.eval(ty);
    let allowed = mult * sigma;
    let value_usage = check(ctx, allowed, value, &ty_value)?;

    // Именно `define`, а не `bind`: значение известно, и тип тела не должен
    // оказаться зависящим от связывания, которого снаружи уже нет.
    let inner = ctx.define(Rc::clone(name), mult, ty_value, ctx.eval(value));
    let (result, body_usage) = body(&inner)?;

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
