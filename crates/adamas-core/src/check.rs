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
use crate::eval::{apply, quote};
use crate::level::{Level, LevelMeta, LevelVar};
use crate::meta::{Metas, unsolved_level_meta};
use crate::mult::Mult;
use crate::sig::{Definition, DefinitionKind, Signature};
use crate::term::{Case, Index, Name, Term};
use crate::value::{Elim, Head, Lvl, Value};

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

    /// Нетотальное определение использовано в стёртом фрагменте.
    #[error("`{name}` не тотальна и не может стоять в типе или доказательстве")]
    PartialConstant {
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

    /// Тип-формер не заканчивается универсумом.
    #[error("`{name}` объявлен как индуктивный тип, но заканчивается на `{found}`")]
    NotADataSort {
        /// Имя типа.
        name: Name,
        /// Что оказалось на месте универсума.
        found: String,
    },

    /// Тип-формер объявлен с большим числом параметров, чем у него связываний.
    #[error("`{name}` объявлен с {expected} параметрами, а связываний всего {found}")]
    DataParameters {
        /// Имя типа.
        name: Name,
        /// Сколько параметров объявлено.
        expected: u32,
        /// Сколько связываний есть на самом деле.
        found: u32,
    },

    /// Конструктор объявлен для имени, которое не индуктивный тип.
    #[error("`{name}` не является индуктивным типом")]
    NotADataType {
        /// Имя.
        name: Name,
    },

    /// Конструктор не повторяет телескоп параметров своего типа.
    #[error(
        "конструктор `{name}` обязан начинаться с параметров `{data}`, но параметр #{index} не совпадает"
    )]
    ConstructorParameter {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
        /// Номер параметра, на котором разошлось.
        index: u32,
    },

    /// Конструктор возвращает не тот тип, которому объявлен.
    #[error("конструктор `{name}` обязан возвращать `{data}`, а возвращает `{found}`")]
    ConstructorResult {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
        /// Что оказалось результатом.
        found: String,
    },

    /// Нарушена строгая позитивность.
    #[error("конструктор `{name}` использует `{data}` в отрицательной позиции")]
    NotStrictlyPositive {
        /// Имя конструктора.
        name: Name,
        /// Имя типа.
        data: Name,
    },

    /// Поле конструктора живёт выше универсума самого типа.
    #[error("поле конструктора `{name}` живёт в `Type {field}`, а тип - в `Type {sort}`")]
    ConstructorUniverse {
        /// Имя конструктора.
        name: Name,
        /// Универсум поля.
        field: String,
        /// Универсум типа.
        sort: String,
    },

    /// Разбирается значение, тип которого не то индуктивное семейство.
    #[error("разбор `{data}`, но значение имеет тип `{ty}`")]
    NotADataValue {
        /// Имя типа из разбора.
        data: Name,
        /// Тип разбираемого значения.
        ty: String,
    },

    /// Число параметров в разборе разошлось с объявлением типа.
    #[error("разбор `{data}` объявляет {found} параметров, а у типа их {expected}")]
    CaseParameters {
        /// Имя типа.
        data: Name,
        /// Сколько параметров у типа.
        expected: u32,
        /// Сколько записано в разборе.
        found: u32,
    },

    /// Конструктор остался без ветви.
    #[error("разбор `{data}` не покрывает конструктор `{constructor}`")]
    NonExhaustive {
        /// Имя типа.
        data: Name,
        /// Непокрытый конструктор.
        constructor: Name,
    },

    /// Ветвь для того, чего разбирать не требуется.
    #[error("в разборе `{data}` лишняя ветвь `{constructor}`")]
    RedundantBranch {
        /// Имя типа.
        data: Name,
        /// Конструктор ветви.
        constructor: Name,
    },

    /// Ветви идут не в порядке объявления конструкторов.
    #[error(
        "ветви `{data}` обязаны идти в порядке объявления: ожидался `{expected}`, встречен `{found}`"
    )]
    BranchOrder {
        /// Имя типа.
        data: Name,
        /// Конструктор, ожидавшийся на этом месте.
        expected: Name,
        /// Конструктор, который там оказался.
        found: Name,
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
            // Зеркальное ограничение: стёртая функция доступна **только** при
            // σ = 0, нетотальная - только при σ ≠ 0. §4.7: доказательством
            // нетотальная функция быть не может, а тип - тот же фрагмент.
            if !crate::total::admits(definition, sigma) {
                return Err(TypeError::PartialConstant {
                    name: Rc::clone(name),
                });
            }
            Ok((definition.instantiate_type(levels), Usage::zero(ctx.size())))
        }

        // Мотив записан в самом разборе, поэтому тип синтезируется, а не
        // берётся из режима проверки.
        Term::Case(case) => infer_case(ctx, metas, sigma, case),

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

/// Проверяет объявление - всё, что можно проверить без тела.
///
/// Идёт против сигнатуры **без** собственного имени: тип, ссылающийся на
/// определяемое, цикличен (`f : f -> Nat`), и разрешать это незачем. Тело
/// проверяется отдельно ([`check_body`]) и уже с именем в сигнатуре - оттуда и
/// берётся рекурсия.
///
/// # Errors
///
/// Линейная кратность; параметр уровня вне арности; тип не является типом.
pub fn check_declaration(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    definition: &Definition,
) -> Result<(), TypeError> {
    if definition.mult == Mult::One {
        return Err(TypeError::LinearDefinition {
            name: Rc::clone(name),
        });
    }
    check_level_scope(name, definition.level_arity, &definition.ty)?;
    is_type(&Ctx::new(signature), metas, &definition.ty)?;
    Ok(())
}

/// Проверяет определение целиком - объявление и тело подряд.
///
/// Годится для **нерекурсивного** определения: тело проверяется против
/// переданной сигнатуры, а собственного имени в ней нет.
/// [`crate::sig::Signature::define`] этой обёрткой не пользуется - ему нужно
/// вставить объявление между двумя шагами.
///
/// # Errors
///
/// То же, что у [`check_declaration`] и [`check_body`].
pub fn check_definition(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    definition: &Definition,
) -> Result<(), TypeError> {
    check_declaration(signature, metas, name, definition)?;
    check_body(signature, metas, name, definition)
}

/// Проверяет тело определения против его типа.
///
/// Тело проверяется при кратности самого определения: для `0`-определения это
/// `σ = 0` - доказательство проверяется, но ничего не расходует.
///
/// Сигнатура здесь обязана **уже содержать** объявление, иначе рекурсивная
/// ссылка не найдёт себя.
///
/// # Errors
///
/// Параметр уровня вне арности; тело не соответствует типу.
pub fn check_body(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    definition: &Definition,
) -> Result<(), TypeError> {
    let Some(body) = &definition.body else {
        return Ok(());
    };
    check_level_scope(name, definition.level_arity, body)?;

    let ctx = Ctx::new(signature);
    let ty_value = ctx.eval(&definition.ty);
    // `0`-определение проверяется при σ = 0, `ω` - при σ = 1: тело
    // присутствует в рантайме один раз, а сколько раз его позовут, определение
    // не решает.
    let sigma = if definition.mult == Mult::Zero {
        Mult::Zero
    } else {
        Mult::One
    };
    check(&ctx, metas, sigma, body, &ty_value)?;

    // Остаточные дырки здесь не проверяются: что с ними делать, решает
    // вызывающий.
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

// ------------------------------------------------------------ индуктивные типы

/// Одно связывание из телескопа `Pi`.
struct Binder {
    mult: Mult,
    name: Name,
    domain: Rc<Term>,
}

/// Снимает цепочку `Pi`, возвращая связывания и итоговый терм.
fn peel_pis(term: &Term) -> (Vec<Binder>, &Term) {
    let mut fields = Vec::new();
    let mut current = term;
    while let Term::Pi(mult, name, domain, codomain) = current {
        fields.push(Binder {
            mult: *mult,
            name: Rc::clone(name),
            domain: Rc::clone(domain),
        });
        current = codomain;
    }
    (fields, current)
}

/// Разбирает применение на голову и аргументы.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut current = term;
    while let Term::App(callee, argument) = current {
        arguments.push(argument.as_ref());
        current = callee;
    }
    arguments.reverse();
    (current, arguments)
}

/// Встречается ли имя в терме.
fn mentions(signature: &Signature, name: &Name, term: &Term) -> bool {
    mentions_seen(signature, name, term, &mut Vec::new())
}

/// То же, с памятью о уже развёрнутых телах.
///
/// Память нужна из-за рекурсии: тело `f` упоминает `f`, и без неё обход
/// разворачивал бы его бесконечно. Взаимной рекурсии в сигнатуре не бывает
/// (ordered scoping, §4.8), так что список короткий - в нём копится цепочка
/// разных имён плюс не более одного повторения.
fn mentions_seen<'a>(
    signature: &'a Signature,
    name: &Name,
    term: &'a Term,
    seen: &mut Vec<&'a Name>,
) -> bool {
    let mut recur = |inner| mentions_seen(signature, name, inner, seen);
    match term {
        Term::Var(_) | Term::Universe(_) => false,
        // Через тело определения - тоже упоминание. Без этого позитивность
        // обходится в две строки: `def G : Type 0 = Bad -> Bad`, затем
        // `mk : G -> Bad`. Прямая запись отвергается, а эта прошла бы, хотя
        // после δ-разворота это тот же самый негативный конструктор.
        Term::Const(other, _) => {
            if other == name {
                return true;
            }
            if seen.contains(&other) {
                return false;
            }
            let Some(body) = signature
                .lookup(other)
                .and_then(|definition| definition.body.as_ref())
            else {
                return false;
            };
            seen.push(other);
            let found = mentions_seen(signature, name, body, seen);
            seen.pop();
            found
        }
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, codomain) => recur(domain) || recur(codomain),
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || recur(body),
        // Имя типа стоит в самом узле, а имена конструкторов - в ветвях:
        // упоминанием считается и то и другое, иначе разбор по `Bad` внутри
        // поля прошёл бы мимо позитивности.
        Term::Case(case) => {
            case.data == *name
                || recur(&case.scrutinee)
                || recur(&case.motive)
                || case
                    .branches
                    .iter()
                    .any(|branch| branch.constructor == *name || recur(&branch.body))
        }
    }
}

/// Стоят ли на первых `params` местах спины ровно параметры телескопа.
///
/// Параметр `i` связан `i`-м снаружи, поэтому там, где в области видимости
/// `depth` связываний, его индекс равен `depth - 1 - i`.
fn uniform_parameters(params: u32, depth: u32, arguments: &[&Term]) -> bool {
    u32::try_from(arguments.len()).is_ok_and(|given| given >= params)
        && (0..params).all(|parameter| {
            depth
                .checked_sub(parameter + 1)
                .is_some_and(|index| *arguments[parameter as usize] == Term::var(index))
        })
}

/// Строгая позитивность плюс единообразие параметров.
///
/// Тип встречается только справа от стрелок, только с аргументами, его не
/// упоминающими, и всегда применённый к своим параметрам в том же порядке.
///
/// Без позитивности объявляется `data Bad where mk : (Bad -> Bad) -> Bad`, из
/// которого строится незавершающийся терм без единой рекурсии в термах, и
/// вместе с ним - житель любого типа. Проверка синтаксическая и сознательно
/// консервативная: отвергает часть корректных объявлений, но не пропускает
/// некорректные.
///
/// Единообразие отделяет параметр от индекса: `List A` рекурсивно упоминает
/// себя с тем же `A`, и только поэтому `A` можно не хранить в значении и не
/// разбирать при элиминации. `data Nest A where n : Nest (Pair A A) -> Nest A`
/// параметр меняет, и здесь он отвергается.
fn positive_field(
    signature: &Signature,
    data: &Name,
    params: u32,
    depth: u32,
    term: &Term,
) -> bool {
    match term {
        // Слева от стрелки тип не должен встречаться вовсе; справа - рекурсия.
        Term::Pi(_, _, domain, codomain) => {
            !mentions(signature, data, domain)
                && positive_field(signature, data, params, depth + 1, codomain)
        }
        other => {
            let (head, arguments) = spine(other);
            match head {
                // Рекурсивное вхождение: аргументы обязаны быть свободны от
                // самого типа, иначе `D (D x)` протащило бы его в позицию,
                // которую проверка не контролирует.
                Term::Const(name, _) if name == data => {
                    uniform_parameters(params, depth, &arguments)
                        && arguments
                            .iter()
                            .all(|argument| !mentions(signature, data, argument))
                }
                _ => !mentions(signature, data, other),
            }
        }
    }
}

/// Тождественная инстанциация параметров уровня.
fn identity_levels(arity: u32) -> Rc<[Level]> {
    (0..arity)
        .map(|index| Level::Var(LevelVar(index)))
        .collect()
}

/// Проверяет тип-формер и возвращает универсум, в котором живёт тип.
///
/// # Errors
///
/// Связываний меньше, чем объявлено параметров; тип-формер не заканчивается
/// универсумом.
pub fn data_sort(name: &Name, params: u32, ty: &Term) -> Result<Level, TypeError> {
    let (fields, result) = peel_pis(ty);
    let found = u32::try_from(fields.len()).unwrap_or(u32::MAX);
    if found < params {
        return Err(TypeError::DataParameters {
            name: Rc::clone(name),
            expected: params,
            found,
        });
    }
    match result {
        Term::Universe(sort) => Ok(sort.clone()),
        other => Err(TypeError::NotADataSort {
            name: Rc::clone(name),
            found: other.to_string(),
        }),
    }
}

/// Проверяет конструктор: телескоп параметров, результат, позитивность,
/// укладку в универсум.
///
/// Тип уже проверен обычной машинерией определений; здесь только то, что
/// отличает конструктор от постулата с похожим типом.
///
/// # Errors
///
/// Имя не индуктивный тип; конструктор не повторяет параметры; результат не
/// тот тип; нарушена строгая позитивность; поле живёт выше универсума самого
/// типа.
pub fn check_constructor(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    data: &Name,
    ty: &Term,
) -> Result<(), TypeError> {
    let Some(declaration) = signature.lookup(data) else {
        return Err(TypeError::UnknownConstant {
            name: Rc::clone(data),
        });
    };
    let DefinitionKind::Data { sort, params, .. } = &declaration.kind else {
        return Err(TypeError::NotADataType {
            name: Rc::clone(data),
        });
    };
    let (params, sort, arity) = (*params, sort.clone(), declaration.level_arity);
    let telescope = peel_pis(&declaration.ty).0;

    let (fields, result) = peel_pis(ty);
    let mismatched = |index: u32| TypeError::ConstructorParameter {
        name: Rc::clone(name),
        data: Rc::clone(data),
        index,
    };

    let mut ctx = Ctx::new(signature);
    for (index, field) in fields.iter().enumerate() {
        let depth = u32::try_from(index).unwrap_or(u32::MAX);
        if depth < params {
            // Параметры конструктор обязан повторить: и по типу, и по
            // кратности. Иначе `List` в результате и `List` в объявлении - два
            // разных семейства, и элиминации не на что опереться.
            let expected = &telescope[index];
            if expected.mult != field.mult
                || !convertible(
                    signature,
                    metas,
                    ctx.size(),
                    &ctx.eval(&expected.domain),
                    &ctx.eval(&field.domain),
                )
            {
                return Err(mismatched(depth));
            }
        } else {
            if !positive_field(signature, data, params, depth, &field.domain) {
                return Err(TypeError::NotStrictlyPositive {
                    name: Rc::clone(name),
                    data: Rc::clone(data),
                });
            }
            // Поле не может жить выше самого типа: иначе `Type ℓ` содержал бы
            // значение, построенное над `Type (ℓ+1)`, и предикативность (§3.2)
            // обходилась бы через data-декларацию. Параметры это правило не
            // ограничивает - они не хранятся в значении, а подставляются.
            let field_level = is_type(&ctx, metas, &field.domain)?;
            if !field_level.leq(&sort) {
                return Err(TypeError::ConstructorUniverse {
                    name: Rc::clone(name),
                    field: field_level.to_string(),
                    sort: sort.to_string(),
                });
            }
        }
        ctx = ctx.bind(Rc::clone(&field.name), field.mult, ctx.eval(&field.domain));
    }

    // Результат - тот самый тип, инстанцированный собственными параметрами
    // уровня и своими же параметрами-термами: конструктор принадлежит всему
    // семейству, а не одному его срезу.
    let (head, arguments) = spine(result);
    let expected = identity_levels(arity);
    let addressed = match head {
        Term::Const(head_name, levels) => head_name == data && **levels == *expected,
        _ => false,
    };
    if !addressed || !uniform_parameters(params, ctx.size(), &arguments) {
        return Err(TypeError::ConstructorResult {
            name: Rc::clone(name),
            data: Rc::clone(data),
            found: result.to_string(),
        });
    }
    Ok(())
}

// ------------------------------------------------------------------ элиминация

/// Синтезирует тип разбора по конструктору.
///
/// Мотив записан в самом узле, поэтому тип получается, а не берётся из режима
/// проверки: результат - `motive indices scrutinee`.
///
/// Кратности достаются правилу даром. Ветвь - функция от полей, поэтому её
/// проверяет обычное правило лямбды: оно же сверяет объявленные кратности полей
/// и расходует каждое поле при `q · σ`. Ветви между собой соединяются
/// **объединением**, а не суммой: выполняется ровно одна.
fn infer_case(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    case: &Case,
) -> Result<(Rc<Value>, Usage), TypeError> {
    let signature = ctx.signature();
    let declaration = signature
        .lookup(&case.data)
        .ok_or_else(|| TypeError::UnknownConstant {
            name: Rc::clone(&case.data),
        })?;
    let DefinitionKind::Data {
        constructors,
        params,
        ..
    } = &declaration.kind
    else {
        return Err(TypeError::NotADataType {
            name: Rc::clone(&case.data),
        });
    };

    // Число параметров и аргументы уровня терм несёт сам, чтобы вычислитель
    // обходился без сигнатуры. Сверяются они здесь и только здесь.
    let params = *params;
    if params != case.params {
        return Err(TypeError::CaseParameters {
            data: Rc::clone(&case.data),
            expected: params,
            found: case.params,
        });
    }
    let found = u32::try_from(case.levels.len())
        .unwrap_or_else(|_| unreachable!("аргументов уровня больше, чем помещается в u32"));
    if found != declaration.level_arity {
        return Err(TypeError::LevelArity {
            name: Rc::clone(&case.data),
            expected: declaration.level_arity,
            found,
        });
    }

    let constructors = constructors.clone();
    let binders = peel_pis(&declaration.ty).0.len();
    let family = declaration.instantiate_type(&case.levels);

    // Тип разбираемого значения обязан быть этим семейством, применённым
    // полностью: параметры, потом индексы.
    let (scrutinee_ty, scrutinee_usage) = infer(ctx, metas, sigma, &case.scrutinee)?;
    let arguments = data_arguments(signature, metas, case, &scrutinee_ty)
        .filter(|arguments| arguments.len() == binders)
        .ok_or_else(|| TypeError::NotADataValue {
            data: Rc::clone(&case.data),
            ty: ctx.quote(&scrutinee_ty).to_string(),
        })?;
    let (data_params, data_indices) = arguments.split_at(params as usize);

    let indexed = instantiate_telescope(family, data_params);
    let motive_ty = motive_type(ctx, metas, case, &indexed, data_params);
    let motive_usage = check(ctx, metas, Mult::Zero, &case.motive, &motive_ty)?;
    let motive = ctx.eval(&case.motive);

    branch_shape(case, &constructors)?;
    let mut branches = Usage::zero(ctx.size());
    for branch in &case.branches {
        let expected = branch_type(ctx, case, &branch.constructor, data_params, &motive);
        let usage = check(ctx, metas, sigma, &branch.body, &expected)?;
        branches = branches.join(&usage);
    }

    let result = data_indices
        .iter()
        .fold(motive, |value, index| apply(&value, Rc::clone(index)));
    let result = apply(&result, ctx.eval(&case.scrutinee));
    Ok((result, scrutinee_usage + &motive_usage + &branches))
}

/// Аргументы, к которым применено индуктивное семейство в типе значения.
///
/// `None` - тип не то семейство. δ-разворот здесь обязателен: у
/// определения-синонима голова своя, и без разворота разбор по нему не прошёл
/// бы, хотя тип тот же самый.
fn data_arguments(
    signature: &Signature,
    metas: &mut Metas,
    case: &Case,
    ty: &Rc<Value>,
) -> Option<Vec<Rc<Value>>> {
    let mut current = Rc::clone(ty);
    loop {
        let applied = match &*current {
            Value::Neutral(Head::Global(name, levels), spine) if *name == case.data => {
                Some((Rc::clone(levels), spine.clone()))
            }
            _ => None,
        };
        if let Some((levels, spine)) = applied {
            if levels.len() != case.levels.len() {
                return None;
            }
            if !levels
                .iter()
                .zip(case.levels.iter())
                .all(|(actual, written)| metas.unify_levels(actual, written))
            {
                return None;
            }
            return spine
                .iter()
                .map(|elim| match elim {
                    Elim::App(argument) => Some(Rc::clone(argument)),
                    Elim::Case(_) => None,
                })
                .collect();
        }
        current = crate::conv::unfold(signature, &current)?;
    }
}

/// Тип мотива: `(0 i⃗ : I) -> (0 x : D levels params i⃗) -> Type ?ℓ`.
///
/// Всё в стёртом фрагменте: мотив - функция на типах, в рантайме его нет.
/// Универсум результата остаётся дыркой, которую решает проверка самого мотива:
/// большая элиминация (`case b of true => Nat; false => Bool`) живёт в том же
/// универсуме, что и её ветви, и заранее он неизвестен.
fn motive_type(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    case: &Case,
    family: &Rc<Value>,
    params: &[Rc<Value>],
) -> Rc<Value> {
    let (telescope, size) = telescope_of(ctx.size(), family);
    let mut scrutinee_ty = Term::Const(Rc::clone(&case.data), Rc::clone(&case.levels));
    for param in params {
        scrutinee_ty = Term::App(Rc::new(scrutinee_ty), Rc::new(quote(size, param)));
    }
    for level in ctx.size()..size {
        scrutinee_ty = Term::App(
            Rc::new(scrutinee_ty),
            Rc::new(Term::Var(Lvl(level).to_index(size))),
        );
    }

    // Складывается изнутри наружу: сперва само разбираемое значение, потом
    // индексы в обратном порядке, чтобы первым объявленным оказался внешний.
    let result = std::iter::once((Mult::Zero, Name::from("x"), scrutinee_ty))
        .chain(telescope.into_iter().rev())
        .fold(
            Term::Universe(metas.fresh_level()),
            |codomain, (_, name, domain)| {
                Term::Pi(Mult::Zero, name, Rc::new(domain), Rc::new(codomain))
            },
        );
    ctx.eval(&result)
}

/// Тип ветви: тип конструктора без параметров, у которого результат заменён на
/// `motive indices (c params fields)`.
///
/// Ветвь проверяется против него обычным правилом лямбды - оттуда берутся и
/// совпадение кратностей полей, и их расход, и η.
fn branch_type(
    ctx: &Ctx<'_>,
    case: &Case,
    constructor: &Name,
    params: &[Rc<Value>],
    motive: &Rc<Value>,
) -> Rc<Value> {
    let declaration = ctx
        .signature()
        .lookup(constructor)
        .unwrap_or_else(|| unreachable!("конструктор `{constructor}` пропал из сигнатуры"));
    let applied = instantiate_telescope(declaration.instantiate_type(&case.levels), params);
    let (telescope, size) = telescope_of(ctx.size(), &applied);

    // Хвост телескопа - `D levels params indices`, оттуда и берутся индексы,
    // выраженные через поля этой ветви.
    let tail = telescope_tail(ctx.size(), &applied);
    let Value::Neutral(_, spine) = &*tail else {
        unreachable!("конструктор `{constructor}` возвращает не индуктивный тип")
    };
    let mut result = quote(size, motive);
    for elim in spine.iter().skip(params.len()) {
        let Elim::App(index) = elim else {
            unreachable!("в результате конструктора `{constructor}` стоит разбор")
        };
        result = Term::App(Rc::new(result), Rc::new(quote(size, index)));
    }

    let mut built = Term::Const(Rc::clone(constructor), Rc::clone(&case.levels));
    for param in params {
        built = Term::App(Rc::new(built), Rc::new(quote(size, param)));
    }
    for level in ctx.size()..size {
        built = Term::App(
            Rc::new(built),
            Rc::new(Term::Var(Lvl(level).to_index(size))),
        );
    }
    result = Term::App(Rc::new(result), Rc::new(built));

    let result = telescope
        .into_iter()
        .rev()
        .fold(result, |codomain, (mult, name, domain)| {
            Term::Pi(mult, name, Rc::new(domain), Rc::new(codomain))
        });
    ctx.eval(&result)
}

/// Подставляет аргументы в телескоп `Pi`, снимая по одному связыванию.
///
/// Не то же, что применение: здесь на входе **тип** семейства или конструктора,
/// а не функция, и параметр подставляется в кодомен, а не в тело.
///
/// # Panics
///
/// Если аргументов больше, чем связываний. Internal invariant: число
/// параметров проверено против объявления.
pub(crate) fn instantiate_telescope(ty: Rc<Value>, arguments: &[Rc<Value>]) -> Rc<Value> {
    arguments
        .iter()
        .fold(ty, |current, argument| match &*current {
            Value::Pi(_, _, _, codomain) => codomain.apply(Rc::clone(argument)),
            other => unreachable!("телескоп короче списка аргументов: {other}"),
        })
}

/// Снимает цепочку `Pi` со значения, возвращая связывания в виде термов и
/// размер контекста, в котором они записаны.
///
/// Домены читаются обратно по одному, каждый в своём контексте: `quote` до
/// увеличения размера, потому что домен живёт снаружи собственного связывания.
fn telescope_of(size: u32, value: &Rc<Value>) -> (Vec<(Mult, Name, Term)>, u32) {
    let mut telescope = Vec::new();
    let mut current = Rc::clone(value);
    let mut size = size;
    while let Value::Pi(mult, name, domain, codomain) = &*current {
        telescope.push((*mult, Rc::clone(name), quote(size, domain)));
        let next = codomain.apply(Value::var(Lvl(size)));
        size += 1;
        current = next;
    }
    (telescope, size)
}

/// То, что остаётся от значения после снятия всех `Pi`.
fn telescope_tail(size: u32, value: &Rc<Value>) -> Rc<Value> {
    let mut current = Rc::clone(value);
    let mut size = size;
    loop {
        let Value::Pi(_, _, _, codomain) = &*current else {
            return current;
        };
        let next = codomain.apply(Value::var(Lvl(size)));
        size += 1;
        current = next;
    }
}

/// Ветви обязаны повторять конструкторы типа - все и в порядке объявления.
///
/// Порядок значим потому, что он объявлен значимым (§9): список конструкторов
/// задаёт порядок ветвей. Требовать его дешевле, чем сопоставлять по имени, и
/// инвариант "ветви параллельны конструкторам" держится сам.
fn branch_shape(case: &Case, constructors: &[Name]) -> Result<(), TypeError> {
    for branch in &case.branches {
        if !constructors.contains(&branch.constructor) {
            return Err(TypeError::RedundantBranch {
                data: Rc::clone(&case.data),
                constructor: Rc::clone(&branch.constructor),
            });
        }
    }
    for (index, constructor) in constructors.iter().enumerate() {
        match case.branches.get(index) {
            Some(branch) if branch.constructor == *constructor => {}
            Some(branch) => {
                return Err(TypeError::BranchOrder {
                    data: Rc::clone(&case.data),
                    expected: Rc::clone(constructor),
                    found: Rc::clone(&branch.constructor),
                });
            }
            None => {
                return Err(TypeError::NonExhaustive {
                    data: Rc::clone(&case.data),
                    constructor: Rc::clone(constructor),
                });
            }
        }
    }
    match case.branches.get(constructors.len()) {
        Some(extra) => Err(TypeError::RedundantBranch {
            data: Rc::clone(&case.data),
            constructor: Rc::clone(&extra.constructor),
        }),
        None => Ok(()),
    }
}
