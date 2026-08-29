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
//! при `σ` и умножает **его вектор использований** на кратность связывания:
//! `Γ + q · Δ`, правило Аткея дословно. Отсюда сразу два ключевых свойства
//! §3.3: аргумент под `0`-связыванием не стоит ничего в рантайме, а стёртая
//! переменная, использованная в рантайм-позиции, даёт `1` там, где разрешён
//! только `0`, и проверка падает.
//!
//! **`σ` не покидает `{0, 1}`.** Масштабирование применяется к вектору, а не
//! вплавлено в кратность суждения, и это не вопрос вкуса. Вплавленная форма
//! (`σ' = q · σ`) выглядит эквивалентной - полукольцо коммутативно, умножение
//! дистрибутивно над сложением, - но эквивалентность держится только на
//! сложении. Сравнение использования с разрешённым (`Mult::admits`) не
//! аддитивно: `1 · ω = ω`, а `ω` допускает что угодно. Поэтому под `σ = ω`
//! проверка линейности выключалась для всех связываний внутри терма, а `σ = ω`
//! получалась из самой обычной записи - аргумент функции по умолчанию имеет
//! кратность `ω` (§4.1). `\(1 x) -> f x x` отвергалось напрямую и принималось в
//! позиции аргумента, то есть тип `(1 x : A) -> B` населялся нелинейной
//! функцией.
//!
//! Ценой стала изменяемость вектора: `Γ + q · Δ` его масштабирует, тогда как
//! вплавленная форма только складывала и снимала верхний слой.
//!
//! # Что несёт ошибка
//!
//! Значения, а не готовую строку (§10 вопрос 49а): собственные [`Term`],
//! полученные обратным чтением и зонканные **в точке возбуждения** ([`read_back`],
//! [`zonked`]). Строка остаётся там, где данные и есть строка, - в именах
//! определений. Рендеринг живёт вне ядра; здесь - аварийный принтер на индексах
//! де Брёйна ([`Term`] реализует `Display`), нужный снапшотам уровня ядра.
//!
//! Спанов у ошибки нет и не будет: термы ядра их не хранят, а идентичность узла
//! не переживает нормализацию. «Где» доносят **телескоп** точки отказа и
//! **маршрут** кадрами, укладываемыми на раскрутке; форма их - в
//! [`crate::error`], а перевод маршрута в спан - работа элаборации
//! (§10 вопрос 49б).

use std::collections::HashSet;
use std::rc::Rc;

use crate::conv::{convertible, whnf};
use crate::ctx::{Ctx, Usage};
use crate::error::refuse;
pub use crate::error::{Binding, ErrorKind, Frame, TypeError};
use crate::eval::{apply, quote};
use crate::level::{Level, LevelMeta, LevelVar};
use crate::meta::{Metas, unsolved_level_meta, unsolved_term_meta};
use crate::mult::Mult;
use crate::row::Row;
use crate::sig::{Definition, DefinitionKind, Signature};
use crate::term::{Binder, Case, Name, Term, spine};
use crate::value::{Elim, Head, Lvl, Value};

/// Значение, уложенное в ошибку: обратное чтение плюс зонканье.
///
/// **Терм, а не строка** (§10 вопрос 49а): готовое сообщение уничтожает
/// структуру до того, как кто-либо решил, как её показывать, а рендеринг живёт
/// вне ядра. **И не значение:** `Value` тащит замыкания с окружениями, не
/// сравнивается и не переживает границу, тогда как `Term` - `'static`.
///
/// **Зонканье обязательно, а не желательно.** [`quote`] уровни нормализует, но
/// решений не подставляет; под схемой хранилища §10 вопроса 51 незонкнутая
/// дырка в сохранённой ошибке протухает вместе с `base`, и обращение к ней -
/// паника. Плюс читаемость: решённая метапеременная выглядела бы как `?0`, то
/// есть «уровень не выведен» там, где выведен, а разошлось совсем другое.
///
/// Цена обратного чтения на пути отказа не считается: отказ редок, и §10
/// вопрос 52 записан ровно про ту границу, за которой это перестанет быть
/// верным.
fn read_back(ctx: &Ctx<'_>, metas: &Metas, value: &Rc<Value>) -> Term {
    crate::meta::zonk_term(metas, &ctx.quote(value))
}

/// То же для терма, который в ошибку кладётся как есть.
fn zonked(metas: &Metas, term: &Term) -> Term {
    crate::meta::zonk_term(metas, term)
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
        // Дырка знает свой тип с рождения: его строит тот, кто её завёл, и
        // хранит хранилище. Использований она не порождает - она замкнута, а
        // зависимость от контекста выражают применения вокруг неё, и их
        // кратности приходят из её же типа.
        Term::Meta(meta) => Ok((Rc::clone(metas.term_type(*meta)), Usage::zero(ctx.size()))),

        Term::Var(index) => {
            let binding = ctx
                .lookup(*index)
                .ok_or(ErrorKind::UnboundIndex { index: *index })?;
            let level = index
                .to_level(ctx.size())
                .ok_or(ErrorKind::UnboundIndex { index: *index })?;
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
        //
        // **Row не проверяется, и это долг, а не решение.** Чтобы сказать, что
        // `State Int` собрана верно, нужен формер метки, а объявление эффектов
        // - Фаза 4 (§3.4). Сегодня цены у долга нет: синтаксиса для row не
        // существует, и пустой её делает не соглашение, а отсутствие способа
        // написать иную. Правило приходит вместе с погашением.
        Term::Pi(Binder { mult, .. }, name, domain, _, codomain) => {
            let domain_level = framed(is_type(ctx, metas, domain), Frame::Domain)?;
            let inner = ctx.bind(Rc::clone(name), *mult, ctx.eval(domain));
            let codomain_level = framed(is_type(&inner, metas, codomain), Frame::Codomain)?;
            Ok((
                Rc::new(Value::Universe(domain_level.max(codomain_level))),
                Usage::zero(ctx.size()),
            ))
        }

        Term::App(callee, argument) => infer_app(ctx, metas, sigma, callee, argument),

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
                    .ok_or_else(|| ErrorKind::UnknownConstant {
                        name: Rc::clone(name),
                    })?;
            // Насыщение здесь дало бы несовпадение арности, то есть ошибку, а
            // не тихо неверный результат. Но правило одно на весь крейт:
            // счётчик, не помещающийся в u32, - поломка, а не вход.
            let found = u32::try_from(levels.len())
                .unwrap_or_else(|_| unreachable!("аргументов уровня больше, чем помещается в u32"));
            if found != definition.level_arity {
                return Err(refuse(
                    ctx,
                    metas,
                    ErrorKind::LevelArity {
                        name: Rc::clone(name),
                        expected: definition.level_arity,
                        found,
                    },
                ));
            }
            if !definition.mult.admits(sigma) {
                return Err(refuse(
                    ctx,
                    metas,
                    ErrorKind::ErasedConstant {
                        name: Rc::clone(name),
                    },
                ));
            }
            // Зеркальное ограничение: стёртая функция доступна **только** при
            // σ = 0, нетотальная - только при σ ≠ 0. §4.7: доказательством
            // нетотальная функция быть не может, а тип - тот же фрагмент.
            if !crate::total::admits(definition, sigma) {
                return Err(refuse(
                    ctx,
                    metas,
                    ErrorKind::PartialConstant {
                        name: Rc::clone(name),
                    },
                ));
            }
            Ok((definition.instantiate_type(levels), Usage::zero(ctx.size())))
        }

        // Мотив записан в самом разборе, поэтому тип синтезируется, а не
        // берётся из режима проверки.
        Term::Case(case) => infer_case(ctx, metas, sigma, case),

        // Домена у лямбды в терме нет, синтезировать не из чего.
        Term::Lam(..) => Err(refuse(
            ctx,
            metas,
            ErrorKind::CannotInfer {
                term: zonked(metas, term),
            },
        )),
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
        // Лямбду проверяют против **развёрнутого** типа: `def Fn = Nat -> Nat`
        // - тип функции, и `\x -> x : Fn` обязано проходить. Разворот стоит
        //   здесь, а не в начале `check`, чтобы не платить за него на каждом
        //   терме: форма ожидаемого типа значима только для лямбды.
        (Term::Lam(..), _) => {
            check_lambda(ctx, metas, sigma, term, &whnf(ctx.signature(), expected))
        }

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
                Err(refuse(
                    ctx,
                    metas,
                    ErrorKind::Mismatch {
                        expected: read_back(ctx, metas, expected),
                        found: read_back(ctx, metas, &found),
                    },
                ))
            }
        }
    }
}

/// Правило лямбды. Ожидаемый тип уже приведён к головной нормальной форме.
fn check_lambda(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    term: &Term,
    expected: &Rc<Value>,
) -> Result<Usage, TypeError> {
    let Term::Lam(mult, name, body) = term else {
        unreachable!("правило лямбды вызвано не на лямбде: {term}")
    };
    let Value::Pi(Binder { mult: pi_mult, .. }, _, domain, _, codomain) = &**expected else {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::NotAFunction {
                ty: read_back(ctx, metas, expected),
            },
        ));
    };
    // Кратность лямбды обязана совпасть с кратностью типа. Проверка
    // конвертируемости её сознательно игнорирует (иначе ломается
    // транзитивность через η), поэтому единственное место, где аннотация на
    // лямбде что-то значит, - здесь.
    if mult != pi_mult {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::LambdaMultiplicity {
                expected: *pi_mult,
                found: *mult,
            },
        ));
    }
    let inner = ctx.bind(Rc::clone(name), *mult, Rc::clone(domain));
    let body_ty = codomain.apply(ctx.fresh());
    let usage = framed(check(&inner, metas, sigma, body, &body_ty), Frame::Body)?;
    let (used, rest) = usage.pop();
    spend(name, *mult * sigma, used)?;
    Ok(rest)
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
    // Универсум ищут в развёрнутой голове: у `def Sort2 = Type 2` голова своя,
    // и без разворота `T : Sort2` не годилось бы как тип вовсе.
    let ty = whnf(ctx.signature(), &ty);
    match &*ty {
        Value::Universe(level) => Ok(level.clone()),
        _ => Err(refuse(
            ctx,
            metas,
            ErrorKind::NotAType {
                term: zonked(metas, term),
                ty: read_back(ctx, metas, &ty),
            },
        )),
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
/// **Область видимости параметров уровня здесь не проверяется**, в отличие от
/// [`check_declaration`]. Это не забытая проверка: `LevelVar` принадлежит
/// определению, а у отдельного терма нет ни имени, ни арности, относительно
/// которых «вне области видимости» было бы определено. Терм с `Level::Var`
/// проверяется как терм гипотетического определения достаточной арности, и
/// ответ консервативен - [`Level::equiv`] и `leq` трактуют переменную как
/// жёсткий атом при любой подстановке. Поэтому такой терм здесь проходит, а в
/// [`Signature::define`] с арностью `0` - нет, и это разные вопросы, а не
/// расхождение.
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
    framed(is_type(&ctx, metas, ty), Frame::Stated)?;
    let ty_value = ctx.eval(ty);
    check(&ctx, metas, Mult::One, term, &ty_value)?;
    no_unsolved(metas, term)
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

/// Отвергает терм, в котором после проверки остались нерешённые дырки.
///
/// Обоих сортов: и уровень, и терм, оставшиеся без решения, означают одно -
/// проверка закончилась, а ответа на вопрос «чем это было» так и нет.
fn no_unsolved(metas: &Metas, term: &Term) -> Result<(), TypeError> {
    if let Some(meta) = unsolved_term_meta(metas, term) {
        return Err(ErrorKind::AmbiguousTerm { meta }.into());
    }
    match unsolved_level_meta(metas, term) {
        Some(meta) => Err(ErrorKind::AmbiguousLevel { meta }.into()),
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

/// То же для дырок терма.
///
/// Отдельная функция, а не общая: сорта дают разные отказы, и склеить их
/// значило бы сообщить «дырка осталась», не сказав какая.
#[must_use]
pub fn unsolved_term_in_definition(
    metas: &Metas,
    definition: &Definition,
) -> Option<crate::term::TermMeta> {
    unsolved_term_meta(metas, &definition.ty).or_else(|| {
        definition
            .body
            .as_ref()
            .and_then(|body| unsolved_term_meta(metas, body))
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
        return Err(ErrorKind::LinearDefinition {
            name: Rc::clone(name),
        }
        .into());
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
        Some(var) if var >= arity => Err(ErrorKind::LevelVarOutOfScope {
            name: Rc::clone(name),
            var,
            arity,
        }
        .into()),
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
    framed(is_type(ctx, metas, ty), Frame::BindingType)?;
    let ty_value = ctx.eval(ty);
    let allowed = mult * sigma;
    // Как и у применения: значение проверяется при кратности суждения из
    // `{0, 1}`, а на `q` умножается вектор.
    let value_usage = framed(
        check(ctx, metas, judgement_under(mult, sigma), value, &ty_value),
        Frame::BindingValue,
    )?;

    // Именно `define`, а не `bind`: значение известно, и тип тела не должен
    // оказаться зависящим от связывания, которого снаружи уже нет.
    let inner = ctx.define(Rc::clone(name), mult, ty_value, ctx.eval(value));
    let (result, body_usage) = framed(body(&inner, metas), Frame::BindingBody)?;

    let (used, rest) = body_usage.pop();
    spend(name, allowed, used)?;
    Ok((result, value_usage.scale(allowed) + &rest))
}

/// Кратность суждения для подтерма, стоящего под связыванием кратности `q`.
///
/// Остаётся в `{0, 1}`: масштабирование на `q` - работа [`Usage::scale`], а не
/// этой величины. Разница видна только при `q = ω`, и она принципиальна.
/// `q · σ = ω` разрешало бы `spend` любое использование ([`Mult::admits`] у
/// `ω` - безусловное `true`), то есть выключало бы проверку линейности для
/// **всех** связываний внутри терма. Аргумент обычной функции - позиция по
/// умолчанию (§4.1: параметр без аннотации имеет кратность `ω`), поэтому
/// выключалась она практически везде: `\(1 x) -> f x x` отвергалось напрямую и
/// принималось в позиции аргумента.
///
/// Стёртое связывание - отдельный случай: `q = 0` уводит подтерм в стёртый
/// фрагмент целиком, и там `σ = 0` не ограничение, а разрешение пользоваться
/// стёртыми переменными.
fn judgement_under(q: Mult, sigma: Mult) -> Mult {
    if q == Mult::Zero { Mult::Zero } else { sigma }
}

/// Проверяет, что фактическое использование укладывается в разрешённое.
fn spend(name: &Name, allowed: Mult, actual: Mult) -> Result<(), TypeError> {
    if allowed.admits(actual) {
        Ok(())
    } else {
        Err(ErrorKind::UsageViolation {
            name: Rc::clone(name),
            declared: allowed,
            actual,
        }
        .into())
    }
}

// ------------------------------------------------------------ индуктивные типы

/// Одно связывание из телескопа `Pi` вместе с тем, что оно связывает.
struct Field {
    /// Кратность и видимость.
    binder: Binder,
    /// Имя - только для печати.
    name: Name,
    domain: Rc<Term>,
    /// Row той стрелки, что ввела это связывание. Хранится, потому что
    /// позитивность обязана смотреть и туда: без неё телескоп конструктора
    /// терял бы метки по дороге.
    row: Row<Term>,
}

/// Снимает цепочку `Pi`, возвращая связывания и итоговый терм.
fn peel_pis(term: &Term) -> (Vec<Field>, &Term) {
    let mut fields = Vec::new();
    let mut current = term;
    while let Term::Pi(binder, name, domain, row, codomain) = current {
        fields.push(Field {
            binder: *binder,
            name: Rc::clone(name),
            domain: Rc::clone(domain),
            row: row.clone(),
        });
        current = codomain;
    }
    (fields, current)
}

/// Упоминает ли имя хоть один аргумент метки.
fn mentioned_in_row(signature: &Signature, name: &Name, row: &Row<Term>) -> bool {
    row.labels()
        .iter()
        .flat_map(|label| &label.arguments)
        .any(|argument| mentions(signature, name, argument))
}

/// Встречается ли имя в терме.
fn mentions(signature: &Signature, name: &Name, term: &Term) -> bool {
    mentions_seen(signature, name, term, &mut HashSet::new())
}

/// То же, с памятью о уже развёрнутых телах.
///
/// Память нужна из-за рекурсии: тело `f` упоминает `f`, и без неё обход
/// разворачивал бы его бесконечно.
///
/// Имя из памяти **не вынимается** после обхода, и это не оптимизация, а
/// условие завершения за разумное время. Ответ на "упоминается ли `name`" от
/// пути не зависит: имя, дошедшее до конца обхода, вернуло `false` и вернёт
/// его при любом следующем вхождении, а `true` схлопывает весь обход
/// немедленно и второй раз не спрашивается. Стек пути вместо множества давал
/// бы `T(k) = 2·T(k-1)` на цепочке `def d_k = d_{k-1} -> d_{k-1}`: 25
/// определений-синонимов занимали 17 секунд.
fn mentions_seen<'a>(
    signature: &'a Signature,
    name: &Name,
    term: &'a Term,
    seen: &mut HashSet<&'a Name>,
) -> bool {
    let mut recur = |inner| mentions_seen(signature, name, inner, seen);
    match term {
        // Дырка имени не упоминает: она замкнута, а её тип живёт отдельно и
        // проверен там, где заведён.
        Term::Var(_) | Term::Universe(_) | Term::Meta(_) => false,
        // Через тело определения - тоже упоминание. Без этого позитивность
        // обходится в две строки: `def G : Type 0 = Bad -> Bad`, затем
        // `mk : G -> Bad`. Прямая запись отвергается, а эта прошла бы, хотя
        // после δ-разворота это тот же самый негативный конструктор.
        Term::Const(other, _) => {
            if other == name {
                return true;
            }
            if !seen.insert(other) {
                return false;
            }
            let Some(body) = signature
                .lookup(other)
                .and_then(|definition| definition.body.as_ref())
            else {
                return false;
            };
            mentions_seen(signature, name, body, seen)
        }
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        // Аргументы меток row - тоже упоминание. Сегодня row пуста у всякой
        // стрелки, но пропуск здесь был бы дырой в **позитивности**: метка
        // `{State Bad}` в домене конструктора спрятала бы `Bad` от проверки, и
        // заметить это было бы нечем.
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || recur(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(recur)
        }
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
/// Голова поля разворачивается, если сама по себе не прошла: `mentions` идёт
/// через тела определений, и без разворота проверка расходилась бы сама с
/// собой. `def Cont = Bool -> Tree` в поле отвергалась, а записанное буквально
/// `(Bool -> Tree)` принималось - при том что после δ это один и тот же тип, а
/// сообщение говорило про отрицательную позицию, которой в терме нет.
///
/// Разворачивается только **голова без аргументов**: применённый синоним
/// (`def F A = A -> Tree`, поле `F Bool`) потребовал бы β-редукции на термах, а
/// её в ядре нет - подстановку заменяет `NbE`, работающий на значениях. Отказ
/// в таком случае остаётся, и он в безопасную сторону.
fn positive_field(
    signature: &Signature,
    data: &Name,
    params: u32,
    depth: u32,
    term: &Term,
) -> bool {
    positive_seen(signature, data, params, depth, term, &mut HashSet::new())
}

fn positive_seen<'a>(
    signature: &'a Signature,
    data: &Name,
    params: u32,
    depth: u32,
    term: &'a Term,
    seen: &mut HashSet<&'a Name>,
) -> bool {
    match term {
        // Слева от стрелки тип не должен встречаться вовсе; справа - рекурсия.
        // Аргументы меток row - та же левая позиция: применение стрелки
        // предъявляет их так же, как домен.
        Term::Pi(_, _, domain, row, codomain) => {
            !mentions(signature, data, domain)
                && !mentioned_in_row(signature, data, row)
                && positive_seen(signature, data, params, depth + 1, codomain, seen)
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
                _ if !mentions(signature, data, other) => true,
                // Тип упомянут, но позиция ещё не разобрана: если голова -
                // определение, смотрим на то, чем она является.
                Term::Const(name, _) if arguments.is_empty() => {
                    let Some(body) = signature
                        .lookup(name)
                        .and_then(|definition| definition.body.as_ref())
                    else {
                        return false;
                    };
                    // Память о развёрнутых - против самоссылки в теле; та же
                    // причина и та же форма, что у `mentions_seen`.
                    seen.insert(name) && positive_seen(signature, data, params, depth, body, seen)
                }
                _ => false,
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
        return Err(ErrorKind::DataParameters {
            name: Rc::clone(name),
            expected: params,
            found,
        }
        .into());
    }
    match result {
        Term::Universe(sort) => Ok(sort.clone()),
        other => Err(ErrorKind::NotADataSort {
            name: Rc::clone(name),
            found: other.clone(),
        }
        .into()),
    }
}

/// Проверяет форму конструктора: телескоп параметров и результат.
///
/// Фаза B1 объявления группы (§10 вопрос 50). Здесь всё, для чего довольно
/// **типов** членов группы: параметры конструктор обязан повторить дословно, а
/// результатом обязан быть тот же тип, применённый к собственным параметрам.
/// Позитивность и укладка в универсум сюда не входят - им нужна закрытая
/// группа, см. [`check_constructor_content`].
///
/// `family` - объявление тип-формера. Оно передаётся, а не ищется по имени:
/// вызывает эту проверку только объявление группы, и семейство у него в руках.
///
/// Тип уже проверен обычной машинерией определений; здесь только то, что
/// отличает конструктор от постулата с похожим типом.
///
/// # Errors
///
/// Имя не индуктивный тип; конструктор не повторяет параметры; результат не
/// тот тип.
pub(crate) fn check_constructor_shape(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    data: &Name,
    family: &Definition,
    ty: &Term,
) -> Result<(), TypeError> {
    let Some((params, _)) = family.data_shape() else {
        return Err(ErrorKind::NotADataType {
            name: Rc::clone(data),
        }
        .into());
    };
    let arity = family.level_arity;
    let telescope = peel_pis(&family.ty).0;

    let (fields, result) = peel_pis(ty);
    let mismatched = |index: u32| ErrorKind::ConstructorParameter {
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
            if expected.binder.mult != field.binder.mult
                || !convertible(
                    signature,
                    metas,
                    ctx.size(),
                    &ctx.eval(&expected.domain),
                    &ctx.eval(&field.domain),
                )
            {
                return Err(mismatched(depth).into());
            }
        }
        ctx = ctx.bind(
            Rc::clone(&field.name),
            field.binder.mult,
            ctx.eval(&field.domain),
        );
    }

    // Результат - тот самый тип, инстанцированный собственными параметрами
    // уровня и своими же параметрами-термами: конструктор принадлежит всему
    // семейству, а не одному его срезу.
    //
    // Уровни сравниваются семантически, а не производным `==`: последний
    // структурен и годится только для `BTreeMap` (см. [`crate::level`]). До
    // этой точки нормализации не происходит - путь идёт по термам, а `zonk` не
    // нормализует, - поэтому обобщение штатно оставляет `max u0 u0` там, где
    // ожидается `u0`, и структурное сравнение отвергло бы корректное
    // объявление.
    let (head, arguments) = spine(result);
    let expected = identity_levels(arity);
    let addressed = match head {
        Term::Const(head_name, levels) => {
            head_name == data
                && levels.len() == expected.len()
                && levels
                    .iter()
                    .zip(expected.iter())
                    .all(|(found, wanted)| found.equiv(wanted))
        }
        _ => false,
    };
    if !addressed || !uniform_parameters(params, ctx.size(), &arguments) {
        return Err(ErrorKind::ConstructorResult {
            name: Rc::clone(name),
            data: Rc::clone(data),
            found: zonked(metas, result),
        }
        .into());
    }
    Ok(())
}

/// Проверяет содержимое конструктора: строгую позитивность и укладку полей в
/// универсум типа.
///
/// Фаза C объявления группы (§10 вопрос 50) - то, для чего нужна **закрытая**
/// группа. Позитивность живёт именно здесь, и это не косметика: она смотрит
/// сквозь определения (`def G = Bad -> Bad`, затем `mk : G -> Bad`), а
/// определение, тело которого ещё не проверено, она видит без тела - и тогда
/// **принимает** негативный конструктор вместо того, чтобы отвергнуть. У всех
/// прочих проверок ядра консервативность направлена в другую сторону, и ошибка
/// здесь означала бы принятую некорректную программу.
///
/// `family` - объявление тип-формера, как и у [`check_constructor_shape`].
///
/// # Errors
///
/// Нарушена строгая позитивность; поле живёт выше универсума самого типа.
pub(crate) fn check_constructor_content(
    signature: &Signature,
    metas: &mut Metas,
    name: &Name,
    data: &Name,
    family: &Definition,
    ty: &Term,
) -> Result<(), TypeError> {
    let Some((params, sort)) = family.data_shape() else {
        return Err(ErrorKind::NotADataType {
            name: Rc::clone(data),
        }
        .into());
    };

    let mut ctx = Ctx::new(signature);
    for (index, field) in peel_pis(ty).0.iter().enumerate() {
        let depth = u32::try_from(index).unwrap_or(u32::MAX);
        // Метка на собственной стрелке конструктора стоит там же, где домен:
        // применение предъявляет её аргументы так же. Проверяется она и на
        // параметрах - там правило то же, а исключать нечего.
        if mentioned_in_row(signature, data, &field.row) {
            return Err(ErrorKind::NotStrictlyPositive {
                name: Rc::clone(name),
                data: Rc::clone(data),
            }
            .into());
        }
        if depth >= params {
            if !positive_field(signature, data, params, depth, &field.domain) {
                return Err(ErrorKind::NotStrictlyPositive {
                    name: Rc::clone(name),
                    data: Rc::clone(data),
                }
                .into());
            }
            // Поле не может жить выше самого типа: иначе `Type ℓ` содержал бы
            // значение, построенное над `Type (ℓ+1)`, и предикативность (§3.2)
            // обходилась бы через data-декларацию. Параметры это правило не
            // ограничивает - они не хранятся в значении, а подставляются.
            let field_level = is_type(&ctx, metas, &field.domain)?;
            if !field_level.leq(sort) {
                return Err(ErrorKind::ConstructorUniverse {
                    name: Rc::clone(name),
                    field: metas.zonk(&field_level),
                    sort: metas.zonk(sort),
                }
                .into());
            }
        }
        ctx = ctx.bind(
            Rc::clone(&field.name),
            field.binder.mult,
            ctx.eval(&field.domain),
        );
    }
    Ok(())
}

// ------------------------------------------------------------------ элиминация

/// Синтезирует тип применения.
fn infer_app(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    sigma: Mult,
    callee: &Term,
    argument: &Term,
) -> Result<(Rc<Value>, Usage), TypeError> {
    let (callee_ty, callee_usage) = framed(infer(ctx, metas, sigma, callee), Frame::Callee)?;
    // Форму типа спрашивают у развёрнутой головы: `def Fn = Nat -> Nat` -
    // такой же тип функции, как записанная стрелка, и `f : Fn` обязана
    // применяться.
    let callee_ty = whnf(ctx.signature(), &callee_ty);
    let Value::Pi(Binder { mult, .. }, _, domain, _, codomain) = &*callee_ty else {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::NotAFunction {
                ty: read_back(ctx, metas, &callee_ty),
            },
        ));
    };
    // Правило Аткея `Γ + q · Δ`: аргумент проверяется при собственной кратности
    // суждения, а на `q` умножается его **вектор использований**. При `q = 0`
    // внутри аргумента ничего не расходуется - это и есть "доказательства
    // ничего не стоят".
    let argument_usage = framed(
        check(ctx, metas, judgement_under(*mult, sigma), argument, domain),
        Frame::Argument,
    )?;
    let result = codomain.apply(ctx.eval(argument));
    Ok((result, callee_usage + &argument_usage.scale(*mult)))
}

/// Синтезирует тип разбора по конструктору.
///
/// Мотив записан в самом узле, поэтому тип получается, а не берётся из режима
/// проверки: результат - `motive indices scrutinee`.
///
/// Кратности достаются правилу даром. Ветвь - функция от полей, поэтому её
/// проверяет обычное правило лямбды: оно же сверяет объявленные кратности
/// полей, а телескоп ветви построен при `q · r` (§3.3), поэтому поле
/// расходуется при `q · r · σ`. Ветви между собой соединяются
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
        .ok_or_else(|| ErrorKind::UnknownConstant {
            name: Rc::clone(&case.data),
        })?;
    let DefinitionKind::Data {
        constructors,
        params,
        ..
    } = &declaration.kind
    else {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::NotADataType {
                name: Rc::clone(&case.data),
            },
        ));
    };

    // Число параметров и аргументы уровня терм несёт сам, чтобы вычислитель
    // обходился без сигнатуры. Сверяются они здесь и только здесь.
    let params = *params;
    if params != case.params {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::CaseParameters {
                data: Rc::clone(&case.data),
                expected: params,
                found: case.params,
            },
        ));
    }
    let found = u32::try_from(case.levels.len())
        .unwrap_or_else(|_| unreachable!("аргументов уровня больше, чем помещается в u32"));
    if found != declaration.level_arity {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::LevelArity {
                name: Rc::clone(&case.data),
                expected: declaration.level_arity,
                found,
            },
        ));
    }

    // Разбор смотрит на значение, то есть тратит его хотя бы однажды. `0`
    // означала бы, что разбираемое стёрто, а ветвь при этом выбирается по
    // нему в рантайме, - стирание перестало бы быть стиранием.
    if case.consumed == Mult::Zero {
        return Err(refuse(
            ctx,
            metas,
            ErrorKind::ErasedScrutinee {
                data: Rc::clone(&case.data),
            },
        ));
    }

    let constructors = constructors.clone();
    let binders = peel_pis(&declaration.ty).0.len();
    let family = declaration.instantiate_type(&case.levels);

    // Тип разбираемого значения обязан быть этим семейством, применённым
    // полностью: параметры, потом индексы.
    let (scrutinee_ty, scrutinee_usage) =
        framed(infer(ctx, metas, sigma, &case.scrutinee), Frame::Scrutinee)?;
    let arguments = data_arguments(signature, metas, case, &scrutinee_ty)
        .filter(|arguments| arguments.len() == binders)
        .ok_or_else(|| ErrorKind::NotADataValue {
            data: Rc::clone(&case.data),
            ty: read_back(ctx, metas, &scrutinee_ty),
        })?;
    let (data_params, data_indices) = arguments.split_at(params as usize);

    let indexed = instantiate_telescope(family, data_params);
    let motive_ty = motive_type(ctx, metas, case, &indexed, data_params);
    let motive_usage = framed(
        check(ctx, metas, Mult::Zero, &case.motive, &motive_ty),
        Frame::Motive,
    )?;
    let motive = ctx.eval(&case.motive);

    branch_shape(case, &constructors)?;
    let mut branches = Usage::zero(ctx.size());
    for (index, branch) in case.branches.iter().enumerate() {
        let expected = branch_type(ctx, case, &branch.constructor, data_params, &motive);
        let usage = framed(
            check(ctx, metas, sigma, &branch.body, &expected),
            Frame::Branch(u32::try_from(index).unwrap_or(u32::MAX)),
        )?;
        branches = branches.join(&usage);
    }

    let result = data_indices
        .iter()
        .fold(motive, |value, index| apply(&value, Rc::clone(index)));
    let result = apply(&result, ctx.eval(&case.scrutinee));
    // То же, что у применения: вектор разбираемого масштабируется кратностью,
    // с которой его потребляют, а ветви соединяются **объединением** -
    // выполняется ровно одна.
    Ok((
        result,
        scrutinee_usage.scale(case.consumed) + &motive_usage + &branches,
    ))
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
    let reduced = whnf(signature, ty);
    let Value::Neutral(Head::Global(name, levels), spine) = &*reduced else {
        return None;
    };
    if *name != case.data || levels.len() != case.levels.len() {
        return None;
    }
    if !levels
        .iter()
        .zip(case.levels.iter())
        .all(|(actual, written)| metas.unify_levels(actual, written))
    {
        return None;
    }
    spine
        .iter()
        .map(|elim| match elim {
            Elim::App(argument) => Some(Rc::clone(argument)),
            Elim::Case(_) => None,
        })
        .collect()
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
    let result = std::iter::once((Binder::explicit(Mult::Zero), Name::from("x"), scrutinee_ty))
        .chain(telescope.into_iter().rev())
        .fold(
            Term::Universe(metas.fresh_level()),
            |codomain, (_, name, domain)| {
                // Мотив связывает всё стёртым и явным: он тип, а не функция,
                // которую пишут в месте вызова.
                Term::Pi(
                    Binder::explicit(Mult::Zero),
                    name,
                    Rc::new(domain),
                    Row::empty(),
                    Rc::new(codomain),
                )
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

    // Поле кратности `q` приходит в ветвь при `q · r` (§3.3): цифра
    // конструктора описывает построение - положить аргумент однажды, - а при
    // разборе она обязана следовать тому, сколько раз доступно само
    // разбираемое. Умножение полукольца даёт три случая даром: `0 · r = 0`,
    // `ω · 1 = ω` (на чём стоит `Ur`), `1 · 1 = 1`.
    let result = telescope
        .into_iter()
        .rev()
        .fold(result, |codomain, (binder, name, domain)| {
            Term::Pi(
                Binder {
                    mult: binder.mult * case.consumed,
                    ..binder
                },
                name,
                Rc::new(domain),
                // Тип ветви строится из телескопа конструктора, а он чист:
                // конструктор не вычисляет, он кладёт.
                Row::empty(),
                Rc::new(codomain),
            )
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
            Value::Pi(_, _, _, _, codomain) => codomain.apply(Rc::clone(argument)),
            other => unreachable!("телескоп короче списка аргументов: {other}"),
        })
}

/// Снимает цепочку `Pi` со значения, возвращая связывания в виде термов и
/// размер контекста, в котором они записаны.
///
/// Домены читаются обратно по одному, каждый в своём контексте: `quote` до
/// увеличения размера, потому что домен живёт снаружи собственного связывания.
fn telescope_of(size: u32, value: &Rc<Value>) -> (Vec<(Binder, Name, Term)>, u32) {
    let mut telescope = Vec::new();
    let mut current = Rc::clone(value);
    let mut size = size;
    while let Value::Pi(binder, name, domain, _, codomain) = &*current {
        telescope.push((*binder, Rc::clone(name), quote(size, domain)));
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
        let Value::Pi(_, _, _, _, codomain) = &*current else {
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
            return Err(ErrorKind::RedundantBranch {
                data: Rc::clone(&case.data),
                constructor: Rc::clone(&branch.constructor),
            }
            .into());
        }
    }
    for (index, constructor) in constructors.iter().enumerate() {
        match case.branches.get(index) {
            Some(branch) if branch.constructor == *constructor => {}
            Some(branch) => {
                return Err(ErrorKind::BranchOrder {
                    data: Rc::clone(&case.data),
                    expected: Rc::clone(constructor),
                    found: Rc::clone(&branch.constructor),
                }
                .into());
            }
            None => {
                return Err(ErrorKind::NonExhaustive {
                    data: Rc::clone(&case.data),
                    constructor: Rc::clone(constructor),
                }
                .into());
            }
        }
    }
    match case.branches.get(constructors.len()) {
        Some(extra) => Err(ErrorKind::RedundantBranch {
            data: Rc::clone(&case.data),
            constructor: Rc::clone(&extra.constructor),
        }
        .into()),
        None => Ok(()),
    }
}

/// Дописывает кадр к отказу, пришедшему из подтерма.
///
/// Кадр укладывается **на раскрутке**, в самой точке вызова: свою роль знает
/// только она, а на успешном пути это не стоит ничего. Пропуск здесь тихий -
/// маршрут просто окажется короче, - поэтому его ловит свойство
/// `a_route_leads_to_the_named_subterm`, а не глаз.
fn framed<T>(outcome: Result<T, TypeError>, frame: Frame) -> Result<T, TypeError> {
    outcome.map_err(|error| error.in_frame(frame))
}
