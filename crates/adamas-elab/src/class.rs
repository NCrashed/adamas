//! Классы и их инстансы: реестр и разрешение (§3.5, §4.1).
//!
//! По §3.5 класс есть module type плюс режим разрешения, а инстанс - его
//! module value. Отсюда и реализация: класс объявляется типом записи,
//! параметризованным своими аргументами, инстанс - записью, а метод -
//! определением верхнего уровня, проецирующим словарь.
//!
//! # Разрешение отложено, и иначе нельзя
//!
//! Вставка имплиситов **энергичная** (§4.1): аргумент выводится там, где имя
//! встретилось. У словаря в этот момент неизвестен тип - `compare Zero Zero`
//! вставляет его раньше, чем аргументы решат `a := Nat`. Поэтому словарь
//! вставляется обычной дыркой, а поиском заполняется потом, когда проверка уже
//! всё решила. Тем же порядком считаются носители (§10 вопрос 76): сначала
//! проверка, потом фаза, читающая её результат.
//!
//! Отдельного списка обязательств при этом не нужно: дырка, дожившая до конца
//! проверки, - и есть обязательство, а класс ли у неё в типе, видно по нему
//! самому.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use adamas_core::eval::quote;
use adamas_core::meta::{Metas, unsolved_term_meta, zonk_term};
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::Term;
use adamas_core::value::Value;
use adamas_parser::ast::Symbol;

use crate::error::ElabError;

/// Объявленные классы и их инстансы.
///
/// Живёт рядом с сигнатурой, а не в ней: ядро о классах не знает и знать не
/// должно - для него словарь есть обычная запись, а метод обычная проекция.
#[derive(Debug, Default)]
pub struct Instances {
    /// Имена объявленных классов.
    classes: HashSet<Symbol>,
    /// Кандидаты: класс и голова аргумента - имя объявленного словаря.
    ///
    /// Голова, а не тип целиком: `instance Eqv (List a)` этим срезом не
    /// поддержан, поэтому ключ однозначен. Область видимости одна на прогон -
    /// импортов в языке ещё нет, и вопрос 48 (приоритет при импорте) пока не
    /// имеет предмета.
    candidates: HashMap<(Symbol, Symbol), Symbol>,
}

impl Instances {
    /// Объявлен ли класс с таким именем.
    #[must_use]
    pub fn is_class(&self, name: &str) -> bool {
        self.classes.contains(name)
    }

    /// Запоминает класс.
    pub fn declare(&mut self, name: &Symbol) {
        self.classes.insert(Rc::clone(name));
    }

    /// Запоминает инстанс. `false` - такой уже есть.
    pub fn add(&mut self, class: &Symbol, head: &Symbol, name: Symbol) -> bool {
        self.candidates
            .insert((Rc::clone(class), Rc::clone(head)), name)
            .is_none()
    }

    /// Кандидат для `class head`, если он один и есть.
    fn candidate(&self, class: &Symbol, head: &Symbol) -> Option<Symbol> {
        self.candidates
            .get(&(Rc::clone(class), Rc::clone(head)))
            .map(Rc::clone)
    }
}

/// Заполняет словари, оставшиеся дырками после проверки.
///
/// Дырка, чей тип есть применение класса, решается **поиском**: у неё нет
/// уравнения, которое бы её определило, и унификация здесь не при чём (§3.5).
/// Дырка с любым другим типом остаётся как была - о ней скажет объявление,
/// которому нерешённая дырка запрещена.
///
/// Проверка здесь нужна **до** поиска: тип словаря становится известен её
/// решениями, а не сам по себе. Зовётся она только если дырка вообще есть,
/// поэтому обычное определение за классы не платит.
///
/// # Errors
///
/// Инстанса для написанного типа нет.
pub fn resolve(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    term: &Term,
    ty: &Term,
    span: Span,
) -> Result<(), ElabError> {
    if unsolved_term_meta(metas, term).is_none() && unsolved_term_meta(metas, ty).is_none() {
        return Ok(());
    }
    // Дырка есть - значит нужна проверка: её решения и делают тип словаря
    // известным. Не сошлось - здесь молчим: об этом скажет объявление, где у
    // ошибки есть маршрут по терму.
    let _ =
        adamas_core::check::check_within(&adamas_core::ctx::Ctx::new(signature), metas, term, ty);
    // И тело, и тип: словарь стоит в обоих - `witnessed : Wit (eq Zero Zero)`
    // несёт его в написанном типе, а не в теле.
    settle(signature, metas, instances, ty, span)?;
    settle(signature, metas, instances, term, span)
}

/// Заполняет словари по уже проверенному терму.
fn settle(
    signature: &Signature,
    metas: &mut Metas,
    instances: &Instances,
    term: &Term,
    span: Span,
) -> Result<(), ElabError> {
    while let Some(meta) = unsolved_term_meta(metas, term) {
        // Тип дырки замкнут по построению, поэтому читается на нулевой
        // глубине; зонканье подставляет всё, что решила проверка.
        let ty = zonk_term(metas, &quote(0, metas.term_type(meta)));
        // Дырка не про класс - её сюда и не звали: решить её могла только
        // унификация, и о том, что не решила, скажет объявление.
        let Some((class, head)) = applied(goal_of(&ty)) else {
            return Ok(());
        };
        if !instances.is_class(&class) {
            return Ok(());
        }
        // Локальный словарь **раньше** глобального инстанса: он и есть тот,
        // о котором договорилась сигнатура, а искать инстанс для переменной
        // всё равно негде. Так пишется всякая полиморфная функция над
        // классом - `same : {Eqv a} => a -> a -> Bool`.
        if let Some(solution) = from_context(signature, metas, &ty) {
            metas.solve_term(meta, solution);
            continue;
        }
        let Some(head) = head else {
            return Err(ElabError::NoInstance {
                class,
                head: Rc::from("переменная"),
                span,
            });
        };
        let Some(name) = instances.candidate(&class, &head) else {
            return Err(ElabError::NoInstance { class, head, span });
        };
        let Some(dictionary) = signature.instantiate(&name, metas) else {
            return Ok(());
        };
        let value = adamas_core::eval::eval(&adamas_core::value::Env::default(), &dictionary);
        metas.solve_term(meta, value);
    }
    Ok(())
}

/// Цель дырки - то, чем оканчивается телескоп её типа.
fn goal_of(ty: &Term) -> &Term {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    current
}

/// Связывание контекста, чей тип и есть цель.
///
/// Тип дырки - телескоп по контексту, оканчивающийся целью, а сама дырка
/// применена к контексту целиком. Значит подходящее связывание - решение:
/// `\x0 … xn -> xk`, и применение к спайну выдаёт ровно его.
///
/// `Let` в телескопе обрывает поиск: определённое связывание в спайн дырки не
/// попадает (`fresh_term_over`), и числа лямбд по телескопу уже не посчитать.
/// Названная граница - словарь, объявленный `let`-ом, отсюда не виден.
fn from_context(signature: &Signature, metas: &mut Metas, ty: &Term) -> Option<Rc<Value>> {
    let mut ctx = adamas_core::ctx::Ctx::new(signature);
    let mut binders = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, name, domain, _, codomain) = current {
        let value = ctx.eval(domain);
        binders.push((binder.mult, Rc::clone(name), Rc::clone(&value)));
        ctx = ctx.bind(Rc::clone(name), binder.mult, value);
        current = codomain;
    }
    if matches!(current, Term::Let(..)) {
        return None;
    }
    let goal = ctx.eval(current);
    let found = binders.iter().position(|(_, _, domain)| {
        adamas_core::conv::convertible(signature, metas, ctx.size(), domain, &goal)
    })?;
    let arity = binders.len();
    let index = u32::try_from(arity - 1 - found).ok()?;
    let solution = binders
        .iter()
        .rev()
        .fold(Term::var(index), |body, (mult, name, _)| {
            Term::Lam(*mult, Rc::clone(name), Rc::new(body))
        });
    Some(adamas_core::eval::eval(
        &adamas_core::value::Env::default(),
        &solution,
    ))
}

/// Имя класса и голова его первого аргумента: `Eqv Nat` даёт `(Eqv, Some(Nat))`.
///
/// Внешний `None` - тип не применение определения, то есть словарём он не
/// является вовсе. Внутренний - голова аргумента переменная, и кандидата для
/// неё искать негде.
fn applied(ty: &Term) -> Option<(Symbol, Option<Symbol>)> {
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
    let name = match head {
        Term::Const(name, _) => Some(Rc::clone(name)),
        // Голова-переменная: инстанса для неё нет и быть не может, а словарь
        // приходит из контекста. Это и есть полиморфный случай.
        _ => None,
    };
    Some((Rc::clone(class), name))
}
