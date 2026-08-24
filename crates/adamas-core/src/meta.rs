//! Метапеременные уровней и их решение.
//!
//! Implicit universe polymorphism (§3.2, §9 Фаза 1) устроен так же, как вывод
//! типов в warm-up'е, только на уровнях, и теми же двумя половинами:
//!
//! - **instantiate** - в месте использования параметры заменяются свежими
//!   дырками ([`Metas::fresh_level`], [`crate::sig::Signature::instantiate`]),
//!   а ограничения решаются по ходу проверки;
//! - **generalize** - на границе определения то, что осталось нерешённым,
//!   возвращается в параметры ([`Generalization`]), и их число и есть арность.
//!
//! Дырка, оставшаяся нерешённой там, где обобщать нельзя, - отказ
//! ([`unsolved_level_meta`]), а не молча выбранный уровень.
//!
//! # Решение неполное, и это записано
//!
//! Решается **паттерн** `?m ~ l`, где `?m` не встречается в `l`, плюс снятие
//! общих `suc` с обеих сторон: конструктор инъективен, поэтому `suc ?m ~ 3`
//! однозначно даёт `?m ~ 2`.
//!
//! Не решается дырка под `max`: `max ?a u ~ max v w` не имеет единственного
//! решения (`?a` может быть чем угодно, не превосходящим правую часть), и
//! угадывать его нельзя - неверная догадка принимает некорректную программу.
//! Отказ отвергает корректную, см. §10 вопрос 39.

use std::rc::Rc;

use crate::level::{Level, LevelMeta, LevelVar};

/// Хранилище метапеременных уровня.
///
/// Решения записываются один раз и не откатываются: backtracking'а в проверке
/// нет, а откат потребовал бы журнала и точек сохранения.
#[derive(Clone, Debug, Default)]
pub struct Metas {
    levels: Vec<Option<Level>>,
}

impl Metas {
    /// Свежая метапеременная уровня.
    pub fn fresh_level(&mut self) -> Level {
        let meta = LevelMeta(
            u32::try_from(self.levels.len())
                .unwrap_or_else(|_| unreachable!("счётчик метапеременных не помещается в u32")),
        );
        self.levels.push(None);
        Level::Meta(meta)
    }

    /// Решение метапеременной, если оно есть.
    #[must_use]
    pub fn solution(&self, LevelMeta(index): LevelMeta) -> Option<&Level> {
        self.levels.get(index as usize)?.as_ref()
    }

    /// Сколько метапеременных заведено.
    #[must_use]
    pub fn len(&self) -> usize {
        self.levels.len()
    }

    /// Заведена ли хоть одна.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.levels.is_empty()
    }

    /// Подставляет решения вглубь. После этого в уровне остаются только
    /// нерешённые метапеременные.
    #[must_use]
    pub fn zonk(&self, level: &Level) -> Level {
        match level {
            Level::Zero | Level::Var(_) => level.clone(),
            Level::Succ(inner) => self.zonk(inner).succ(),
            Level::Max(left, right) => self.zonk(left).max(self.zonk(right)),
            Level::Meta(meta) => match self.solution(*meta) {
                Some(solved) => self.zonk(&solved.clone()),
                None => level.clone(),
            },
        }
    }

    /// Приводит два уровня к равенству, решая метапеременные.
    ///
    /// `false` - уровни несовместимы либо ограничение вне решаемого класса
    /// (см. заголовок модуля). Различить эти два случая вызывающий не может и
    /// не должен: и то и другое - отказ типизации.
    pub fn unify_levels(&mut self, left: &Level, right: &Level) -> bool {
        // Нормальная форма, а не просто зонканная: она канонична и полна
        // (см. `crate::level`), и без неё снятие `suc` ниже не срабатывает там,
        // где должно. Уровень `Pi`, домен и кодомен которого делят один
        // параметр, - это `max (suc ?l) (suc ?l)`, снаружи `max`, снимать
        // нечего; нормализация сводит его к `suc ?l`, и дальше всё обычно.
        // На действительно неоднозначные случаи это не влияет: `max ?a ?b`
        // остаётся `max`.
        let left = self.zonk(left).normalize();
        let right = self.zonk(right).normalize();

        // Уже равны как выражения - решать нечего. Проверка идёт первой,
        // потому что `?m ~ ?m` не должно превращаться в самоприсваивание.
        if left.equiv(&right) {
            return true;
        }

        // Снимаем общие `suc`: конструктор инъективен, поэтому
        // `suc a ~ suc b` равносильно `a ~ b`, а `suc ?m ~ 3` - это `?m ~ 2`.
        // Единственность решения здесь есть, в отличие от `max`, и без этого
        // шага не проходила бы самая обычная проверка `Type ?l` против
        // `Type 3`: правило универсума даёт `suc ?l`, а дырка оказывалась бы
        // под конструктором.
        let (left_base, left_offset) = peel(&left);
        let (right_base, right_offset) = peel(&right);
        let common = left_offset.min(right_offset);
        if common > 0 {
            return self.unify_levels(
                &raise(left_base, left_offset - common),
                &raise(right_base, right_offset - common),
            );
        }

        match (&left, &right) {
            (Level::Meta(meta), other) | (other, Level::Meta(meta)) => self.solve(*meta, other),
            // Обе стороны жёсткие и неравны, либо метапеременная спрятана под
            // конструктором - решать нечем.
            _ => false,
        }
    }

    /// Решает метапеременную уровнем, проверив, что не порождает цикл.
    fn solve(&mut self, meta: LevelMeta, level: &Level) -> bool {
        if occurs(meta, level) {
            return false;
        }
        let LevelMeta(index) = meta;
        match self.levels.get_mut(index as usize) {
            // Решённая сюда не доходит: `zonk` раскрыл бы её раньше.
            Some(slot) if slot.is_none() => {
                *slot = Some(level.clone());
                true
            }
            _ => false,
        }
    }
}

/// Снимает цепочку `suc`, возвращая основание и её длину.
fn peel(level: &Level) -> (&Level, u32) {
    let mut current = level;
    let mut offset = 0;
    while let Level::Succ(inner) = current {
        current = inner;
        offset += 1;
    }
    (current, offset)
}

/// Обратная операция: надстраивает `offset` штук `suc`.
fn raise(base: &Level, offset: u32) -> Level {
    (0..offset).fold(base.clone(), |level, _| level.succ())
}

/// Встречается ли метапеременная внутри уровня.
///
/// Без этой проверки `?m ~ suc ?m` решилось бы бесконечным уровнем.
fn occurs(meta: LevelMeta, level: &Level) -> bool {
    match level {
        Level::Zero | Level::Var(_) => false,
        Level::Succ(inner) => occurs(meta, inner),
        Level::Max(left, right) => occurs(meta, left) || occurs(meta, right),
        Level::Meta(other) => *other == meta,
    }
}

/// Обобщение: нерешённые дырки становятся параметрами уровня.
///
/// Обратная операция к [`Metas::fresh_level`] на границе определения. В месте
/// использования параметры заменяются дырками, здесь то, что осталось
/// незаполненным, возвращается в параметры - та же пара instantiate/generalize,
/// что у `let`-полиморфизма в warm-up'е, только на уровнях.
///
/// Нумерация плотная и задана порядком первого появления, поэтому одно и то же
/// определение получает одни и те же параметры независимо от того, сколько
/// дырок было заведено по дороге и в каком порядке.
#[derive(Debug, Default)]
pub struct Generalization {
    bound: Vec<LevelMeta>,
}

impl Generalization {
    /// Собирает нерешённые дырки уровня в порядке появления.
    pub fn collect_level(&mut self, metas: &Metas, level: &Level) {
        match metas.zonk(level) {
            Level::Zero | Level::Var(_) => {}
            Level::Succ(inner) => self.collect_level(metas, &inner),
            Level::Max(left, right) => {
                self.collect_level(metas, &left);
                self.collect_level(metas, &right);
            }
            Level::Meta(meta) => {
                if !self.bound.contains(&meta) {
                    self.bound.push(meta);
                }
            }
        }
    }

    /// То же по всем уровням терма.
    pub fn collect_term(&mut self, metas: &Metas, term: &crate::term::Term) {
        use crate::term::Term;

        match term {
            Term::Var(_) => {}
            Term::Universe(level) => self.collect_level(metas, level),
            Term::Lam(_, _, body) => self.collect_term(metas, body),
            Term::App(callee, argument) => {
                self.collect_term(metas, callee);
                self.collect_term(metas, argument);
            }
            Term::Pi(_, _, domain, codomain) => {
                self.collect_term(metas, domain);
                self.collect_term(metas, codomain);
            }
            Term::Let(_, _, ty, value, body) => {
                self.collect_term(metas, ty);
                self.collect_term(metas, value);
                self.collect_term(metas, body);
            }
            Term::Const(_, levels) => {
                for level in levels.iter() {
                    self.collect_level(metas, level);
                }
            }
            Term::Case(case) => {
                for level in case.levels.iter() {
                    self.collect_level(metas, level);
                }
                self.collect_term(metas, &case.scrutinee);
                self.collect_term(metas, &case.motive);
                for branch in &case.branches {
                    self.collect_term(metas, &branch.body);
                }
            }
        }
    }

    /// Сколько параметров уровня получится.
    #[must_use]
    pub fn arity(&self) -> u32 {
        u32::try_from(self.bound.len())
            .unwrap_or_else(|_| unreachable!("параметров уровня не бывает столько"))
    }

    /// Заменяет собранные дырки параметрами.
    ///
    /// Дырка, которую не собирали, остаётся дыркой - так вызывающий видит, что
    /// она осталась, вместо того чтобы получить молча подставленный параметр.
    #[must_use]
    pub fn apply_level(&self, metas: &Metas, level: &Level) -> Level {
        match metas.zonk(level) {
            Level::Succ(inner) => self.apply_level(metas, &inner).succ(),
            Level::Max(left, right) => self
                .apply_level(metas, &left)
                .max(self.apply_level(metas, &right)),
            Level::Meta(meta) => self.bound.iter().position(|bound| *bound == meta).map_or(
                Level::Meta(meta),
                |index| {
                    Level::Var(LevelVar(
                        u32::try_from(index).unwrap_or_else(|_| unreachable!("индекс параметра")),
                    ))
                },
            ),
            other => other,
        }
    }

    /// То же по всем уровням терма.
    #[must_use]
    pub fn apply_term(&self, metas: &Metas, term: &crate::term::Term) -> crate::term::Term {
        use crate::term::Term;

        let recur = |inner: &Rc<Term>| Rc::new(self.apply_term(metas, inner));
        match term {
            Term::Var(_) => term.clone(),
            Term::Universe(level) => Term::Universe(self.apply_level(metas, level)),
            Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), recur(body)),
            Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
            Term::Pi(mult, name, domain, codomain) => {
                Term::Pi(*mult, Rc::clone(name), recur(domain), recur(codomain))
            }
            Term::Let(mult, name, ty, value, body) => {
                Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), recur(body))
            }
            Term::Const(name, levels) => Term::Const(
                Rc::clone(name),
                levels
                    .iter()
                    .map(|level| self.apply_level(metas, level))
                    .collect(),
            ),
            Term::Case(case) => Term::Case(Rc::new(crate::term::Case {
                data: Rc::clone(&case.data),
                levels: case
                    .levels
                    .iter()
                    .map(|level| self.apply_level(metas, level))
                    .collect(),
                params: case.params,
                scrutinee: recur(&case.scrutinee),
                motive: recur(&case.motive),
                branches: case
                    .branches
                    .iter()
                    .map(|branch| crate::term::Branch {
                        constructor: Rc::clone(&branch.constructor),
                        body: recur(&branch.body),
                    })
                    .collect(),
            })),
        }
    }
}

/// Первая нерешённая метапеременная уровня в терме, если она есть.
///
/// Определение, в котором после проверки осталась дырка, неоднозначно: ничто в
/// его типе не заставит вывод её заполнить. Обобщать такие дырки в параметры -
/// работа следующего среза; пока это отказ.
#[must_use]
pub fn unsolved_level_meta(metas: &Metas, term: &crate::term::Term) -> Option<LevelMeta> {
    use crate::term::Term;

    fn in_level(metas: &Metas, level: &Level) -> Option<LevelMeta> {
        match metas.zonk(level) {
            Level::Zero | Level::Var(_) => None,
            Level::Succ(inner) => in_level(metas, &inner),
            Level::Max(left, right) => in_level(metas, &left).or_else(|| in_level(metas, &right)),
            Level::Meta(meta) => Some(meta),
        }
    }

    match term {
        Term::Var(_) => None,
        Term::Universe(level) => in_level(metas, level),
        Term::Lam(_, _, body) => unsolved_level_meta(metas, body),
        Term::App(callee, argument) => {
            unsolved_level_meta(metas, callee).or_else(|| unsolved_level_meta(metas, argument))
        }
        Term::Pi(_, _, domain, codomain) => {
            unsolved_level_meta(metas, domain).or_else(|| unsolved_level_meta(metas, codomain))
        }
        Term::Let(_, _, ty, value, body) => unsolved_level_meta(metas, ty)
            .or_else(|| unsolved_level_meta(metas, value))
            .or_else(|| unsolved_level_meta(metas, body)),
        Term::Const(_, levels) => levels.iter().find_map(|level| in_level(metas, level)),
        Term::Case(case) => case
            .levels
            .iter()
            .find_map(|level| in_level(metas, level))
            .or_else(|| unsolved_level_meta(metas, &case.scrutinee))
            .or_else(|| unsolved_level_meta(metas, &case.motive))
            .or_else(|| {
                case.branches
                    .iter()
                    .find_map(|branch| unsolved_level_meta(metas, &branch.body))
            }),
    }
}

/// Заменяет решённые метапеременные во всём терме.
#[must_use]
pub fn zonk_term(metas: &Metas, term: &crate::term::Term) -> crate::term::Term {
    use crate::term::Term;

    let recur = |inner: &Rc<Term>| Rc::new(zonk_term(metas, inner));
    match term {
        Term::Var(_) => term.clone(),
        Term::Universe(level) => Term::Universe(metas.zonk(level)),
        Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), recur(body)),
        Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
        Term::Pi(mult, name, domain, codomain) => {
            Term::Pi(*mult, Rc::clone(name), recur(domain), recur(codomain))
        }
        Term::Let(mult, name, ty, value, body) => {
            Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), recur(body))
        }
        Term::Const(name, levels) => Term::Const(
            Rc::clone(name),
            levels.iter().map(|level| metas.zonk(level)).collect(),
        ),
        Term::Case(case) => Term::Case(Rc::new(crate::term::Case {
            data: Rc::clone(&case.data),
            levels: case.levels.iter().map(|level| metas.zonk(level)).collect(),
            params: case.params,
            scrutinee: recur(&case.scrutinee),
            motive: recur(&case.motive),
            branches: case
                .branches
                .iter()
                .map(|branch| crate::term::Branch {
                    constructor: Rc::clone(&branch.constructor),
                    body: recur(&branch.body),
                })
                .collect(),
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::Metas;
    use crate::level::{Level, LevelVar};

    #[test]
    fn a_bare_metavariable_is_solved_by_anything() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(metas.unify_levels(&meta, &Level::number(3)));
        assert_eq!(metas.zonk(&meta), Level::number(3));
    }

    #[test]
    fn solving_works_in_both_directions() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(metas.unify_levels(&Level::number(2), &meta));
        assert_eq!(metas.zonk(&meta), Level::number(2));
    }

    #[test]
    fn a_solved_metavariable_keeps_its_solution() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(metas.unify_levels(&meta, &Level::number(1)));
        assert!(
            metas.unify_levels(&meta, &Level::number(1)),
            "то же решение"
        );
        assert!(
            !metas.unify_levels(&meta, &Level::number(2)),
            "другое решение"
        );
    }

    #[test]
    fn occurs_check_rejects_infinite_levels() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(!metas.unify_levels(&meta, &meta.clone().succ()));
    }

    #[test]
    fn identical_metavariables_unify_without_self_assignment() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(metas.unify_levels(&meta, &meta.clone()));
        assert!(metas.solution(crate::level::LevelMeta(0)).is_none());
    }

    #[test]
    fn rigid_levels_are_compared_not_solved() {
        let mut metas = Metas::default();
        assert!(metas.unify_levels(&Level::number(2), &Level::number(2)));
        assert!(!metas.unify_levels(&Level::number(2), &Level::number(3)));
    }

    /// `suc` инъективен, поэтому дырка под ним решается однозначно.
    ///
    /// Без этого не проходила бы обычная проверка `Type ?l` против `Type 3`:
    /// правило универсума даёт `suc ?l`, и дырка оказывается под конструктором.
    #[test]
    fn a_metavariable_under_succ_is_solved_by_peeling() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(metas.unify_levels(&meta.clone().succ(), &Level::number(3)));
        assert_eq!(metas.zonk(&meta), Level::number(2));
    }

    #[test]
    fn peeling_respects_the_absence_of_a_predecessor() {
        // `suc x ~ 0` неразрешимо: нуль не является преемником.
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        assert!(!metas.unify_levels(&meta.succ(), &Level::Zero));
    }

    #[test]
    fn peeling_works_under_a_common_prefix() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        // `suc (suc ?m) ~ suc (suc u0)` сводится к `?m ~ u0`.
        let left = meta.clone().succ().succ();
        let right = Level::Var(LevelVar(0)).succ().succ();
        assert!(metas.unify_levels(&left, &right));
        assert_eq!(metas.zonk(&meta), Level::Var(LevelVar(0)));
    }

    /// Граница решаемого класса, зафиксированная тестом: метапеременная под
    /// `max` не решается, потому что решение не единственно.
    #[test]
    fn a_metavariable_under_max_is_out_of_the_solvable_class() {
        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        let left = meta.max(Level::Var(LevelVar(0)));
        assert!(!metas.unify_levels(&left, &Level::number(5)));
    }

    #[test]
    fn zonking_follows_chains_of_solutions() {
        let mut metas = Metas::default();
        let first = metas.fresh_level();
        let second = metas.fresh_level();
        assert!(metas.unify_levels(&first, &second));
        assert!(metas.unify_levels(&second, &Level::number(4)));
        assert_eq!(metas.zonk(&first), Level::number(4));
    }

    #[test]
    fn unsolved_metavariables_are_visible_in_terms() {
        use crate::term::Term;

        let mut metas = Metas::default();
        let meta = metas.fresh_level();
        let term = Term::Universe(meta.clone().max(Level::Var(LevelVar(0))));

        assert!(super::unsolved_level_meta(&metas, &term).is_some());
        assert!(metas.unify_levels(&meta, &Level::number(2)));
        assert!(
            super::unsolved_level_meta(&metas, &term).is_none(),
            "после решения дырок не остаётся"
        );
    }
}
