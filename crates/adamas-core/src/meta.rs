//! Метапеременные уровней и их решение.
//!
//! Implicit universe polymorphism (§3.2, §9 Фаза 1) устроен так же, как вывод
//! типов в warm-up'е, только на уровнях: в месте использования параметры
//! заменяются свежими метапеременными, а ограничения решаются по ходу
//! проверки.
//!
//! **Обобщения ещё нет.** Арность определения объявляется, а не выводится, и
//! дырка, оставшаяся нерешённой к концу проверки, - отказ
//! ([`unsolved_level_meta`]), а не новый параметр. Обобщение - следующий срез.
//!
//! # Решение неполное, и это записано
//!
//! Решается **паттерн**: `?m ~ l`, где `?m` не встречается в `l`. Всё
//! остальное - метапеременная под `max` или `suc` - сравнивается как есть и
//! при расхождении даёт отказ. `max ?a u ~ max v w` не имеет единственного
//! решения (`?a` может быть чем угодно, не превосходящим правую часть), и
//! угадывать его нельзя: неверная догадка принимает некорректную программу.
//! Отказ отвергает корректную - см. §10 вопрос 39.

use std::rc::Rc;

use crate::level::{Level, LevelMeta};

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
        let left = self.zonk(left);
        let right = self.zonk(right);

        // Уже равны как выражения - решать нечего. Проверка идёт первой,
        // потому что `?m ~ ?m` не должно превращаться в самоприсваивание.
        if left.equiv(&right) {
            return true;
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
