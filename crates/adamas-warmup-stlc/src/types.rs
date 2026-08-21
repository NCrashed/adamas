//! Типы, схемы и метаконтекст.
//!
//! Каждой метапеременной приписан уровень вложенности `let`, на котором она
//! создана; обобщаются те, чей уровень больше текущего (приём OCaml - иначе на
//! каждом `let` пришлось бы обходить всё окружение). Унификация обязана
//! понижать уровни, см. [`crate::unify`].

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

/// Ссылка на метапеременную в [`MetaCtx`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MetaId(u32);

/// Глубина вложенности `let`. Нужна для обобщения.
pub(crate) type Level = u32;

/// Тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    /// Целые числа.
    Int,
    /// Логические значения.
    Bool,
    /// Функция из первого во второй.
    Fun(Rc<Type>, Rc<Type>),
    /// Связанная переменная типа: `a` в `a -> a`. Появляется при обобщении.
    Var(u32),
    /// Нерешённая метапеременная. В результате [`crate::check`] не
    /// встречается: перед возвратом тип обобщается, и всё нерешённое
    /// становится [`Type::Var`].
    Meta(MetaId),
}

impl Type {
    pub(crate) fn fun(from: Rc<Self>, to: Rc<Self>) -> Rc<Self> {
        Rc::new(Self::Fun(from, to))
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => f.write_str("Int"),
            Self::Bool => f.write_str("Bool"),
            Self::Var(index) => write!(f, "{}", var_name(*index)),
            Self::Meta(MetaId(id)) => write!(f, "?{id}"),
            Self::Fun(from, to) => {
                // Стрелка правоассоциативна, поэтому скобки нужны только слева.
                if matches!(**from, Self::Fun(..)) {
                    write!(f, "({from}) -> {to}")
                } else {
                    write!(f, "{from} -> {to}")
                }
            }
        }
    }
}

/// Имя связанной переменной по индексу: `a`, `b`, … `z`, `a1`, `b1`, …
fn var_name(index: u32) -> String {
    let letter = char::from(b'a' + u8::try_from(index % 26).unwrap_or(0));
    let round = index / 26;
    if round == 0 {
        letter.to_string()
    } else {
        format!("{letter}{round}")
    }
}

/// Полиморфная схема: `arity` связанных переменных над телом, в котором они
/// представлены как [`Type::Var`] с индексами `0..arity`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Scheme {
    pub(crate) arity: u32,
    pub(crate) body: Rc<Type>,
}

impl Scheme {
    /// Мономорфная схема - тип без единой связанной переменной.
    pub(crate) fn mono(body: Rc<Type>) -> Self {
        Self { arity: 0, body }
    }
}

#[derive(Clone, Debug)]
struct Entry {
    level: Level,
    solution: Option<Rc<Type>>,
}

/// Хранилище метапеременных.
#[derive(Clone, Debug, Default)]
pub(crate) struct MetaCtx {
    entries: Vec<Entry>,
}

impl MetaCtx {
    pub(crate) fn fresh(&mut self, level: Level) -> Rc<Type> {
        let id = MetaId(narrow(self.entries.len()));
        self.entries.push(Entry {
            level,
            solution: None,
        });
        Rc::new(Type::Meta(id))
    }

    fn entry(&self, MetaId(id): MetaId) -> Option<&Entry> {
        self.entries.get(id as usize)
    }

    pub(crate) fn level_of(&self, id: MetaId) -> Level {
        self.entry(id).map_or(0, |entry| entry.level)
    }

    pub(crate) fn lower_level(&mut self, MetaId(id): MetaId, level: Level) {
        if let Some(entry) = self.entries.get_mut(id as usize) {
            entry.level = entry.level.min(level);
        }
    }

    pub(crate) fn solve(&mut self, MetaId(id): MetaId, ty: Rc<Type>) {
        if let Some(entry) = self.entries.get_mut(id as usize) {
            entry.solution = Some(ty);
        }
    }

    /// Раскрывает решённые метапеременные в голове типа - ровно настолько,
    /// чтобы стало видно конструктор. Вглубь не идёт: это [`Self::quantify`].
    pub(crate) fn force(&self, ty: &Rc<Type>) -> Rc<Type> {
        let mut current = Rc::clone(ty);
        while let Type::Meta(id) = *current {
            match self.entry(id).and_then(|entry| entry.solution.as_ref()) {
                Some(solution) => current = Rc::clone(solution),
                None => break,
            }
        }
        current
    }

    /// Обобщает тип: метапеременные с уровнем строго больше `level` становятся
    /// связанными переменными схемы.
    pub(crate) fn generalize(&self, level: Level, ty: &Rc<Type>) -> Scheme {
        let mut bound = HashMap::new();
        let body = self.quantify(Some(level), ty, &mut bound);
        Scheme {
            arity: narrow(bound.len()),
            body,
        }
    }

    /// Печатает два типа с общей таблицей имён: `?3` читателю ничего не
    /// говорит, а раздельные таблицы сделали бы "ожидался `a -> b`, получен
    /// `a`" ложью - три буквы означали бы три независимые метапеременные.
    pub(crate) fn render_pair(&self, left: &Rc<Type>, right: &Rc<Type>) -> (String, String) {
        let mut bound = HashMap::new();
        let left = self.quantify(None, left, &mut bound).to_string();
        let right = self.quantify(None, right, &mut bound).to_string();
        (left, right)
    }

    /// `threshold = Some(level)` - заменить метапеременные глубже уровня;
    /// `None` - заменить все.
    fn quantify(
        &self,
        threshold: Option<Level>,
        ty: &Rc<Type>,
        bound: &mut HashMap<MetaId, u32>,
    ) -> Rc<Type> {
        let forced = self.force(ty);
        match &*forced {
            Type::Fun(from, to) => Type::fun(
                self.quantify(threshold, from, bound),
                self.quantify(threshold, to, bound),
            ),
            Type::Meta(id) if threshold.is_none_or(|level| self.level_of(*id) > level) => {
                let next = narrow(bound.len());
                let index = *bound.entry(*id).or_insert(next);
                Rc::new(Type::Var(index))
            }
            _ => forced,
        }
    }

    /// Инстанцирует схему: каждая связанная переменная заменяется свежей
    /// метапеременной текущего уровня.
    pub(crate) fn instantiate(&mut self, scheme: &Scheme, level: Level) -> Rc<Type> {
        if scheme.arity == 0 {
            return Rc::clone(&scheme.body);
        }
        let fresh: Vec<Rc<Type>> = (0..scheme.arity).map(|_| self.fresh(level)).collect();
        substitute(&scheme.body, &fresh)
    }
}

/// Сужает счётчик до `u32`.
///
/// Переполнение - internal invariant, не пользовательская ошибка: ни
/// метапеременных, ни связанных переменных на четыре миллиарда в программе не
/// бывает. Паника здесь строго лучше насыщения: при `unwrap_or(u32::MAX)` все
/// идентификаторы за пределом схлопнулись бы в один, начали унифицироваться
/// друг с другом и выдали бы неверные типы без единой ошибки.
#[expect(clippy::expect_used, reason = "internal invariant, см. описание")]
fn narrow(count: usize) -> u32 {
    u32::try_from(count).expect("счётчик не переполняет u32")
}

fn substitute(ty: &Rc<Type>, args: &[Rc<Type>]) -> Rc<Type> {
    match &**ty {
        Type::Var(index) => args
            .get(*index as usize)
            .map_or_else(|| Rc::clone(ty), Rc::clone),
        Type::Fun(from, to) => Type::fun(substitute(from, args), substitute(to, args)),
        _ => Rc::clone(ty),
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{MetaCtx, Type};

    #[test]
    fn arrow_is_right_associative_when_printed() {
        let inner = Type::fun(Rc::new(Type::Int), Rc::new(Type::Bool));
        let right = Type::fun(Rc::new(Type::Int), Rc::clone(&inner));
        let left = Type::fun(Rc::clone(&inner), Rc::new(Type::Int));
        assert_eq!(right.to_string(), "Int -> Int -> Bool");
        assert_eq!(left.to_string(), "(Int -> Bool) -> Int");
    }

    #[test]
    fn force_follows_chains_of_solutions() {
        let mut ctx = MetaCtx::default();
        let a = ctx.fresh(0);
        let b = ctx.fresh(0);
        let (Type::Meta(a_id), Type::Meta(b_id)) = (&*a, &*b) else {
            panic!("fresh обязан вернуть метапеременную");
        };
        ctx.solve(*a_id, Rc::clone(&b));
        ctx.solve(*b_id, Rc::new(Type::Int));
        assert_eq!(*ctx.force(&a), Type::Int);
    }

    #[test]
    fn generalization_respects_levels() {
        let mut ctx = MetaCtx::default();
        let outer = ctx.fresh(0);
        let inner = ctx.fresh(1);
        let ty = Type::fun(Rc::clone(&outer), Rc::clone(&inner));

        // На уровне 0 обобщается только та, что создана глубже.
        let scheme = ctx.generalize(0, &ty);
        assert_eq!(scheme.arity, 1);
        // На уровне 1 не обобщается ничего.
        assert_eq!(ctx.generalize(1, &ty).arity, 0);
    }

    #[test]
    fn instantiation_gives_independent_metas() {
        let mut ctx = MetaCtx::default();
        let var = Rc::new(Type::Var(0));
        let scheme = super::Scheme {
            arity: 1,
            body: Type::fun(Rc::clone(&var), var),
        };
        let first = ctx.instantiate(&scheme, 0);
        let second = ctx.instantiate(&scheme, 0);
        assert_ne!(
            first, second,
            "две инстанциации не должны делить метапеременную"
        );
    }
}
