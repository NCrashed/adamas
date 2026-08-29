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

use crate::level::{Level, LevelMeta, LevelVar, peel};
use crate::term::{Term, TermMeta};
use crate::value::Value;

/// Хранилище метапеременных уровня - одно на прогон элаборации (§10 вопрос 51).
///
/// Решения записываются один раз и не откатываются: backtracking'а в проверке
/// нет, а откат потребовал бы журнала и точек сохранения.
///
/// # Идентификатор - имя, а не номер слота
///
/// Счётчик монотонный и не перезапускается, поэтому [`LevelMeta`] осмыслен сам
/// по себе: он называет дырку, а не место в векторе. Хранилище - вектор со
/// смещением `base`: индексация остаётся O(1), а идентификатор ниже
/// границы (дырка прошлого объявления, память под неё освобождена) или выше
/// конца (дырка чужого хранилища) даёт **громкий отказ**, а не молча взятый
/// чужой слот.
///
/// Отказ здесь - паника, и это не путь пользовательской ошибки: попасть сюда
/// можно только смешав два хранилища или удержав дырку через границу
/// объявления, а и то и другое - баг вызывающего в компиляторе.
///
/// [`Clone`] хранилище не выводит намеренно: копия раздавала бы те же
/// идентификаторы от того же `base`, то есть ровно то смешение, ради запрета
/// которого всё это и заведено.
#[derive(Debug, Default)]
pub struct Metas {
    /// Живые дырки, начиная с `base`, - обоих сортов вперемешку.
    slots: Vec<Slot>,
    /// Идентификатор первой живой дырки. Он же - граница обобщения: всё, что
    /// живо, заведено текущим объявлением, потому что предыдущее закончилось
    /// [`Metas::release`].
    base: u32,
}

/// Живая дырка одного из двух сортов.
///
/// Сорта делят **один счётчик**, поэтому идентификатор называет дырку
/// однозначно: `?7` - это ровно одна дырка, а не две разных в разных
/// таблицах. Обращение не тем сортом - паника, как и обращение за границу:
/// оба случая означают баг вызывающего, а не ошибку в проверяемой программе.
#[derive(Debug)]
enum Slot {
    /// Дырка уровня; решение - выражение уровня.
    Level(Option<Level>),
    /// Дырка терма. Тип известен с рождения - его строит тот, кто дырку
    /// завёл, - а решение приходит от унификации и **замкнуто**: цепочка
    /// лямбд по контексту, в котором дырка заведена.
    Term {
        /// Замкнутый тип: телескоп по контексту, оканчивающийся целью.
        ty: Rc<Value>,
        /// Решение, когда оно найдено.
        solution: Option<Rc<Value>>,
    },
}

impl Metas {
    /// Свежая метапеременная уровня.
    pub fn fresh_level(&mut self) -> Level {
        let meta = LevelMeta(self.limit());
        self.slots.push(Slot::Level(None));
        Level::Meta(meta)
    }

    /// Свежая метапеременная терма, стоящая в контексте размера `size`.
    ///
    /// Возвращается не сама дырка, а она же, **применённая к контексту**:
    /// `?m x₀ … x_{n-1}`. Так дырка остаётся замкнутым термом, а её
    /// зависимость от связываний выражается спайном - тем же способом, каким
    /// её выражает всякое застрявшее вычисление. Решением тогда становится
    /// замкнутая цепочка лямбд, и подставлять её можно куда угодно без сдвигов.
    pub fn fresh_term(&mut self, ty: Rc<Value>, size: u32) -> Term {
        self.fresh_term_over(ty, &(0..size).collect::<Vec<u32>>(), size)
    }

    /// То же, но спайн - только перечисленные уровни контекста размера `size`.
    ///
    /// Нужно связыванию со значением (`let`): вычисление подставляет его
    /// значение, поэтому переменной в спайне оно не остаётся, а спайн из
    /// не-переменных выходит из паттернового фрагмента и не решается вовсе
    /// (см. [`crate::solve`]). Такое связывание в спайн не берут; в типе дырки
    /// оно остаётся - но `Let`'ом, а не `Pi`, - и вычисление типа его
    /// подставляет так же, как подставит проверка.
    ///
    /// `levels` обязан идти по возрастанию: спайн читается снаружи внутрь.
    pub fn fresh_term_over(&mut self, ty: Rc<Value>, levels: &[u32], size: u32) -> Term {
        let meta = TermMeta(self.limit());
        self.slots.push(Slot::Term { ty, solution: None });
        // Аргументы идут от внешнего связывания к внутреннему: уровень 0 -
        // самый внешний, а индекс до него из контекста размера `size` равен
        // `size - 1`.
        levels.iter().fold(Term::Meta(meta), |term, level| {
            Term::App(Rc::new(term), Rc::new(Term::var(size - 1 - level)))
        })
    }

    /// Решение метапеременной терма, если оно есть.
    ///
    /// # Panics
    ///
    /// Если дырка не из этого хранилища, пережила границу объявления или
    /// оказалась другого сорта.
    #[must_use]
    pub fn term_solution(&self, meta: TermMeta) -> Option<&Rc<Value>> {
        match &self.slots[self.offset(meta.0)] {
            Slot::Term { solution, .. } => solution.as_ref(),
            Slot::Level(_) => unreachable!("?{} - дырка уровня, а не терма", meta.0),
        }
    }

    /// Тип метапеременной терма - замкнутый, вместе с телескопом контекста.
    ///
    /// # Panics
    ///
    /// Те же случаи, что у [`Metas::term_solution`].
    #[must_use]
    pub fn term_type(&self, meta: TermMeta) -> &Rc<Value> {
        match &self.slots[self.offset(meta.0)] {
            Slot::Term { ty, .. } => ty,
            Slot::Level(_) => unreachable!("?{} - дырка уровня, а не терма", meta.0),
        }
    }

    /// Записывает решение метапеременной терма.
    ///
    /// # Panics
    ///
    /// Если дырка уже решена: решения не переписываются, backtracking'а в
    /// проверке нет.
    pub fn solve_term(&mut self, meta: TermMeta, value: Rc<Value>) {
        let offset = self.offset(meta.0);
        match &mut self.slots[offset] {
            Slot::Term {
                solution: solution @ None,
                ..
            } => *solution = Some(value),
            Slot::Term { .. } => unreachable!("?{} решена дважды", meta.0),
            Slot::Level(_) => unreachable!("?{} - дырка уровня, а не терма", meta.0),
        }
    }

    /// Отпускает все живые дырки и сдвигает границу.
    ///
    /// Зовётся на границе объявления - там, где все дырки либо решены, либо
    /// обобщены в параметры, либо стали отказом. После этого их
    /// идентификаторы остаются занятыми навсегда: обратиться по такому - не
    /// «не найдено», а ошибка, и хранилище отвечает на неё паникой.
    pub fn release(&mut self) {
        self.base = self.limit();
        self.slots.clear();
    }

    /// Идентификатор за последней живой дыркой.
    fn limit(&self) -> u32 {
        let live = u32::try_from(self.slots.len())
            .unwrap_or_else(|_| unreachable!("живых дырок не бывает столько"));
        self.base
            .checked_add(live)
            .unwrap_or_else(|| unreachable!("счётчик метапеременных не помещается в u32"))
    }

    /// Смещение дырки в живом диапазоне.
    ///
    /// Паникует вне диапазона - см. заголовок типа. Проверка одна на все
    /// обращения и работает в любой сборке: делать её отладочной значило бы
    /// оставить release без неё, а именно там дырка и берёт чужой слот молча.
    fn offset(&self, name: u32) -> usize {
        name.checked_sub(self.base)
            .and_then(|offset| usize::try_from(offset).ok())
            .filter(|offset| *offset < self.slots.len())
            .unwrap_or_else(|| {
                unreachable!(
                    "дырка ?{name} вне живого диапазона [{}, {})",
                    self.base,
                    self.limit()
                )
            })
    }

    /// Решение метапеременной, если оно есть.
    ///
    /// # Panics
    ///
    /// Если дырка не из этого хранилища или пережила границу объявления.
    #[must_use]
    pub fn solution(&self, meta: LevelMeta) -> Option<&Level> {
        match &self.slots[self.offset(meta.0)] {
            Slot::Level(solution) => solution.as_ref(),
            Slot::Term { .. } => unreachable!("?{} - дырка терма, а не уровня", meta.0),
        }
    }

    /// Жива ли хоть одна дырка.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
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
        // Живость проверяет `offset`: дырка вне диапазона - баг вызывающего, а
        // не повод отказать в типизации.
        let offset = self.offset(meta.0);
        let Slot::Level(slot) = &mut self.slots[offset] else {
            unreachable!("?{} - дырка терма, а не уровня", meta.0)
        };
        // Решённая сюда не доходит: `zonk` раскрыл бы её раньше.
        debug_assert!(slot.is_none(), "решённая дырка дошла до solve");
        *slot = Some(level.clone());
        true
    }
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
            // Дырка терма своих уровней не носит: они живут в её типе, а он
            // хранится отдельно и обобщается вместе с определением.
            Term::Var(_) | Term::Meta(_) => {}
            Term::Universe(level) => self.collect_level(metas, level),
            Term::Record(fields) => {
                for field in fields.iter() {
                    self.collect_term(metas, &field.ty);
                }
            }
            Term::Object(fields) => {
                for (_, value) in fields.iter() {
                    self.collect_term(metas, value);
                }
            }
            Term::Project(record, _) => self.collect_term(metas, record),
            Term::Lam(_, _, body) => self.collect_term(metas, body),
            Term::App(callee, argument) => {
                self.collect_term(metas, callee);
                self.collect_term(metas, argument);
            }
            Term::Pi(_, _, domain, row, codomain) => {
                self.collect_term(metas, domain);
                self.collect_term(metas, codomain);
                for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                    self.collect_term(metas, argument);
                }
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
            Term::Var(_) | Term::Meta(_) => term.clone(),
            Term::Universe(level) => Term::Universe(self.apply_level(metas, level)),
            Term::Record(fields) => Term::Record(
                fields
                    .iter()
                    .map(|field| crate::term::Field {
                        name: Rc::clone(&field.name),
                        mult: field.mult,
                        ty: recur(&field.ty),
                    })
                    .collect(),
            ),
            Term::Object(fields) => Term::Object(
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Term::Project(record, name) => Term::Project(recur(record), Rc::clone(name)),
            Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), recur(body)),
            Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
            Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
                *binder,
                Rc::clone(name),
                recur(domain),
                row.map(|argument| self.apply_term(metas, argument)),
                recur(codomain),
            ),
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
                consumed: case.consumed,
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

/// Первая нерешённая метапеременная **терма**, если она есть.
///
/// Дырка, дожившая до сигнатуры, означала бы определение, чьё тело зависит от
/// хранилища, которого уже нет, - тот же довод, что и у уровневых. Обобщать её
/// в параметр, в отличие от уровневой, нечем: аргумент терма выводится в месте
/// использования или пишется руками, а не поднимается в сигнатуру.
#[must_use]
pub fn unsolved_term_meta(metas: &Metas, term: &Term) -> Option<TermMeta> {
    let recur = |inner: &Rc<Term>| unsolved_term_meta(metas, inner);
    match term {
        Term::Meta(meta) => metas.term_solution(*meta).is_none().then_some(*meta),
        Term::Var(_) | Term::Universe(_) | Term::Const(..) => None,
        Term::Record(fields) => fields.iter().find_map(|field| recur(&field.ty)),
        Term::Object(fields) => fields.iter().find_map(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee).or_else(|| recur(argument)),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain).or_else(|| recur(codomain)).or_else(|| {
                row.labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .find_map(|argument| unsolved_term_meta(metas, argument))
            })
        }
        Term::Let(_, _, ty, value, body) => {
            recur(ty).or_else(|| recur(value)).or_else(|| recur(body))
        }
        Term::Case(case) => recur(&case.scrutinee)
            .or_else(|| recur(&case.motive))
            .or_else(|| {
                case.branches
                    .iter()
                    .find_map(|branch| unsolved_term_meta(metas, &branch.body))
            }),
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
        Term::Var(_) | Term::Meta(_) => None,
        Term::Universe(level) => in_level(metas, level),
        Term::Record(fields) => fields
            .iter()
            .find_map(|field| unsolved_level_meta(metas, &field.ty)),
        Term::Object(fields) => fields
            .iter()
            .find_map(|(_, value)| unsolved_level_meta(metas, value)),
        Term::Project(record, _) => unsolved_level_meta(metas, record),
        Term::Lam(_, _, body) => unsolved_level_meta(metas, body),
        Term::App(callee, argument) => {
            unsolved_level_meta(metas, callee).or_else(|| unsolved_level_meta(metas, argument))
        }
        Term::Pi(_, _, domain, row, codomain) => unsolved_level_meta(metas, domain)
            .or_else(|| unsolved_level_meta(metas, codomain))
            .or_else(|| {
                row.labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .find_map(|argument| unsolved_level_meta(metas, argument))
            }),
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
        // Решённая дырка подставляется целиком: решение замкнуто, поэтому
        // обратное чтение идёт в пустом контексте и сдвигов не требует.
        //
        // Подставленное зонкается заново: решение хранится таким, каким его
        // записали, и уровни внутри него могли решиться позже. Без этого
        // прохода дырка уровня уезжает в определение живой, а обобщение её не
        // видит - оно смотрит уже зонканный тип.
        Term::Record(fields) => Term::Record(
            fields
                .iter()
                .map(|field| crate::term::Field {
                    name: Rc::clone(&field.name),
                    mult: field.mult,
                    ty: recur(&field.ty),
                })
                .collect(),
        ),
        Term::Object(fields) => Term::Object(
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), recur(value)))
                .collect(),
        ),
        Term::Project(record, name) => Term::Project(recur(record), Rc::clone(name)),
        Term::Meta(meta) => match metas.term_solution(*meta) {
            Some(solution) => zonk_term(metas, &crate::eval::quote(0, solution)),
            None => term.clone(),
        },
        Term::Universe(level) => Term::Universe(metas.zonk(level)),
        Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), recur(body)),
        Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            recur(domain),
            row.map(|argument| zonk_term(metas, argument)),
            recur(codomain),
        ),
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
            consumed: case.consumed,
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
