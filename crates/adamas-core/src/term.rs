//! Термы core-языка (§3.2).
//!
//! Переменные - индексы де Брёйна: `Index(0)` указывает на ближайшее
//! связывание. Значения (`crate::value`) используют уровни, считающие с
//! другого конца; пара "индексы в термах, уровни в значениях" - обычная для
//! `NbE`, потому что делает подстановку в замыканиях бесплатной.
//!
//! Имена хранятся только для печати. Единственный источник истины о том, на
//! что ссылается переменная, - индекс.

use std::fmt;
use std::rc::Rc;

use crate::level::Level;
use crate::mult::Mult;
use crate::row::Row;
use crate::visibility::Visibility;

/// Индекс де Брёйна: сколько связываний отсчитать наружу.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Index(pub u32);

impl Index {
    /// Уровень, на который указывает индекс в контексте размера `size`.
    ///
    /// Обратна [`crate::value::Lvl::to_index`]. `None`, если индекс за
    /// пределами контекста, - в отличие от обратной операции, здесь это
    /// нормальный исход: индекс приходит из терма, а терм может быть
    /// незамкнутым, и отвечать на это должен проверяющий, а не паника.
    #[must_use]
    pub fn to_level(self, size: u32) -> Option<crate::value::Lvl> {
        size.checked_sub(self.0)
            .and_then(|distance| distance.checked_sub(1))
            .map(crate::value::Lvl)
    }
}

/// Имя для печати. На семантику не влияет.
pub type Name = Rc<str>;

/// Терм core-языка.
///
/// Зависимых пар (`(q x : A) ** B` из §3.2) здесь нет: механика у них та же,
/// что у `Pi`, но срез до них не дошёл. Состояние ядра целиком - в
/// [`crate::lib`](crate), здесь оно не пересказывается.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// Переменная.
    Var(Index),
    /// `\(q x : _) -> body`. Тип параметра в терме не хранится: его знает
    /// проверяющий из ожидаемого `Pi`.
    Lam(Mult, Name, Rc<Term>),
    /// Применение.
    App(Rc<Term>, Rc<Term>),
    /// Зависимая функция `(q x : domain) -> ε ▷ codomain`.
    ///
    /// Row описывает, что происходит при применении, и стоит там же, где
    /// кратность, по той же причине: принимающая сторона обязана знать
    /// контракт до вызова (§3.4). Сегодня она всегда пуста - правила
    /// погашения приходят Фазой 4, - но поле заводится сейчас, потому что
    /// добавить его задним числом значит тронуть все места конструирования;
    /// см. заголовок [`crate::row`].
    ///
    /// Кратность и видимость собраны в [`Binder`]: обе - часть типа, обе
    /// сравниваются конвертируемостью, и порознь они дали бы шесть позиций
    /// подряд, из которых читатель узнаёт разве что порядок.
    Pi(Binder, Name, Rc<Term>, Row<Term>, Rc<Term>),
    /// `Type level`.
    Universe(Level),
    /// `let q x : ty = value in body`.
    ///
    /// Кратность здесь по той же причине, что и на `Pi`: связывание тратит
    /// значение, и без неё `let 1 h = openFile … in …` нечем выразить.
    Let(Mult, Name, Rc<Term>, Rc<Term>, Rc<Term>),
    /// Ссылка на определение из [`crate::sig::Signature`] вместе с аргументами
    /// уровня.
    ///
    /// Список заполняется выводом, а не руками:
    /// [`Signature::instantiate`](crate::sig::Signature::instantiate) ставит
    /// туда свежие дырки, а решает их проверка конвертируемости. Собирать этот
    /// узел напрямую значит обойти вывод и получить `LevelArity` там, где он
    /// сработал бы.
    Const(Name, Rc<[Level]>),
    /// Разбор значения индуктивного типа по конструктору.
    Case(Rc<Case>),
    /// Тип записи: телескоп полей и, возможно, хвост-row.
    ///
    /// Телескоп, а не набор: тип поля вправе ссылаться на предыдущие поля, и
    /// это то, что делает запись первоклассным Σ-типом (§4.2). Отсюда же
    /// цена решения от 2026-08-29: запись с зависимостью между полями
    /// **закрыта** - переставлять её поля нечем, а row-полиморфизм на
    /// перестановке и стоит.
    ///
    /// Хвост (`{ x : A | r }`) делает её открытой, и тогда зависимости в ней
    /// нет по тому же правилу: поля из `r` не вправе ссылаться на поля головы,
    /// а голова - на поля `r`, которых она не знает.
    Record(Fields),
    /// Сорт рядов: `Row ℓ`.
    ///
    /// Третий сорт рядом с `Type` и `Level` (§3.2, лог 2026-08-27). Ряд
    /// записи однороден по уровню: все его поля живут в `Type ℓ`, и без этого
    /// универсум открытой записи не вычислялся бы - хвост неизвестен.
    ///
    /// Сам `Row ℓ` живёт в `Type (ℓ+1)`, поэтому `{0 r : Row ℓ} -> …` есть
    /// обычная `Pi`, а row-переменная - обычное связывание.
    RowKind(Level),
    /// Ряд: набор полей и, возможно, хвост. Значение сорта `Row ℓ`.
    ///
    /// Порядок в нём не значим - в отличие от телескопа записи, - потому что
    /// зависимости в открытой записи нет. Одноимённые метки законны и
    /// **затеняют**: scoped labels (§4.2, Leijen 2005), внешняя видна.
    /// Написать дубликат руками нельзя - это отвергает поверхность; берётся он
    /// от extension.
    Row(Fields),
    /// Значение записи: `{ x = a, y = b }`.
    ///
    /// Поля хранятся в порядке типа, а не написания: порядок значим, и
    /// приводит к нему проверка.
    Object(Rc<[(Name, Rc<Term>)]>),
    /// Проекция поля: `e.x`.
    Project(Rc<Term>, Name),
    /// Метапеременная терма - дырка, которую заполняет вывод (§4.1).
    ///
    /// Замкнута: зависимость от контекста выражается **применением** к его
    /// связываниям, а не хранится внутри. Так дырка остаётся термом, который
    /// можно подставить куда угодно, а решением оказывается замкнутая цепочка
    /// лямбд - см. [`Metas::fresh_term`](crate::meta::Metas::fresh_term).
    ///
    /// В том, что сохраняется надолго - в типах и телах определений, - не
    /// встречается: проверка определения отвергает остаточные дырки.
    Meta(TermMeta),
}

/// Поля с подставленными аргументами уровня.
fn substituted(fields: &Fields, arguments: &[Level]) -> Fields {
    Fields {
        fields: fields
            .iter()
            .map(|field| Field {
                name: Rc::clone(&field.name),
                mult: field.mult,
                ty: Rc::new(field.ty.substitute_levels(arguments)),
            })
            .collect(),
        tail: fields
            .tail
            .as_ref()
            .map(|it| Rc::new(it.substitute_levels(arguments))),
    }
}

/// Поля вместе с хвостом: `{ x : A, y : B | r }`.
///
/// Отдельная структура, а не два поля варианта, потому что поля и хвост
/// ходят вместе всюду - и в типе записи, и в ряде. [`Deref`] до среза полей
/// даёт обходам читать их как раньше: хвост спрашивают только те, кому он
/// нужен.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fields {
    /// Поля в написанном порядке.
    pub fields: Rc<[Field]>,
    /// Хвост-row, если запись открыта.
    pub tail: Option<Rc<Term>>,
}

impl Fields {
    /// Закрытая запись: полей столько, сколько написано.
    #[must_use]
    pub fn closed(fields: Rc<[Field]>) -> Self {
        Self { fields, tail: None }
    }

    /// Открыта ли она хвостом.
    #[must_use]
    pub fn is_open(&self) -> bool {
        self.tail.is_some()
    }
}

/// Читать поля как срез удобно, и на это [`Deref`] и заведён. **Строить так
/// нельзя:** `From<Vec<Field>>` и `FromIterator` отсюда убраны намеренно.
/// Пересобранный список полей, отданный в `.into()`, закрывал бы запись
/// молча - и закрывал: за один срез это случилось шесть раз, каждый раз в
/// новом проходе. Пусть тот, кто собирает, скажет про хвост вслух.
impl std::ops::Deref for Fields {
    type Target = [Field];

    fn deref(&self) -> &Self::Target {
        &self.fields
    }
}

/// Поле записи: имя, кратность и тип.
///
/// Кратность - как у поля конструктора (§4.1): запись кладёт значение однажды.
/// Тип живёт **под предыдущими полями** телескопа, поэтому индексы де Брёйна в
/// нём отсчитываются от них: `{ len : Nat, data : Vect a len }` читает `len`
/// как `#0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    /// Имя поля - им же идёт проекция.
    pub name: Name,
    /// Кратность: сколько раз конструирование расходует значение.
    pub mult: Mult,
    /// Тип поля, под предыдущими полями.
    pub ty: Rc<Term>,
}

/// Метапеременная терма.
///
/// Живёт в [`Metas`](crate::meta::Metas) вместе с уровневыми и делит с ними
/// счётчик: `?7` называет ровно одну дырку, какого бы сорта она ни была.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermMeta(pub u32);

/// Разбор значения индуктивного типа по конструктору (§9 Фаза 1).
///
/// **Собственных связываний узел не вводит.** И мотив, и ветви - обычные термы
/// функционального типа: мотив ждёт индексы и само разбираемое значение и
/// выдаёт тип результата, ветвь ждёт поля своего конструктора. Из-за этого
/// `case` не участвует в сдвигах индексов вовсе, а η-правило и проверка
/// кратностей достаются ему от правила лямбды даром - ветвь проверяется
/// ровно как функция от полей.
///
/// Мотив обязателен: без него `case` не может быть зависимым, а тип результата
/// брался бы из режима проверки, и тогда `case` перестал бы синтезировать
/// собственный тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Case {
    /// Индуктивный тип, по которому идёт разбор.
    pub data: Name,
    /// Аргументы уровня этого типа.
    pub levels: Rc<[Level]>,
    /// Сколько первых аргументов конструктора - параметры.
    ///
    /// Ветвь их не получает: они определены типом разбираемого значения, а не
    /// выбором конструктора. Число дублирует сигнатуру затем, чтобы
    /// [`crate::eval`] обходился без неё; проверка типов сверяет.
    pub params: u32,
    /// Кратность, с которой разбор потребляет разбираемое, - `r` из §3.3.
    ///
    /// Стоит на узле по той же причине, что и число параметров: взять её
    /// неоткуда. У применения кратность аргумента написана в `Pi`, а у разбора
    /// типа, из которого её достать, нет вовсе.
    ///
    /// На неё умножается вектор использований разбираемого, и на неё же -
    /// кратности полей в типе ветви. Отсюда три случая даром: стёртое поле
    /// остаётся стёртым, ω-поле неограниченным даже при линейном разборе, а
    /// линейное поле линейно ровно тогда, когда линеен сам разбор.
    ///
    /// `0` здесь незаконна и отвергается проверкой: разбор смотрит на
    /// значение, то есть потребляет его хотя бы однажды.
    pub consumed: Mult,
    /// Что разбирается.
    pub scrutinee: Rc<Term>,
    /// Мотив: `(0 i⃗ : I) -> (0 x : D levels params i⃗) -> Type ℓ`.
    pub motive: Rc<Term>,
    /// Ветви в порядке объявления конструкторов.
    pub branches: Vec<Branch>,
}

/// Чем `Pi` ограничивает аргумент: сколько раз и кто его пишет.
///
/// Обе части - **часть типа**, и обе сравниваются конвертируемостью (§3.2,
/// §4.1). Имя в связывание не входит: оно только для печати, а два байта
/// рядом с толстым `Rc<str>` стоили бы восьми - `Name` выравнивает структуру
/// по слову, и `Term` вырос бы на каждом узле.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binder {
    /// Сколько раз функция вправе израсходовать аргумент.
    pub mult: Mult,
    /// Пишется он в месте вызова или выводится.
    pub visibility: Visibility,
}

impl Binder {
    /// Обычное связывание: аргумент пишется.
    #[must_use]
    pub const fn explicit(mult: Mult) -> Self {
        Self {
            mult,
            visibility: Visibility::Explicit,
        }
    }

    /// Выводимое связывание: `{q x : A} -> …`.
    #[must_use]
    pub const fn implicit(mult: Mult) -> Self {
        Self {
            mult,
            visibility: Visibility::Implicit,
        }
    }
}

/// Ветвь разбора - функция от полей конструктора.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branch {
    /// Конструктор, который она разбирает.
    pub constructor: Name,
    /// Тело: функция от полей, идущих после параметров.
    pub body: Rc<Term>,
}

impl Term {
    /// Переменная по индексу.
    #[must_use]
    pub fn var(index: u32) -> Self {
        Self::Var(Index(index))
    }

    /// `Type n`.
    #[must_use]
    pub fn universe(level: u32) -> Self {
        Self::Universe(Level::number(level))
    }

    /// Применение к нескольким аргументам, левоассоциативно.
    #[must_use]
    pub fn apply(self, arguments: impl IntoIterator<Item = Self>) -> Self {
        arguments.into_iter().fold(self, |callee, argument| {
            Self::App(Rc::new(callee), Rc::new(argument))
        })
    }

    /// Ссылка на определение без параметров уровня.
    #[must_use]
    pub fn constant(name: &str) -> Self {
        Self::Const(name.into(), Rc::from([]))
    }

    /// Подставляет аргументы вместо параметров уровня по всему терму.
    ///
    /// Так тип определения инстанцируется в месте использования.
    ///
    /// Пустой список - тождество, и выход здесь ранний: подстановка стоит на
    /// двух горячих путях (тип определения на каждом [`Self::Const`] в
    /// [`crate::check::infer`], тело на каждом δ-развороте), а у подавляющего
    /// большинства определений параметров уровня нет вовсе. Без выхода терм
    /// пересобирался бы целиком, чтобы получиться прежним.
    #[must_use]
    pub fn substitute_levels(&self, arguments: &[Level]) -> Self {
        if arguments.is_empty() {
            return self.clone();
        }
        let recur = |term: &Rc<Self>| Rc::new(term.substitute_levels(arguments));
        match self {
            Self::Var(_) | Self::Meta(_) => self.clone(),
            Self::Universe(level) => Self::Universe(level.substitute(arguments)),
            Self::RowKind(level) => Self::RowKind(level.substitute(arguments)),
            Self::Lam(mult, name, body) => Self::Lam(*mult, Rc::clone(name), recur(body)),
            Self::App(callee, argument) => Self::App(recur(callee), recur(argument)),
            Self::Pi(binder, name, domain, row, codomain) => Self::Pi(
                *binder,
                Rc::clone(name),
                recur(domain),
                row.map(|argument| argument.substitute_levels(arguments)),
                recur(codomain),
            ),
            Self::Let(mult, name, ty, value, body) => {
                Self::Let(*mult, Rc::clone(name), recur(ty), recur(value), recur(body))
            }
            Self::Const(name, levels) => Self::Const(
                Rc::clone(name),
                levels
                    .iter()
                    .map(|level| level.substitute(arguments))
                    .collect(),
            ),
            Self::Record(fields) => Self::Record(substituted(fields, arguments)),
            Self::Row(fields) => Self::Row(substituted(fields, arguments)),
            Self::Object(fields) => Self::Object(
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Self::Project(record, name) => Self::Project(recur(record), Rc::clone(name)),
            Self::Case(case) => Self::Case(Rc::new(Case {
                data: Rc::clone(&case.data),
                levels: case
                    .levels
                    .iter()
                    .map(|level| level.substitute(arguments))
                    .collect(),
                params: case.params,
                consumed: case.consumed,
                scrutinee: recur(&case.scrutinee),
                motive: recur(&case.motive),
                branches: case
                    .branches
                    .iter()
                    .map(|branch| Branch {
                        constructor: Rc::clone(&branch.constructor),
                        body: recur(&branch.body),
                    })
                    .collect(),
            })),
        }
    }

    /// Наибольший индекс параметра уровня, встречающийся в терме.
    #[must_use]
    pub fn max_level_var(&self) -> Option<u32> {
        let join = |a: Option<u32>, b: Option<u32>| match (a, b) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (found, None) | (None, found) => found,
        };
        match self {
            Self::Var(_) | Self::Meta(_) => None,
            Self::Universe(level) | Self::RowKind(level) => level.max_var(),
            Self::Lam(_, _, body) => body.max_level_var(),
            Self::App(callee, argument) => join(callee.max_level_var(), argument.max_level_var()),
            Self::Pi(_, _, domain, row, codomain) => {
                row.labels().iter().flat_map(|label| &label.arguments).fold(
                    join(domain.max_level_var(), codomain.max_level_var()),
                    |found, argument| join(found, argument.max_level_var()),
                )
            }
            Self::Record(fields) | Self::Row(fields) => fields
                .iter()
                .fold(None, |found, field| join(found, field.ty.max_level_var()))
                .max(fields.tail.as_ref().and_then(|it| it.max_level_var())),
            Self::Object(fields) => fields
                .iter()
                .fold(None, |found, (_, value)| join(found, value.max_level_var())),
            Self::Project(record, _) => record.max_level_var(),
            Self::Let(_, _, ty, value, body) => join(
                ty.max_level_var(),
                join(value.max_level_var(), body.max_level_var()),
            ),
            Self::Const(_, levels) => levels
                .iter()
                .fold(None, |found, level| join(found, level.max_var())),
            Self::Case(case) => {
                let levels = case
                    .levels
                    .iter()
                    .fold(None, |found, level| join(found, level.max_var()));
                let branches = case.branches.iter().fold(None, |found, branch| {
                    join(found, branch.body.max_level_var())
                });
                join(
                    join(levels, branches),
                    join(case.scrutinee.max_level_var(), case.motive.max_level_var()),
                )
            }
        }
    }
}

/// Разбирает применение на голову и аргументы.
///
/// Живёт рядом с [`Term`], а не у пользователей: на неё смотрят и проверка
/// позитивности ([`crate::check`]), и поиск рекурсивных вызовов
/// ([`crate::total`]), и «голова» у них обязана значить одно и то же. Двух
/// копий здесь уже было достаточно, чтобы правка в одной оставила другую
/// прежней, а компилятор бы этого не заметил.
pub(crate) fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut current = term;
    while let Term::App(callee, argument) = current {
        arguments.push(argument.as_ref());
        current = callee;
    }
    arguments.reverse();
    (current, arguments)
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Имя не печатается: одно и то же имя может быть у разных
            // связываний, а индекс однозначен.
            Self::Var(Index(index)) => write!(f, "#{index}"),
            Self::Meta(TermMeta(name)) => write!(f, "?{name}"),
            Self::Universe(level) => write!(f, "Type {level}"),
            Self::Lam(mult, name, body) => write!(f, "\\({mult} {name}) -> {body}"),
            Self::App(callee, argument) => {
                write!(f, "{} {}", Callee(callee), Atom(argument))
            }
            Self::RowKind(level) => write!(f, "Row {level}"),
            Self::Record(fields) | Self::Row(fields) => {
                let written: Vec<String> = fields
                    .iter()
                    .map(|field| format!("{} {} : {}", field.mult, field.name, field.ty))
                    .collect();
                // Хвост отделяется `|`, а не запятой: он не поле, и написан в
                // §4.2 так же. Запятая перед ним читалась бы как пустое поле.
                let tail = match &fields.tail {
                    Some(tail) if written.is_empty() => format!("| {tail}"),
                    Some(tail) => format!(" | {tail}"),
                    None => String::new(),
                };
                write!(f, "{{{}{tail}}}", written.join(", "))
            }
            Self::Object(fields) => {
                let written: Vec<String> = fields
                    .iter()
                    .map(|(name, value)| format!("{name} = {value}"))
                    .collect();
                write!(f, "{{{}}}", written.join(", "))
            }
            Self::Project(record, name) => write!(f, "{}.{name}", Atom(record)),
            Self::Pi(binder, name, domain, row, codomain) => {
                // Вид скобок несёт связывание: у выводимого они фигурные.
                let (open, close) = binder.visibility.brackets();
                let mult = binder.mult;
                write!(
                    f,
                    "{open}{mult} {name} : {domain}{close} -> {row}{codomain}"
                )
            }
            Self::Let(mult, name, ty, value, body) => {
                write!(f, "let {mult} {name} : {ty} = {value} in {body}")
            }
            Self::Const(name, levels) if levels.is_empty() => write!(f, "{name}"),
            Self::Const(name, levels) => {
                let printed: Vec<String> = levels.iter().map(ToString::to_string).collect();
                write!(f, "{name}{{{}}}", printed.join(", "))
            }
            // Имя семейства и аргументы уровня печатаются: по конструкторам
            // ветвей они восстанавливаются не всегда - у разбора пустого
            // семейства ветвей нет вовсе, - а производное равенство их
            // различает. Без них два разных разбора печатались одинаково, и
            // `Mismatch` показывал две дословно совпадающие строки.
            Self::Case(case) => {
                let branches: Vec<String> = case
                    .branches
                    .iter()
                    .map(|branch| format!("{} => {}", branch.constructor, branch.body))
                    .collect();
                write!(f, "case {} : {}", Atom(&case.scrutinee), case.data)?;
                if !case.levels.is_empty() {
                    let levels: Vec<String> = case.levels.iter().map(ToString::to_string).collect();
                    write!(f, "{{{}}}", levels.join(", "))?;
                }
                write!(
                    f,
                    " return {} of {{{}}}",
                    Atom(&case.motive),
                    branches.join("; ")
                )
            }
        }
    }
}

/// Позиция функции: применение слева от применения скобок не требует.
struct Callee<'a>(&'a Term);

impl fmt::Display for Callee<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::Const(..)
            | Term::App(..) => {
                write!(f, "{}", self.0)
            }
            other => write!(f, "({other})"),
        }
    }
}

/// Позиция аргумента: всё составное берётся в скобки.
struct Atom<'a>(&'a Term);

impl fmt::Display for Atom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Term::Var(_) | Term::Universe(_) | Term::RowKind(_) | Term::Const(..) => {
                write!(f, "{}", self.0)
            }
            other => write!(f, "({other})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::row::{Label, Row};
    use crate::term::Binder;

    use super::Term;
    use crate::mult::Mult;

    #[test]
    fn application_prints_left_associatively() {
        let term = Term::var(0).apply([Term::var(1), Term::var(2)]);
        assert_eq!(term.to_string(), "#0 #1 #2");
    }

    #[test]
    fn arguments_are_parenthesised() {
        let identity = Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)));
        let term = Term::var(0).apply([identity]);
        assert_eq!(term.to_string(), "#0 (\\(ω x) -> #0)");
    }

    #[test]
    fn a_case_prints_the_family_it_scrutinises() {
        use crate::level::Level;

        // Два разбора по разным пустым семействам: ветвей нет, восстановить имя
        // не по чему, а производное равенство их различает. Печататься одинаково
        // они не должны - иначе `Mismatch` показывает две совпадающие строки.
        let empty = |data: &str, levels: &[Level]| {
            Term::Case(Rc::new(super::Case {
                data: data.into(),
                levels: levels.iter().cloned().collect(),
                params: 0,
                consumed: Mult::One,
                scrutinee: Rc::new(Term::var(0)),
                motive: Rc::new(Term::Lam(
                    Mult::Zero,
                    "x".into(),
                    Rc::new(Term::universe(0)),
                )),
                branches: Vec::new(),
            }))
        };
        assert_ne!(
            empty("Void", &[]).to_string(),
            empty("Empty", &[]).to_string()
        );
        assert_ne!(
            empty("F", &[Level::Zero]).to_string(),
            empty("F", &[Level::number(1)]).to_string(),
            "аргументы уровня тоже различают разборы"
        );
        assert_eq!(
            empty("Void", &[]).to_string(),
            "case #0 : Void return (\\(0 x) -> Type 0) of {}"
        );
    }

    #[test]
    fn substituting_nothing_changes_nothing() {
        use crate::level::{Level, LevelVar};

        // Ранний выход при пустом списке обязан совпадать с тем, что делает
        // общий путь: переменная вне списка аргументов остаётся собой.
        let term = Term::Pi(
            Binder::explicit(Mult::Zero),
            "a".into(),
            Rc::new(Term::Universe(Level::Var(LevelVar(0)))),
            Row::empty(),
            Rc::new(Term::Universe(Level::Var(LevelVar(1)).succ())),
        );
        assert_eq!(term.substitute_levels(&[]), term);
    }

    #[test]
    fn pi_shows_its_multiplicity() {
        let pi = Term::Pi(
            Binder::explicit(Mult::Zero),
            "a".into(),
            Rc::new(Term::universe(0)),
            Row::empty(),
            Rc::new(Term::var(0)),
        );
        assert_eq!(pi.to_string(), "(0 a : Type 0) -> #0");
    }

    #[test]
    fn pi_shows_its_row_and_hides_the_empty_one() {
        // Пустая row не печатается вовсе: её отсутствие и означает чистую
        // стрелку, а печатать `{}` значило бы засорить каждый тип в языке,
        // где эффектов ещё нет ни у одной функции.
        let with = |row| {
            Term::Pi(
                Binder::explicit(Mult::Many),
                "a".into(),
                Rc::new(Term::universe(0)),
                row,
                Rc::new(Term::var(0)),
            )
            .to_string()
        };
        assert_eq!(with(Row::empty()), "(ω a : Type 0) -> #0");
        assert_eq!(
            with(Row::new([
                Label {
                    name: "State".into(),
                    arguments: vec![Term::constant("Int")],
                },
                Label {
                    name: "IO".into(),
                    arguments: Vec::new(),
                },
            ])),
            // Группы упорядочены по имени, а не по написанию (§3.4).
            "(ω a : Type 0) -> {IO, State Int} #0"
        );
    }
}
