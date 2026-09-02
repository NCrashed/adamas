//! AST поверхностного языка (§4).
//!
//! Дерево типизированное и со спанами; комментарии в нём не лежат - они
//! отдельной таблицей ([`crate::token::Comment`]), решение записано в decision
//! log 2026-08-25.
//!
//! Что покрывает спан узла, сказано один раз - в заголовке [`crate::parser`],
//! раздел «Спаны». Здесь у каждого поля `span` записано только то, что из
//! общего правила не выводится.
//!
//! # Что дерево не решает
//!
//! **Имя не разделено на переменную и конструктор.** В клаузе `map f Nil` обе
//! лексемы - [`PatternKind::Name`], и какая из них связывает, а какая
//! разбирает, решает элаборация по сигнатуре. Парсер этого знать не может:
//! таблица определений собирается позже, а угадывать по регистру буквы -
//! отдельное решение, которого §4 не принимала.
//!
//! **Фикситеты не расставлены.** `a + b * c` остаётся плоской цепочкой
//! ([`Chain`]): `infixl 6 +` объявляется в prelude (§4.4), то есть в программе,
//! и до её разбора таблица неизвестна. Так же устроен GHC, где скобки
//! расставляет renamer, а не парсер.
//!
//! **Кратность не подставлена по умолчанию.** Отсутствие аннотации -
//! [`None`], а не «ω»: умолчание зависит от позиции (параметр функции - ω,
//! поле конструктора - 1, §4.1), и знает о ней элаборация.

use std::fmt;
use std::rc::Rc;

use adamas_core::source::Span;

/// Текст имени. `Rc` - потому что элаборация отдаёт его ядру, где имя тоже
/// `Rc<str>`, и копировать посимвольно там незачем.
pub type Symbol = Rc<str>;

/// Имя вместе с местом, где оно написано.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name {
    /// Текст.
    pub text: Symbol,
    /// Где написано.
    pub span: Span,
}

/// Кратность из §3.2, как она написана в исходнике.
///
/// Собственная, а не [`adamas_core::mult::Mult`]: у поверхностной кратности
/// есть спан и есть состояние «не написана», которого у ядерной нет и быть не
/// должно.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mult {
    /// `0` - стёртая.
    Zero,
    /// `1` - линейная.
    One,
    /// `ω` - неограниченная.
    Many,
}

impl fmt::Display for Mult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::Many => "ω",
        })
    }
}

/// Написанная кратность вместе с местом.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultAnn {
    /// Какая.
    pub mult: Mult,
    /// Сама кратность, без имён за ней.
    pub span: Span,
}

/// Видимость параметра: круглые скобки против фигурных (§4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    /// `(x : A)` - аргумент пишется в месте вызова.
    Explicit,
    /// `{x : A}` - аргумент выводится.
    Implicit,
}

/// Группа связываний с общим типом: `(0 n m : Nat)`.
///
/// Имён несколько, потому что §4.1 пишет `{ℓ ℓ' : Level}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    /// Круглые или фигурные скобки.
    pub visibility: Visibility,
    /// Кратность, если написана.
    pub mult: Option<MultAnn>,
    /// Имена, связываемые этой группой.
    pub names: Vec<Name>,
    /// Общий тип. `None` - тип не написан: так пишутся параметры семейства
    /// (`data Pair a b where`, §4.1), и подставляет его элаборация.
    pub ty: Option<Expr>,
    /// Умолчание хвостового параметра: `(b = a)`, `(idx = UInt32)` (§4.1).
    ///
    /// Пишется только у параметра - типового конструктора, класса, алиаса, - и
    /// только у одного имени: группа `(a b = x)` связывает двоих, а умолчание
    /// у них одно на двоих смысла не имеет. Термовых умолчаний нет вовсе, и
    /// грамматика их не принимает: в позиции типа `=` за связыванием не стоит.
    pub default: Option<Expr>,
    /// Скобки целиком, или само имя у параметра без скобок.
    pub span: Span,
}

/// Метка эффекта, как она написана: `State Int`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectLabel {
    /// Имя конструктора метки.
    pub name: Name,
    /// Аргументы, к которым он применён.
    pub arguments: Vec<Expr>,
    /// Метка целиком.
    pub span: Span,
}

/// Вид литерала. Класс преобразования выбирается по нему же (§4.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitKind {
    /// `42` - `FromNat`.
    Nat,
    /// `-42` - `FromInt`.
    Int,
    /// `3.14`, `-1e9` - `FromFloat`.
    Float,
    /// `"..."`.
    Str,
}

/// Литерал. Текст хранится как написан (`0xff` не превращается в `255`):
/// раскодировка - работа элаборации, а печать обязана вернуть исходное
/// написание.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lit {
    /// Вид.
    pub kind: LitKind,
    /// Текст вместе со знаком и кавычками. Пробел между знаком и числом в
    /// текст не попадает, в спан - попадает: `- 42` пишется криво, но читается
    /// как число.
    pub text: Symbol,
    /// Литерал вместе со знаком.
    pub span: Span,
}

/// Цепочка операторов без расставленных скобок.
///
/// `a + b * c` - это `head = a`, `tail = [(+, b), (*, c)]`. Скобки расставит
/// тот, кто узнает фикситеты, - см. заголовок модуля.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chain {
    /// Первый операнд.
    pub head: Box<Expr>,
    /// Оператор и следующий за ним операнд.
    pub tail: Vec<(Name, Expr)>,
}

/// Выражение. Типы и термы - одна синтаксическая категория: язык зависимый,
/// и `Vect (n + 1) a` в позиции типа устроено ровно как выражение.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    /// Что за выражение.
    pub kind: ExprKind,
    /// Выражение целиком - вместе со скобками, если они написаны. Узла у
    /// скобок нет, а спан их помнит: на них указывает диагностика.
    pub span: Span,
}

/// Разновидность выражения.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// Имя: переменная, конструктор или определение - решает элаборация.
    Name(Name),
    /// Литерал.
    Lit(Lit),
    /// `_` - дырка, которую заполняет вывод.
    Hole,
    /// Применение: `f x`.
    App(Box<Expr>, Box<Expr>),
    /// Применение типа: `runExcept @IOError prog` (§4.1).
    TypeApp(Box<Expr>, Box<Expr>),
    /// `using productMonoid expr` - именованный инстанс в области видимости
    /// (§4.3).
    ///
    /// Область - всё, что правее: применение связывает теснее, поэтому
    /// `using p f x` читается как `using p (f x)`.
    Using {
        /// Имя инстанса.
        name: Name,
        /// Что под ним элаборируется.
        body: Box<Expr>,
    },
    /// `\x y -> body`.
    Lam {
        /// Параметры.
        params: Vec<LamParam>,
        /// Тело.
        body: Box<Expr>,
    },
    /// Зависимая функция: `(0 n : Nat) (a : Type) -> body`.
    Pi {
        /// Группы связываний до стрелки.
        binders: Vec<Binder>,
        /// Кодомен.
        codomain: Box<Expr>,
    },
    /// Независимая функция: `A -> B`.
    Arrow(Box<Expr>, Box<Expr>),
    /// Row эффектов перед типом: `A -> {State Int} B` (§3.4).
    ///
    /// Узел стоит на месте **кодомена**, а не самой стрелки: так `A -> {ε} B`
    /// и `{ε} A` разбираются одной формой, а различает их то, куда она попала.
    /// Элаборация снимает её со стрелки в поле `Pi`; написанная сама по себе,
    /// она есть нульместная функция (§3.4), и та ждёт единицы из prelude.
    Effectful {
        /// Метки: имя конструктора и его аргументы.
        labels: Vec<EffectLabel>,
        /// Хвост, если написан: `{IO | e}`.
        tail: Option<Name>,
        /// Что стоит за row.
        body: Box<Expr>,
    },
    /// Блок операторов - тело определения или `let` (§4.1).
    Block(Block),
    /// `if c then a else b`.
    If {
        /// Условие.
        cond: Box<Expr>,
        /// Ветка «да».
        then_branch: Box<Expr>,
        /// Ветка «нет».
        else_branch: Box<Expr>,
    },
    /// `case e of` с ветками в блоке.
    Case {
        /// Что разбирается.
        scrutinee: Box<Expr>,
        /// Ветки в порядке написания: побеждает первая совпавшая.
        alts: Vec<Alt>,
    },
    /// Тип записи: `{ x : A, y : B }` (§4.2).
    ///
    /// Порядок написания сохраняется: поле вправе ссылаться на предыдущие, и
    /// сортировка сломала бы зависимость. Решение от 2026-08-29: запись с
    /// зависимостью между полями закрыта.
    RecordType(Vec<RecordField>, Option<Name>),
    /// Значение записи: `{ x = a, y }`, где второе - punning для `y = y`.
    Record(Vec<(Name, Expr)>),
    /// Проекция поля: `p.x`.
    Project(Box<Expr>, Name),
    /// Обновление или расширение: `{ p | x = v, y = w }` (§4.2).
    ///
    /// Одна форма на обе операции: есть ли поле у исходной записи, решает не
    /// автор, а её тип. Возвращаемый тип отражает результат.
    Update(Box<Expr>, Vec<(Name, Expr)>),
    /// Кортеж `(a, b)`; пустой - `()`.
    Tuple(Vec<Expr>),
    /// Список `[a, b, c]`.
    List(Vec<Expr>),
    /// Цепочка операторов.
    Chain(Chain),
}

/// Поле в типе записи: имя и тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordField {
    /// Имя поля.
    pub name: Name,
    /// Написанный тип.
    pub ty: Expr,
}

/// Параметр лямбды.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LamParam {
    /// Что за параметр.
    pub kind: LamParamKind,
    /// Параметр целиком.
    pub span: Span,
}

/// Разновидность параметра лямбды.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LamParamKind {
    /// `\x -> e`, `\_ -> e`, `\() -> e` (§4.1).
    Pattern(Pattern),
    /// `\(0 x : A) -> e` - с типом и кратностью.
    Binder(Binder),
}

/// Ветка `case`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alt {
    /// Паттерн ветки.
    pub pattern: Pattern,
    /// Тело.
    pub body: Expr,
    /// Ветка целиком.
    pub span: Span,
}

/// Блок операторов: тело определения, тело `let`, тело ветки.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    /// Операторы в порядке написания.
    pub stmts: Vec<Stmt>,
    /// От первого оператора до последнего: границы блока виртуальны, и в спан
    /// они не входят.
    pub span: Span,
}

/// Оператор блока.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    /// Что за оператор.
    pub kind: StmtKind,
    /// Оператор целиком.
    pub span: Span,
}

/// Разновидность оператора.
///
/// Do-нотации нет и не будет: строгий порядок вычислений (§3.1) плюс эффекты в
/// типе делают цепочку `let`-биндингов тем же самым (§4.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// `let` со своим блоком связываний.
    Let(Vec<Binding>),
    /// Выражение. Последнее в блоке - значение блока.
    Expr(Expr),
}

/// Связывание внутри `let`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// Кратность, если написана: `let 1 h = openFile path` (§4.1).
    pub mult: Option<MultAnn>,
    /// Имя.
    pub name: Name,
    /// Параметры, если это локальная функция.
    pub params: Vec<Pattern>,
    /// Тип, если написан.
    pub ty: Option<Expr>,
    /// Тело.
    pub body: Expr,
    /// Связывание целиком.
    pub span: Span,
}

/// Паттерн.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern {
    /// Что за паттерн.
    pub kind: PatternKind,
    /// Паттерн целиком - вместе со скобками, если они написаны.
    pub span: Span,
}

/// Разновидность паттерна.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternKind {
    /// Имя: связывание или конструктор без полей - решает элаборация.
    Name(Name),
    /// `_` - связывание без имени.
    Wildcard,
    /// Литерал в паттерне.
    Lit(Lit),
    /// Конструктор с полями: `Cons x xs`.
    App {
        /// Имя конструктора.
        head: Name,
        /// Поля.
        fields: Vec<Pattern>,
    },
    /// Кортеж `(x, y)`; пустой - `()`.
    Tuple(Vec<Pattern>),
}

/// Клауза определения: паттерны на аргументы, тело и локальные определения.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    /// По паттерну на аргумент.
    pub patterns: Vec<Pattern>,
    /// Тело.
    pub body: Expr,
    /// Блок `where`, если он есть.
    pub wheres: Vec<Decl>,
    /// Клауза целиком, вместе с блоком `where`.
    pub span: Span,
}

/// Объявление верхнего уровня.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    /// Что за объявление.
    pub kind: DeclKind,
    /// Объявление целиком: `data` - по последний конструктор, `resource` - по
    /// последний член, группа клауз - по последнюю клаузу.
    pub span: Span,
}

/// Разновидность объявления.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    /// `type Point = { x : Nat }` - алиас типа (§4.2).
    ///
    /// Не nominal type: `Point` и написанное справа полностью взаимозаменяемы,
    /// а различает их только имя в сообщениях. Отдельная форма нужна затем,
    /// что написать её сигнатурой нечем: `Point : Type` обобщается в `∀u`, а
    /// конкретный универсум в поверхностном языке не пишется.
    Alias {
        /// Имя алиаса.
        name: Name,
        /// Параметры: `type Twice a = a -> a`, `type Bag (a : Type)`.
        ///
        /// Пишутся теми же формами, что у семейства - голым именем или
        /// связыванием в скобках, - и означают то же: алиас с параметрами есть
        /// типовая функция, а абстрактный член с параметрами - её объявление.
        params: Vec<Binder>,
        /// Что он называет. `None` - написано `type T` без уравнения: так
        /// сигнатура модуля объявляет **абстрактный** типовой член (§4.8), и
        /// больше нигде эта форма не законна.
        body: Option<Expr>,
    },

    /// Сигнатура: `map : (a -> b) -> Vect n a -> Vect n b`.
    Signature {
        /// Имя.
        name: Name,
        /// Тип.
        ty: Expr,
        /// Атрибуты, написанные перед ней: `@total` и прочие (§4.7).
        ///
        /// Стоят при сигнатуре, а не при клаузах: обязательство берёт на
        /// себя определение целиком, а объявляет его сигнатура.
        attributes: Vec<Name>,
    },
    /// Клаузы одного определения, идущие подряд.
    Clauses {
        /// Имя.
        name: Name,
        /// Клаузы в порядке написания.
        clauses: Vec<Clause>,
    },
    /// Индуктивный тип: `data Vect : … where …`.
    Data(Data),
    /// Модуль или его сигнатура: `module M where …` (§4.8).
    Module(ModuleDecl),
    /// Класс или инстанс: `class Ord a where …` (§4.1, §3.5).
    Class(ClassDecl),
    /// Группа взаимной рекурсии: `mutual` и блок объявлений (§4.8).
    ///
    /// Отдельной структуры не заводит: члены - обычные объявления, а группой
    /// их делает то, что объявляются они разом (§10 вопрос 50).
    Mutual(Vec<Decl>),
    /// Ресурсный тип: `resource File where drop h = …` (§3.3).
    Resource(Resource),
}

/// Класс или его инстанс.
///
/// Одна структура на обе формы: по §3.5 класс есть module type плюс режим
/// разрешения, а инстанс - его module value, и различает их `instance`.
/// Голова написана применением - `Ord a` у класса, `Ord Int` у инстанса, -
/// потому что разбирается она одинаково, а смысл аргументу придаёт форма:
/// у класса это связываемый параметр, у инстанса написанный тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl {
    /// Маркер `coherent` перед `class` (§3.5): запрос на глобальную
    /// уникальность инстансов. У инстанса всегда `false` - маркер ставится
    /// классу, а условия пригодности проверяются на каждом его инстансе.
    pub coherent: bool,
    /// `instance Ord Int where` против `class Ord a where`.
    pub instance: bool,
    /// Имя инстанса: `instance productMonoid : Monoid Int where` (§4.3).
    ///
    /// `None` - анонимный. Имя нужно тем инстансам, которых на один тип
    /// несколько: выбрать между ними автоматика не вправе.
    pub name: Option<Name>,
    /// Голова: имя класса у класса, применение целиком у инстанса.
    pub head: Expr,
    /// Параметры класса: `class Mul a (b = a) where …` (§4.1).
    ///
    /// У инстанса пуст: там написана голова целиком, и параметров у неё нет -
    /// есть аргументы. Разбираются те же формы, что у семейства, вместе с
    /// умолчаниями хвостовых.
    pub params: Vec<Binder>,
    /// Суперклассы: `class Ord a when Eqv a where …` (§4.1).
    ///
    /// Словарь суперкласса - поле словаря класса, разряжаемое в точке
    /// объявления инстанса (§3.5). У инстанса этот список пуст: контекст ему
    /// пишется головой, а не `when`.
    pub superclasses: Vec<Expr>,
    /// Члены: сигнатуры методов у класса, клаузы у инстанса.
    pub members: Vec<Decl>,
}

/// Модуль или сигнатура модуля.
///
/// Одна структура на обе формы: различает их `signature`, а всё остальное -
/// имя, аннотация и члены - у них общее. Сигнатура несёт объявления без
/// реализаций, модуль - с ними, и решает это элаборация, а не разбор.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleDecl {
    /// `module type S where` против `module M where`.
    pub signature: bool,
    /// Имя.
    pub name: Name,
    /// Параметры функтора: `module OrderedMap (Key : Ord) where` (§4.8).
    /// Пусто - обычный модуль.
    pub params: Vec<Binder>,
    /// Тело, написанное выражением: `module IntMap = OrderedMap IntOrd`.
    /// `None` - тело написано блоком членов.
    pub body: Option<Expr>,
    /// Аннотация сигнатурой: `module IntOrd : Ord where`. У самой сигнатуры её
    /// не бывает.
    pub ascription: Option<Expr>,
    /// Запечатывает ли аннотация: `:>` против `:` (§3.5).
    ///
    /// Проверка и сокрытие - разные операции: первая оставляет представление
    /// видимым, вторая делает определение непрозрачным. Без аннотации
    /// запечатывать нечем, и тогда здесь `false`.
    pub sealed: bool,
    /// Члены в порядке написания: порядок значим, член видит предыдущих (§4.8).
    pub members: Vec<Decl>,
}

/// Индуктивный тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Data {
    /// Объявлен ли тип уникальным: `unique data Array …` (§3.3).
    ///
    /// Маркер на декларации, а не атрибут в типе: кратность `1` ограничивает
    /// потребление, а не производство, и `1` на параметре не гарантирует
    /// отсутствия других ссылок на значение. Уникальность держится тем, что
    /// ω-связывания такого типа не существует вовсе.
    pub unique: bool,
    /// Имя семейства.
    pub name: Name,
    /// Параметры, написанные до `where`: `data Pair a b where` (§4.1).
    pub params: Vec<Binder>,
    /// Тип-формер, если написан: `data Vect : (0 n : Nat) -> Type -> Type`.
    /// Отсутствует - семейство живёт в `Type` с выведенным уровнем.
    pub kind: Option<Expr>,
    /// Конструкторы: имя и тип каждого. Порядок задаёт порядок ветвей разбора.
    pub constructors: Vec<Constructor>,
}

/// Конструктор индуктивного типа.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    /// Имя.
    pub name: Name,
    /// Тип.
    pub ty: Expr,
    /// Конструктор целиком.
    pub span: Span,
}

/// Ресурсный тип (§3.3): связывания линейны, `drop` вызывается автоматически.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resource {
    /// Имя.
    pub name: Name,
    /// Параметры.
    pub params: Vec<Binder>,
    /// Тело: конструкторы (голые сигнатуры) и `drop` (сигнатура с клаузами).
    /// Различать их - работа элаборации: парсер видит одинаковые объявления и
    /// не знает, какое имя что значит.
    pub members: Vec<Decl>,
}

/// Разобранный файл.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    /// Объявления в порядке написания.
    pub decls: Vec<Decl>,
    /// От первого объявления до последнего - не весь файл: комментарий перед
    /// первым и пустая строка после последнего не принадлежат никому.
    pub span: Span,
}

/// Содержит ли выражение форму, открывающую layout-блок.
///
/// Таких форм две - `case` и блок операторов, - и обе тянутся до строки,
/// начатой левее: где форма кончилась, видно только по отступу. Отсюда два
/// следствия, и спрашивают о них разные места. За такой формой на строке
/// ничего не стоит - это проверяет [`crate::parser`], отвергая `g case … y`.
/// В скобки её не взять - под скобкой layout выключен (§10 вопрос 55), -
/// поэтому [`crate::printer`] их и не ставит, а вместо этого разрывает строку
/// там, где иначе `else` уехал бы внутрь блока.
///
/// Обход циклом, а не спуском: спайн применения разбор набирает циклом,
/// предел вложенности на него не тратится, и рекурсия упёрлась бы в стек.
#[must_use]
pub fn contains_block(expr: &Expr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match &expr.kind {
            ExprKind::Case { .. } | ExprKind::Block(_) => return true,
            ExprKind::Name(_) | ExprKind::Lit(_) | ExprKind::Hole => {}
            ExprKind::Effectful { labels, body, .. } => {
                pending.push(body);
                pending.extend(labels.iter().flat_map(|label| &label.arguments));
            }
            ExprKind::RecordType(fields, _) => pending.extend(fields.iter().map(|it| &it.ty)),
            ExprKind::Record(fields) => pending.extend(fields.iter().map(|(_, it)| it)),
            ExprKind::Project(inner, _) => pending.push(inner),
            ExprKind::Update(base, fields) => {
                pending.push(base);
                pending.extend(fields.iter().map(|(_, it)| it));
            }
            ExprKind::App(left, right)
            | ExprKind::TypeApp(left, right)
            | ExprKind::Arrow(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ExprKind::Lam { body, .. } | ExprKind::Using { body, .. } => pending.push(body),
            ExprKind::Pi { binders, codomain } => {
                pending.extend(binders.iter().filter_map(|binder| binder.ty.as_ref()));
                pending.push(codomain);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                pending.push(cond);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => pending.extend(items),
            ExprKind::Chain(chain) => {
                pending.push(&chain.head);
                pending.extend(chain.tail.iter().map(|(_, operand)| operand));
            }
        }
    }
    false
}

/// Отладочная печать дерева s-выражениями.
///
/// Не путать с обратной печатью, которая появится отдельно: та обязана выдать
/// исходник, который снова разберётся, эта - показать форму дерева. Спаны не
/// печатаются намеренно: снапшот иначе ехал бы от правки пробела в соседней
/// строке.
///
/// Нужна снапшотам и будущему `adamas check --dump-ast`.
#[must_use]
pub fn dump(module: &Module) -> String {
    let mut out = String::new();
    for decl in &module.decls {
        dump_decl(&mut out, decl, 0);
        out.push('\n');
    }
    out
}

/// Отступ и перевод строки перед узлом, который печатается со своей строки.
fn line(out: &mut String, depth: usize) {
    out.push('\n');
    for _ in 0..depth {
        out.push_str("  ");
    }
}

/// Класс или инстанс: `(class (Eqv a) (sig eq …))`.
fn dump_class(out: &mut String, class: &ClassDecl, depth: usize) {
    if class.coherent {
        out.push_str("(coherent ");
    }
    out.push_str(if class.instance {
        "(instance "
    } else {
        "(class "
    });
    if let Some(name) = &class.name {
        out.push_str(&name.text);
        out.push_str(" : ");
    }
    dump_expr(out, &class.head);
    for param in &class.params {
        out.push(' ');
        dump_binder(out, param);
    }
    for superclass in &class.superclasses {
        out.push_str(" when ");
        dump_expr(out, superclass);
    }
    dump_block(out, "", &class.members, depth);
    if class.coherent {
        out.push(')');
    }
}

/// `{State Int | e} A`: `(row ((State Int)) | e A)`.
fn dump_row(out: &mut String, labels: &[EffectLabel], tail: Option<&Name>, body: &Expr) {
    out.push_str("(row (");
    dump_list(out, labels, |out, label| {
        out.push_str(&label.name.text);
        for argument in &label.arguments {
            out.push(' ');
            dump_expr(out, argument);
        }
    });
    out.push(')');
    if let Some(tail) = tail {
        out.push_str(" | ");
        out.push_str(&tail.text);
    }
    out.push(' ');
    dump_expr(out, body);
    out.push(')');
}

/// `\x y -> body`: `(lam (x y) body)`.
fn dump_lambda(out: &mut String, params: &[LamParam], body: &Expr) {
    out.push_str("(lam (");
    dump_list(out, params, |out, param| match &param.kind {
        LamParamKind::Pattern(pattern) => dump_pattern(out, pattern),
        LamParamKind::Binder(binder) => dump_binder(out, binder),
    });
    out.push_str(") ");
    dump_expr(out, body);
    out.push(')');
}

/// `using name expr`: `(using name expr)`.
fn dump_using(out: &mut String, name: &Name, body: &Expr) {
    out.push_str("(using ");
    out.push_str(&name.text);
    out.push(' ');
    dump_expr(out, body);
    out.push(')');
}

/// Модуль или его сигнатура: `(module M : S …)`.
fn dump_module(out: &mut String, module: &ModuleDecl, depth: usize) {
    out.push_str(if module.signature {
        "(module-type "
    } else {
        "(module "
    });
    out.push_str(&module.name.text);
    for param in &module.params {
        out.push(' ');
        dump_binder(out, param);
    }
    if let Some(ascription) = &module.ascription {
        out.push_str(if module.sealed { " :> " } else { " : " });
        dump_expr(out, ascription);
    }
    if let Some(body) = &module.body {
        out.push_str(" = ");
        dump_expr(out, body);
    }
    dump_block(out, "", &module.members, depth);
}

/// Заголовок и вложенные объявления, каждое со своей строки.
fn dump_block(out: &mut String, head: &str, members: &[Decl], depth: usize) {
    out.push_str(head);
    for member in members {
        out.push('\n');
        out.push_str(&"  ".repeat(depth + 1));
        dump_decl(out, member, depth + 1);
    }
    out.push(')');
}

/// Печатает объявление без завершающего перевода строки: где его ставить,
/// решает вызывающий - вложенное объявление продолжается скобкой.
fn dump_decl(out: &mut String, decl: &Decl, depth: usize) {
    match &decl.kind {
        DeclKind::Alias { name, params, body } => {
            out.push_str("(alias ");
            out.push_str(&name.text);
            for param in params {
                out.push(' ');
                dump_binder(out, param);
            }
            if let Some(body) = body {
                out.push(' ');
                dump_expr(out, body);
            }
            out.push(')');
        }
        DeclKind::Class(class) => dump_class(out, class, depth),
        DeclKind::Mutual(members) => dump_block(out, "(mutual", members, depth),
        DeclKind::Module(module) => dump_module(out, module, depth),
        DeclKind::Signature {
            name,
            ty,
            attributes,
        } => {
            out.push_str("(sig ");
            for attribute in attributes {
                out.push('@');
                out.push_str(&attribute.text);
                out.push(' ');
            }
            out.push_str(&name.text);
            out.push(' ');
            dump_expr(out, ty);
            out.push(')');
        }
        DeclKind::Clauses { name, clauses } => {
            out.push_str("(def ");
            out.push_str(&name.text);
            for clause in clauses {
                line(out, depth + 1);
                out.push_str("(clause (");
                dump_list(out, &clause.patterns, dump_pattern);
                out.push_str(") ");
                dump_expr(out, &clause.body);
                for local in &clause.wheres {
                    line(out, depth + 2);
                    out.push_str("(where ");
                    dump_decl(out, local, depth + 2);
                    out.push(')');
                }
                out.push(')');
            }
            out.push(')');
        }
        DeclKind::Data(data) => {
            out.push_str("(data ");
            out.push_str(&data.name.text);
            for param in &data.params {
                out.push(' ');
                dump_binder(out, param);
            }
            if let Some(kind) = &data.kind {
                line(out, depth + 1);
                out.push_str("(kind ");
                dump_expr(out, kind);
                out.push(')');
            }
            for constructor in &data.constructors {
                line(out, depth + 1);
                out.push_str("(ctor ");
                out.push_str(&constructor.name.text);
                out.push(' ');
                dump_expr(out, &constructor.ty);
                out.push(')');
            }
            out.push(')');
        }
        DeclKind::Resource(resource) => {
            out.push_str("(resource ");
            out.push_str(&resource.name.text);
            for param in &resource.params {
                out.push(' ');
                dump_binder(out, param);
            }
            for member in &resource.members {
                line(out, depth + 1);
                dump_decl(out, member, depth + 1);
            }
            out.push(')');
        }
    }
}

/// Печатает элементы через пробел.
fn dump_list<T>(out: &mut String, items: &[T], each: fn(&mut String, &T)) {
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        each(out, item);
    }
}

fn dump_binder(out: &mut String, binder: &Binder) {
    // Параметр, написанный голым именем, так и печатается: скобки вокруг него
    // показывали бы то, чего в исходнике нет.
    if let (Visibility::Explicit, None, None, None, [name]) = (
        binder.visibility,
        binder.mult,
        binder.ty.as_ref(),
        binder.default.as_ref(),
        binder.names.as_slice(),
    ) {
        out.push_str(&name.text);
        return;
    }
    let (open, close) = match binder.visibility {
        Visibility::Explicit => ('(', ')'),
        Visibility::Implicit => ('{', '}'),
    };
    out.push(open);
    if let Some(mult) = binder.mult {
        out.push_str(&mult.mult.to_string());
        out.push(' ');
    }
    dump_list(out, &binder.names, |out, name| out.push_str(&name.text));
    if let Some(ty) = &binder.ty {
        out.push_str(" : ");
        dump_expr(out, ty);
    }
    if let Some(default) = &binder.default {
        out.push_str(" = ");
        dump_expr(out, default);
    }
    out.push(close);
}

/// Обновление: `(update p (x v))`.
fn dump_update(out: &mut String, base: &Expr, fields: &[(Name, Expr)]) {
    out.push_str("(update ");
    dump_expr(out, base);
    for (name, value) in fields {
        out.push_str(" (");
        out.push_str(&name.text);
        out.push(' ');
        dump_expr(out, value);
        out.push(')');
    }
    out.push(')');
}

/// Проекция: `(. p x)`.
fn dump_projection(out: &mut String, inner: &Expr, name: &Name) {
    out.push_str("(. ");
    dump_expr(out, inner);
    out.push(' ');
    out.push_str(&name.text);
    out.push(')');
}

/// Запись или её тип: `(record (x Nat) (y Nat))`.
fn dump_record(out: &mut String, kind: &ExprKind) {
    let (head, fields, tail): (&str, Vec<(&Symbol, &Expr)>, Option<&Name>) = match kind {
        ExprKind::RecordType(fields, tail) => (
            "record",
            fields.iter().map(|it| (&it.name.text, &it.ty)).collect(),
            tail.as_ref(),
        ),
        ExprKind::Record(fields) => (
            "object",
            fields.iter().map(|(name, it)| (&name.text, it)).collect(),
            None,
        ),
        _ => unreachable!("не запись"),
    };
    out.push('(');
    out.push_str(head);
    for (name, value) in fields {
        out.push_str(" (");
        out.push_str(name);
        out.push(' ');
        dump_expr(out, value);
        out.push(')');
    }
    if let Some(tail) = tail {
        out.push_str(" | ");
        out.push_str(&tail.text);
    }
    out.push(')');
}

fn dump_expr(out: &mut String, expr: &Expr) {
    match &expr.kind {
        ExprKind::Name(name) => out.push_str(&name.text),
        ExprKind::Lit(lit) => out.push_str(&lit.text),
        ExprKind::Hole => out.push('_'),
        ExprKind::Effectful { labels, tail, body } => dump_row(out, labels, tail.as_ref(), body),
        ExprKind::RecordType(..) | ExprKind::Record(_) => dump_record(out, &expr.kind),
        ExprKind::Using { name, body } => dump_using(out, name, body),
        ExprKind::Project(inner, name) => dump_projection(out, inner, name),
        ExprKind::Update(base, fields) => dump_update(out, base, fields),
        // Спайн применения печатается в один список: `(f x y)` читается, а
        // `(app (app f x) y)` - нет.
        ExprKind::App(..) => {
            out.push('(');
            dump_spine(out, expr);
            out.push(')');
        }
        ExprKind::TypeApp(callee, argument) => {
            out.push_str("(@ ");
            dump_expr(out, callee);
            out.push(' ');
            dump_expr(out, argument);
            out.push(')');
        }
        ExprKind::Lam { params, body } => dump_lambda(out, params, body),
        ExprKind::Pi { binders, codomain } => {
            out.push_str("(pi (");
            dump_list(out, binders, dump_binder);
            out.push_str(") ");
            dump_expr(out, codomain);
            out.push(')');
        }
        ExprKind::Arrow(domain, codomain) => {
            out.push_str("(-> ");
            dump_expr(out, domain);
            out.push(' ');
            dump_expr(out, codomain);
            out.push(')');
        }
        ExprKind::Block(block) => {
            out.push_str("(block ");
            dump_list(out, &block.stmts, dump_stmt);
            out.push(')');
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            out.push_str("(if ");
            dump_list(out, &[cond, then_branch, else_branch], |out, part| {
                dump_expr(out, part);
            });
            out.push(')');
        }
        ExprKind::Case { scrutinee, alts } => {
            out.push_str("(case ");
            dump_expr(out, scrutinee);
            for alt in alts {
                out.push_str(" (alt ");
                dump_pattern(out, &alt.pattern);
                out.push(' ');
                dump_expr(out, &alt.body);
                out.push(')');
            }
            out.push(')');
        }
        ExprKind::Tuple(items) => {
            out.push_str("(tuple");
            for item in items {
                out.push(' ');
                dump_expr(out, item);
            }
            out.push(')');
        }
        ExprKind::List(items) => {
            out.push_str("(list");
            for item in items {
                out.push(' ');
                dump_expr(out, item);
            }
            out.push(')');
        }
        ExprKind::Chain(chain) => {
            out.push_str("(chain ");
            dump_expr(out, &chain.head);
            for (operator, operand) in &chain.tail {
                out.push_str(" (");
                out.push_str(&operator.text);
                out.push(' ');
                dump_expr(out, operand);
                out.push(')');
            }
            out.push(')');
        }
    }
}

/// Разворачивает спайн применения слева направо.
///
/// Циклом, а не спуском: длина спайна ничем не ограничена - см.
/// [`contains_block`].
fn dump_spine(out: &mut String, expr: &Expr) {
    let mut arguments = Vec::new();
    let mut head = expr;
    while let ExprKind::App(callee, argument) = &head.kind {
        arguments.push(argument);
        head = callee;
    }
    dump_expr(out, head);
    for argument in arguments.iter().rev() {
        out.push(' ');
        dump_expr(out, argument);
    }
}

fn dump_stmt(out: &mut String, stmt: &Stmt) {
    match &stmt.kind {
        StmtKind::Let(bindings) => {
            out.push_str("(let");
            for binding in bindings {
                out.push_str(" (");
                if let Some(mult) = binding.mult {
                    out.push_str(&mult.mult.to_string());
                    out.push(' ');
                }
                out.push_str(&binding.name.text);
                for param in &binding.params {
                    out.push(' ');
                    dump_pattern(out, param);
                }
                if let Some(ty) = &binding.ty {
                    out.push_str(" : ");
                    dump_expr(out, ty);
                }
                out.push_str(" = ");
                dump_expr(out, &binding.body);
                out.push(')');
            }
            out.push(')');
        }
        StmtKind::Expr(expr) => dump_expr(out, expr),
    }
}

fn dump_pattern(out: &mut String, pattern: &Pattern) {
    match &pattern.kind {
        PatternKind::Name(name) => out.push_str(&name.text),
        PatternKind::Wildcard => out.push('_'),
        PatternKind::Lit(lit) => out.push_str(&lit.text),
        PatternKind::App { head, fields } => {
            out.push('(');
            out.push_str(&head.text);
            for field in fields {
                out.push(' ');
                dump_pattern(out, field);
            }
            out.push(')');
        }
        PatternKind::Tuple(items) => {
            out.push_str("(tuple");
            for item in items {
                out.push(' ');
                dump_pattern(out, item);
            }
            out.push(')');
        }
    }
}
