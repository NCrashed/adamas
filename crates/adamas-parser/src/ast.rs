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
    /// Скобки целиком, или само имя у параметра без скобок.
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
    /// Кортеж `(a, b)`; пустой - `()`.
    Tuple(Vec<Expr>),
    /// Список `[a, b, c]`.
    List(Vec<Expr>),
    /// Цепочка операторов.
    Chain(Chain),
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
    /// Сигнатура: `map : (a -> b) -> Vect n a -> Vect n b`.
    Signature {
        /// Имя.
        name: Name,
        /// Тип.
        ty: Expr,
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
    /// Ресурсный тип: `resource File where drop h = …` (§3.3).
    Resource(Resource),
}

/// Индуктивный тип.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Data {
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
    /// Тело: `drop` и всё, что объявлено рядом.
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

/// Печатает объявление без завершающего перевода строки: где его ставить,
/// решает вызывающий - вложенное объявление продолжается скобкой.
fn dump_decl(out: &mut String, decl: &Decl, depth: usize) {
    match &decl.kind {
        DeclKind::Signature { name, ty } => {
            out.push_str("(sig ");
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
    if let (Visibility::Explicit, None, None, [name]) = (
        binder.visibility,
        binder.mult,
        binder.ty.as_ref(),
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
    out.push(close);
}

fn dump_expr(out: &mut String, expr: &Expr) {
    match &expr.kind {
        ExprKind::Name(name) => out.push_str(&name.text),
        ExprKind::Lit(lit) => out.push_str(&lit.text),
        ExprKind::Hole => out.push('_'),
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
        ExprKind::Lam { params, body } => {
            out.push_str("(lam (");
            dump_list(out, params, |out, param| match &param.kind {
                LamParamKind::Pattern(pattern) => dump_pattern(out, pattern),
                LamParamKind::Binder(binder) => dump_binder(out, binder),
            });
            out.push_str(") ");
            dump_expr(out, body);
            out.push(')');
        }
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
fn dump_spine(out: &mut String, expr: &Expr) {
    if let ExprKind::App(callee, argument) = &expr.kind {
        dump_spine(out, callee);
        out.push(' ');
        dump_expr(out, argument);
    } else {
        dump_expr(out, expr);
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
