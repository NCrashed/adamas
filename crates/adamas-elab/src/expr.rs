//! Выражения и паттерны поверхностного языка в термы ядра.
//!
//! Границы фрагмента и причина каждой - в [`crate`] и в [`Missing`]; правило
//! регистра - у [`is_reference`]. Здесь - сами правила элаборации, по одному
//! на форму, и то, что из них следует: тому же порядку следует обратный проход
//! маршрута ([`crate::route`]).

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::check::{check, infer, is_type};
use adamas_core::conv::{convertible, whnf, whnf_solved};
use adamas_core::ctx::Ctx;
use adamas_core::eval::{apply, eval, quote};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern as CorePattern, PatternError, compile_case};
use adamas_core::row::{Label, Row};
use adamas_core::sig::{Definition, DefinitionKind, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Binder, Field as CoreField, Fields, Index, Name as CoreName, Rows, Term};
use adamas_core::value::{Elim, Env, Head, Lvl, Value};
use adamas_parser::ast::{
    self, Binding, Block, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind,
    Symbol, Visibility,
};

use crate::decl::CLOSING;
use crate::error::{ElabError, Missing};
use crate::fixity::Fixities;
use crate::live;
use crate::own::Owned;

/// Умолчание кратности с поправкой на домен-универсум (§4.1).
///
/// Аргумент-тип стирается: типов в рантайме нет вовсе, и `Level` с `Effect`
/// дизайн объявил всегда стёртыми ровно поэтому. Без этого `Type -> Type`
/// читается при `ω`, а параметр семейства стёрт, и `Option` под написанный
/// кинд не подходит.
///
/// Поправка **позиционная**, как и само умолчание. Она не трогает ни поле
/// конструктора - там умолчание `1`, и `MkDyn : (a : Type) -> a -> Dyn`
/// хранит тип, а стерев его, разбор перестал бы отдавать хранимое, - ни
/// телескоп параметров объявления: у алиаса `type Id (a : Type) = a` тело и
/// есть параметр, то есть расходует его однажды.
fn kinded(written: Option<ast::MultAnn>, ty: &Expr, default: Mult) -> Mult {
    if written.is_none() && default == Mult::Many && universe(ty) {
        return Mult::Zero;
    }
    default
}

/// Написан ли универсум: `Type` и ничего больше.
///
/// Проверка синтаксическая, и это не приближение: конкретный универсум в
/// поверхностном языке не пишется (§3.2), поэтому иных записей у него нет.
fn universe(ty: &Expr) -> bool {
    matches!(&ty.kind, ExprKind::Name(name) if &*name.text == "Type")
}

/// Имя единицы. Соглашение то же, каким `if` берёт `Bool` (§3.4): типа этого
/// ядро не знает, а сахар `{ε} A` без него не разворачивается.
pub(crate) const UNIT: &str = "Unit";

/// Имя ветки, принимающей значение вычисления.
pub(crate) const RETURN: &str = "return";

/// Ветка `return`, которую подставляет её отсутствие: значение вычисления и
/// есть ответ хендлера, то есть `b := a`.
fn identity_return(span: Span) -> ast::HandlerBranch {
    let name = |text: &str| ast::Name {
        text: Rc::from(text),
        span,
    };
    ast::HandlerBranch {
        name: name(RETURN),
        params: vec![name("v")],
        body: Expr {
            kind: ExprKind::Name(name("v")),
            span,
        },
        span,
    }
}

/// Что написано у хендлера.
#[derive(Clone, Copy)]
struct Handled<'a> {
    /// Мультишотный ли.
    multi: bool,
    /// Написанная метка, если есть.
    label: Option<&'a ast::EffectLabel>,
    /// Вычисление под хендлером.
    computation: &'a Expr,
    /// Ветки в порядке написания.
    branches: &'a [ast::HandlerBranch],
    /// Хендлер целиком.
    span: Span,
}

/// Row без первого вхождения метки: остаток и есть ρ (§3.4).
///
/// Снимается **первое** вхождение имени, и другого выбора нет: элиминатор
/// ставит снимаемую метку первой в своём домене, а порядок внутри группы
/// одноимённых значим - внутренний хендлер перехватывает раньше внешнего. Взять
/// не первое значило бы пройти мимо внутреннего, а это `mask`, отдельный
/// примитив, которого в дизайне нет.
///
/// Написанные аргументы метки поэтому не выбирают вхождение, а **закрепляют**
/// его: они говорят, чем должно оказаться `p⃗` у первого. Не совпало - отказ,
/// и правило §3.4 остаётся тем же.
fn without(row: &Row<Rc<Value>>, effect: &str) -> Option<Snatched> {
    let mut labels = Vec::with_capacity(row.labels().len());
    let mut removed = None;
    for label in row.labels() {
        if removed.is_none() && &*label.name == effect {
            removed = Some(label.arguments.clone());
            continue;
        }
        labels.push(label.clone());
    }
    removed.map(|arguments| Snatched {
        rest: Row::closing(labels, row.tail()),
        arguments,
    })
}

/// Что дало снятие метки: остаток row и аргументы снятого вхождения.
struct Snatched {
    /// Остаток - глубина хендлера ρ.
    rest: Row<Rc<Value>>,
    /// Аргументы снятой метки: с ними сверяется написанная.
    arguments: Vec<Rc<Value>>,
}

/// Имя параметром лямбды.
fn bind_as(name: ast::Name) -> ast::LamParam {
    let span = name.span;
    ast::LamParam {
        kind: LamParamKind::Pattern(Pattern {
            kind: PatternKind::Name(name),
            span,
        }),
        span,
    }
}

/// Ветки в порядке объявления операций; `return` первой.
///
/// Порядок написания значения не имеет - сопоставляются они по имени, - а
/// элиминатор ждёт их в объявленном. Ветка `return` необязательна: без неё
/// значение вычисления и есть ответ, то есть `b := a`.
fn ordered_branches<'a>(
    operations: &[Symbol],
    branches: &'a [ast::HandlerBranch],
    identity: &'a ast::HandlerBranch,
    span: Span,
) -> Result<Vec<&'a ast::HandlerBranch>, ElabError> {
    let mut seen: Vec<&Symbol> = Vec::new();
    for branch in branches {
        if seen.iter().any(|it| ***it == *branch.name.text) {
            return Err(ElabError::HandlerBranch {
                name: Rc::clone(&branch.name.text),
                why: "ветка написана дважды",
                span: branch.span,
            });
        }
        seen.push(&branch.name.text);
        let known =
            &*branch.name.text == RETURN || operations.iter().any(|it| **it == *branch.name.text);
        if !known {
            return Err(ElabError::HandlerBranch {
                name: Rc::clone(&branch.name.text),
                why: "такой операции у эффекта нет",
                span: branch.name.span,
            });
        }
    }
    let named = |wanted: &str| branches.iter().find(|it| &*it.name.text == wanted);
    let mut ordered = Vec::with_capacity(operations.len() + 1);
    ordered.push(named(RETURN).unwrap_or(identity));
    for operation in operations {
        ordered.push(named(operation).ok_or_else(|| ElabError::HandlerBranch {
            name: Rc::clone(operation),
            why: "ветка не написана, а хендлер обязан покрыть все операции",
            span,
        })?);
    }
    Ok(ordered)
}

/// Имена, которыми записывается число (§4.3). Соглашение то же, каким `if`
/// берёт `Bool`: ядро этих имён не знает, а сахар без них не разворачивается.
pub(crate) const ZERO: &str = "Zero";

/// Конструктор-последователь.
pub(crate) const SUCC: &str = "Succ";

/// Пустой список.
pub(crate) const NIL: &str = "Nil";

/// Присоединение к списку.
pub(crate) const CONS: &str = "Cons";

/// Преобразование литерала. Не объявлено - литерал есть само число.
pub(crate) const FROM_NAT: &str = "fromNat";

/// Имя резумпции. Связывает его сама форма хендлера (§3.4), поэтому оно и
/// единственное в языке магическое: вложенный хендлер его затеняет.
pub(crate) const RESUME: &str = "resume";

/// Что написанный тип говорит о теле клаузы - после того, как паттерны сняли
/// свои связывания.
struct Rest {
    /// Тип тела. `None` - написанного типа не хватило.
    result: Option<Rc<Value>>,
    /// Окружающая row тела: её несёт последняя снятая стрелка (§3.4).
    ambient: Row<Rc<Value>>,
}

/// Домен связывания, если тип им является.
fn domain_of(ty: &Value) -> Option<Rc<Value>> {
    match ty {
        Value::Pi(_, _, domain, _, _) => Some(Rc::clone(domain)),
        _ => None,
    }
}

/// Ждёт ли спайн типа единицу хоть одним связыванием.
///
/// Приближение сверху для [`Elaborator::suspends`]: имплиситы у имени ещё не
/// вставлены, поэтому какое именно связывание окажется первым, здесь неизвестно.
fn awaits_unit(ty: &Term) -> bool {
    let mut current = ty;
    while let Term::Pi(_, _, domain, _, codomain) = current {
        if matches!(&**domain, Term::Const(name, ..) if &**name == UNIT) {
            return true;
        }
        current = codomain;
    }
    false
}

/// Разбирает ли имя (заглавное) или связывает (строчное).
///
/// §4.1: заглавное имя ссылается на объявленное - в паттерне разбирает, в типе
/// обязано быть известным; строчное связывает. Правило локально, поэтому чтобы
/// прочитать клаузу, не нужно знать, что объявлено выше, и опечатка в имени
/// конструктора называется там, где написана, вместо переменной, ловящей всё.
///
/// Письменности без регистра попадают в «строчные»: конструкторов ими не
/// назвать, и это названная цена решения от 2026-08-25.
#[must_use]
pub fn is_reference(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

/// Поднятое в implicit-параметр имя (§4.1, §4.2).
///
/// Свободное имя типа и row-переменная записи поднимаются одним механизмом и
/// различаются только сортом связывания: у первого - дырка, у второй -
/// `Row ℓ`.
struct Lifted {
    /// Имя, под которым связывание встанет в телескоп.
    name: Symbol,
    /// Ряд ли это.
    row: bool,
}

/// Несвязанные имена сигнатуры, разделённые по сорту подъёма.
#[derive(Default)]
struct Unbound {
    /// Обычные свободные: тип у них - дырка.
    names: Vec<Symbol>,
    /// Написанные в хвосте записи: тип у них - `Row ℓ`.
    tails: Vec<Symbol>,
}

impl Unbound {
    /// Встречалось ли имя - в любой из групп.
    fn has(&self, name: &Symbol) -> bool {
        self.names.contains(name) || self.tails.contains(name)
    }
}

/// Записи сигнатуры, которым auto-lift раздаёт row-переменную, - по спану
/// каждой (§4.2).
///
/// **Только отрицательные позиции.** Запись слева от стрелки - то, что
/// функция принимает, и `{x, y | r}` там значит «не меньше этих полей»:
/// квантор по `r` инстанцирует вызывающий, принося свою запись. Запись справа
/// от стрелки - то, что функция обязана произвести, и квантор там требует
/// произвести её при **любом** `r`: полей, которых автор не знает, взять
/// неоткуда, и тип выходит необитаемым. Для эффектов симметрия верна - там
/// row в результате есть разрешение, а не обязательство, - и эта разница
/// записана в решении от 2026-08-29.
///
/// Сохранение полей поэтому пишется явно: `keep : {x : Nat | r} -> {x : Nat | r}`.
/// §4.11 так и пишет.
///
/// Вложенная в другую запись не считается: там она поле, а поле - это тип, и
/// закрывает его та же запись, что его объявила. Под применение типа
/// (`List { x : Nat }`) подъём тоже не идёт: вариантность чужого конструктора
/// неизвестна, а синоним стрелки её переворачивает.
///
/// Спан, а не число: по нему запись потом себя и узнает. Одна написанная
/// группа связываний элаборируется по разу на имя, и счёт вхождений разъехался
/// бы с раздачей.
fn written_rows(expr: &Expr, negative: bool, found: &mut Vec<Span>) {
    match &expr.kind {
        // Запись с написанным хвостом свою переменную уже назвала.
        // Зависимая закрыта по §4.2, и правило читается из текста: поле,
        // назвавшее предыдущее, - и есть зависимость. Считать это по
        // элаборированной записи поздно: параметр раздаётся раньше, чем поля
        // проверены, и снятый после раздачи хвост оставил бы параметр без
        // потребителя - то есть невыводимым в каждом употреблении.
        ExprKind::RecordType(fields, None) if negative && !depends_by_text(fields) => {
            found.push(expr.span);
        }
        ExprKind::Arrow(left, right) => {
            written_rows(left, !negative, found);
            written_rows(right, negative, found);
        }
        ExprKind::Pi { binders, codomain } => {
            for ty in binders.iter().filter_map(|it| it.ty.as_ref()) {
                written_rows(ty, !negative, found);
            }
            written_rows(codomain, negative, found);
        }
        _ => {}
    }
}

/// Есть ли у записи поле, чей тип зависит от предыдущего.
///
/// Телескоп: `i`-е поле стоит под `i` связываниями, и упоминание любого из них
/// и есть зависимость (§4.2).
fn dependent(fields: &[CoreField]) -> bool {
    fields.iter().enumerate().any(|(index, field)| {
        field
            .ty
            .mentions_recent(0, u32::try_from(index).unwrap_or(u32::MAX))
    })
}

/// То же по тексту: назвал ли тип поля имя одного из предыдущих.
///
/// §4.2 требует, чтобы правило читалось из объявления, и здесь это буквально
/// так: имя ищется вхождением, затенение не разбирается. Разойтись с
/// [`dependent`] эти два взгляда могут только в сторону строгости - имя,
/// затенённое внутренним связыванием, текст сочтёт зависимостью, а элаборация
/// нет, - и цена такого расхождения одна: запись, которую можно было бы
/// открыть, останется закрытой.
fn depends_by_text(fields: &[ast::RecordField]) -> bool {
    let mut earlier: Vec<&Symbol> = Vec::with_capacity(fields.len());
    for field in fields {
        if names_any(&field.ty, &earlier) {
            return true;
        }
        earlier.push(&field.name.text);
    }
    false
}

/// Первый написанный хвост effect row в выражении: `{IO | e}` даёт `e`.
///
/// Ищется синтаксически, а не через сбор свободных имён: хвост эффектной row
/// туда не попадает вовсе - `free_in` его не собирает, потому что связывает его
/// не подъём, а `named_tail`, заводящий дырку и отдающий её обобщению. Для
/// сигнатуры это верно, для конструктора - нет: обобщение делает конструктор
/// row-полиморфным при row-арности семейства нуль.
fn written_row_tail(expr: &Expr) -> Option<&ast::Name> {
    let recur = written_row_tail;
    match &expr.kind {
        ExprKind::Effectful { tail, body, labels } => tail.as_ref().or_else(|| {
            recur(body).or_else(|| {
                labels
                    .iter()
                    .flat_map(|it| &it.arguments)
                    .find_map(written_row_tail)
            })
        }),
        ExprKind::Name(_) | ExprKind::Lit(_) | ExprKind::Hole => None,
        ExprKind::Project(inner, _) => recur(inner),
        ExprKind::App(left, right)
        | ExprKind::TypeApp(left, right)
        | ExprKind::Arrow(left, right) => recur(left).or_else(|| recur(right)),
        ExprKind::Using { body, .. } | ExprKind::Lam { body, .. } => recur(body),
        ExprKind::Pi { binders, codomain } => binders
            .iter()
            .filter_map(|it| it.ty.as_ref())
            .find_map(written_row_tail)
            .or_else(|| recur(codomain)),
        ExprKind::Block(block) => block.stmts.iter().find_map(|stmt| match &stmt.kind {
            ast::StmtKind::Expr(inner) => recur(inner),
            ast::StmtKind::Let(bindings) => bindings.iter().find_map(|it| {
                it.ty
                    .as_ref()
                    .and_then(written_row_tail)
                    .or_else(|| recur(&it.body))
            }),
        }),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => recur(cond)
            .or_else(|| recur(then_branch))
            .or_else(|| recur(else_branch)),
        ExprKind::Case { scrutinee, alts } => {
            recur(scrutinee).or_else(|| alts.iter().find_map(|alt| recur(&alt.body)))
        }
        ExprKind::Handle {
            computation,
            branches,
            ..
        } => recur(computation).or_else(|| branches.iter().find_map(|it| recur(&it.body))),
        ExprKind::RecordType(fields, _) => fields.iter().find_map(|it| written_row_tail(&it.ty)),
        ExprKind::Record(fields) => fields.iter().find_map(|(_, value)| recur(value)),
        ExprKind::Update(base, fields) => {
            recur(base).or_else(|| fields.iter().find_map(|(_, value)| recur(value)))
        }
        ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().find_map(written_row_tail),
        ExprKind::Chain(chain) => {
            recur(&chain.head).or_else(|| chain.tail.iter().find_map(|(_, item)| recur(item)))
        }
    }
}

/// Встречается ли в выражении хоть одно из имён.
pub(crate) fn names_any(expr: &Expr, wanted: &[&Symbol]) -> bool {
    let recur = |inner: &Expr| names_any(inner, wanted);
    match &expr.kind {
        ExprKind::Name(name) => wanted.iter().any(|it| **it == name.text),
        ExprKind::Lit(_) | ExprKind::Hole => false,
        ExprKind::Effectful { labels, body, .. } => {
            recur(body) || labels.iter().flat_map(|it| &it.arguments).any(recur)
        }
        ExprKind::Project(inner, _) => recur(inner),
        ExprKind::App(left, right)
        | ExprKind::TypeApp(left, right)
        | ExprKind::Arrow(left, right) => recur(left) || recur(right),
        ExprKind::Using { body, .. } | ExprKind::Lam { body, .. } => recur(body),
        ExprKind::Pi { binders, codomain } => {
            binders.iter().filter_map(|it| it.ty.as_ref()).any(&recur) || recur(codomain)
        }
        ExprKind::Block(block) => block.stmts.iter().any(|stmt| match &stmt.kind {
            ast::StmtKind::Expr(inner) => recur(inner),
            ast::StmtKind::Let(bindings) => bindings
                .iter()
                .any(|it| it.ty.as_ref().is_some_and(&recur) || recur(&it.body)),
        }),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => recur(cond) || recur(then_branch) || recur(else_branch),
        ExprKind::Case { scrutinee, alts } => {
            recur(scrutinee) || alts.iter().any(|alt| recur(&alt.body))
        }
        ExprKind::Handle {
            label,
            computation,
            branches,
            ..
        } => {
            recur(computation)
                || branches.iter().any(|it| recur(&it.body))
                || label.iter().flat_map(|label| &label.arguments).any(&recur)
        }
        ExprKind::RecordType(inner, _) => inner.iter().any(|it| recur(&it.ty)),
        ExprKind::Record(inner) => inner.iter().any(|(_, value)| recur(value)),
        ExprKind::Update(base, inner) => recur(base) || inner.iter().any(|(_, value)| recur(value)),
        ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().any(&recur),
        ExprKind::Chain(chain) => {
            recur(&chain.head) || chain.tail.iter().any(|(_, item)| recur(item))
        }
    }
}

/// Связывание написанной группы, разложенной в плоский список.
///
/// Группа `(0 n m : Nat)` даёт два таких: кратность, видимость и тип у них
/// общие, а `siblings` различает - см. [`Elaborator::pi`].
struct Written<'a> {
    /// Кратность: написанная либо умолчание позиции.
    mult: Mult,
    /// Круглые скобки против фигурных.
    visibility: Visibility,
    /// Имя связывания.
    name: Symbol,
    /// Написанный тип - общий на все имена группы.
    ty: &'a Expr,
    /// Сколько имён своей группы стоит перед этим: столько прячется от типа.
    siblings: usize,
}

/// Модуль, чьё тело элаборируется (§4.8).
///
/// Члены подняты на верхний уровень под квалифицированными именами, и короткое
/// имя внутри тела - ссылка на своего же соседа: `compare` рядом с
/// `type T = Int` видит `T`, то есть `IntOrd.T`. Заслоняет одноимённое
/// глобальное - это ordered scoping §4.8, а не особый случай.
///
/// У функтора член поднят **вместе с параметрами**, поэтому ссылка на него
/// изнутри применяется к ним: написанное `insert` есть `F.insert Key`.
#[derive(Clone)]
pub(crate) struct Enclosing<'a> {
    /// Имя модуля - им квалифицируются члены.
    pub name: Symbol,
    /// Параметры функтора как написаны. Пусто - обычный модуль.
    ///
    /// Написанными, а не элаборированными: граница объявления освобождает
    /// дырки (`Metas::release`), и телескоп, посчитанный один раз на всех,
    /// умер бы на первом же члене. Каждый член элаборирует его заново и
    /// обобщает свои уровни сам - применяются они к нему тоже по одному.
    pub params: &'a [ast::Binder],
}

impl Enclosing<'_> {
    /// Имена параметров в порядке написания.
    fn names(&self) -> impl Iterator<Item = &Symbol> {
        self.params
            .iter()
            .flat_map(|binder| binder.names.iter().map(|name| &name.text))
    }
}

/// Член сигнатуры модуля или класса, как он написан.
///
/// Параметры несёт только абстрактный типовой член: у члена с написанным
/// типом их нет и быть не может - тип там пишется целиком.
pub(crate) struct WrittenField<'a> {
    /// Имя поля.
    pub name: ast::Name,
    /// Параметры абстрактного типового члена: `type Bag (a : Type)`.
    pub params: &'a [ast::Binder],
    /// Написанный тип. `None` - абстрактный типовой член.
    pub ty: Option<&'a Expr>,
}

/// Параметр семейства - уже элаборированный.
///
/// Живёт отдельно от [`ast::Binder`], потому что переиспользуется: kind и все
/// конструкторы обязаны нести один и тот же телескоп, а элаборация написанного
/// дважды дала бы два разных набора дырок уровня.
#[derive(Clone)]
pub(crate) struct Param {
    /// Кратность параметра - написанная либо `ω` по умолчанию (§4.1).
    pub mult: Mult,
    /// Имя, каким оно написано: под ним параметр виден в типах конструкторов.
    pub name: Symbol,
    /// Тип параметра. `data Pair a b` его не пишет, и там стоит дырка.
    pub ty: Rc<Term>,
}

/// Член объявляемой группы (§10 вопрос 50).
///
/// Пока группа объявляется, в сигнатуре её нет, а ссылаться на членов надо:
/// конструктор называет своё семейство, тело определения - само определение.
/// Значит всё, что о члене знает вставка имени, приходит отсюда.
#[derive(Clone)]
pub(crate) struct Member {
    /// Имя, каким оно написано.
    pub name: Symbol,
    /// Аргументы уровня - общие на всё объявление; их считает вызывающий
    /// обобщением по типу члена, и это §10 вопрос 63.
    pub levels: Rc<[Level]>,
    /// Аргументы-row - вторая компонента арности (§10 вопрос 73), и правило у
    /// них то же, что у уровней: свой параметр приходит переменной, чужой -
    /// дыркой. Пустой список означал бы тождественную подстановку, а ядро её
    /// не ловит: параметры соседа читались бы как свои, и `mutual` над двумя
    /// эффектными сигнатурами отвергался, тогда как те же два определения
    /// подряд проходят.
    pub rows: Rows,
    /// Уже элаборированный тип. По нему вставляются имплиситы: спросить его у
    /// сигнатуры нельзя, там члена ещё нет.
    pub ty: Rc<Term>,
}

/// Связывание написанного типа: что о нём известно до элаборации тела.
#[derive(Clone, Debug)]
struct Argument {
    /// Кратность из `Pi`.
    mult: Mult,
    /// Домен - тип, который получит связывание.
    ///
    /// Живёт под теми же связываниями, что и в исходном телескопе, а
    /// элаборация связывает их в том же порядке, поэтому вычислять его можно
    /// прямо в её контексте. Держится это на том, что параметров у семейств
    /// пока нет (§10 вопрос про `FamilyParameters`): появись они, телескоп
    /// конструктора начинался бы с них, а паттерн - нет.
    domain: Rc<Term>,
    /// Имя связывания. Имплиситу оно нужно как имя переменной: аргумента ему
    /// никто не писал, а тело вправе его назвать - тем именем, под которым его
    /// подняли (см. `lifting`).
    name: CoreName,
    /// Выводится ли аргумент вместо того, чтобы писаться.
    implicit: bool,
    /// Объявлена ли голова домена `unique` или `resource`.
    owned: bool,
    /// Функция ли это - домен сам `Pi`.
    functional: bool,
    /// Деструктор, если голова домена - ресурсный тип.
    drop: Option<Symbol>,
}

impl Argument {
    /// Привязано ли связывание к своему scope.
    ///
    /// §3.3: «параметр кратности `1` функционального типа наследует то же
    /// ограничение внутри вызываемой функции». Без этого правила функция,
    /// возвращающая свой аргумент, выносит наружу захваченное замыкание, и
    /// запрет на позицию возврата обходится в одну строку.
    fn scoped(&self) -> bool {
        self.functional && self.mult == Mult::One
    }

    /// Закрывается ли связывание автоматически, когда о нём забыли.
    ///
    /// Стёртое не закрывается: `drop` расходует ресурс, а стёртое связывание
    /// расходовать нечем - вставка отвергала бы корректную программу (§3.3,
    /// §10 вопрос 71).
    fn closes(&self) -> Option<&Symbol> {
        self.drop.as_ref().filter(|_| self.mult != Mult::Zero)
    }
}

/// Локальное связывание: имя, видно ли оно поиску (см. `hiding`), владеет ли
/// оно (§3.3) и не привязано ли к своему scope.
struct Bound {
    name: Symbol,
    /// Кратность, с которой связывание объявлено.
    mult: Mult,
    /// Тип связывания. Нужен вставке имплиситов: дырка замкнута телескопом
    /// контекста, и построить её тип без типов связываний нечем.
    ty: Rc<Value>,
    visible: bool,
    owned: bool,
    /// Значение связывания, если оно `let`. Вычисление его подставляет,
    /// поэтому переменной такое связывание не остаётся - см. `fresh_meta`.
    value: Option<Rc<Term>>,
    /// Значение, которое не вправе покинуть scope: замыкание над владеющим
    /// связыванием, связывание, инициализированное таким замыканием, и
    /// `1`-параметр функционального типа (§3.3).
    scoped: bool,
}

impl Bound {
    fn visible(name: &Symbol, mult: Mult, ty: Rc<Value>) -> Self {
        Self {
            name: Rc::clone(name),
            mult,
            ty,
            visible: true,
            owned: false,
            scoped: false,
            value: None,
        }
    }

    fn owning(name: &Symbol, mult: Mult, ty: Rc<Value>, owned: bool) -> Self {
        Self {
            owned,
            ..Self::visible(name, mult, ty)
        }
    }

    fn owning_scoping(name: &Symbol, mult: Mult, ty: Rc<Value>, owned: bool, scoped: bool) -> Self {
        Self {
            owned,
            scoped,
            ..Self::visible(name, mult, ty)
        }
    }
}

/// Где стоит элаборируемое выражение - для правила scope-bound (§3.3).
///
/// Значение, привязанное к scope, применяется и передаётся аргументом, но не
/// возвращается и не кладётся в поле конструктора. Позиция синтаксическая, но
/// проверять её на лямбда-литерале недостаточно: §3.3 прямо показывает обход
/// через `let`, и есть ещё два - функция, возвращающая свой аргумент, и
/// конструктор. Поэтому позиция здесь встречается со **свойством значения**,
/// которое элаборация считает и распространяет.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Position {
    /// Аргумент, голова применения, значение `let` - откуда значение не уедет.
    Inner,
    /// Возвращаемое значение функции: тело клаузы, тело лямбды, хвост блока.
    Returned,
    /// Аргумент конструктора: значение уедет внутри собранного.
    Field,
}

impl Position {
    /// Как это называется в сообщении; `None` - позиция, откуда не уедет.
    fn face(self) -> Option<&'static str> {
        match self {
            Self::Inner => None,
            Self::Returned => Some("возвращается"),
            Self::Field => Some("кладётся в поле конструктора"),
        }
    }
}

/// Состояние элаборации: сигнатура, хранилище дырок и локальные связывания.
pub(crate) struct Elaborator<'a> {
    /// Уже объявленное. Элаборация её не меняет - объявляет вызывающий.
    pub signature: &'a Signature,
    /// Хранилище дырок уровня: одно на прогон (§10 вопрос 51).
    pub metas: &'a mut Metas,
    /// Типы, объявленные `unique` или `resource` (§3.3). Как и хранилище
    /// дырок, приходит снаружи: прогон элаборации - модуль целиком.
    pub owned: &'a Owned,
    /// Объявленные фикситеты (§4.4). Приходит снаружи по тому же доводу:
    /// таблица собирается по ходу объявлений, а прогон элаборации - модуль.
    pub fixities: &'a Fixities,
    /// Локальные связывания снаружи внутрь; индекс де Брёйна - расстояние от
    /// конца.
    scope: Vec<Bound>,
    /// Типовой контекст, двигающийся вместе с областью видимости.
    ///
    /// Тот же, которым пользуется ядро: имена, кратности и типы связываний
    /// плюс окружение вычисления. Заводить свой значило бы держать второй
    /// источник истины о том, что связано.
    ctx: Ctx<'a>,
    /// Члены объявляемой группы вместе с арностью параметров уровня.
    ///
    /// В сигнатуре их ещё нет - она увидит группу целиком (§10 вопрос 50), - а
    /// ссылаться на них надо: конструктор называет своё семейство, тело
    /// называет само определение. Спросить арность у сигнатуры поэтому нечего,
    /// и её считает вызывающий обобщением по типу члена; это и есть §10
    /// вопрос 63.
    group: Vec<Member>,
    /// Связывания написанного типа - по одному на `Pi` его спайна.
    ///
    /// Лямбда в ядре несёт кратность, и `check` требует, чтобы она совпадала с
    /// кратностью `Pi`. Вывести её элаборация не может - она не
    /// типонаправленная, - но здесь и выводить нечего: тип **написан**, и
    /// спайн его виден синтаксически. Оттуда же берётся деструктор: голова
    /// домена видна тем же взглядом. Дальше видимого спайна (кодомен -
    /// константа, разворачивающаяся в `Pi`) записи кончаются, и лямбда снова
    /// берёт `ω` без закрытия.
    declared: Vec<Argument>,
    /// Синтезировано ли первое связывание написанного типа сахаром `{ε} A`.
    ///
    /// Нульместных функций в ядре нет, и приостановленное вычисление
    /// разворачивается в стрелку от единицы (см. `suspended`). Аргументом
    /// определения это связывание не является, поэтому писать его не обязаны -
    /// ровно как ветка хендлера не связывает то, что вставил тот же сахар.
    /// Различить по ядерному типу нечем (`{State s} s` и `Unit -> {State s} s`
    /// после сахара одинаковы), а по написанному - видно сразу.
    declared_suspends: bool,
    /// Тип объявления значением - им шагает разбор паттернов клаузы.
    declared_ty: Option<Rc<Value>>,
    /// Записи, ожидающие ближайшую лямбду. Их выставляет тот, кто знает
    /// написанный тип: клауза - остатком спайна после своих паттернов, `let` -
    /// спайном своей аннотации.
    expected: Vec<Argument>,
    /// Ожидаемый тип **результата** - то, чем окажется выражение, когда спайн
    /// кончится.
    ///
    /// `expected` несёт связывания написанного типа, а результат выбрасывал:
    /// он нужен был лишь тому, кто вставляет имплиситы. Хендлеру он нужен
    /// иначе - его ответ `b` есть результат применения элиминатора, и знать
    /// его надо **до** веток (§10 вопрос 87).
    ///
    /// Живёт только в хвостовой позиции: при спуске в аргумент снимается, иначе
    /// вложенный `handle` принял бы за свой ответ результат объемлющего.
    result: Option<Rc<Value>>,
    /// Идёт ли элаборация в позиции типа - см. `typing`.
    types: bool,
    /// Записи сигнатуры, которым роздана row-переменная (§4.2), - по спану
    /// каждой в порядке написания.
    ///
    /// `None` - записи закрыты: так элаборируются алиас `type` и всё, что
    /// сигнатурой не является. Auto-lift применяется только там, где
    /// row-переменную есть кому связать.
    ///
    /// **Ключ - спан, а не счётчик.** Один написанный тип элаборируется
    /// столько раз, сколько имён в его группе (`(0 a b : { x : Nat })` - два),
    /// и счётчик уезжал бы на каждом: второе имя искало бы переменную, которой
    /// никто не связал, и молча получало закрытую запись. Спан один на всю
    /// группу, поэтому и переменная одна - как и обязано быть у одного
    /// написанного типа.
    rows: Option<Vec<Span>>,
    /// Row-переменная auto-lift'а - одна на всю написанную сигнатуру (§3.4).
    ///
    /// `None` - позиция сигнатурой не является, и стрелки её замкнуты: алиас
    /// `type`, тело, конструктор. Одна на сигнатуру, а не по одной на позицию,
    /// и это критично для higher-order: `withFile : String -> (File -> {IO} a)
    /// -> {IO, Except IOError} a` обязан пробросить эффекты колбэка в
    /// результат, а разные переменные разорвали бы связь.
    lifted: Option<Row<Term>>,
    /// Хвосты, названные руками: `{IO | e}` (§3.4).
    ///
    /// Одно имя - одна переменная на сигнатуру, по тому же доводу, что и у
    /// `instantiated`: два вхождения `e` обязаны быть одним параметром, иначе
    /// написанная связь между позициями теряется.
    tails: HashMap<Symbol, Row<Term>>,
    /// Запрещена ли вставка имплиситов ближайшему имени - см. `type_app`.
    bare: bool,
    /// Модуль, чьё тело элаборируется (§4.8). `None` - верхний уровень.
    enclosing: Option<Enclosing<'a>>,
    /// Именованные инстансы, выбранные `using`: класс и имя (§4.3).
    ///
    /// Выбор действует на **вставку**, а не на разрешение: словарь для
    /// этого класса не заводится дыркой вовсе, а сразу берётся написанным.
    /// Иначе выбор пришлось бы доносить до отложенного поиска, а он
    /// работает по дыркам, у которых места написания уже нет.
    using: Vec<(Symbol, Symbol)>,
    /// Где стоит ближайший подтерм - см. [`Position`].
    position: Position,
    /// Привязано ли к scope значение, которое только что собрано, и каким
    /// именем оно к нему привязано.
    ///
    /// Обратный канал правила scope-bound: свойство считается снизу вверх -
    /// лямбда привязана захватом, имя привязано своим связыванием, блок
    /// привязан своим хвостом, - а запрещает его позиция, известная сверху.
    /// Применение свойство **не** передаёт: результат применения к scope не
    /// привязан, а построить возвращающее замыкание нельзя - запрет на
    /// позицию возврата не даёт собрать его вовсе.
    produced: Option<Symbol>,
    /// Аргументы уровня, уже выданные имени в этом объявлении.
    ///
    /// Одно имя - один набор дырок, а не свежий на каждое вхождение. Иначе
    /// `f : D -> D` над полиморфным по уровню `D` читается как `∀u v. D{u} ->
    /// D{v}`: обобщение идёт до проверки тела, связать два параметра потом
    /// нечем, и тождество над таким семейством не пишется. Тот же довод уже
    /// стоял за общими дырками у члена группы (`self_levels` в
    /// [`crate::decl`]), здесь он распространён на объявленное.
    ///
    /// Цена названа: два вхождения одного имени на разных уровнях в одной
    /// сигнатуре теперь несовместимы. Написать их всё равно нечем - уровни в
    /// поверхностном языке не именуются, - и появится это вместе с
    /// имплиситами (§4.1).
    instantiated: HashMap<Symbol, Term>,
}

impl<'a> Elaborator<'a> {
    /// Элаборатор с пустым локальным контекстом.
    pub(crate) fn new(
        signature: &'a Signature,
        metas: &'a mut Metas,
        owned: &'a Owned,
        fixities: &'a Fixities,
    ) -> Self {
        Self::with_group(signature, metas, owned, fixities, Vec::new())
    }

    /// То же, внутри тела модуля: короткое имя члена ищется квалифицированным.
    pub(crate) fn within(mut self, enclosing: Option<&Enclosing<'a>>) -> Self {
        self.enclosing = enclosing.cloned();
        self
    }

    /// Выполняет `body` под параметрами, ничего вокруг результата не строя.
    ///
    /// [`Self::wrapped`] делает то же и оборачивает результат в `Pi`; здесь
    /// нужен сам результат - тело функтора, которое обернётся лямбдой.
    pub(crate) fn beneath<T>(
        &mut self,
        params: &[Param],
        body: impl FnOnce(&mut Self) -> Result<T, ElabError>,
    ) -> Result<T, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            return body(self);
        };
        let bound = self.typed(&param.ty);
        self.binding(Bound::visible(&param.name, param.mult, bound), |it| {
            it.beneath(rest, body)
        })
    }

    /// То же, но с членами объявляемой группы.
    pub(crate) fn with_group(
        signature: &'a Signature,
        metas: &'a mut Metas,
        owned: &'a Owned,
        fixities: &'a Fixities,
        group: Vec<Member>,
    ) -> Self {
        Self {
            signature,
            metas,
            owned,
            fixities,
            ctx: Ctx::new(signature),
            scope: Vec::new(),
            group,
            declared: Vec::new(),
            declared_suspends: false,
            declared_ty: None,
            expected: Vec::new(),
            result: None,
            bare: false,
            enclosing: None,
            using: Vec::new(),
            rows: None,
            lifted: None,
            tails: HashMap::new(),
            types: false,
            position: Position::Inner,
            produced: None,
            instantiated: HashMap::new(),
        }
    }

    /// Кратности написанного типа - те, что достанутся лямбдам тела.
    pub(crate) fn declaring(mut self, ty: &Term) -> Self {
        self.declared = pi_arguments(ty, self.owned);
        self.declared_ty = Some(eval(&Env::default(), ty));
        self
    }

    /// Отмечает, что первое связывание написанного типа синтезировал сахар
    /// `{ε} A`, и клауза вправе его не писать.
    ///
    /// Знание синтаксическое, поэтому и приходит оно от того, кто держит
    /// написанное. Метод инстанса его сегодня не получает: тип метода приходит
    /// из заголовка класса, а не из написанного при инстансе, и связывание там
    /// пишут как раньше.
    pub(crate) fn suspending(mut self, written: bool) -> Self {
        self.declared_suspends = written;
        self
    }

    /// Выполняет `body` в позиции типа.
    ///
    /// Несвязанное строчное имя означает здесь не опечатку, а свободную
    /// переменную, которую §4.1 поднимает в implicit-параметр, - и отвечать
    /// на неё «имя не найдено» значит отправить искать опечатку там, где её
    /// нет.
    pub(crate) fn typing<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.types, true);
        let outcome = body(self);
        self.types = outer;
        outcome
    }

    /// Телескоп параметров семейства: `data Vect (a : Type) : … where`.
    ///
    /// Элаборируется **один раз** на объявление и переиспользуется: kind и
    /// каждый конструктор обязаны нести один и тот же телескоп, а не два
    /// одинаково выглядящих. Домен, которого не написали (`data Pair a b`), -
    /// дырка: чем параметр окажется, скажет его употребление, ровно как у
    /// поднятого имени.
    ///
    /// # Errors
    ///
    /// Если тип параметра не элаборируется либо имя заглавное.
    /// `uppercase` - разрешено ли заглавное имя параметра.
    ///
    /// У семейства нет: `data Pair a b` называет типовые переменные, и правило
    /// регистра §4.1 держит их строчными. У функтора **есть**: его параметр -
    /// модуль, а модули заглавные, и §4.8 так и пишет - `(Key : Ord)`.
    /// Двусмысленности здесь нет и быть не может: имя стоит в написанной
    /// группе связываний, то есть связывает по форме записи, а не по регистру.
    ///
    /// `default` - кратность параметра, у которого она не написана. У
    /// **типового формера** - семейства, класса, алиаса - она нулевая:
    /// параметр в значении не хранится (§10 вопрос 78), и конструктор получает
    /// его так же, как поднятое имя получает `{0 a : Type}` (§4.1). Написав ей
    /// `ω`, язык лишился бы всякого полиморфного конструктора: `plain y = Wrap
    /// y` при `{0 b : Type}` требует `b` в параметре `Wrap`, и при ω-параметре
    /// это расход стёртой переменной. У **функтора** умолчание обычное: его
    /// параметр - модуль, значение с полями, и стирать его нечем.
    pub(crate) fn telescope(
        &mut self,
        params: &[ast::Binder],
        uppercase: bool,
        default: Mult,
    ) -> Result<Vec<Param>, ElabError> {
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        let mut found = Vec::new();
        for binder in params {
            for name in &binder.names {
                if !uppercase {
                    Self::binds(name)?;
                }
                // Ненаписанный тип параметра - `Type`, а не общая дырка:
                // `data Pair a b` называет типы, а параметр иного рода
                // пишется (`(0 n : Nat)`). Универсум семейства обязан
                // вместить уровни своих параметров, и без этого умолчания
                // считать их было бы нечем.
                let domain = match &binder.ty {
                    Some(ty) => self.typing(|it| it.expr(ty, Mult::Many))?,
                    None => Term::Universe(self.metas.fresh_level()),
                };
                let mult = match &binder.ty {
                    Some(ty) => self.binder_mult(binder.mult, ty, default, binder.span)?,
                    None => Self::multiplicity(binder.mult, default),
                };
                let bound = self.typed(&domain);
                self.ctx = self
                    .ctx
                    .bind(CoreName::from(&*name.text), mult, Rc::clone(&bound));
                self.scope.push(Bound::visible(&name.text, mult, bound));
                found.push(Param {
                    mult,
                    name: Rc::clone(&name.text),
                    ty: Rc::new(domain),
                });
            }
        }
        self.scope.truncate(depth);
        self.ctx = outer;
        Ok(found)
    }

    /// Тип терма, каким его видит ядро. `None` - не вывелся.
    pub(crate) fn inferred(&mut self, term: &Term) -> Option<Term> {
        let (ty, _) = infer(&self.ctx, self.metas, Mult::Zero, term).ok()?;
        Some(quote(self.ctx.size(), &ty))
    }

    /// Уровень универсума, в котором обязано жить семейство с такими
    /// параметрами.
    ///
    /// Поле конструктора типа `a` живёт там же, где `a`, то есть в универсуме
    /// параметра. Значит семейство обязано быть не ниже, иначе предикативность
    /// (§3.2) обходится через data-декларацию. Берётся максимум - наименьшее,
    /// что подходит; так же, как `Type 0` был наименьшим у семейства без
    /// параметров.
    #[must_use]
    pub(crate) fn sort(params: &[Param], written: Level) -> Level {
        params
            .iter()
            .fold(written, |found, param| match &*param.ty {
                Term::Universe(level) => found.max(level.clone()),
                _ => found,
            })
    }

    /// Выполняет `body` под параметрами и оборачивает результат в `Pi`.
    ///
    /// `implicit` - у kind параметры пишутся (`Vect a n`), у конструктора
    /// выводятся (`Nil`, а не `Nil Int`).
    pub(crate) fn wrapped(
        &mut self,
        params: &[Param],
        implicit: bool,
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            return body(self);
        };
        let bound = self.typed(&param.ty);
        let inner = self.binding(Bound::visible(&param.name, param.mult, bound), |it| {
            it.wrapped(rest, implicit, body)
        })?;
        let binder = if implicit {
            Binder::implicit(param.mult)
        } else {
            Binder::explicit(param.mult)
        };
        Ok(Term::Pi(
            binder,
            CoreName::from(&*param.name),
            Rc::clone(&param.ty),
            Row::empty(),
            Rc::new(inner),
        ))
    }

    /// Написанный тип объявления - со свободными именами, поднятыми в
    /// implicit-параметры (§4.1).
    ///
    /// `Nil : Vect a 0` объявляется как `{0 a : ?t} -> Vect a 0`. Кратность
    /// `0`: поднятое имя живёт в стёртом фрагменте, и платить за него в
    /// рантайме не за что.
    ///
    /// Тип связывания - **дырка**, а не `Type`: подъём не знает, чем имя
    /// окажется. `Cons : a -> Vect a n -> Vect a (n + 1)` поднимает `n`, и что
    /// это `Nat`, говорит только kind семейства. Дырку решает проверка - там же,
    /// где решает всё прочее.
    pub(crate) fn declaration(&mut self, ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        self.declared_type(ty, default, true)
    }

    /// То же для конструктора: подъём не применяется (§3.4).
    ///
    /// Тип конструктора приходит из `data`, и стрелки его - не позиции
    /// сигнатуры, а форма самого значения: поле его есть данные семейства, а
    /// семейство row-параметра не несёт. Открытая row у поля означала бы, что
    /// два `MkCell` с разными эффектами дают один тип `Cell`, а разбор потом
    /// не знает, какой из них лежит. Зваться откуда угодно конструктор при
    /// этом не перестаёт: пустую row гасит любая окружающая.
    pub(crate) fn constructor_type(&mut self, ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        // Отсутствие подъёма само по себе хвост не запрещает: написанный
        // руками проходил мимо него и делал конструктор row-полиморфным при
        // row-арности семейства нуль. Элиминация подставляет такому `&[]`, и
        // переменная остаётся свободной - тип получается тихо неверный: у двух
        // полей со своими хвостами номер параметра начинал зависеть от того,
        // какое из них тронуло тело, а законная программа, зовущая оба,
        // отвергалась непогашенностью с чужим именем в сообщении.
        self.unlifted(
            ty,
            default,
            "поле есть данные семейства, а семейство row-параметра не несёт - \
             напишите набор меток замкнутым",
        )
    }

    /// То же для члена класса и члена `module type` (§4.3).
    ///
    /// Свободные имена поднимаются в implicit-связывания **поля**, и универсум
    /// словаря считается по полям: член, квантифицирующий по `Type ℓ`,
    /// поднимает словарь на этаж выше. А row не поднимается, и причина другая,
    /// чем у конструктора: row-параметр принадлежит определению, связывания
    /// row в термах не существует, и хвосту у поля стать нечем.
    pub(crate) fn member_type(&mut self, ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        self.unlifted(
            ty,
            default,
            "row-параметр принадлежит определению, а член живёт в его теле - \
             связать хвост нечем",
        )
    }

    /// Общее у обоих: имена поднимаются, row - нет, написанный хвост отвергнут.
    fn unlifted(&mut self, ty: &Expr, default: Mult, why: &'static str) -> Result<Term, ElabError> {
        // Отсутствие подъёма само по себе хвост не запрещает: написанный
        // руками проходил мимо него и оставлял переменную свободной - тип
        // получался тихо неверный.
        if let Some(name) = written_row_tail(ty) {
            return Err(ElabError::WrittenRowTail {
                name: Rc::clone(&name.text),
                why,
                span: name.span,
            });
        }
        self.declared_type(ty, default, false)
    }

    fn declared_type(&mut self, ty: &Expr, default: Mult, lift: bool) -> Result<Term, ElabError> {
        let (names, tails) = self.unbound(ty);
        // Порядок связывания: сначала обычные свободные имена, потом
        // написанные хвосты, потом безымянные row-переменные подъёма. Все они
        // implicit, и порядок виден только `@`-применению; складывать разные
        // сорта в одну последовательность появления значило бы двигать позицию
        // `@`-аргумента от того, где в тексте случилась запись.
        let mut lifted: Vec<Lifted> = names
            .into_iter()
            .map(|name| Lifted { name, row: false })
            .chain(tails.into_iter().map(|name| Lifted { name, row: true }))
            .collect();
        // Записи сигнатуры получают row-переменную каждая своя, и собираются
        // они синтаксически - до элаборации, ровно как свободные имена: имя
        // связывания нужно знать раньше, чем оно понадобится.
        let mut rows = Vec::new();
        written_rows(ty, false, &mut rows);
        for index in 0..rows.len() {
            lifted.push(Lifted {
                name: Rc::from(format!("#row{index}").as_str()),
                row: true,
            });
        }
        self.rows = Some(rows);
        // Auto-lift (§3.4): свежая row-переменная на всю сигнатуру. Параметром
        // она станет обобщением на границе объявления - тем же проходом, что
        // делает параметрами уровни.
        self.lifted = lift.then(|| self.metas.fresh_row());
        self.tails.clear();
        let elaborated = self.lifting(&lifted, ty, default);
        self.lifted = None;
        elaborated
    }

    fn lifting(&mut self, lifted: &[Lifted], ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        let Some((first, rest)) = lifted.split_first() else {
            return self.typing(|it| it.expr(ty, default));
        };
        let level = self.metas.fresh_level();
        let domain = if first.row {
            Term::RowKind(level)
        } else {
            let sort = Rc::new(Value::Universe(level));
            self.fresh_meta(&sort)
        };
        let bound = self.ctx.eval(&domain);
        let body = self.under(&first.name, Mult::Zero, bound, |it| {
            it.lifting(rest, ty, default)
        })?;
        Ok(Term::Pi(
            Binder::implicit(Mult::Zero),
            CoreName::from(&*first.name),
            Rc::new(domain),
            Row::empty(),
            Rc::new(body),
        ))
    }

    /// Несвязанные имена написанного типа - те, что §4.1 поднимает в
    /// implicit-параметры: обычные и стоящие в хвосте записи.
    ///
    /// Порядок в каждой группе - первого появления в тексте: `Vect n a` даёт
    /// `{n} {a}`, и автор видит их там же, где написал. Отбираются строчные
    /// имена, которые ничем не разрешаются: заглавное обязано быть объявленным
    /// (правило регистра §4.1), а разрешившееся - не свободно.
    fn unbound(&self, expr: &Expr) -> (Vec<Symbol>, Vec<Symbol>) {
        let mut found = Unbound::default();
        let mut bound: Vec<Symbol> = Vec::new();
        self.free_in(expr, &mut bound, &mut found);
        (found.names, found.tails)
    }

    fn free_in(&self, expr: &Expr, bound: &mut Vec<Symbol>, found: &mut Unbound) {
        match &expr.kind {
            ExprKind::Name(name) => self.free_name(name, bound, found),
            // Метка row - объявленное имя, свободной быть не может; аргументы
            // её - обычные термы, и свободные имена в них поднимаются как
            // всюду. Хвост здесь не считается: он приходит с auto-lift.
            ExprKind::Effectful { labels, body, .. } => {
                self.free_in(body, bound, found);
                for argument in labels.iter().flat_map(|it| &it.arguments) {
                    self.free_in(argument, bound, found);
                }
            }
            // Имя инстанса свободным не считается: оно обязано быть
            // объявленным, как и всякая ссылка (§4.3).
            ExprKind::Using { body, .. } => self.free_in(body, bound, found),
            ExprKind::App(callee, argument) | ExprKind::TypeApp(callee, argument) => {
                self.free_in(callee, bound, found);
                self.free_in(argument, bound, found);
            }
            ExprKind::Arrow(domain, codomain) => {
                self.free_in(domain, bound, found);
                self.free_in(codomain, bound, found);
            }
            ExprKind::Chain(chain) => {
                self.free_in(&chain.head, bound, found);
                for (operator, operand) in &chain.tail {
                    self.free_name(operator, bound, found);
                    self.free_in(operand, bound, found);
                }
            }
            // Связывание закрывает своё имя для всего, что под ним. Тип группы
            // `(x y : A)` при этом читается до обоих имён - как и в самой
            // элаборации, где та же группа прячет их от собственного домена.
            ExprKind::Pi { binders, codomain } => {
                let depth = bound.len();
                for binder in binders {
                    if let Some(ty) = &binder.ty {
                        self.free_in(ty, bound, found);
                    }
                    bound.extend(binder.names.iter().map(|it| Rc::clone(&it.text)));
                }
                self.free_in(codomain, bound, found);
                bound.truncate(depth);
            }
            // Тип записи связывает свои поля для последующих: телескоп.
            // Хвост стоит снаружи полей и ими не заслоняется.
            ExprKind::RecordType(fields, tail) => {
                if let Some(tail) = tail {
                    self.tail_name(tail, bound, found);
                }
                let depth = bound.len();
                for field in fields {
                    self.free_in(&field.ty, bound, found);
                    bound.push(Rc::clone(&field.name.text));
                }
                bound.truncate(depth);
            }
            ExprKind::Record(fields) => {
                for (_, value) in fields {
                    self.free_in(value, bound, found);
                }
            }
            ExprKind::Project(record, _) => self.free_in(record, bound, found),
            ExprKind::Update(base, fields) => {
                self.free_in(base, bound, found);
                for (_, value) in fields {
                    self.free_in(value, bound, found);
                }
            }
            ExprKind::Lam { params, body } => {
                let depth = bound.len();
                for param in params {
                    match &param.kind {
                        LamParamKind::Pattern(pattern) => binds_names(pattern, bound),
                        LamParamKind::Binder(binder) => {
                            bound.extend(binder.names.iter().map(|it| Rc::clone(&it.text)));
                        }
                    }
                }
                self.free_in(body, bound, found);
                bound.truncate(depth);
            }
            // Формы, до которых элаборация типа не доходит вовсе: искать в них
            // свободные имена значило бы поднять параметр ради того, что всё
            // равно ответит `Missing`.
            ExprKind::Block(_)
            | ExprKind::If { .. }
            | ExprKind::Case { .. }
            | ExprKind::Handle { .. }
            | ExprKind::Tuple(_)
            | ExprKind::List(_)
            | ExprKind::Lit(_)
            | ExprKind::Hole => {}
        }
    }

    /// Как имя члена выглядит на верхнем уровне: `T` внутри `IntOrd` есть
    /// `IntOrd.T`. `None` - элаборируется не тело модуля.
    fn qualified_name(&self, name: &str) -> Option<Symbol> {
        let enclosing = self.enclosing.as_ref()?;
        Some(Rc::from(format!("{}.{name}", enclosing.name).as_str()))
    }

    /// Применяет ссылку на члена к параметрам функтора.
    ///
    /// Член поднят вместе с ними, поэтому написанное внутри `insert` есть
    /// `F.insert Key` - **специализированный** член, а не общий. Параметры
    /// стоят у него implicit-связываниями, и потому пишутся здесь, а не
    /// вставляются дырками: дырку пришлось бы решать унификацией, а ответ
    /// известен - это связывание, стоящее прямо в области видимости.
    fn specialized(&mut self, mut term: Term, mut ty: Rc<Value>) -> (Term, Rc<Value>) {
        let Some(enclosing) = self.enclosing.clone() else {
            return (term, ty);
        };
        let names: Vec<Symbol> = enclosing.names().map(Rc::clone).collect();
        for name in names {
            let Some(index) = self.local(&name) else {
                break;
            };
            let Value::Pi(_, _, _, _, codomain) = &*ty else {
                break;
            };
            let codomain = codomain.clone();
            let argument = Term::var(index);
            let value = self.ctx.eval(&argument);
            term = Term::App(Rc::new(term), Rc::new(argument));
            ty = codomain.apply(value);
        }
        (term, ty)
    }

    /// То же, но только если такой член уже объявлен.
    fn qualified(&self, name: &str) -> Option<Symbol> {
        let full = self.qualified_name(name)?;
        self.signature.lookup(&full).is_some().then_some(full)
    }

    /// Член объявляемой группы под своим именем или под квалифицированным.
    ///
    /// Второе - рекурсивная ссылка внутри модуля: определение объявлено как
    /// `NatEq.eq`, а в теле написано `eq`, и найти себя оно обязано.
    fn member_of_group(&self, name: &str) -> Option<&Member> {
        let full = self.qualified_name(name);
        self.group.iter().find(|member| {
            *member.name == *name || full.as_ref().is_some_and(|it| member.name == *it)
        })
    }

    fn free_name(&self, name: &ast::Name, bound: &[Symbol], found: &mut Unbound) {
        if !self.resolves(name, bound) && !found.has(&name.text) {
            found.names.push(Rc::clone(&name.text));
        }
    }

    /// Имя в хвосте записи. Поднимается как ряд, а не как тип: `{x : Nat | r}`
    /// говорит про `r` всё, что о нём нужно знать.
    ///
    /// Если то же имя уже поднято обычным свободным, оно **переезжает** в ряды:
    /// сорт назначает написанная позиция, а порядок обхода - нет.
    fn tail_name(&self, name: &ast::Name, bound: &[Symbol], found: &mut Unbound) {
        if self.resolves(name, bound) || found.tails.contains(&name.text) {
            return;
        }
        found.names.retain(|it| *it != name.text);
        found.tails.push(Rc::clone(&name.text));
    }

    /// Разрешается ли имя чем-то, кроме подъёма.
    fn resolves(&self, name: &ast::Name, bound: &[Symbol]) -> bool {
        is_reference(&name.text)
            || &*name.text == "Type"
            || bound.contains(&name.text)
            || self.local(&name.text).is_some()
            || self.member_of_group(&name.text).is_some()
            || self.qualified(&name.text).is_some()
            || self.signature.lookup(&name.text).is_some()
    }

    /// Универсум написанного типа - в текущем контексте, а не в пустом.
    ///
    /// Нужно телу функтора: тип его члена живёт под параметрами, и считать
    /// его сортом в пустом контексте нечем.
    ///
    /// # Errors
    ///
    /// Если написанное типом не является.
    /// Глубина контекста элаборации.
    pub(crate) fn depth(&self) -> u32 {
        self.ctx.size()
    }

    pub(crate) fn sort_of(&mut self, term: &Term) -> Result<Level, adamas_core::check::TypeError> {
        is_type(&self.ctx, self.metas, term)
    }

    /// Свежая дырка терма, стоящая в текущем контексте.
    ///
    /// Тип её - телескоп по контексту, оканчивающийся целью: дырка замкнута, и
    /// зависимость от связываний выражена применением к ним. Кратности
    /// телескопа - `0`: дырку заводят на месте типа, а тип живёт в стёртом
    /// фрагменте, и применение к контексту не должно ничего расходовать.
    fn fresh_meta(&mut self, goal: &Rc<Value>) -> Term {
        self.fresh_meta_outside(goal, 0)
    }

    /// То же, но телескоп собирается **без** `skip` внутренних связываний.
    ///
    /// Дырка тогда от них не зависит, а индексы спайна всё равно считаются для
    /// сегодняшнего контекста - того, что глубже. Нужно это цели разбора:
    /// мотив переписывает разбираемое в собственное связывание, не трогая
    /// индексы, и дырка, у которой разбираемое стоит в спайне, перестаёт быть
    /// типизируемой. `case v of Nil -> True` над `Vect Zero` отвечало
    /// «ожидался `Vect Zero`, получен `Vect #1`», а побуквенно та же клауза
    /// проходила.
    fn fresh_meta_outside(&mut self, goal: &Rc<Value>, skip: usize) -> Term {
        let size = self.ctx.size();
        let outer = u32::try_from(self.scope.len().saturating_sub(skip)).unwrap_or(u32::MAX);
        let mut telescope = quote(outer, goal);
        let mut spine = Vec::new();
        let kept = self.scope.len().saturating_sub(skip);
        for (depth, bound) in self.scope[..kept].iter().enumerate().rev() {
            let depth = u32::try_from(depth).unwrap_or(u32::MAX);
            let ty = Rc::new(quote(depth, &bound.ty));
            let name = CoreName::from(&*bound.name);
            // Связывание со значением идёт `Let`ом: индексы цели считаны по
            // всему контексту, и пропустить его значило бы их сдвинуть.
            // Вычисление телескопа его подставит - ровно так же, как подставит
            // проверка, - и параметром дырки оно не станет.
            telescope = if let Some(value) = &bound.value {
                Term::Let(Mult::Zero, name, ty, Rc::clone(value), Rc::new(telescope))
            } else {
                spine.push(depth);
                Term::Pi(
                    Binder::explicit(Mult::Zero),
                    name,
                    ty,
                    Row::empty(),
                    Rc::new(telescope),
                )
            };
        }
        spine.reverse();
        let closed = eval(&Env::default(), &telescope);
        self.metas.fresh_term_over(closed, &spine, size)
    }

    /// Тип связывания как значение - настолько, насколько он известен.
    ///
    /// **Проверка обязательна перед вычислением, а не желательна:** `eval`
    /// вправе паниковать на нетипизированном входе, а элаборация вычисляет то,
    /// что ядро ещё не смотрело. Без этой проверки первый же неверно
    /// написанный домен ронял бы процесс вместо отказа.
    ///
    /// **Отказ ядра здесь не отказ элаборации, а «типа пока нет».** Причин
    /// две, и обе законные. Тип может быть неверен - тогда об этом скажет
    /// `check`, которому терм и уйдёт: он авторитет, а не этот проход. И тип
    /// может называть члена объявляемой группы (`Succ : Nat -> Nat`), которого
    /// в сигнатуре ещё нет по построению (§10 вопрос 50), - здесь это не
    /// ошибка вовсе.
    ///
    /// Контекст элаборации поэтому **best-effort**: он нужен ей самой - чтобы
    /// строить типы дырок, - и полнота его не влияет ни на принимаемые
    /// программы, ни на отвергаемые. Названная цена: под связыванием, тип
    /// которого не сошёлся, вставка имплиситов знает меньше.
    /// Терм значением - без проверки, что он тип.
    pub(crate) fn valued(&self, term: &Term) -> Rc<Value> {
        self.ctx.eval(term)
    }

    pub(crate) fn typed(&mut self, term: &Term) -> Rc<Value> {
        if is_type(&self.ctx, self.metas, term).is_err() {
            return self.hole();
        }
        self.ctx.eval(term)
    }

    /// Дырка на месте типа, которого не написали.
    fn hole(&mut self) -> Rc<Value> {
        let level = self.metas.fresh_level();
        let sort = Rc::new(Value::Universe(level));
        let meta = self.fresh_meta(&sort);
        self.ctx.eval(&meta)
    }

    /// Выполняет `body` под связыванием `name` типа `ty`.
    fn under<T>(
        &mut self,
        name: &Symbol,
        mult: Mult,
        ty: Rc<Value>,
        body: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.binding(Bound::visible(name, mult, ty), body)
    }

    /// То же, но связывание несёт свойства владения и привязки к scope (§3.3).
    ///
    /// Область видимости и типовой контекст двигаются вместе и только здесь:
    /// разойдись они, индекс де Брёйна указывал бы на одно связывание, а тип -
    /// на другое.
    fn binding<T>(&mut self, bound: Bound, body: impl FnOnce(&mut Self) -> T) -> T {
        let inner = self.ctx.bind(
            CoreName::from(&*bound.name),
            bound.mult,
            Rc::clone(&bound.ty),
        );
        let outer = std::mem::replace(&mut self.ctx, inner);
        self.scope.push(bound);
        let outcome = body(self);
        self.scope.pop();
        self.ctx = outer;
        outcome
    }

    /// Чем лямбда привязана к scope: захваченным владеющим связыванием либо
    /// захваченным значением, которое само привязано.
    ///
    /// Сам по себе захват законен - §3.3 разрешает применить такую лямбду и
    /// передать её аргументом. Незаконен **побег**, и его ловит позиция.
    fn captured(&self, body: &Expr) -> Option<&Symbol> {
        self.scope
            .iter()
            .rev()
            .find(|bound| {
                bound.visible && (bound.owned || bound.scoped) && self.mentions(&bound.name, body)
            })
            .map(|bound| &bound.name)
    }

    /// Расходуется ли `name` в теле - правило вставки `drop` (см.
    /// [`crate::live`]). Кратности параметров берутся из сигнатуры, а
    /// локальные имена - из текущей области видимости: затенённая голова
    /// применения чужих кратностей не получает.
    fn mentions(&self, name: &str, body: &Expr) -> bool {
        self.mentions_beside(name, body, &[])
    }

    /// То же, но связывания, которых в области видимости ещё нет: решение о
    /// вставке принимается **до** того, как переменные клаузы и параметры
    /// лямбды туда попадут, а затенять голову они уже вправе.
    fn mentions_beside(&self, name: &str, body: &Expr, beside: &[Symbol]) -> bool {
        let mut locals = self.locals();
        locals.extend_from_slice(beside);
        live::Spent::new(self.signature, &locals).mentions(name, body)
    }

    /// То же для того, что стоит после связывания `let`.
    fn mentioned_later(&self, name: &str, tail: &[Binding], rest: &[Stmt]) -> bool {
        let locals = self.locals();
        live::Spent::new(self.signature, &locals).in_bindings_body(name, tail, rest)
    }

    /// Видимые локальные имена.
    fn locals(&self) -> Vec<Symbol> {
        self.scope
            .iter()
            .filter(|bound| bound.visible)
            .map(|bound| Rc::clone(&bound.name))
            .collect()
    }

    /// Привязано ли имя к scope своим связыванием.
    fn scoped_name(&self, name: &str) -> Option<&Symbol> {
        self.scope
            .iter()
            .rev()
            .find(|bound| bound.visible && bound.scoped && &*bound.name == name)
            .map(|bound| &bound.name)
    }

    /// Выполняет `body` в позиции `position`.
    fn placed<T>(&mut self, position: Position, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.position, position);
        let outcome = body(self);
        self.position = outer;
        outcome
    }

    /// Выполняет `body` вне хвостовой позиции: ожидаемый результат снимается.
    ///
    /// Аргумент применения результатом объемлющего не является, и `handle` в
    /// нём обязан выводить свой ответ сам.
    fn aside<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = self.result.take();
        let outcome = body(self);
        self.result = outer;
        outcome
    }

    /// Выполняет `body`, спрятав `count` последних связываний.
    ///
    /// Спрятанное связывание место в контексте занимает, а имени не имеет:
    /// индексы де Брёйна остаются верными, а поиск по имени сквозь него
    /// проходит наружу. Нужно это ровно группе `(x y : A)`, где `A` написано
    /// раньше обоих имён и видеть их не может.
    fn hiding<T>(&mut self, count: usize, body: impl FnOnce(&mut Self) -> T) -> T {
        let from = self.scope.len() - count;
        for bound in &mut self.scope[from..] {
            bound.visible = false;
        }
        let outcome = body(self);
        for bound in &mut self.scope[from..] {
            bound.visible = true;
        }
        outcome
    }

    /// Точечное имя целиком, если каждое его звено - имя, а не выражение.
    ///
    /// Связывание обрывает разбор: `m.f` при локальном `m` - проекция из
    /// записи, что бы ни было объявлено под именем `m.f`.
    fn dotted(&self, expr: &Expr) -> Option<String> {
        match &expr.kind {
            ExprKind::Name(name) => self
                .local(&name.text)
                .is_none()
                .then(|| name.text.to_string()),
            ExprKind::Project(inner, field) => {
                let prefix = self.dotted(inner)?;
                Some(format!("{prefix}.{}", field.text))
            }
            _ => None,
        }
    }

    /// Поднятый член под точечным именем - если он объявлен.
    ///
    /// Не объявлен - значит префикс модулем не был (или поля с таким именем у
    /// него нет), и об этом скажет проекция, у которой есть тип записи.
    fn member(&self, record: &Expr, field: &str) -> Option<Symbol> {
        let full: Symbol = Rc::from(format!("{}.{field}", self.dotted(record)?).as_str());
        // Сосед по модулю заслоняет глобальное имя тем же правилом, что и у
        // простого имени: `N.f` внутри `M` - это `M.N.f`.
        let neighbour = self
            .qualified_name(&full)
            .is_some_and(|it| self.signature.lookup(&it).is_some());
        (neighbour || self.signature.lookup(&full).is_some()).then_some(full)
    }

    /// Индекс де Брёйна локального связывания.
    fn local(&self, name: &str) -> Option<u32> {
        self.scope
            .iter()
            .rposition(|bound| bound.visible && &*bound.name == name)
            .and_then(|position| u32::try_from(self.scope.len() - 1 - position).ok())
    }

    /// Имя, которое связывает, обязано быть строчным (§4.1).
    ///
    /// Заглавное ссылается на объявленное, и связывать им значило бы заслонить
    /// то, на что оно ссылается: `let Zero : Nat = …` делал конструктор
    /// недостижимым до конца блока.
    fn binds(name: &ast::Name) -> Result<(), ElabError> {
        if is_reference(&name.text) {
            return Err(ElabError::UppercaseBinding {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        }
        Ok(())
    }

    /// Кратность связывания: написанная либо умолчание позиции (§4.1).
    fn multiplicity(written: Option<ast::MultAnn>, default: Mult) -> Mult {
        written.map_or(default, |ann| match ann.mult {
            ast::Mult::Zero => Mult::Zero,
            ast::Mult::One => Mult::One,
            ast::Mult::Many => Mult::Many,
        })
    }

    /// То же, с поправкой на владение (§3.3).
    ///
    /// Связывание unique- или resource-типа получает `1`, если не объявлено
    /// `0`: стёртые упоминания в доказательствах законны, а вот явное `ω` -
    /// ошибка **на самом связывании**. Так закрывается дыра ω→1: значений
    /// такого типа при кратности `ω` не существует, потому что не существует
    /// связывания, которое их удержало бы.
    fn binder_mult(
        &self,
        written: Option<ast::MultAnn>,
        ty: &Expr,
        default: Mult,
        span: Span,
    ) -> Result<Mult, ElabError> {
        let Some(owned) = self.owned.of(ty) else {
            return Ok(Self::multiplicity(written, default));
        };
        match written.map(|ann| ann.mult) {
            None | Some(ast::Mult::One) => Ok(Mult::One),
            Some(ast::Mult::Zero) => Ok(Mult::Zero),
            Some(ast::Mult::Many) => Err(ElabError::UnrestrictedOwned {
                owned,
                span: written.map_or(span, |ann| ann.span),
            }),
        }
    }

    /// Выражение в терм.
    ///
    /// `default` - кратность связываний, у которых она не написана: `ω` у
    /// параметра функции, `1` у поля конструктора (§4.1). Умолчание
    /// **позиционное**: оно расходуется на связывание, к которому пришло, и
    /// доходит только до кодомена - там стоит следующий параметр той же
    /// сигнатуры. В домен и в любой другой подтерм элаборация уходит с `ω`:
    /// `(Nat -> Nat) -> C` берёт поле типа «функция», а не поле с кратностью
    /// поля.
    pub(crate) fn expr(&mut self, expr: &Expr, default: Mult) -> Result<Term, ElabError> {
        // Кратности ждут ближайшую лямбду и только её: подтерм, до которого
        // спустились иначе, написанным типом не накрыт.
        let expected = std::mem::take(&mut self.expected);
        // То же с позицией: её выставляет тот, кто спускается, и достаётся она
        // ближайшему подтерму, а не всему, что под ним.
        let position = std::mem::replace(&mut self.position, Position::Inner);
        // Свойство «привязано к scope» считается снизу вверх, и каждый разбор
        // отвечает за своё: собранное здесь не наследует чужого.
        self.produced = None;
        let term = self.form(expr, default, &expected, position)?;
        // Позиция встречается со свойством: привязанное к scope значение
        // возвращать и класть в поле конструктора нельзя (§3.3).
        if let (Some(face), Some(name)) = (position.face(), self.produced.as_ref()) {
            return Err(ElabError::ScopeBound {
                name: Rc::clone(name),
                face,
                span: expr.span,
            });
        }
        Ok(term)
    }

    /// Форма выражения - без правила позиции, которое стоит вокруг неё.
    fn form(
        &mut self,
        expr: &Expr,
        default: Mult,
        expected: &[Argument],
        position: Position,
    ) -> Result<Term, ElabError> {
        let missing = |what| {
            Err(ElabError::Missing {
                what,
                span: expr.span,
            })
        };
        match &expr.kind {
            // `using p expr` - выбор именованного инстанса на всё, что правее
            // (§4.3). Класс берётся из типа самого инстанса: заключение его
            // есть применение класса, и другого источника не нужно.
            ExprKind::Using { name, body } => {
                let Some(class) = self.class_of(&name.text) else {
                    return Err(ElabError::UnknownName {
                        name: Rc::clone(&name.text),
                        span: name.span,
                    });
                };
                self.using.push((class, Rc::clone(&name.text)));
                let inner = self.expr(body, default);
                self.using.pop();
                inner
            }
            ExprKind::Name(name) => {
                if let Some(scoped) = self.scoped_name(&name.text) {
                    self.produced = Some(Rc::clone(scoped));
                }
                self.name(name)
            }
            // Спайн собирается циклом. Рекурсия по `callee` уходила на глубину
            // числа аргументов, а его ограничивает только длина файла: предел
            // вложенности парсера на плоское `f a b c …` не тратится, и тысячи
            // аргументов роняли процесс вместо отказа (§10 вопрос 62).
            ExprKind::App(..) => self.application(expr),
            ExprKind::Arrow(domain, codomain) => self.arrow(domain, codomain, default, expr.span),
            ExprKind::Pi { binders, codomain } => self.pi(binders, codomain, default),
            ExprKind::Effectful { .. } => self.suspended(expr, default),
            ExprKind::Lam { params, body } => {
                // Захват - то, чем лямбда привязывается к scope. Позиция
                // решает снаружи; здесь только считается свойство, и ставится
                // оно **после** сборки: тело - тоже выражение, и свой ответ
                // оно затрёт своим.
                let captured = self.captured(body).cloned();
                let term = self.lam(params, body, expected)?;
                self.produced = captured;
                Ok(term)
            }
            ExprKind::Block(block) => self.block(block, position),
            ExprKind::Chain(chain) => self.chain(chain, expr.span),

            // Тип записи - телескоп: каждое следующее поле элаборируется под
            // предыдущими, потому что вправе на них ссылаться (§4.2).
            ExprKind::RecordType(fields, tail) => {
                self.record_type(fields, tail.as_ref(), expr.span)
            }
            ExprKind::Record(fields) => self.record(fields),
            ExprKind::Project(record, name) => {
                // Точечное имя, чей префикс называет объявленный модуль, есть
                // ссылка на **поднятый член**, а не проекция из записи. Внутри
                // модуля так было всегда; снаружи проекция теряла аргументы
                // уровня тех членов, которых не касалась (решение 2026-08-31).
                if let Some(full) = self.member(record, &name.text) {
                    return self.name(&ast::Name {
                        text: full,
                        span: name.span,
                    });
                }
                let inner = self.placed(Position::Inner, |it| it.expr(record, Mult::Many))?;
                Ok(Term::Project(Rc::new(inner), CoreName::from(&*name.text)))
            }
            ExprKind::Update(base, fields) => self.update(base, fields, expr.span),
            ExprKind::TypeApp(..) => self.type_app(expr),

            // `_` - дырка терма: решать её теперь есть чем, и нерешённая
            // доезжает до объявления своим отказом (`AmbiguousTerm`), а не
            // «механизма нет».
            ExprKind::Hole => {
                let goal = self.hole();
                Ok(self.fresh_meta(&goal))
            }
            ExprKind::Lit(lit) => self.literal(lit),
            // `if` - разбор по `Bool` (§4.1), и записывается он ровно им:
            // отдельного узла в ядре нет, а различать их было бы двумя путями
            // к одному терму.
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let alts = conditional(then_branch, else_branch);
                self.case(cond, &alts, expr.span, position)
            }
            ExprKind::Case { scrutinee, alts } => self.case(scrutinee, alts, expr.span, position),
            ExprKind::Handle {
                multi,
                label,
                computation,
                branches,
            } => self.handled(Handled {
                multi: *multi,
                label: label.as_deref(),
                computation,
                branches,
                span: expr.span,
            }),
            ExprKind::Tuple(items) if items.is_empty() => missing(Missing::Unit),
            ExprKind::Tuple(_) => missing(Missing::Tuple),
            ExprKind::List(items) => self.list(items, expr.span),
        }
    }

    /// `case e of …` - разбор выражением (§4.1).
    ///
    /// # Разбор компилируется тем же компилятором, что и клаузы
    ///
    /// Вложенные паттерны, порядок «побеждает первая совпавшая» и проверка
    /// полноты уже написаны ([`adamas_core::pattern`]), и второй экземпляр
    /// этого не нужен ни здесь, ни где-либо ещё. Компилятор работает с
    /// колонкой-**связыванием**, поэтому разбор идёт по нему: написанное
    /// переменной берётся как есть, прочее связывается `let`ом - одним
    /// связыванием, а не всем контекстом.
    ///
    /// **Подъём в функцию от контекста отменён** (§10 вопрос 82, закрыт логом
    /// 2026-09-02 вариантом «узел в ядре»). Применение к `Γ` засчитывалось как
    /// безусловное употребление каждого связывания контекста, включая те,
    /// которых ни одна ветвь не называет, - и оттуда же шли ещё три
    /// расхождения с §3.3: позиция до ветвей не доходила, поветвенной вставки
    /// `drop` не возникало, размеры для тотальности терялись. Все четыре были
    /// одной формой и исчезли вместе с ней.
    ///
    /// # Мотив недепендентный, и это названная граница
    ///
    /// Тип результата - дырка. Заводится она **вне** связывания разбираемого
    /// (см. `discriminated`), поэтому разбор над семейством с написанным
    /// индексом проходит; зависеть от самого разбираемого мотив по-прежнему не
    /// может. `case` над `Vect a n`, чей результат меняется от ветви к ветви,
    /// отсюда не пишется; ему нужен написанный мотив, и это отдельный срез.
    fn case(
        &mut self,
        scrutinee: &Expr,
        alts: &[ast::Alt],
        span: Span,
        position: Position,
    ) -> Result<Term, ElabError> {
        if alts.is_empty() {
            return Err(ElabError::EmptyCase { span });
        }
        let value = self.placed(Position::Inner, |it| it.expr(scrutinee, Mult::Many))?;
        let Some(ty) = self.synthesized(&value) else {
            return Err(ElabError::NotMatchable { span });
        };
        // Разбор идёт по **связыванию**: колонка у ядра - переменная, а не
        // терм. Написанное переменной берётся как есть, и терм выходит тот же,
        // что у клауз; прочее связывается `let`ом - **одним** связыванием, а не
        // всем контекстом. Применение к контексту расходовало бы всякое его
        // `1`-связывание, которого ни одна ветвь не называет (§10 вопрос 82).
        if let Term::Var(index) = &value {
            if let Some(level) = index.to_level(self.ctx.size()) {
                return self.discriminated(level, alts, span, position);
            }
        }
        let domain = quote(self.ctx.size(), &ty);
        let mult = self.consumption(scrutinee, &domain);
        let name: Symbol = Rc::from("case");
        let outer = self.scope.len();
        let saved = self.ctx.clone();
        self.ctx = self.ctx.bind(CoreName::from(&*name), mult, Rc::clone(&ty));
        self.scope.push(Bound {
            visible: false,
            ..Bound::visible(&name, mult, ty)
        });
        let inner = self.discriminated(Lvl(self.ctx.size() - 1), alts, span, position);
        self.scope.truncate(outer);
        self.ctx = saved;
        Ok(Term::Let(
            mult,
            CoreName::from(&*name),
            Rc::new(domain),
            Rc::new(value),
            Rc::new(inner?),
        ))
    }

    /// Разбор по связыванию: дерево строит тот же компилятор, что и у клауз.
    ///
    /// Лямбд вокруг дерева нет и контекст в аргументы не поднимается: тела
    /// ветвей живут под тем же контекстом, что и сам разбор, поэтому кратности
    /// считаются поветвенно - ядром, а не элаборацией.
    fn discriminated(
        &mut self,
        level: Lvl,
        alts: &[ast::Alt],
        span: Span,
        position: Position,
    ) -> Result<Term, ElabError> {
        // Цель заводится **без** разбираемого в спайне: связывание его стоит
        // последним - его только что положил вызывающий, - а мотив перепишет
        // его в своё, оставив индексы прежними. Дырка, зависящая от него,
        // после этого не типизируется, и `case` над семейством с неголым
        // индексом отвергался там, где клауза проходила.
        let sort = Rc::new(Value::Universe(self.metas.fresh_level()));
        let result = self.fresh_meta_outside(&sort, 1);
        let mut clauses = Vec::with_capacity(alts.len());
        // Паттерны собираются заранее: они затеняют имена в своих телах, а
        // решение о вставке `drop` принимается до спуска в тело.
        let patterns = alts
            .iter()
            .map(|alt| self.pattern(&alt.pattern))
            .collect::<Result<Vec<_>, _>>()?;
        let forgotten = self.forgotten(alts, &patterns);
        // Позиция разбора достаётся **каждой** ветви: разбор сам значения не
        // строит, его строят ветви, и возвращается наружу то, что построила
        // сработавшая. Без этого `if c then k else k` отмывал бы привязку к
        // scope, которую прямое `k` не проходит (§10 вопрос 82).
        let mut produced = None;
        for ((alt, pattern), closing) in alts.iter().zip(patterns).zip(&forgotten) {
            let body = self.placed(position, |it| {
                it.branch(&alt.pattern, &pattern, &alt.body, closing)
            })?;
            produced = produced.or_else(|| self.produced.take());
            clauses.push(Clause {
                patterns: vec![pattern],
                body,
            });
        }
        let tree =
            compile_case(&self.ctx, self.metas, level, &result, &clauses).map_err(|error| {
                ElabError::Clauses {
                    span: alts
                        .get(clause_of(&error))
                        .map_or(span, |alt: &ast::Alt| alt.span),
                    error: Box::new(error),
                }
            })?;
        self.produced = produced;
        Ok(tree.term)
    }
    /// Что каждая ветвь обязана закрыть сама.
    ///
    /// Ресурс, которого не называет **ни одна** ветвь, закрывает правило
    /// снаружи - там решение и принимается, по телу целиком. Ресурс, который
    /// называют **все**, закрывать не надо вовсе. Остаётся середина: одна ветвь
    /// его расходует, другая забыла, - и забывшая обязана закрыть его сама,
    /// иначе второй путь течёт.
    ///
    /// Это переоткрытый §10 вопрос 71: «клауза и есть ветвь» верно ровно до тех
    /// пор, пока разбор не написан выражением - он заводит ветвь **внутри**
    /// того, что видит правило.
    fn forgotten(&self, alts: &[ast::Alt], patterns: &[CorePattern]) -> Vec<Vec<(Symbol, Symbol)>> {
        let mut found = vec![Vec::new(); alts.len()];
        let owned: Vec<(Symbol, Symbol)> = self
            .scope
            .iter()
            // Стёртое не закрывается: `drop` расходует ресурс, а расходовать
            // стёртое связывание нечем (§10 вопрос 71).
            .filter(|bound| bound.visible && bound.owned && bound.mult != Mult::Zero)
            .filter_map(|bound| {
                head_name(&bound.ty)
                    .and_then(|name| self.owned.destructor_of(name))
                    .map(|drop| (Rc::clone(&bound.name), Rc::clone(drop)))
            })
            .collect();
        for (name, drop) in owned {
            let mentioned: Vec<bool> = alts
                .iter()
                .zip(patterns)
                .map(|(alt, pattern)| {
                    let mut beside = Vec::new();
                    variables_of(pattern, &mut beside);
                    // Затенённое имя ветвь не называет, чем бы ни было
                    // написано в теле: `Full h -> h` при внешнем ресурсном `h`
                    // говорит о своём поле. Список `beside` этого не решает -
                    // он про то, у каких имён не спрашивать кратность в
                    // сигнатуре, - и без явной проверки упоминание затеняющего
                    // засчитывалось ресурсу, а путь оставался незакрытым.
                    !beside.iter().any(|it| **it == *name)
                        && self.mentions_beside(&name, &alt.body, &beside)
                })
                .collect();
            if !mentioned.iter().any(|it| *it) {
                continue;
            }
            for (at, seen) in mentioned.iter().enumerate() {
                if !seen {
                    found[at].push((Rc::clone(&name), Rc::clone(&drop)));
                }
            }
        }
        found
    }

    /// `{ε} A` - нульместная функция `(ω _ : Unit) -> ε ▷ A` (§3.4).
    ///
    /// Приостановленное вычисление в строгом языке (§3.1) есть замыкание без
    /// аргументов, а нульместных функций в ядре нет: их место занимает
    /// аргумент-единица. Регресса при этом не возникает - внутренняя `ε ▷ A`
    /// не самостоятельный тип, а поле и кодомен той же стрелки.
    ///
    /// Единица берётся **по имени**, тем же соглашением, каким `if` берёт
    /// `Bool` с `True` и `False`: не объявлена - откажет обычный поиск, и
    /// скажет он про имя, а не про форму, которая его позвала.
    fn suspended(&mut self, expr: &Expr, default: Mult) -> Result<Term, ElabError> {
        let (row, body) = split_row(expr);
        let row = self.effects(row)?;
        let unit = self.name(&ast::Name {
            text: Rc::from("Unit"),
            span: expr.span,
        })?;
        let anonymous: Symbol = Rc::from("_");
        let bound = self.typed(&unit);
        let body = self.under(&anonymous, Mult::Many, bound, |it| it.expr(body, default))?;
        Ok(Term::Pi(
            Binder::explicit(Mult::Many),
            CoreName::from("_"),
            Rc::new(unit),
            row,
            Rc::new(body),
        ))
    }

    /// Row, написанная перед типом, в поле `Pi` (§3.4).
    ///
    /// Метка обязана оканчиваться сортом `Effect`: `{Maybe Int}` - не row, а
    /// ошибка, и сказать об этом должен тот, кто её читает. Проверяет это
    /// обычный вывод типа применения: строить второе правило для того же
    /// вопроса незачем.
    fn effects(&mut self, written: Option<&Expr>) -> Result<Row<Term>, ElabError> {
        let Some(row) = written else {
            return Ok(self.opened());
        };
        let ExprKind::Effectful { labels, tail, .. } = &row.kind else {
            return Ok(self.opened());
        };
        // Написанный хвост закрывает auto-lift на этой позиции: программист
        // управляет полиморфизмом сам (§3.4). Одноимённые хвосты одной
        // сигнатуры - один параметр.
        let tail = match tail {
            Some(name) => self.named_tail(&name.text),
            None => self.opened(),
        };
        let written = labels;
        let mut labels = Vec::with_capacity(written.len());
        for label in written {
            let head = self.name(&label.name)?;
            let Term::Const(name, ..) = &head else {
                return Err(ElabError::NotAnEffect {
                    name: Rc::clone(&label.name.text),
                    span: label.span,
                });
            };
            let name = CoreName::from(&**name);
            let mut arguments = Vec::with_capacity(label.arguments.len());
            let mut applied = head.clone();
            for argument in &label.arguments {
                let argument = self.typing(|it| it.expr(argument, Mult::Many))?;
                applied = Term::App(Rc::new(applied), Rc::new(argument.clone()));
                arguments.push(argument);
            }
            // Через `synthesized`, а не напрямую: метка объявляемого эффекта
            // сигнатуре ещё не известна, а собственная операция называет её по
            // построению - в её же row.
            let sorted = self.synthesized(&applied);
            if !matches!(sorted.as_deref(), Some(Value::EffectKind)) {
                return Err(ElabError::NotAnEffect {
                    name: Rc::clone(&label.name.text),
                    span: label.span,
                });
            }
            labels.push(Label { name, arguments });
        }
        Ok(Row::closing(labels, tail.tail()))
    }

    /// Совпадают ли аргументы метки с написанными.
    fn same_arguments(&mut self, found: &[Rc<Value>], wanted: &[Rc<Value>]) -> bool {
        found.len() == wanted.len()
            && found.iter().zip(wanted).all(|(found, wanted)| {
                convertible(self.signature, self.metas, self.ctx.size(), found, wanted)
            })
    }

    /// `A -> B`: связывание без имени.
    ///
    /// Правило владения (§3.3) действует и здесь: `drop : File -> Unit` даёт
    /// `(1 _ : File) -> Unit`, и писать кратность руками не нужно. Домен-
    /// универсум даёт `0` - см. [`kinded`].
    fn arrow(
        &mut self,
        domain: &Expr,
        codomain: &Expr,
        default: Mult,
        span: Span,
    ) -> Result<Term, ElabError> {
        let mult = self.binder_mult(None, domain, kinded(None, domain, default), span)?;
        let domain = self.expr(domain, Mult::Many)?;
        let anonymous: Symbol = Rc::from("_");
        let bound = self.typed(&domain);
        // Row снимается с кодомена и встаёт полем стрелки: написана она перед
        // типом результата, а описывает применение (§3.4).
        let (row, codomain) = split_row(codomain);
        let row = self.effects(row)?;
        let codomain = self.under(&anonymous, mult, bound, |inner| {
            inner.expr(codomain, default)
        })?;
        Ok(Term::Pi(
            // Стрелка пишется без скобок, поэтому связывание у неё явное:
            // выводить нечего, аргумент стоит в месте вызова.
            Binder::explicit(mult),
            CoreName::from("_"),
            Rc::new(domain),
            row,
            Rc::new(codomain),
        ))
    }

    /// Числовой литерал (§4.3).
    ///
    /// `42` разворачивается унарно в `Succ`-цепочку над `Zero` и, если
    /// `fromNat` объявлена, применяется к ней. Имена берутся по соглашению -
    /// тем же, каким `if` берёт `Bool`, а сахар `{ε} A` берёт `Unit`.
    ///
    /// **Названная цена: терм литерала размером с само число.** Примитивного
    /// числа в ядре нет, оно приходит с представлением (§4.9, Фаза 6), а до
    /// него `42` есть сорок два конструктора. Предел вложенности это знает и
    /// считает литерал по значению.
    ///
    /// Отрицательные и дробные не пишутся: им нужны `Int` и `Float`, которых
    /// без примитивного представления не существует.
    fn literal(&mut self, lit: &ast::Lit) -> Result<Term, ElabError> {
        let refuse = || {
            Err(ElabError::Missing {
                what: Missing::Literal,
                span: lit.span,
            })
        };
        if lit.kind != ast::LitKind::Nat {
            return refuse();
        }
        let Ok(value) = lit.text.parse::<u32>() else {
            return refuse();
        };
        let named = |text: &str| ast::Name {
            text: Rc::from(text),
            span: lit.span,
        };
        let zero = self.name(&named(ZERO))?;
        let successor = self.name(&named(SUCC))?;
        let numeral = (0..value).fold(zero, |built, _| {
            Term::App(Rc::new(successor.clone()), Rc::new(built))
        });
        // Преобразование применяется, только если объявлено: без него литерал
        // и есть число, и требовать класс ради `x : Nat` значило бы требовать
        // prelude там, где он ни при чём.
        match self.signature.lookup(FROM_NAT) {
            None => Ok(numeral),
            Some(_) => Ok(self.name(&named(FROM_NAT))?.apply([numeral])),
        }
    }

    /// Список: `[a, b]` есть `Cons a (Cons b Nil)` (§4.4).
    ///
    /// Имена берутся по соглашению, как `Bool` у `if` и `Unit` у сахара
    /// `{ε} A`. Собирается справа налево - список правоассоциативен по
    /// построению, и хвост его есть список же.
    fn list(&mut self, items: &[Expr], span: Span) -> Result<Term, ElabError> {
        let named = |text: &str| ast::Name {
            text: Rc::from(text),
            span,
        };
        let empty = self.name(&named(NIL))?;
        let cons = self.name(&named(CONS))?;
        let mut built = empty;
        for item in items.iter().rev() {
            // Элемент уезжает внутрь собранного значения, как поле
            // конструктора: позиция у него та же (§3.3).
            let item = self.placed(Position::Field, |it| it.expr(item, Mult::Many))?;
            built = cons.clone().apply([item, built]);
        }
        self.produced = None;
        Ok(built)
    }

    /// Row позиции, где ничего не написано, - подъём или пустая.
    fn opened(&self) -> Row<Term> {
        self.lifted.clone().unwrap_or_else(Row::empty)
    }

    /// Хвост, названный руками. Второе вхождение того же имени берёт первую.
    fn named_tail(&mut self, name: &Symbol) -> Row<Term> {
        if let Some(known) = self.tails.get(name) {
            return known.clone();
        }
        let fresh = self.metas.fresh_row();
        self.tails.insert(Rc::clone(name), fresh.clone());
        fresh
    }

    /// Тип терма - у ядра, а если оно не знает, то у объявляемой группы.
    ///
    /// Рекурсивный вызов в разбираемом (`if even k then …` внутри `even`)
    /// сигнатуре ещё не известен по построению (§10 вопрос 50), а тип его
    /// известен группе. Считается он тем же правилом применения: спайн
    /// снимает по связыванию за аргумент.
    fn synthesized(&mut self, term: &Term) -> Option<Rc<Value>> {
        if let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Zero, term) {
            return Some(ty);
        }
        let mut arguments = Vec::new();
        let mut head = term;
        while let Term::App(callee, argument) = head {
            arguments.push(&**argument);
            head = callee;
        }
        arguments.reverse();
        let Term::Const(name, levels, _) = head else {
            return None;
        };
        let member = self.group.iter().find(|it| *it.name == **name)?;
        let mut ty = eval(&Env::default(), &member.ty.substitute_levels(levels));
        for argument in arguments {
            let Value::Pi(_, _, _, _, codomain) = &*ty else {
                return None;
            };
            let codomain = codomain.clone();
            ty = codomain.apply(self.ctx.eval(argument));
        }
        Some(ty)
    }

    /// Тело одной ветви - под переменными её паттерна.
    fn branch(
        &mut self,
        written: &Pattern,
        compiled: &CorePattern,
        body: &Expr,
        closing: &[(Symbol, Symbol)],
    ) -> Result<Term, ElabError> {
        let mut names = Vec::new();
        variables_of(compiled, &mut names);
        let mut bound = Vec::new();
        let mut level = self.ctx.size();
        // Тип разбираемого сюда не приходит: ветвь `case` собирается отдельно
        // от него, и поля берут дырку - решать её будет проверка.
        self.pattern_variables(
            Some(written),
            compiled,
            Mult::Many,
            None,
            body,
            &names,
            &mut bound,
            &mut level,
        );
        // Индекс закрываемого извне считается **до** спуска в ветвь. Внутри
        // неё имя затеняется переменной паттерна, а поиск идёт изнутри наружу,
        // и `case b of Full h -> …` при внешнем ресурсном `h` подставлял бы
        // `drop` паттерновому: корректная программа отвергалась несовпадением
        // типов, а вставка промахивалась мимо того, что обязана была закрыть.
        let outer_drops: Vec<(u32, Symbol)> = closing
            .iter()
            .filter_map(|(name, drop)| self.local(name).map(|index| (index, drop.clone())))
            .collect();
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        for variable in &bound {
            let ty = match &variable.ty {
                Some(ty) => Rc::clone(ty),
                None => self.hole(),
            };
            self.ctx = self.ctx.bind(
                CoreName::from(&*variable.name),
                variable.mult,
                Rc::clone(&ty),
            );
            self.scope.push(Bound {
                // Решённое разбором связывание уходит из спайна дырок: в нём
                // оно было бы вторым именем решившего, и спайн переставал бы
                // быть паттерном Миллера.
                value: variable.value.clone(),
                ..Bound::owning_scoping(
                    &variable.name,
                    variable.mult,
                    ty,
                    variable.owned,
                    variable.scoped,
                )
            });
        }
        // Закрываются двое. Ресурс, о котором забыла **эта** ветвь: решение
        // выше принимается по телу целиком, а ветвь - отдельный путь (§3.3,
        // §10 вопрос 71). И ресурс, который ветвь **сама разобрала**: поле,
        // связанное её паттерном, - такое же владение, как аргумент, и клауза
        // закрывает его тем же `closing_of`. В ветви этого не делалось вовсе,
        // и `byCase s = case s of Listen h -> True` уносил дескриптор молча,
        // тогда как побуквенно та же клауза его закрывала.
        let shift = u32::try_from(bound.len()).unwrap_or(u32::MAX);
        let mut drops: Vec<(u32, Symbol)> = closing_of(&bound);
        drops.extend(
            outer_drops
                .into_iter()
                .map(|(index, drop)| (index.saturating_add(shift), drop)),
        );
        lifo(&mut drops);
        let term = self.closing_all(&drops, |it| it.expr(body, Mult::Many));
        self.scope.truncate(depth);
        self.ctx = outer;
        term
    }

    /// Кратность, с которой разбор потребляет разбираемое (§3.3, вопрос 65).
    ///
    /// У написанного имени берётся кратность его связывания: разбирается
    /// именно оно. У составного выражения связывания нет, и решает голова
    /// типа - владеемое потребляется однажды, прочее неограниченно.
    fn consumption(&self, scrutinee: &Expr, ty: &Term) -> Mult {
        if let ExprKind::Name(name) = &scrutinee.kind {
            if let Some(bound) = self
                .scope
                .iter()
                .rev()
                .find(|bound| bound.visible && bound.name == name.text)
            {
                return bound.mult;
            }
        }
        let mut head = ty;
        while let Term::App(callee, _) = head {
            head = callee;
        }
        match head {
            Term::Const(name, _, _) if self.owned.owns(name) => Mult::One,
            _ => Mult::Many,
        }
    }

    /// `{ x : A, y : B }` - телескоп полей.
    ///
    /// Поле кратности `1` (§4.1): запись кладёт значение однажды - тот же
    /// довод, что у поля конструктора.
    fn record_type(
        &mut self,
        fields: &[ast::RecordField],
        written: Option<&ast::Name>,
        span: Span,
    ) -> Result<Term, ElabError> {
        // Хвост берётся один раз на запись - до полей: связывание его стоит
        // снаружи них, и внутри индекс был бы уже другим.
        let tail = match written {
            Some(name) => Some(Rc::new(self.tail_variable(name)?)),
            None => self.row_variable(span),
        };
        let inner = self.record_fields(fields)?;
        // **Зависимость закрывает запись** (§4.2), и auto-lift обязан это
        // видеть: `{ a : Type, b : a }` - закрытая запись, а не открытая,
        // которой не написали хвост. Раздача метит запись по спану, до полей,
        // и зависимость к тому моменту ещё не известна - поэтому переменная
        // снимается здесь, когда поля уже элаборированы. Написанный хвост так
        // не снимается: автор попросил открытую запись явно, и отвечает ему
        // ядро отказом, а не молчаливым сужением написанного.
        let tail = tail.filter(|_| written.is_some() || !dependent(&inner));
        Ok(Term::Record(Fields {
            fields: inner.into(),
            tail,
        }))
    }

    /// Row-переменная этой записи, если сигнатура их раздаёт (§4.2).
    ///
    /// Закрыты записи в алиасе `type` и всюду, где связать переменную нечем:
    /// раздаёт их `declaration`, и раздаёт ровно тем, кого насчитала. Запись
    /// узнаёт свою по спану, поэтому повторная элаборация одного написанного
    /// типа берёт ту же переменную, а не следующую.
    fn row_variable(&mut self, span: Span) -> Option<Rc<Term>> {
        let index = self.rows.as_ref()?.iter().position(|it| *it == span)?;
        let name: Symbol = Rc::from(format!("#row{index}").as_str());
        self.local(&name).map(|it| Rc::new(Term::var(it)))
    }

    /// Написанный хвост `{ x : Nat | r }`.
    ///
    /// Связывания он не создаёт - только ссылается: `r` либо поднят подъёмом
    /// сигнатуры, либо написан связыванием сам. Ненайденное имя здесь ошибка,
    /// а не закрытая запись: молча потерять хвост значило бы сузить
    /// написанный тип.
    fn tail_variable(&mut self, name: &ast::Name) -> Result<Term, ElabError> {
        self.local(&name.text)
            .map(Term::var)
            .ok_or_else(|| ElabError::UnknownName {
                name: Rc::clone(&name.text),
                span: name.span,
            })
    }

    /// Поля записи телескопом - каждое под предыдущими.
    ///
    /// **Владеемого поля у записи не бывает.** У конструктора это правило с
    /// исключениями - держатель бывает `unique` или `resource`, - а у записи
    /// исключений нет: объявляется она `type`, деструктора у неё нет, а
    /// связывание её `ω`. `type Box = { h : File }` поэтому не закрывался
    /// никогда, а `ω`-связывание позволяло проецировать поле сколько угодно
    /// раз, то есть закрыть дескриптор дважды. Прямой аналог на `data`-обёртке
    /// отвергался всегда - запись была единственным обходом (§3.3, вопрос 77).
    fn record_fields(&mut self, fields: &[ast::RecordField]) -> Result<Vec<CoreField>, ElabError> {
        let Some((field, rest)) = fields.split_first() else {
            return Ok(Vec::new());
        };
        Self::binds(&field.name)?;
        let ty = self.typing(|it| it.expr(&field.ty, Mult::Many))?;
        if let Some(how) = self.owned.of(&field.ty) {
            return Err(ElabError::OwnedRecordField {
                field: Rc::clone(&field.name.text),
                ty: crate::own::head(&field.ty)
                    .cloned()
                    .unwrap_or_else(|| Rc::from("_")),
                owned: how,
                span: field.ty.span,
            });
        }
        let bound = self.typed(&ty);
        let tail = self.binding(Bound::visible(&field.name.text, Mult::One, bound), |it| {
            it.record_fields(rest)
        })?;
        let head = CoreField {
            name: CoreName::from(&*field.name.text),
            mult: Mult::One,
            ty: Rc::new(ty),
        };
        Ok(std::iter::once(head).chain(tail).collect())
    }

    /// Телескоп полей по членам сигнатуры модуля (§4.8).
    ///
    /// Тот же телескоп, что у записи: член видит предыдущих, поэтому
    /// `compare : T -> T -> Ordering` находит `T`. Абстрактный типовой член
    /// (`type T` без уравнения) - поле сорта `Type` со свежей дыркой уровня:
    /// какой универсум ему достанется, решает тот, кто сигнатуру реализует.
    pub(crate) fn module_members(
        &mut self,
        members: &[WrittenField<'_>],
    ) -> Result<Vec<CoreField>, ElabError> {
        let Some((first, rest)) = members.split_first() else {
            return Ok(Vec::new());
        };
        let ty = if let Some(written) = first.ty {
            // Свободные имена члена поднимаются в implicit-связывания его
            // поля, а универсум словаря считается по полям: член,
            // квантифицирующий по `Type ℓ`, поднимает словарь на этаж выше
            // (решение 2026-09-03). Подъёма row здесь нет: row-параметр
            // принадлежит определению, а связывания row в термах не
            // существует, поэтому написанный хвост у члена связать нечем.
            self.member_type(written, Mult::Many)?
        } else {
            // Абстрактный типовой член: тип его - сорт, а с параметрами -
            // телескоп по ним, оканчивающийся сортом. Написать этот телескоп
            // сигнатурой нельзя по той же причине, по какой не пишется алиас:
            // конкретный универсум в поверхностном языке не выражается.
            let params = self.telescope(first.params, false, Mult::Many)?;
            let level = self.metas.fresh_level();
            self.wrapped(&params, false, |_| Ok(Term::Universe(level)))?
        };
        let bound = self.typed(&ty);
        let tail = self.binding(Bound::visible(&first.name.text, Mult::One, bound), |it| {
            it.module_members(rest)
        })?;
        let head = CoreField {
            name: CoreName::from(&*first.name.text),
            mult: Mult::One,
            ty: Rc::new(ty),
        };
        Ok(std::iter::once(head).chain(tail).collect())
    }

    /// `{ p | x = v }` - обновление и расширение одной формой (§4.2).
    ///
    /// Различает их **тип исходной записи**, а не автор: есть поле - update,
    /// нет - extension. Собирается результат пересборкой: у каждого поля
    /// исходной берётся либо написанное значение, либо её собственная
    /// проекция, а ненаписанные поля дописываются следом.
    ///
    /// # Открытая запись сюда не проходит, и это названная граница
    ///
    /// У записи с хвостом полей не перечислить - их знает только хвост, - а
    /// пересборка перечисляет. Правильный ответ - расширение и ограничение
    /// как операции ядра; §4.2 их и предполагает («элаборатор вставляет
    /// restriction перед extension»), но заводить их ради формы, которой в
    /// §4.2 нет ни одного примера с открытой записью, значило бы строить
    /// механизм без потребителя.
    fn update(
        &mut self,
        base: &Expr,
        fields: &[(ast::Name, Expr)],
        span: Span,
    ) -> Result<Term, ElabError> {
        let value = self.placed(Position::Inner, |it| it.expr(base, Mult::Many))?;
        let Some(ty) = self.synthesized(&value) else {
            return Err(ElabError::NotMatchable { span });
        };
        // Голова разворачивается: `Point` - алиас, и §4.2 требует, чтобы он был
        // полностью взаимозаменяем с тем, что назвал.
        let ty = whnf(self.signature, &ty);
        let Value::Record(telescope) = &*ty else {
            return Err(ElabError::NotUpdatable { span });
        };
        // У открытой записи полей не перечислить - их знает хвост, - поэтому
        // пересобрать её нечем и переопределение уходит в ядро как есть
        // (§4.2). Какая метка обновляется, а какая дописывается, решает там
        // тип базы - тот же критерий, что и здесь.
        if telescope.is_open() {
            let mut written = Vec::with_capacity(fields.len());
            for (name, value) in fields {
                let value = self.placed(Position::Field, |it| it.expr(value, Mult::One))?;
                written.push((CoreName::from(&*name.text), Rc::new(value)));
            }
            self.produced = None;
            return Ok(Term::With(Rc::new(value), written.into()));
        }
        let mut written = Vec::new();
        for field in telescope.fields() {
            let name = CoreName::from(&*field.name);
            let update = fields.iter().find(|(it, _)| *it.text == *field.name);
            let value = match update {
                Some((_, value)) => self.placed(Position::Field, |it| it.expr(value, Mult::One))?,
                None => Term::Project(Rc::new(value.clone()), Rc::clone(&name)),
            };
            written.push((name, Rc::new(value)));
        }
        // Ненаписанного поля у исходной нет - это расширение, и дописывается
        // оно следом, в порядке написания.
        for (name, value) in fields {
            if telescope.fields().iter().any(|it| *it.name == *name.text) {
                continue;
            }
            let value = self.placed(Position::Field, |it| it.expr(value, Mult::One))?;
            written.push((CoreName::from(&*name.text), Rc::new(value)));
        }
        self.produced = None;
        Ok(Term::Object(written.into()))
    }

    /// `{ x = a, y }` - значение записи.
    fn record(&mut self, fields: &[(ast::Name, Expr)]) -> Result<Term, ElabError> {
        let mut written = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            // Поле уезжает внутрь собранного - та же позиция, что у аргумента
            // конструктора (§3.3).
            let value = self.placed(Position::Field, |it| it.expr(value, Mult::One))?;
            written.push((CoreName::from(&*name.text), Rc::new(value)));
        }
        self.produced = None;
        Ok(Term::Object(written.into()))
    }

    /// `f @A @B` - выводимый аргумент, написанный явно (§4.1).
    ///
    /// Голова элаборируется **без** вставки: `@` пишет ровно те аргументы,
    /// которые иначе стали бы дырками, и вставленную дырку `@` уже не заменит.
    /// Остаток ведущих имплиситов вставляется после цепочки, поэтому `g @Nat x`
    /// при `g : {a} -> {b} -> a -> b -> …` пишет `a` и выводит `b`.
    ///
    /// Цепочка снимается циклом по той же причине, что и спайн применения:
    /// длину её ограничивает только текст.
    fn type_app(&mut self, expr: &Expr) -> Result<Term, ElabError> {
        let mut written = Vec::new();
        let mut head = expr;
        while let ExprKind::TypeApp(callee, argument) = &head.kind {
            written.push(&**argument);
            head = callee;
        }
        let mut term = self.placed(Position::Inner, |it| {
            // Точечное имя поднятого члена - тоже имя (решение 2026-08-31), и
            // вставку `@` обязано отключать так же: иначе первый выводимый
            // аргумент уже занят дыркой, и писать его нечем.
            let named = match &head.kind {
                ExprKind::Name(_) => true,
                ExprKind::Project(record, field) => it.member(record, &field.text).is_some(),
                _ => false,
            };
            if named {
                it.bare(|it| it.expr(head, Mult::Many))
            } else {
                it.expr(head, Mult::Many)
            }
        })?;
        let mut ty = infer(&self.ctx, self.metas, Mult::Zero, &term)
            .map(|(ty, _)| ty)
            .map_err(|_| ElabError::NoImplicitParameter { span: expr.span })?;
        for argument in written.into_iter().rev() {
            let Value::Pi(binder, _, _, _, codomain) = &*ty else {
                return Err(ElabError::NoImplicitParameter {
                    span: argument.span,
                });
            };
            if !binder.visibility.is_implicit() {
                return Err(ElabError::NoImplicitParameter {
                    span: argument.span,
                });
            }
            let codomain = codomain.clone();
            // Написанный аргумент - тип, и подходит ли он домену, скажет
            // `check`: авторитет он, а не этот проход.
            let written = self.typing(|it| it.expr(argument, Mult::Zero))?;
            let value = self.typed(&written);
            term = Term::App(Rc::new(term), Rc::new(written));
            ty = codomain.apply(value);
        }
        // Применение к scope результат к нему не привязывает - см. `App`.
        self.produced = None;
        Ok(self.implicits(term, ty))
    }

    /// Выполняет `body`, не вставляя имплиситы ближайшему имени.
    fn bare<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.bare, true);
        let outcome = body(self);
        self.bare = outer;
        outcome
    }

    /// Собирает ли применение с такой головой значение - то есть конструктор
    /// ли она.
    ///
    /// Аргумент конструктора уезжает внутри собранного, и §3.3 запрещает
    /// класть туда привязанное к scope; аргумент функции таким свойством не
    /// обладает.
    fn constructs(&self, head: &Expr) -> bool {
        let ExprKind::Name(name) = &head.kind else {
            return false;
        };
        self.builds(name)
    }

    /// То же по имени: у оператора головы-выражения нет, а конструктором он
    /// быть может - `(::)` кладёт аргумент в ячейку списка так же, как `Cons`.
    ///
    /// **Конструктор владеемого типа исключается** (§3.3): «захваченный ресурс
    /// покидает свой scope только внутри чего-то, у чего есть деструктор». У
    /// обычного замыкания деструктора нет, поэтому оно и не выпускается; у
    /// `resource`-обёртки он есть, и ответственность за захваченное переходит
    /// к нему. Локальность проверки от этого не страдает - §3.3 разбирает это
    /// отдельно: наружу выходит уже не scope-bound-значение, потоковое
    /// свойство переведено в типовое, а типовое дисциплинируется кратностью
    /// `1` и деструктором и потому корректно межпроцедурно.
    ///
    /// Без исключения не пишется вся документированная идиома переноса
    /// владения: `spawn`/`Task` из §3.3, `reify` из §3.4, `Callback` с
    /// `drop = unregister` из §5.3.
    fn builds(&self, name: &ast::Name) -> bool {
        self.local(&name.text).is_none()
            && self
                .signature
                .lookup(&name.text)
                .is_some_and(|it| match &it.kind {
                    DefinitionKind::Constructor { data } => !self.owned.owns(data),
                    _ => false,
                })
    }

    /// Имя: связывание, `Type` или ссылка на объявленное.
    fn name(&mut self, name: &ast::Name) -> Result<Term, ElabError> {
        if let Some(index) = self.local(&name.text) {
            return Ok(Term::var(index));
        }
        // `Type` заслоняется локальным связыванием, но не определением: имя
        // занято языком, и переопределить его нечем.
        if &*name.text == "Type" {
            return Ok(Term::Universe(self.metas.fresh_level()));
        }
        // Сорт `Effect` пишется именем и заслоняется тем же правилом, что и
        // `Type`: локальным связыванием - да, определением - нет. Уровня у него
        // нет, поэтому и дырки заводить не под что (§3.4).
        if &*name.text == "Effect" {
            return Ok(Term::EffectKind);
        }
        // Член объявляемой группы: аргументы уровня - дырки, числом в арность,
        // посчитанную вызывающим. Тип его сигнатура ещё не знает (§10 вопрос
        // 50), поэтому имплиситы вставляются по типу, принесённому в группе.
        if let Some(member) = self.member_of_group(&name.text) {
            let term = Term::Const(
                CoreName::from(&*member.name),
                Rc::clone(&member.levels),
                member.rows.clone(),
            );
            let ty = eval(&Env::default(), &member.ty);
            let (term, ty) = self.specialized(term, ty);
            if self.bare {
                return Ok(term);
            }
            return Ok(self.implicits(term, ty));
        }
        // Сосед по модулю заслоняет глобальное имя: члены подняты на верхний
        // уровень, но написаны они внутри, и видеть автор обязан своего.
        if let Some(full) = self.qualified(&name.text) {
            if let Some(term) = self.signature.instantiate(&full, self.metas) {
                let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Zero, &term) else {
                    return Ok(term);
                };
                let (term, ty) = self.specialized(term, ty);
                if self.bare {
                    return Ok(term);
                }
                return Ok(self.implicits(term, ty));
            }
        }
        // Аргументы уровня подставляются дырками - это implicit UP со стороны
        // места использования (§3.2), - и одному имени они выдаются один раз
        // на объявление (см. `instantiated`).
        if let Some(term) = self.instantiated.get(&name.text).cloned() {
            return Ok(self.implicit_use(&name.text, term));
        }
        let term = self
            .signature
            .instantiate(&name.text, self.metas)
            .ok_or_else(|| {
                if self.types && !is_reference(&name.text) {
                    return ElabError::Missing {
                        what: Missing::FreeTypeVariable,
                        span: name.span,
                    };
                }
                ElabError::UnknownName {
                    name: Rc::clone(&name.text),
                    span: name.span,
                }
            })?;
        self.instantiated
            .insert(Rc::clone(&name.text), term.clone());
        Ok(self.implicit_use(&name.text, term))
    }

    /// Вставляет выводимые аргументы имени, тип которого знает ядро.
    ///
    /// Под `@` не вставляет ничего: аргументы там пишутся, и дырка на месте
    /// первого из них заняла бы его место.
    ///
    /// Кэш `instantiated` держит имя **без** них: аргументы уровня у имени в
    /// объявлении общие, а имплиситы - нет. `id x` и `id y` в одном теле стоят
    /// при разных типах, и общая дырка связала бы их в один.
    fn implicit_use(&mut self, name: &str, term: Term) -> Term {
        // Отбор по объявленному типу идёт до `infer`: тот вычисляет тип
        // целиком, а имён без имплиситов в обычной программе подавляющее
        // большинство, и платить за них этим вычислением не за что.
        let opens = self
            .signature
            .lookup(name)
            .is_some_and(|definition| opens_implicit(&definition.ty));
        if self.bare || !opens {
            return term;
        }
        let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Zero, &term) else {
            // Тип не сошёлся - вставлять нечего, а сказать об этом полагается
            // `check`: авторитет он, а не этот проход (см. `typed`).
            return term;
        };
        self.implicits(term, ty)
    }

    /// `f a b c` - спайн целиком, а не по одному применению за раз.
    ///
    /// Собирается он **циклом**: рекурсия по левому поддереву стоила бы кадра
    /// на аргумент, а их ограничивает только длина файла - предел вложенности
    /// парсера на плоское `f a b c …` не тратится (§10 вопрос 62).
    fn application(&mut self, expr: &Expr) -> Result<Term, ElabError> {
        let mut arguments = Vec::new();
        let mut head = expr;
        while let ExprKind::App(callee, argument) = &head.kind {
            arguments.push(&**argument);
            head = callee;
        }
        // Аргумент конструктора уезжает внутри собранного значения, а аргумент
        // функции - нет: §3.3 разрешает замыканию над владеющим связыванием
        // применяться и передаваться.
        let inside = if self.constructs(head) {
            Position::Field
        } else {
            Position::Inner
        };
        let mut term = self.placed(Position::Inner, |it| it.expr(head, Mult::Many))?;
        // Привязанность головы к scope: её переживает **частичное** применение,
        // потому что недоприменённое и есть замыкание над ней.
        let captured = self.produced.take();
        // Имя головы нужно умолчаниям параметров: они дописываются по
        // **написанной** арности применения (§4.1, правило 1), и спросить о
        // них можно только зная, к чему применяются.
        let named = match &term {
            Term::Const(name, _, _) => Some(Rc::clone(name)),
            _ => None,
        };
        let mut given: Vec<Term> = Vec::with_capacity(arguments.len());
        // Имплисит стоит не только в голове: `f Zero True` при
        // `f : Nat -> {0 a : Type} -> a -> Nat` обязано получить `a` между
        // написанными аргументами. Голову свою вставку уже получила - её
        // делает `name`, - поэтому тип нужен ровно для середины спайна.
        //
        // Тип не вывелся - применение собирается как раньше, без вставки:
        // голова бывает и лямбдой, выводить которую нечем. Сказать об этом
        // полагается `check`, а не этому проходу.
        let mut ty = infer(&self.ctx, self.metas, Mult::Zero, &term)
            .ok()
            .map(|(ty, _)| ty);
        for argument in arguments.into_iter().rev() {
            if let Some(current) = ty.take() {
                let (inserted, rest) = self.inserted(term, current);
                term = inserted;
                ty = Some(rest);
            }
            // Ожидаемый тип аргумента - домен того связывания, к которому он
            // приписывается; исполнение по нему и решается (§3.4).
            let expected = ty.as_deref().and_then(domain_of);
            let argument =
                self.aside(|it| it.placed(inside, |it| it.expr(argument, Mult::Many)))?;
            let argument = self.executed(argument, expected.as_ref());
            ty = ty.and_then(|it| self.stepped(&it, &argument));
            term = Term::App(Rc::new(term), Rc::new(argument.clone()));
            given.push(argument);
        }
        // Умолчания хвостовых параметров - дописанные аргументы, и ничем от
        // написанных не отличаются: вставка имплиситов перед ними та же.
        if let Some(head) = named {
            while let Some(argument) = self.default_argument(&head, &given) {
                if let Some(current) = ty.take() {
                    let (inserted, rest) = self.inserted(term, current);
                    term = inserted;
                    ty = Some(rest);
                }
                ty = ty.and_then(|it| self.stepped(&it, &argument));
                term = Term::App(Rc::new(term), Rc::new(argument.clone()));
                given.push(argument);
            }
        }
        // Применение свойство **передаёт**, пока результат остаётся функцией.
        // Прежде оно его снимало всегда, и рядом стояло обоснование «построить
        // возвращающее замыкание нельзя - запрет на позицию возврата не даёт
        // собрать его вовсе». Собирает: `feedPut k s = k MkUnit` при
        // `(1 k : Unit -> Nat -> Nat)` возвращает недоприменённое `k`, то есть
        // замыкание над ним, и через такого помощника резумпция переживала
        // ветку хендлера (§10 вопрос 90).
        //
        // Неизвестный тип результата считается функцией: тип здесь
        // best-effort, а дыра в гарантии дороже лишнего отказа.
        self.produced = captured.filter(|_| !ty.as_deref().is_some_and(saturated));
        Ok(term)
    }

    /// Умолчание параметра, следующего за написанными (§4.1).
    ///
    /// Хранится оно определением `C#default{k}` - лямбдой по предшествующим
    /// параметрам, - поэтому применяется к уже собранным аргументам и
    /// разворачивается. Разворот здесь обязателен: оставленное применение
    /// прошло бы проверку типов (δ и β его сводят), но голову аргумента читает
    /// поиск инстанса, а он смотрит на написанное.
    fn default_argument(&mut self, head: &str, given: &[Term]) -> Option<Term> {
        let name = format!("{head}#default{}", given.len());
        let term = self.signature.instantiate(&name, self.metas)?;
        let applied = given.iter().fold(term, |callee, argument| {
            Term::App(Rc::new(callee), Rc::new(argument.clone()))
        });
        let value = adamas_core::conv::whnf(self.signature, &self.ctx.eval(&applied));
        Some(quote(self.ctx.size(), &value))
    }

    /// Тип применения к написанному аргументу - если он вычислим.
    ///
    /// Аргумент вычисляется только после проверки: `eval` работает на
    /// типизированных термах, а элаборация встречает и другие - `(Type Type)`
    /// роняло бы её на применении не-функции. Тот же порядок, что у `typed`:
    /// сперва авторитет, потом вычисление.
    fn stepped(&mut self, ty: &Rc<Value>, argument: &Term) -> Option<Rc<Value>> {
        let Value::Pi(_, _, domain, _, codomain) = &**ty else {
            return None;
        };
        let (domain, codomain) = (Rc::clone(domain), codomain.clone());
        // Проверка здесь - **ворота** для `eval`, а не суждение о программе:
        // решает за неё `check`, а тут нужно лишь не звать `eval` на терме, на
        // котором он развалится. Поэтому решения прохода откатываются: без
        // этого он закрывал row операции в `{Ask}` (при `σ = 0` окружающая
        // пуста по §3.4), отказ уходил в `.ok()?`, а запись оставалась - и
        // `plus ask ask` отвергалось там, где `let n : Nat = ask` проходило.
        //
        // Ни одно `σ` не годится обоим сортам аргументов. При `0` окружающая
        // пуста, и эффектный аргумент не гасится; при `ω` считается расход, и
        // стёртая позиция отвергается кратностью (`vect.adamas`). Ворота
        // пробуют оба и довольствуются любым: сказать, какое верно, - дело
        // настоящей проверки, у которой есть и `σ`, и окружающая.
        let mark = self.metas.mark();
        let mut checked = check(&self.ctx, self.metas, Mult::Zero, argument, &domain);
        self.metas.rollback(mark);
        if checked.is_err() {
            checked = check(&self.ctx, self.metas, Mult::Many, argument, &domain);
            self.metas.rollback(mark);
        }
        checked.ok()?;
        Some(codomain.apply(self.ctx.eval(argument)))
    }

    /// Исполняет приостановленное вычисление, если его не ждут (§3.4).
    ///
    /// Одна и та же запись означает «передать вычисление» и «выполнить его», а
    /// различает их ожидаемый тип: против типа вычисления терм передаётся как
    /// есть, против любого другого - применяется к единице, и его row обязана
    /// погаситься окружающей. Форма правила та же, что у вставки имплиситов, и
    /// детерминизм тот же.
    ///
    /// `expected` - `None` там, где написанного типа нет; тогда правило не
    /// срабатывает, и вычисление пишется применённым руками. Режим `infer`
    /// §3.4 живёт отдельно, у `run`: ожидаемого типа у отбрасываемого оператора
    /// блока нет вовсе, и вычисление в нём исполняется безусловно. Не покрыто
    /// ни тем, ни другим тело лямбды - остаток спайна до него доходит, но
    /// `Argument` результирующего типа не несёт (§9, Фаза 4).
    fn executed(&mut self, term: Term, expected: Option<&Rc<Value>>) -> Term {
        if expected.is_none_or(|ty| self.computation(ty)) {
            return term;
        }
        self.run(term)
    }

    /// `handle e with …` - применение элиминатора эффекта (§3.4).
    ///
    /// Метка не пишется: её называют ветки, а операция принадлежит ровно
    /// одному эффекту. Первое (внутреннее) её вхождение снимается с row
    /// вычисления, остаток и есть ρ - глубина хендлера, - и он передаётся
    /// элиминатору аргументом-row.
    /// Отвергает ресурс в области видимости (§3.4, ограничение `handleMulti`).
    ///
    /// Резумпция там `ω` и зовёт продолжение сколько угодно раз, а деструктор
    /// срабатывает один: при втором вызове ресурс был бы уже закрыт. Проверка
    /// стоит на области видимости, а не на упоминании, - резумпцию вправе
    /// сохранить, и куда дойдёт сохранённая копия, статически неизвестно.
    fn without_resource(&self, computation: &Expr, span: Span) -> Result<(), ElabError> {
        if let Some(owned) = self.scope.iter().rev().find(|bound| bound.owned) {
            return Err(ElabError::MultiWithResource {
                name: Rc::clone(&owned.name),
                span,
            });
        }
        // Лексической области видимости мало, и это ревью 2026-09-04 показало
        // двойным закрытием: живой случай - ресурс **внутри** обрабатываемого
        // вычисления, где упоминания в точке `handleMulti` нет вовсе. Свойство
        // это принадлежит определению, а не типу, - как и кратность носителя, -
        // и спрашивается обходом тел.
        if !self.owned.any_resource() {
            return Ok(());
        }
        let Some(head) = applied_head(computation) else {
            // Голова не имя - вычисление пришло параметром или собрано на
            // месте, и спросить его определение не у кого.
            return Err(ElabError::MultiWithUnknown { span });
        };
        if self.local(&head).is_some() {
            return Err(ElabError::MultiWithUnknown { span });
        }
        if self.holds_resource(&head, &mut Vec::new()) {
            return Err(ElabError::MultiOverHolder { name: head, span });
        }
        Ok(())
    }

    /// Держит ли определение ресурс - своим связыванием или через вызов такого.
    ///
    /// Спрашивается по телу, а не по типу: в типе этого нет. Признак - вставка
    /// закрытия или вызов деструктора; дальше по вызовам, с отметкой пройденных,
    /// потому что определения бывают взаимно рекурсивны.
    fn holds_resource(&self, name: &str, seen: &mut Vec<Symbol>) -> bool {
        if name == CLOSING || self.owned.named(name).is_some() {
            return true;
        }
        if seen.iter().any(|it| &**it == name) {
            return false;
        }
        seen.push(Rc::from(name));
        let Some(body) = self.signature.lookup(name).and_then(|it| it.body.as_ref()) else {
            return false;
        };
        let mut called = Vec::new();
        constants(body, &mut called);
        called.iter().any(|it| self.holds_resource(it, seen))
    }

    fn handled(&mut self, handled: Handled<'_>) -> Result<Term, ElabError> {
        let Handled {
            multi,
            label,
            computation,
            branches,
            span,
        } = handled;
        if multi {
            self.without_resource(computation, span)?;
        }
        let effect = self.handled_effect(label, branches, span)?;
        // Написанные аргументы метки закрепляют вхождение, а не выбирают его:
        // снимается всё то же первое, а они говорят, чем обязаны оказаться его
        // (§4.1). Сверка - ниже, когда вхождение снято.
        let wanted = match label {
            Some(label) => Some(self.label_arguments(label)?),
            None => None,
        };
        let operations = self.operations_of(&effect);
        let identity = identity_return(span);
        let ordered = ordered_branches(&operations, branches, &identity, span)?;

        // Вычисление элаборируется в окружающей самого `handle`: передаётся
        // оно замыканием, а не исполняется здесь.
        let value = self.expr(computation, Mult::Many)?;
        let ty = self
            .synthesized(&value)
            .ok_or_else(|| ElabError::NotHandled {
                effect: Rc::clone(&effect),
                span: computation.span,
            })?;
        let Value::Pi(_, _, _, row, _) = &*whnf_solved(self.signature, self.metas, &ty) else {
            return Err(ElabError::NotHandled {
                effect: Rc::clone(&effect),
                span: computation.span,
            });
        };
        let Snatched {
            rest: rho,
            arguments,
        } = without(row, &effect).ok_or_else(|| ElabError::NotHandled {
            effect: Rc::clone(&effect),
            span: computation.span,
        })?;
        if let (Some(wanted), Some(label)) = (wanted, label) {
            if !self.same_arguments(&arguments, &wanted) {
                return Err(ElabError::HandlerLabel {
                    name: Rc::clone(&label.name.text),
                    why: "первое вхождение написано с другими аргументами",
                    span: label.span,
                });
            }
        }
        let quoted = rho.map(|argument| quote(self.ctx.size(), argument));

        let name: Symbol = Rc::from(
            format!(
                "{}.{effect}",
                if multi { "#handleMulti" } else { "#handle" }
            )
            .as_str(),
        );
        let eliminator = self
            .signature
            .lookup(&name)
            .ok_or_else(|| ElabError::UnknownName {
                name: Rc::clone(&name),
                span,
            })?;
        // Параметров-row у элиминатора два, и порядок их задан построением его
        // типа (см. `handler_type`): обобщение собирает дырки в порядке
        // появления, домен вычисления встречается раньше домена ветки, поэтому
        // ρ нулевой, а λ первый. Прочие, если операция принесла свои,
        // остаются дырками.
        //
        // λ - окружающая **применения**: ветка выполняется там, где написан
        // сам хендлер, а не в остатке вычисления. Совпадать они не обязаны, и
        // ровно на этом стоит хендлер-трансформер §3.4.
        let ambient = self
            .ctx
            .row()
            .clone()
            .map(|argument| quote(self.ctx.size(), argument));
        let rows: Vec<Row<Term>> = [quoted.clone(), ambient]
            .into_iter()
            .chain((2..eliminator.row_arity).map(|_| self.metas.fresh_row()))
            .take(eliminator.row_arity as usize)
            .collect();
        let levels = self.handler_levels(&effect, eliminator.level_arity);
        let mut term = Term::Const(CoreName::from(&*name), levels.into(), Rows::new(rows));
        let Some(mut current) = self.synthesized(&term) else {
            return Err(ElabError::UnknownName { name, span });
        };
        let (inserted, rest) = self.inserted(term, current);
        term = inserted;
        current = rest;

        self.answered(&current, ordered.len());

        // Аргументы идут в порядке связываний: вычисление, `return`, ветки по
        // объявлению. Тела веток работают в окружающей самого `handle` - там,
        // где хендлер и написан, - а не в остатке вычисления: остаток несёт
        // `resume`, и связь между ними держит обычное погашение в точке, где
        // резумпцию зовут (§3.4). Контекст поэтому не подменяется вовсе -
        // окружающую ветки задаёт row в её ожидаемом типе.
        for branch in std::iter::once(None).chain(ordered.into_iter().map(Some)) {
            let argument = match branch {
                None => value.clone(),
                Some(branch) => self.branch_lambda(&current, branch)?,
            };
            // Тип шагает **без** проверки аргумента: арность известна, а
            // проверка идёт при `σ = 0`, где окружающая пуста (§3.4), - и
            // погасила бы хвост ρ пустой row, то есть решила бы за настоящую
            // проверку, которая пойдёт при своей кратности.
            let Value::Pi(_, _, _, _, codomain) = &*current else {
                // Арность элиминатора равна числу веток плюс вычисление -
                // построением его типа (см. `handler_type`), - и спайн,
                // кончившийся раньше, означает расхождение объявления с этим
                // местом. Молчаливое усечение прятало бы его в неверный терм.
                return Err(ElabError::HandlerBranch {
                    name: Rc::clone(&effect),
                    why: "спайн элиминатора короче, чем у него веток",
                    span,
                });
            };
            let codomain = codomain.clone();
            let value = self.ctx.eval(&argument);
            term = Term::App(Rc::new(term), Rc::new(argument));
            current = codomain.apply(value);
        }
        Ok(term)
    }

    /// Сводит ответ хендлера с ожидаемым - **до** проверки веток (§10 вопрос 87).
    ///
    /// Ответ есть результат применения элиминатора, то есть имплисит `b`, и
    /// вставлен он дыркой. Ветка `return v -> Nil` проверяется против него, а
    /// против дырки не проверяется ничто, у чего нет режима вывода; обходили
    /// это отдельным определением.
    ///
    /// Спайн снимается **без** аргументов: кодомен элиминатора от них не
    /// зависит (см. `handler_type`), поэтому подставить можно что угодно.
    fn answered(&mut self, spine: &Rc<Value>, branches: usize) {
        let Some(expected) = self.result.clone() else {
            return;
        };
        let mut answer = Rc::clone(spine);
        for _ in 0..=branches {
            let Value::Pi(_, _, _, _, codomain) = &*answer else {
                break;
            };
            answer = codomain.clone().apply(self.ctx.fresh());
        }
        convertible(
            self.signature,
            self.metas,
            self.ctx.size(),
            &answer,
            &expected,
        );
    }
    /// Аргументы-уровни элиминатора.
    ///
    /// Порядок их задан построением его типа (см. `handler_type`): обобщение
    /// собирает дырки в порядке появления, поэтому сперва идут параметры метки,
    /// затем универсумы результата вычисления и ответа хендлера, затем те, что
    /// принесли операции своими implicit-параметрами.
    ///
    /// Первые выводятся - их держат тип вычисления и ожидаемый тип, - а
    /// последние связать нечем и не с чем: `throw : e -> a` поднимает `a`
    /// (§4.1), ветка по нему полиморфна, метка о нём не несёт ничего, тип
    /// вычисления его не называет. Свежая дырка на этом месте осталась бы
    /// нерешённой навсегда, отвергая всякий хендлер, чья ветка не зовёт
    /// `resume`, - то есть ровно `try` из §4.4.
    ///
    /// Берётся нуль: аргумент этот стёрт, ветка обращается с поднятым именем
    /// только параметрически, и никакой другой уровень здесь не выразимее.
    fn handler_levels(&mut self, effect: &Symbol, arity: u32) -> Vec<Level> {
        let inferred = self
            .signature
            .lookup(effect)
            .map_or(0, |it| it.level_arity)
            .saturating_add(2);
        (0..arity)
            .map(|index| {
                if index < inferred {
                    self.metas.fresh_level()
                } else {
                    Level::Zero
                }
            })
            .collect()
    }

    /// Аргументы написанной метки - значениями, которыми сравнивают вхождения.
    fn label_arguments(&mut self, label: &ast::EffectLabel) -> Result<Vec<Rc<Value>>, ElabError> {
        let mut found = Vec::with_capacity(label.arguments.len());
        for argument in &label.arguments {
            let argument = self.typing(|it| it.expr(argument, Mult::Many))?;
            found.push(self.ctx.eval(&argument));
        }
        Ok(found)
    }

    /// Эффект, который снимает хендлер: написанная метка либо первая
    /// ветка-операция.
    fn handled_effect(
        &self,
        label: Option<&ast::EffectLabel>,
        branches: &[ast::HandlerBranch],
        span: Span,
    ) -> Result<Symbol, ElabError> {
        if let Some(label) = label {
            return match self.signature.lookup(&label.name.text).map(|it| &it.kind) {
                Some(DefinitionKind::Effect { .. }) => Ok(Rc::clone(&label.name.text)),
                _ => Err(ElabError::HandlerLabel {
                    name: Rc::clone(&label.name.text),
                    why: "обязана быть эффектом",
                    span: label.span,
                }),
            };
        }
        let named = branches
            .iter()
            .find(|branch| &*branch.name.text != RETURN)
            .ok_or(ElabError::HandlerBranch {
                name: Rc::from(RETURN),
                why: "хендлер без веток операций метки не называет",
                span,
            })?;
        match self
            .signature
            .lookup(&named.name.text)
            .map(|definition| &definition.kind)
        {
            Some(DefinitionKind::Operation { effect }) => Ok(Rc::from(&**effect)),
            _ => Err(ElabError::HandlerBranch {
                name: Rc::clone(&named.name.text),
                why: "ветка называет операцию эффекта",
                span: named.name.span,
            }),
        }
    }

    /// Операции эффекта в порядке объявления.
    fn operations_of(&self, effect: &str) -> Vec<Symbol> {
        match self.signature.lookup(effect).map(|it| &it.kind) {
            Some(DefinitionKind::Effect { operations, .. }) => {
                operations.iter().map(|it| Rc::from(&**it)).collect()
            }
            _ => Vec::new(),
        }
    }

    /// Ветка лямбдой: написанные аргументы плюс резумпция.
    ///
    /// Собирается она поверхностной записью и элаборируется обычной лямбдой -
    /// оттуда берутся и кратности связываний, и закрытие ресурсов.
    fn branch_lambda(
        &mut self,
        expected: &Rc<Value>,
        branch: &ast::HandlerBranch,
    ) -> Result<Term, ElabError> {
        let Value::Pi(_, _, domain, _, _) = &*whnf_solved(self.signature, self.metas, expected)
        else {
            return Err(ElabError::HandlerBranch {
                name: Rc::clone(&branch.name.text),
                why: "столько веток у эффекта нет",
                span: branch.span,
            });
        };
        let domain = quote(self.ctx.size(), domain);
        let bound = pi_arguments(&domain, self.owned);
        let mut params: Vec<ast::LamParam> = branch
            .params
            .iter()
            .map(|name| bind_as(name.clone()))
            .collect();
        if &*branch.name.text != RETURN {
            params.push(bind_as(ast::Name {
                text: Rc::from(RESUME),
                span: branch.name.span,
            }));
        }
        let params = spread_branch(&bound, params, branch.name.span);
        self.lam(&params, &branch.body, &bound)
    }

    /// Исполняет вычисление безусловно - режим `infer` (§3.4).
    fn run(&mut self, term: Term) -> Term {
        if !self.suspends(&term) {
            return term;
        }
        // Кратность суждения `ω`, а не `0`: при `0` окружающая row пуста
        // (§3.4), и вывод типа спотыкался бы о непогашенные эффекты у всего,
        // что их производит, - то есть ровно у того, ради чего правило и есть.
        let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Many, &term) else {
            return term;
        };
        if !self.computation(&ty) {
            return term;
        }
        let Some(unit) = self.unit_value() else {
            return term;
        };
        Term::App(Rc::new(term), Rc::new(unit))
    }

    /// Тип отброшенного значения; владеемый - отказ.
    ///
    /// Вставка `drop` решается по **написанному** типу (§3.3), а у оператора
    /// его нет вовсе, поэтому ресурс здесь закрыть нечем. Отказ, а не молчание:
    /// направление консервативности у владения то же, что и везде.
    ///
    /// Тип не вывелся - берётся дырка, и сказать об этом полагается `check`:
    /// авторитет он, а не этот проход.
    fn discarded(&mut self, value: &Term, span: Span) -> Result<Term, ElabError> {
        let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Many, value) else {
            let sort = Rc::new(Value::Universe(self.metas.fresh_level()));
            return Ok(self.fresh_meta(&sort));
        };
        // Голова читается **после** подстановки решений и δ. Выведенный тип
        // кодомена приходит нейтралью с дыркой в голове - `infer` приводит к
        // головной форме только тип вызываемого, - и ворота обходились всяким
        // выражением, чей результирующий тип выведен, а не написан: разбор
        // выражением (мотив у него свежая дырка) или вызов полиморфной
        // функции. Ресурс уезжал молча, тогда как монотипный тот же ресурс
        // отвергался.
        let ty = whnf_solved(self.signature, self.metas, &ty);
        if let Some(owned) = head_name(&ty).and_then(|head| self.owned.how(head)) {
            return Err(ElabError::OwnedDiscarded { owned, span });
        }
        Ok(quote(self.ctx.size(), &ty))
    }

    /// Тип приостановленного вычисления: стрелка от единицы (§3.4).
    ///
    /// Собственного типа у вычисления нет - `{ε} A` есть сахар, - поэтому и
    /// узнаётся оно по форме. Единица берётся по имени, тем же соглашением,
    /// каким её ставит сам сахар, и обязана быть типом с одним конструктором:
    /// иначе это не единица, и стрелка от неё - обычная функция.
    fn computation(&mut self, ty: &Rc<Value>) -> bool {
        let Value::Pi(_, _, domain, _, _) = &*whnf_solved(self.signature, self.metas, ty) else {
            return false;
        };
        let Value::Neutral(Head::Global(name, ..), spine) =
            &*whnf_solved(self.signature, self.metas, domain)
        else {
            return false;
        };
        spine.is_empty() && &**name == UNIT && self.unit_value().is_some()
    }

    /// Значение единицы - её единственный конструктор.
    ///
    /// Второго имени по соглашению не заводится: тип назван, а какой у него
    /// конструктор, знает сигнатура.
    fn unit_value(&mut self) -> Option<Term> {
        let [only] = self.signature.constructors(UNIT)? else {
            return None;
        };
        let only = Rc::clone(only);
        self.signature.instantiate(&only, self.metas)
    }

    /// Может ли терм оказаться вычислением - дёшево, до всякого вывода типа.
    ///
    /// Отбор по объявленному типу идёт до `infer` тем же доводом, каким его
    /// ведёт вставка имплиситов: вывод считает тип целиком, а вычислений в
    /// обычной программе единицы. Приближение сверху: отвечает «может» чаще,
    /// чем нужно, но никогда не пропускает настоящее вычисление.
    fn suspends(&self, term: &Term) -> bool {
        let mut head = term;
        while let Term::App(callee, _) = head {
            head = callee;
        }
        match head {
            Term::Const(name, ..) => self
                .signature
                .lookup(name)
                .is_some_and(|definition| awaits_unit(&definition.ty)),
            Term::Var(Index(index)) => self
                .scope
                .len()
                .checked_sub(*index as usize + 1)
                .and_then(|position| self.scope.get(position))
                .is_some_and(|bound| matches!(&*bound.ty, Value::Pi(..))),
            // Блок собирается в цепочку `let`, а разбор - в узел с ветвями;
            // вычислением бывает то, чем они кончаются.
            Term::Let(_, _, _, _, body) => self.suspends(body),
            Term::Case(case) => case.branches.iter().any(|it| self.suspends(&it.body)),
            _ => false,
        }
    }

    /// Применяет `term` к дырке на каждое ведущее implicit-связывание его типа.
    ///
    /// Вставка **энергичная**: аргумент выводится там, где имя встретилось, а
    /// не там, где до него доберётся проверка. Названная цена - `f = id`:
    /// имплисит вставится и останется нерешённым, потому что обобщать его
    /// нечем. Отложенная вставка требует двунаправленной элаборации, и это
    /// отдельный срез.
    fn implicits(&mut self, term: Term, ty: Rc<Value>) -> Term {
        self.inserted(term, ty).0
    }

    /// То же вместе с типом, до которого вставка дошла.
    ///
    /// Тип нужен применению: имплисит стоит не только в голове спайна, но и
    /// между написанными аргументами, и вставлять его там можно только зная,
    /// что осталось от телескопа.
    fn inserted(&mut self, mut term: Term, mut ty: Rc<Value>) -> (Term, Rc<Value>) {
        loop {
            let Value::Pi(binder, _, domain, _, codomain) = &*ty else {
                return (term, ty);
            };
            if !binder.visibility.is_implicit() {
                return (term, ty);
            }
            let (domain, codomain) = (Rc::clone(domain), codomain.clone());
            // `using` выбирает словарь до всякого поиска: место написания
            // здесь ещё есть, а у дырки его уже не будет.
            let argument = self
                .chosen(&domain)
                .unwrap_or_else(|| self.fresh_meta(&domain));
            let value = self.ctx.eval(&argument);
            term = Term::App(Rc::new(term), Rc::new(argument));
            ty = codomain.apply(value);
        }
    }

    /// Написанный `using`-инстанс для этого домена, если он есть.
    fn chosen(&mut self, domain: &Rc<Value>) -> Option<Term> {
        let head = head_name(domain)?;
        let chosen = self
            .using
            .iter()
            .rev()
            .find(|(class, _)| **class == **head)
            .map(|(_, name)| Rc::clone(name))?;
        self.signature.instantiate(&chosen, self.metas)
    }

    /// Класс, инстансом которого объявлено имя: `Monoid Int` даёт `Monoid`.
    fn class_of(&self, name: &str) -> Option<Symbol> {
        let mut current = &self.signature.lookup(name)?.ty;
        while let Term::Pi(_, _, _, _, codomain) = current {
            current = codomain;
        }
        let Term::App(callee, _) = current else {
            return None;
        };
        let Term::Const(class, _, _) = &**callee else {
            return None;
        };
        Some(Rc::from(&**class))
    }

    /// `(q x y : A) {r z : B} -> C`.
    ///
    /// Группы разворачиваются в плоский список связываний: `(x y : A)` - это
    /// два `Pi`, и второй видит первое связывание, поэтому тип элаборируется
    /// заново под каждым именем. Заново - но не в другой области видимости:
    /// `A` написано раньше обоих имён, и собственные имена группы для него
    /// спрятаны (`hiding`), иначе `(0 t : Type) -> (0 t x : t) -> …` дало бы
    /// `x` тип соседа по группе вместо написанного снаружи. Отсюда `siblings`
    /// в плоском списке - сколько имён группы стоит перед этим.
    ///
    /// Дырки уровня у каждого имени свои: общий `Type` в записи не значит
    /// общий универсум, а более общее прочтение здесь безопасно.
    ///
    /// **Кратность у фигурной группы - то же умолчание `ω`, что у круглой.**
    /// Подъём свободного имени даёт `0`, и расхождение намеренное: написать
    /// группу - это и есть способ попросить имплисит, доживающий до рантайма
    /// (`replicate : {n : Nat} -> a -> Vect n a`). Так же различает Idris 2.
    fn pi(
        &mut self,
        binders: &[ast::Binder],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let mut flat: Vec<Written<'_>> = Vec::new();
        for binder in binders {
            // Связывание без написанного типа бывает у параметра семейства
            // (`data Pair a b`), и туда этот путь не ведёт: `(a) -> Nat`
            // разбирается как применение в скобках, а не как связывание.
            let Some(ty) = &binder.ty else {
                return Err(ElabError::Missing {
                    what: Missing::TypelessBinder,
                    span: binder.span,
                });
            };
            let mult = self.binder_mult(
                binder.mult,
                ty,
                kinded(binder.mult, ty, default),
                binder.span,
            )?;
            for (siblings, name) in binder.names.iter().enumerate() {
                Self::binds(name)?;
                flat.push(Written {
                    mult,
                    visibility: binder.visibility,
                    name: Rc::clone(&name.text),
                    ty,
                    siblings,
                });
            }
        }
        self.pi_flat(&flat, codomain, default)
    }

    fn pi_flat(
        &mut self,
        binders: &[Written<'_>],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let Some((first, rest)) = binders.split_first() else {
            return self.expr(codomain, default);
        };
        let domain = self.hiding(first.siblings, |inner| inner.expr(first.ty, Mult::Many))?;
        let owns = self.owned.of(first.ty).is_some();
        let bound = self.typed(&domain);
        // Row снимается с кодомена и у связывания с именем - тем же правилом,
        // что у безымянной стрелки: `(x : A) -> {IO} B` и `A -> {IO} B`
        // различаются именем аргумента, а не тем, где написаны эффекты. Снимать
        // её вправе только последнее связывание группы: у `(x : A) (y : B) ->
        // {IO} C` кодомен принадлежит `y`.
        let (written, codomain) = if rest.is_empty() {
            split_row(codomain)
        } else {
            (None, codomain)
        };
        let row = self.effects(written)?;
        let body = self.binding(
            Bound::owning(&first.name, first.mult, bound, owns),
            |inner| inner.pi_flat(rest, codomain, default),
        )?;
        let binder = match first.visibility {
            Visibility::Explicit => Binder::explicit(first.mult),
            Visibility::Implicit => Binder::implicit(first.mult),
        };
        Ok(Term::Pi(
            binder,
            CoreName::from(&*first.name),
            Rc::new(domain),
            row,
            Rc::new(body),
        ))
    }

    /// `\x y -> body`.
    ///
    /// `expected` - связывания написанного типа, по одному на параметр.
    /// Кончились (тип не написан, кодомен не виден насквозь) - берётся `ω` без
    /// закрытия, и лямбда под не-`ω` связыванием остаётся невыразимой.
    ///
    /// Ресурс закрывается здесь по тому же правилу, что и аргумент клаузы:
    /// `f = \h -> True` и `f h = True` - одно определение, записанное дважды,
    /// и вести себя обязаны одинаково.
    fn lam(
        &mut self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
    ) -> Result<Term, ElabError> {
        // Считается до спуска: индексы закрываемых меряются от тела, то есть
        // от точки, где связаны все параметры этой лямбды.
        let drops = self.closing_params(params, body, expected);
        self.lam_params(params, body, expected, &drops)
    }

    fn lam_params(
        &mut self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
        drops: &[(u32, Symbol)],
    ) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            // Остаток спайна достаётся телу: `\x -> \y -> e` - две лямбды под
            // теми же `Pi`, что и `\x y -> e`.
            self.expected = expected.to_vec();
            // Тело лямбды - её возвращаемое значение, и правило §3.3 стоит
            // здесь так же, как у тела клаузы.
            let inner = self.closing_all(drops, |it| {
                it.placed(Position::Returned, |it| it.expr(body, Mult::Many))
            });
            // И правило исполнения по ожидаемому типу - тоже. Прежде оно тело
            // лямбды не покрывало: остаток спайна до него доходил, а
            // результирующего типа `Argument` не несла (§9 Фаза 4), и
            // `\b -> get` отвергался там, где `f b = get` принимался.
            let result = self.result.clone();
            return inner.map(|body| self.executed(body, result.as_ref()));
        };
        let name = match &param.kind {
            LamParamKind::Binder(_) => {
                return Err(ElabError::Missing {
                    what: Missing::LambdaAnnotation,
                    span: param.span,
                });
            }
            LamParamKind::Pattern(pattern) => match &pattern.kind {
                PatternKind::Name(name) if !is_reference(&name.text) => Rc::clone(&name.text),
                PatternKind::Wildcard => Rc::from("_"),
                PatternKind::Tuple(items) if items.is_empty() => {
                    return Err(ElabError::Missing {
                        what: Missing::Unit,
                        span: pattern.span,
                    });
                }
                _ => {
                    // Разбор в параметре лямбды - это `case` без мотива.
                    return Err(ElabError::Missing {
                        what: Missing::LambdaPattern,
                        span: pattern.span,
                    });
                }
            },
        };
        let (mult, deeper) = expected
            .split_first()
            .map_or((Mult::Many, expected), |(argument, rest)| {
                (argument.mult, rest)
            });
        // Тип параметра приходит из написанного типа; там, где он не
        // написан, лямбда и кратности не получает, и связывание берёт тип
        // дырки - решать её потом будет проверка.
        let ty = match expected.first() {
            Some(argument) => {
                let domain = Rc::clone(&argument.domain);
                self.typed(&domain)
            }
            None => self.hole(),
        };
        let bound = expected.first().map_or_else(
            || Bound::visible(&name, mult, Rc::clone(&ty)),
            |argument| {
                Bound::owning_scoping(
                    &name,
                    mult,
                    Rc::clone(&ty),
                    argument.owned,
                    argument.scoped(),
                )
            },
        );
        // Ожидаемый результат шагает вместе со спайном: связывание снято, и
        // телу достаётся кодомен, а не весь тип.
        let stepped = self.result.take().and_then(|ty| match &*ty {
            Value::Pi(_, _, _, _, codomain) => Some(codomain.clone().apply(self.ctx.fresh())),
            _ => None,
        });
        self.result = stepped;
        let inner = self.binding(bound, |inner| inner.lam_params(rest, body, deeper, drops))?;
        Ok(Term::Lam(mult, CoreName::from(&*name), Rc::new(inner)))
    }

    /// Параметры лямбды, которые она обязана закрыть сама.
    ///
    /// Правило то же, что у аргументов клаузы: ресурс, не упомянутый в теле,
    /// закрывается. Разбор в параметре сюда не попадает - его элаборация
    /// отвергает, - а `_` попадает: имени у него нет, упоминанию взяться
    /// неоткуда, и закрыть его обязаны всегда.
    fn closing_params(
        &self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
    ) -> Vec<(u32, Symbol)> {
        // Параметры связывают тело и затеняют в нём головы применений, а в
        // области видимости их ещё нет - решение принимается до спуска.
        let beside: Vec<Symbol> = params
            .iter()
            .filter_map(|param| match &param.kind {
                LamParamKind::Pattern(pattern) => match &pattern.kind {
                    PatternKind::Name(name) => Some(Rc::clone(&name.text)),
                    _ => None,
                },
                LamParamKind::Binder(_) => None,
            })
            .collect();
        let mut found: Vec<(u32, Symbol)> = Vec::new();
        for (position, param) in params.iter().enumerate() {
            let Some(drop) = expected.get(position).and_then(Argument::closes) else {
                continue;
            };
            let LamParamKind::Pattern(pattern) = &param.kind else {
                continue;
            };
            let mentioned = match &pattern.kind {
                PatternKind::Name(name) if !is_reference(&name.text) => {
                    self.mentions_beside(&name.text, body, &beside)
                }
                PatternKind::Wildcard => false,
                _ => continue,
            };
            if mentioned {
                continue;
            }
            let index = u32::try_from(params.len() - 1 - position).unwrap_or(u32::MAX);
            found.push((index, drop.clone()));
        }
        lifo(&mut found);
        found
    }

    /// Блок операторов: цепочка `let` и значение последним.
    fn block(&mut self, block: &Block, position: Position) -> Result<Term, ElabError> {
        self.statements(&block.stmts, position)
    }

    fn statements(&mut self, stmts: &[Stmt], position: Position) -> Result<Term, ElabError> {
        let Some((first, rest)) = stmts.split_first() else {
            // Пустых блоков layout не делает.
            unreachable!("блок без операторов")
        };
        match &first.kind {
            // Хвост блока стоит там же, где блок: возвращаемое значение
            // остаётся возвращаемым (§3.3), и отказ придёт на нём, а не на
            // блоке целиком. Закрытие сюда больше не копится - его ставит на
            // себя каждое связывание, см. `bindings`.
            StmtKind::Expr(expr) if rest.is_empty() => {
                self.placed(position, |it| it.expr(expr, Mult::Many))
            }
            // Оператор, значение которого отбрасывается: пишется он ради
            // эффектов (§3.4), а связывание ему нужно затем, чтобы вычисление
            // случилось до хвоста и в написанном порядке.
            //
            // Кратность `1`, а не `ω`, по тому же доводу, что и у вставленного
            // `drop`: при `ω` вектор использований масштабируется до `ω`, и
            // значение, потребившее что-то линейное, оказалось бы израсходовано
            // сверх меры.
            StmtKind::Expr(expr) => {
                let value = self.placed(Position::Inner, |it| it.expr(expr, Mult::Many))?;
                // Ожидаемого типа здесь нет - это и есть режим `infer` §3.4, и
                // вычисление в нём исполняется.
                let value = self.run(value);
                let ty = self.discarded(&value, first.span)?;
                let anonymous: Symbol = Rc::from("_");
                let bound = Bound {
                    value: Some(Rc::new(value.clone())),
                    ..Bound::visible(&anonymous, Mult::One, self.typed(&ty))
                };
                let body = self.binding(bound, |inner| inner.statements(rest, position))?;
                Ok(Term::Let(
                    Mult::One,
                    CoreName::from("_"),
                    Rc::new(ty),
                    Rc::new(value),
                    Rc::new(body),
                ))
            }
            // Блок кончается связыванием: значения у него нет, и дело не в
            // недостающем механизме - написана неполная форма.
            StmtKind::Let(_) if rest.is_empty() => {
                Err(ElabError::BlockWithoutValue { span: first.span })
            }
            StmtKind::Let(bindings) => self.bindings(bindings, rest, position),
        }
    }

    /// `let` со своими связываниями: каждое даёт узел `Let`, вложенный в
    /// следующее.
    fn bindings(
        &mut self,
        bindings: &[Binding],
        rest: &[Stmt],
        position: Position,
    ) -> Result<Term, ElabError> {
        let Some((binding, tail)) = bindings.split_first() else {
            return self.statements(rest, position);
        };
        if !binding.params.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: binding.span,
            });
        }
        let Some(ty) = &binding.ty else {
            return Err(ElabError::Missing {
                what: Missing::UntypedLet,
                span: binding.span,
            });
        };
        Self::binds(&binding.name)?;
        let mult = self.binder_mult(binding.mult, ty, Mult::Many, binding.span)?;
        // Ресурс, имя которого дальше не встречается, закрывается сам (§3.3);
        // стёртое связывание - нет, расходовать там нечего.
        let closes = mult != Mult::Zero
            && !self.mentioned_later(&binding.name.text, tail, rest)
            && self.owned.destructor(ty).is_some();
        let drop = closes.then(|| self.owned.destructor(ty).cloned()).flatten();
        let owns = self.owned.of(ty).is_some();
        let ty = self.typing(|inner| inner.expr(ty, Mult::Many))?;
        // Аннотация `let` - тот же написанный тип, и лямбда значения берёт
        // кратности у него.
        self.expected = pi_arguments(&ty, self.owned);
        // Аннотация снята до конца - остаток и есть ожидаемый результат.
        self.result = Some(self.typed(&peeled(&ty)));
        let annotation = self.typed(&ty);
        let value = self.expr(&binding.body, Mult::Many)?;
        // Аннотация и есть ожидаемый тип - `let n : Bool = get` исполняет,
        // `let f : {State Bool} Bool = get` передаёт (§3.4).
        let value = self.executed(value, Some(&annotation));
        // §3.3: связывание, инициализированное привязанным к scope значением,
        // само привязано. Без этого правило обходится в одну строку - и обход
        // выписан в §3.3 дословно.
        let scoped = self.produced.take().is_some();
        let bound = Bound {
            value: Some(Rc::new(value.clone())),
            ..Bound::owning_scoping(&binding.name.text, mult, annotation, owns, scoped)
        };
        // Вставка оборачивает **остаток блока**, а не его хвост: область
        // видимости связывания начинается здесь, и всё, что стоит между `let` и
        // хвостом, обязано быть внутри неё. Пока закрытие копилось до хвоста,
        // ресурс, за которым в блоке стоял хоть один оператор, при обрыве не
        // закрывался вовсе - машина не знала, что вошла в scope, - а разница
        // между «закрылся» и «утёк» была в одной строке между `let` и хвостом
        // (ревью 2026-09-04).
        //
        // LIFO выходит само: связывание, стоящее ниже, оборачивает меньший
        // кусок и закрывается первым.
        let body = self.binding(bound, |inner| {
            let rest = |it: &mut Self| it.bindings(tail, rest, position);
            match &drop {
                Some(drop) => inner.closing(Some(drop), 0, rest),
                None => rest(inner),
            }
        })?;
        Ok(Term::Let(
            mult,
            CoreName::from(&*binding.name.text),
            Rc::new(ty),
            Rc::new(value),
            Rc::new(body),
        ))
    }

    /// Собирает тело под вставленным `drop` и оборачивает его вызовом.
    ///
    /// `index` - индекс закрываемого связывания в области видимости **без**
    /// вставки; связывание самого вызова добавляется здесь и учитывается уже
    /// при сборке тела.
    ///
    /// Кратность вставки - `1`, а не `ω`: при `ω` вектор использований
    /// значения масштабируется до `ω`, и ресурс, связанный при `1`, тут же
    /// оказался бы израсходован сверх меры - отказ на программе, которую
    /// вставка и должна была починить.
    fn closing(
        &mut self,
        drop: Option<&Symbol>,
        index: u32,
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        let Some(drop) = drop else {
            return body(self);
        };
        // Тело считается **первым**: `drop` стоит в точке выхода из scope
        // (§3.3), а не входа в него. Прежняя форма - `let _ = drop h in тело` -
        // вычисляла деструктор раньше тела, и до исполнения эффектов этого не
        // было видно: результат отбрасывается, а `drop` не производил ничего.
        // С первым же эффектным `drop` порядок стал наблюдаем и оказался
        // обратным обещанному.
        let value = body(self)?;

        // Связать значение тела нужно с его типом, а написан он нигде: спайн
        // ожидаемого результирующего типа не несёт (§9 Фаза 4). Синтезируется
        // он по уже собранному терму - тот для того и собран.
        let Some(held) = self.held_type(&value) else {
            // Синтез не удался - тело есть **значение** (лямбда, запись):
            // вычислять до `drop` нечего, и прежняя форма верна. Тело при этом
            // собрано без связывания над ним, поэтому сдвигается.
            let (call, result) = self.destructor(drop, index);
            return Ok(Term::Let(
                Mult::One,
                CoreName::from("_"),
                Rc::new(result),
                Rc::new(call),
                Rc::new(adamas_core::pattern::shift_free(&value, 1)),
            ));
        };

        // Оба вычисления приостановлены, поэтому деструктор стоит под одним
        // связыванием - триггером - и индекс его аргумента на единицу глубже.
        let Some(closing) = self.closing_eliminator() else {
            // Единицы в программе нет, значит нет и эффектов: раскручивать
            // нечего, и прежняя форма считает то же самое.
            let (call, result) = self.destructor(drop, index.saturating_add(1));
            return Ok(Term::Let(
                Mult::One,
                CoreName::from("held"),
                Rc::new(quote(self.ctx.size(), &held)),
                Rc::new(value),
                Rc::new(Term::Let(
                    Mult::One,
                    CoreName::from("_"),
                    Rc::new(result),
                    Rc::new(call),
                    Rc::new(Term::var(1)),
                )),
            ));
        };
        let (call, result) = self.destructor(drop, index.saturating_add(1));
        let suspend = |term: Term| Term::Lam(Mult::Many, CoreName::from("_"), Rc::new(term));
        Ok(closing.apply([
            quote(self.ctx.size(), &held),
            result,
            suspend(adamas_core::pattern::shift_free(&value, 1)),
            suspend(call),
        ]))
    }

    /// Элиминатор scope с **окружающей** row в аргументе. `None` - не объявлен.
    ///
    /// Row подставляется, а не берётся дыркой, и это не оптимизация. Дырка
    /// связалась бы с окружающей только при погашении самого применения, а тело
    /// проверяется раньше - аргументом, - и его собственные эффекты гасить было
    /// бы нечем: `{Log | e}` против `{| ?0}` даёт отказ, потому что метки у
    /// нерешённой дырки нет ни одной.
    fn closing_eliminator(&mut self) -> Option<Term> {
        let definition = self.signature.lookup(CLOSING)?;
        let (levels, rows) = (definition.level_arity, definition.row_arity);
        let levels: Rc<[Level]> = (0..levels).map(|_| self.metas.fresh_level()).collect();
        let size = self.ctx.size();
        let ambient = self.ctx.row().map(|value| quote(size, value));
        let rows = Rows::new((0..rows).map(|_| ambient.clone()).collect::<Vec<_>>());
        Some(Term::Const(CoreName::from(CLOSING), levels, rows))
    }

    /// Тип тела, которое связывается ради `drop` в точке выхода.
    ///
    /// От [`Elaborator::synthesized`] отличается первой попыткой: при `σ = 0`
    /// окружающая пуста (§3.4), и эффектное тело синтеза не получает вовсе, а
    /// именно эффектное тело правку и потребовало. Неудачная попытка
    /// откатывается: решать за настоящую проверку она не вправе.
    fn held_type(&mut self, term: &Term) -> Option<Rc<Value>> {
        let mark = self.metas.mark();
        if let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Many, term) {
            return Some(ty);
        }
        self.metas.rollback(mark);
        self.synthesized(term)
    }

    /// Вызов деструктора и тип его результата.
    ///
    /// Аргументы уровня свежие на каждую вставку: два `drop` в одном
    /// определении - два независимых вхождения, и общие дырки связали бы их
    /// уровни между собой без причины.
    fn destructor(&mut self, drop: &Symbol, index: u32) -> (Term, Term) {
        let Some(definition) = self.signature.lookup(drop) else {
            unreachable!("деструктор `{drop}` объявлен вместе с типом")
        };
        let levels: Rc<[Level]> = (0..definition.level_arity)
            .map(|_| self.metas.fresh_level())
            .collect();
        let Term::Pi(_, _, _, _, result) = definition.ty.substitute_levels(&levels) else {
            unreachable!("`{drop}` проверен на форму при объявлении")
        };
        let call =
            Term::Const(CoreName::from(&**drop), levels, Rows::none()).apply([Term::var(index)]);
        (call, (*result).clone())
    }

    /// Цепочка операторов.
    ///
    /// Длиннее одного оператора - сперва расставляются скобки по объявленным
    /// фикситетам (§4.4), и цепочка становится вложенными одноместными: той
    /// формой, которую разбирает всё, что ниже.
    /// Операнды - те же аргументы применения, поэтому цепочка **становится**
    /// применением и уходит в тот же проход. Своя элаборация операндов, стоявшая
    /// здесь раньше, ожидаемого типа не видела вовсе: не вставлялись имплиситы
    /// посреди спайна и не исполнялось вычисление по ожидаемому типу, и
    /// `ask + ask` отвергалось там, где `plus ask ask` проходило.
    fn chain(&mut self, chain: &ast::Chain, span: Span) -> Result<Term, ElabError> {
        let [(operator, operand)] = &chain.tail[..] else {
            let resolved = self.fixities.resolve(chain, span)?;
            return self.expr(&resolved, Mult::Many);
        };
        let head = ast::Expr {
            kind: ast::ExprKind::Name(operator.clone()),
            span: operator.span,
        };
        let applied = ast::Expr {
            kind: ast::ExprKind::App(
                Box::new(ast::Expr {
                    kind: ast::ExprKind::App(Box::new(head), chain.head.clone()),
                    span,
                }),
                Box::new(operand.clone()),
            ),
            span,
        };
        self.expr(&applied, Mult::Many)
    }

    // --- паттерны ---------------------------------------------------------

    /// Паттерн клаузы или ветки.
    pub(crate) fn pattern(&self, pattern: &Pattern) -> Result<CorePattern, ElabError> {
        match &pattern.kind {
            PatternKind::Wildcard => Ok(CorePattern::Var(CoreName::from("_"))),
            PatternKind::Name(name) => {
                if is_reference(&name.text) {
                    self.constructor(name, Vec::new())
                } else {
                    Ok(CorePattern::Var(CoreName::from(&*name.text)))
                }
            }
            PatternKind::App { head, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<Vec<_>, _>>()?;
                self.constructor(head, fields)
            }
            PatternKind::Lit(_) => Err(ElabError::Missing {
                what: Missing::Literal,
                span: pattern.span,
            }),
            PatternKind::Tuple(items) => Err(ElabError::Missing {
                what: if items.is_empty() {
                    Missing::Unit
                } else {
                    Missing::Tuple
                },
                span: pattern.span,
            }),
        }
    }

    /// Имя конструктора: обязано быть объявленным конструктором.
    fn constructor(
        &self,
        name: &ast::Name,
        fields: Vec<CorePattern>,
    ) -> Result<CorePattern, ElabError> {
        let Some(declared) = self.signature.lookup(&name.text) else {
            return Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        };
        let DefinitionKind::Constructor { data, .. } = &declared.kind else {
            return Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        };
        // Параметры семейства полями не являются: разбор их не связывает, а
        // подставляет из типа разбираемого. В паттерне их поэтому нет вовсе -
        // ни написанных, ни вставленных.
        let params = self
            .signature
            .lookup(data)
            .and_then(Definition::data_shape)
            .map_or(0, |(params, _)| params);
        Ok(CorePattern::Constructor(
            CoreName::from(&*name.text),
            hidden_fields(&declared.ty, params, fields),
        ))
    }

    /// Клауза: паттерны, затем тело в контексте их переменных.
    ///
    /// Порядок переменных - слева направо в глубину: этого ждёт
    /// [`adamas_core::pattern::compile`], и другого тело видеть не может.
    pub(crate) fn clause(&mut self, clause: &ast::Clause) -> Result<Clause, ElabError> {
        if !clause.wheres.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: clause.span,
            });
        }
        let mut seen: Vec<&ast::Name> = Vec::new();
        for pattern in &clause.patterns {
            repeated(pattern, &mut seen)?;
        }
        let written = self.spread(&clause.patterns)?;
        let patterns: Vec<CorePattern> = written.iter().map(|(_, it)| it.clone()).collect();

        // Тип связывания виден и у аргумента верхнего уровня (по спайну
        // написанного), и у поля (по объявлению конструктора), поэтому
        // владение и закрытие считаются одним проходом по паттернам.
        let (bound, rest) = self.clause_variables(&written, &clause.body);
        let closing = closing_of(&bound);
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        // По одному: домен связывания живёт под предыдущими, и вычислить его
        // можно только тогда, когда те уже стоят в контексте.
        for variable in &bound {
            let ty = match &variable.ty {
                Some(ty) => Rc::clone(ty),
                None => self.hole(),
            };
            self.ctx = self.ctx.bind(
                CoreName::from(&*variable.name),
                variable.mult,
                Rc::clone(&ty),
            );
            self.scope.push(Bound {
                // Решённое разбором связывание уходит из спайна дырок: в нём
                // оно было бы вторым именем решившего, и спайн переставал бы
                // быть паттерном Миллера.
                value: variable.value.clone(),
                ..Bound::owning_scoping(
                    &variable.name,
                    variable.mult,
                    ty,
                    variable.owned,
                    variable.scoped,
                )
            });
        }
        // Паттерны сняли первые связывания написанного типа; остаток спайна -
        // тем лямбдам, которыми клауза продолжается.
        self.expected = self
            .declared
            .split_at(patterns.len().min(self.declared.len()))
            .1
            .to_vec();
        // Тело клаузы - возвращаемое значение определения (§3.3).
        // Окружающая row тела - у элаборации она нужна затем же, зачем ядру:
        // вывод типа в ней спотыкается о непогашенные эффекты, а на нём стоит
        // правило исполнения (§3.4).
        self.result.clone_from(&rest.result);
        self.ctx = self.ctx.within(rest.ambient);
        // Тип, оставшийся от написанного после паттернов, и есть ожидаемый
        // тип тела: по нему решается исполнение.
        let body = self
            .closing_all(&closing, |it| {
                it.placed(Position::Returned, |it| it.expr(&clause.body, Mult::Many))
            })
            .map(|body| self.executed(body, rest.result.as_ref()));
        self.scope.truncate(depth);
        self.ctx = outer;

        Ok(Clause {
            patterns,
            body: body?,
        })
    }

    /// Паттерны клаузы, разложенные по связываниям объявленного типа.
    ///
    /// Имплисит аргумента не получает, но связывание вводит, и подняли его
    /// (`lifting`) в тот же телескоп, по которому идут паттерны. Значит паттерн
    /// у него обязан быть: [`adamas_core::pattern::compile`] считает арность по
    /// их числу, и без вставки первый написанный паттерн встал бы на место
    /// имплисита. Имя берётся из связывания - оно и есть то, под которым тип
    /// назвал переменную.
    ///
    /// Написанное, не покрытое телескопом, идёт следом как есть: спайн виден
    /// синтаксически, и дальше него записей нет (см. `declared`).
    ///
    /// Связывание-единица, синтезированное сахаром `{ε} A`, вставляется по тому
    /// же соображению: аргументом определения оно не является, и §4.1 пишет
    /// `counter =` без него. Написанное при этом уважается - `counter u =`
    /// связывает единицу сам, - потому что вставка идёт только там, где
    /// паттернов не написали вовсе.
    fn spread<'p>(
        &self,
        written: &'p [Pattern],
    ) -> Result<Vec<(Option<&'p Pattern>, CorePattern)>, ElabError> {
        let mut found = Vec::new();
        let mut rest = written.iter();
        let mut suspends = self.declared_suspends && written.is_empty();
        for argument in &self.declared {
            if argument.implicit {
                found.push((None, CorePattern::Var(Rc::clone(&argument.name))));
                continue;
            }
            if std::mem::take(&mut suspends) {
                found.push((None, CorePattern::Var(Rc::clone(&argument.name))));
                continue;
            }
            let Some(pattern) = rest.next() else {
                break;
            };
            found.push((Some(pattern), self.pattern(pattern)?));
        }
        for pattern in rest {
            found.push((Some(pattern), self.pattern(pattern)?));
        }
        Ok(found)
    }

    /// Переменные паттернов клаузы в порядке связывания - вместе с типами.
    ///
    /// Проход один на три вопроса - тип связывания, владеет ли оно и
    /// закрывается ли, - потому что все три решает **тип**, а он известен на
    /// каждом шаге: у аргумента верхнего уровня из телескопа написанного, у
    /// поля из объявления конструктора при аргументах семейства, взятых у
    /// типа разбираемого.
    ///
    /// # Тип - значение, а не терм, и это не оптимизация
    ///
    /// Домен связывания, взятый термом, записан на глубине **своего места в
    /// телескопе**, а связывается на глубине **числа уже связанных
    /// переменных**. Совпадают они, только пока каждый аргумент даёт ровно
    /// одну переменную; `f (Wrap x) (Wrap y)` их разводит, и `y` получал тип
    /// чужого связывания (лог 2026-08-31). Значение от глубины не зависит:
    /// уровни в нём абсолютны, и телескоп шагает применением замыкания - тем
    /// же, чем шагает проверка.
    fn clause_variables(
        &mut self,
        written: &[(Option<&Pattern>, CorePattern)],
        body: &Expr,
    ) -> (Vec<BoundVar>, Rest) {
        // Имена собираются первым проходом: они связывают тело, а значит и
        // затеняют в нём головы применений, - но в области видимости их ещё
        // нет, решение о вставке принимается раньше.
        let mut names = Vec::new();
        for (_, pattern) in written {
            variables_of(pattern, &mut names);
        }
        let mut found = Vec::new();
        let mut level = self.ctx.size();
        let mut current = self.declared_ty.clone();
        let mut ambient = Row::empty();
        for (source, pattern) in written {
            let (mult, domain, codomain) = match current.as_deref() {
                Some(Value::Pi(binder, _, domain, row, codomain)) => {
                    // Окружающую row тела несёт последняя снятая стрелка
                    // (§3.4): под связыванием работают уже в ней.
                    ambient = row.clone();
                    (binder.mult, Some(Rc::clone(domain)), Some(codomain.clone()))
                }
                _ => (Mult::Many, None, None),
            };
            let value = self.pattern_variables(
                *source, pattern, mult, domain, body, &names, &mut found, &mut level,
            );
            current = match (codomain, value) {
                (Some(codomain), Some(value)) => Some(codomain.apply(value)),
                _ => None,
            };
        }
        // Остаток написанного типа считается по дороге: шагает по нему этот
        // проход, и второй такой был бы его копией.
        (
            found,
            Rest {
                result: current,
                ambient,
            },
        )
    }

    /// То же для одного паттерна, вглубь. Возвращает значение разобранного -
    /// им шагает телескоп дальше.
    ///
    /// `written` теряется у имплисита, которого автор не писал, и там, где у
    /// ядра формы нет вовсе; тогда упоминание считается состоявшимся -
    /// направление ошибки то же, что и везде: пропущенный `drop` вместо
    /// лишнего.
    #[allow(clippy::too_many_arguments)]
    fn pattern_variables(
        &mut self,
        written: Option<&Pattern>,
        compiled: &CorePattern,
        mult: Mult,
        ty: Option<Rc<Value>>,
        body: &Expr,
        beside: &[Symbol],
        found: &mut Vec<BoundVar>,
        level: &mut u32,
    ) -> Option<Rc<Value>> {
        match compiled {
            CorePattern::Var(name) => {
                // `_` закрывается всегда: имени у него нет, упоминанию взяться
                // неоткуда.
                let mentioned = match written.map(|it| &it.kind) {
                    Some(PatternKind::Wildcard) => false,
                    Some(PatternKind::Name(written)) if !is_reference(&written.text) => {
                        self.mentions_beside(&written.text, body, beside)
                    }
                    _ => true,
                };
                let head = ty.as_deref().and_then(head_name);
                let drop = head
                    .and_then(|name| self.owned.destructor_of(name))
                    .cloned()
                    .filter(|_| mult != Mult::Zero && !mentioned);
                let owned = head.is_some_and(|name| self.owned.owns(name));
                // §3.3: параметр кратности `1` функционального типа наследует
                // то же ограничение внутри вызываемой функции.
                let scoped = mult == Mult::One && matches!(ty.as_deref(), Some(Value::Pi(..)));
                found.push(BoundVar {
                    value: None,
                    name: Rc::from(&**name),
                    mult,
                    ty,
                    owned,
                    scoped,
                    drop,
                });
                let bound = Value::var(Lvl(*level));
                *level += 1;
                Some(bound)
            }
            CorePattern::Constructor(constructor, fields) => self.constructor_variables(
                written,
                constructor,
                fields,
                mult,
                ty.as_ref(),
                body,
                beside,
                found,
                level,
            ),
        }
    }

    /// То же для паттерна-конструктора: телескоп его типа шагает полями, а
    /// аргументы семейства берутся у типа разбираемого.
    ///
    /// `consumed` - кратность, с которой потребляется само разбираемое, и поле
    /// связывается при `qᵢ · consumed`: §3.3 пишет это дословно - «поле,
    /// связанное при `qᵢ·r`, разобранное в свою очередь, даёт `r' = qᵢ·r`».
    /// Ядро так и делает; элаборация же брала `qᵢ` как есть, и вложенный
    /// разбор давал полю `1` там, где ядро дало `ω`. Отсюда отказ на
    /// `case`-версии программы, которую клаузами написать можно: «`_`
    /// объявлена с кратностью 1, а использована ω» - про безымянное `_`,
    /// которого автор не писал.
    #[allow(clippy::too_many_arguments)]
    fn constructor_variables(
        &mut self,
        written: Option<&Pattern>,
        constructor: &CoreName,
        fields: &[CorePattern],
        consumed: Mult,
        ty: Option<&Rc<Value>>,
        body: &Expr,
        beside: &[Symbol],
        found: &mut Vec<BoundVar>,
        level: &mut u32,
    ) -> Option<Rc<Value>> {
        let inner = match written.map(|it| &it.kind) {
            Some(PatternKind::App { fields, .. }) => fields.as_slice(),
            _ => &[],
        };
        // Тип конструктора несёт **свои** параметры уровня, и брать его
        // как есть значило бы впустить `LevelVar` семейства в
        // определение, которое его не объявляло. Инстанциация свежими
        // дырками - то же, что делает всякая ссылка на объявленное.
        let declared = self.signature.lookup(constructor).map(|definition| {
            let params = match &definition.kind {
                DefinitionKind::Constructor { data } => self
                    .signature
                    .lookup(data)
                    .and_then(|it| it.data_shape().map(|(params, _)| params as usize))
                    .unwrap_or(0),
                _ => 0,
            };
            (definition.ty.clone(), definition.level_arity, params)
        });
        let Some((declared, arity, params)) = declared else {
            for (position, field) in fields.iter().enumerate() {
                self.pattern_variables(
                    inner.get(position),
                    field,
                    Mult::Many,
                    None,
                    body,
                    beside,
                    found,
                    level,
                );
            }
            return None;
        };
        let levels: Vec<Level> = (0..arity).map(|_| self.metas.fresh_level()).collect();
        let mut current = eval(&Env::default(), &declared.substitute_levels(&levels));
        // Аргументы семейства берутся у **типа разбираемого**: ветвь
        // их не связывает, а телескоп конструктора с них начинается.
        let spine = arguments_of(ty.map(std::convert::AsRef::as_ref));
        let mut known = spine.len() >= params;
        let mut applied = Vec::new();
        for argument in spine.into_iter().take(params) {
            // Телескоп шагает **замыканием кодомена**: `current` тут
            // тип, а не функция, и применять его как значение нельзя.
            let Value::Pi(_, _, _, _, codomain) = &*current else {
                known = false;
                break;
            };
            let codomain = codomain.clone();
            current = codomain.apply(Rc::clone(&argument));
            applied.push(argument);
        }
        for (position, field) in fields.iter().enumerate() {
            let (mult, domain, codomain) = match (known, &*current) {
                (true, Value::Pi(binder, _, domain, _, codomain)) => (
                    binder.mult * consumed,
                    Some(Rc::clone(domain)),
                    Some(codomain.clone()),
                ),
                _ => (Mult::Many, None, None),
            };
            let value = self.pattern_variables(
                inner.get(position),
                field,
                mult,
                domain,
                body,
                beside,
                found,
                level,
            );
            match (codomain, value) {
                (Some(codomain), Some(value)) => {
                    applied.push(Rc::clone(&value));
                    current = codomain.apply(value);
                }
                _ => return None,
            }
        }
        // Разбор решил индексы за автора: результат конструктора обязан
        // совпасть с типом разбираемого, и там, где у разбираемого стоит
        // переменная, она этим и определяется (§3.3, уточнение).
        if known {
            self.refine(ty, &current, params, found);
        }
        let name = CoreName::from(&**constructor);
        Some(applied.into_iter().fold(
            Value::constant(name, &levels, Rc::from([])),
            |callee, argument| apply(&callee, argument),
        ))
    }

    /// Записывает индексы, решённые разбором, значениями своих связываний.
    ///
    /// Зачем это элаборации, а не одному ядру: дырка, заведённая в ветви,
    /// несёт контекст спайном, и связывание, которое разбор уже решил, стоит в
    /// нём **вторым именем** решившего. `sym Refl = Refl` при `y := x` давало
    /// `?m a x x` - спайн нелинеен, паттерна Миллера нет, и решения не
    /// находилось, хотя оно единственно. Записанное значение выводит связывание
    /// из спайна: [`Elaborator::fresh_meta_outside`] ставит такие `Let`ом.
    ///
    /// Узко намеренно: решается только переменная переменной, и только той,
    /// что стоит **раньше**. Значение связывания живёт на его же глубине, и
    /// индекс, решённый полем конструктора (`n := Succ k` у `Vect`), туда не
    /// выражается - поле связывается позже. Такой индекс остаётся нерешённым,
    /// то есть ровно как сегодня.
    fn refine(
        &self,
        scrutinee: Option<&Rc<Value>>,
        result: &Rc<Value>,
        params: usize,
        found: &mut [BoundVar],
    ) {
        let base = self.ctx.size();
        let theirs = arguments_of(scrutinee.map(std::convert::AsRef::as_ref));
        let mine = arguments_of(Some(result));
        for (position, their) in theirs.iter().enumerate().skip(params) {
            let (Some(target), Some(source)) =
                (variable(their), mine.get(position).and_then(variable))
            else {
                continue;
            };
            // Раньше базы - связывание не этой клаузы, и трогать его нельзя:
            // область видимости у клауз общая.
            if target < base || source >= target {
                continue;
            }
            let Some(bound) = found.get_mut((target - base) as usize) else {
                continue;
            };
            if bound.value.is_some() {
                continue;
            }
            // Индекс на глубине связывания: переменная уровня `source` стоит от
            // него на `target - source - 1` связываний.
            bound.value = Some(Rc::new(Term::var(target - source - 1)));
        }
    }

    /// Оборачивает тело цепочкой вставленных `drop`.
    fn closing_all(
        &mut self,
        drops: &[(u32, Symbol)],
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        // Снимается **последний**, потому что обёртка теперь ставит свой `drop`
        // после тела: самый внешний слой срабатывает позже всех. Список идёт в
        // порядке LIFO, значит первым его элементом обязан быть внутренний слой.
        let Some(((index, drop), rest)) = drops.split_last() else {
            return body(self);
        };
        let drop = drop.clone();
        self.closing(Some(&drop), *index, |it| it.closing_all(rest, body))
    }
}

/// Переменная паттерна: имя, владение и деструктор, если её надо закрыть.
struct BoundVar {
    name: Symbol,
    /// Кратность и тип связывания - из телескопа, по которому шёл разбор.
    mult: Mult,
    /// Тип связывания - **значением**: терм пришлось бы сдвигать, потому что
    /// записан он на глубине своего места в телескопе, а связывается на
    /// глубине числа уже связанных переменных.
    ty: Option<Rc<Value>>,
    owned: bool,
    scoped: bool,
    drop: Option<Symbol>,
    /// Значение, решённое разбором индексов: `y := x` у `Refl`. `None` - не
    /// решено, то есть обычная переменная.
    value: Option<Rc<Term>>,
}

/// Закрываемые связывания в порядке вставки.
///
/// Индекс - расстояние от конца списка связанных: последняя переменная стоит
/// ближе всех. Порядок - LIFO, как обещает §3.3 для вложенных scope.
fn closing_of(bound: &[BoundVar]) -> Vec<(u32, Symbol)> {
    let mut found: Vec<(u32, Symbol)> = bound
        .iter()
        .enumerate()
        .filter_map(|(position, variable)| {
            let index = u32::try_from(bound.len() - 1 - position).unwrap_or(u32::MAX);
            variable.drop.clone().map(|drop| (index, drop))
        })
        .collect();
    lifo(&mut found);
    found
}

/// Снимает row с кодомена: `A -> {ε} B` есть стрелка с row и кодоменом `B`.
///
/// Написанный хвост сюда не проходит: он приходит вместе с auto-lift (§3.4,
/// Фаза 4), и связать его сегодня нечем.
fn split_row(codomain: &Expr) -> (Option<&Expr>, &Expr) {
    match &codomain.kind {
        ExprKind::Effectful { body, .. } => (Some(codomain), body),
        _ => (None, codomain),
    }
}

/// Имена переменных паттерна слева направо в глубину.
fn variables_of(pattern: &CorePattern, names: &mut Vec<Symbol>) {
    match pattern {
        CorePattern::Var(name) => names.push(Rc::from(&**name)),
        CorePattern::Constructor(_, fields) => {
            for field in fields {
                variables_of(field, names);
            }
        }
    }
}

/// Переставляет закрываемые в порядок закрытия: последнее связывание первым.
///
/// Поправки на глубину здесь больше нет: прежняя форма вкладывала вставки друг
/// в друга, и каждая следующая видела область видимости на связывание глубже, -
/// а нынешняя ставит каждое закрытие ровно под одно.
fn lifo(found: &mut [(u32, Symbol)]) {
    found.reverse();
}

/// Ветки `if` как альтернативы разбора по `Bool`.
///
/// Спаны берутся у самих веток: ошибка внутри ветки указывает на неё, а не на
/// `if` целиком. Имена конструкторов - `True` и `False`; не найдись они, откажет
/// компилятор клауз, и скажет он это про имя, а не про `if`.
fn conditional(then_branch: &Expr, else_branch: &Expr) -> Vec<ast::Alt> {
    let alt = |text: &str, body: &Expr| ast::Alt {
        pattern: Pattern {
            kind: PatternKind::Name(ast::Name {
                text: Rc::from(text),
                span: body.span,
            }),
            span: body.span,
        },
        body: body.clone(),
        span: body.span,
    };
    vec![alt("True", then_branch), alt("False", else_branch)]
}

/// Номер клаузы, на которой споткнулась сборка; `0` - когда его нет.
fn clause_of(error: &PatternError) -> usize {
    match error {
        PatternError::ClauseArity { clause, .. }
        | PatternError::UnboundInBody { clause }
        | PatternError::UnreachableClause { clause } => *clause,
        _ => 0,
    }
}

/// Начинается ли телескоп с выводимого связывания.
fn opens_implicit(ty: &Term) -> bool {
    matches!(ty, Term::Pi(binder, ..) if binder.visibility.is_implicit())
}

/// Поля конструктора с `_` на местах имплиситов.
///
/// То же, что `spread` делает с паттернами клаузы, и по той же причине:
/// имплисит поднялся в телескоп конструктора, а `Cons x xs` про него не знает.
/// Разбирать его нечем - имя типа в паттерне не пишется, - поэтому `_`.
///
/// Первые `params` связываний пропускаются вовсе: параметры семейства полем не
/// становятся, разбор берёт их из типа разбираемого, и ветвь их не связывает.
fn hidden_fields(ty: &Term, params: u32, written: Vec<CorePattern>) -> Vec<CorePattern> {
    let mut found = Vec::new();
    let mut rest = written.into_iter();
    let mut current = ty;
    let mut skipped = 0;
    while let Term::Pi(binder, _, _, _, codomain) = current {
        if skipped < params {
            skipped += 1;
            current = codomain;
            continue;
        }
        if binder.visibility.is_implicit() {
            found.push(CorePattern::Var(CoreName::from("_")));
        } else {
            let Some(pattern) = rest.next() else {
                break;
            };
            found.push(pattern);
        }
        current = codomain;
    }
    found.extend(rest);
    found
}

/// Связывания по спайну `Pi` - столько, сколько видно синтаксически.
fn pi_arguments(ty: &Term, owned: &Owned) -> Vec<Argument> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, bound, domain, _, codomain) = current {
        let mult = &binder.mult;
        let mut head = &**domain;
        while let Term::App(callee, _) = head {
            head = callee;
        }
        let name = match head {
            Term::Const(name, _, _) => Some(name),
            _ => None,
        };
        found.push(Argument {
            mult: *mult,
            domain: Rc::clone(domain),
            name: Rc::clone(bound),
            implicit: binder.visibility.is_implicit(),
            owned: name.is_some_and(|name| owned.owns(name)),
            functional: matches!(&**domain, Term::Pi(..)),
            drop: name.and_then(|name| owned.destructor_of(name)).cloned(),
        });
        current = codomain;
    }
    found
}

/// Параметры ветки хендлера, разложенные по связываниям её типа.
///
/// Имплисит аргумента не получает, но связывание вводит, и без вставки первый
/// написанный параметр встал бы на его место - ровно то же соображение, что у
/// клаузы (см. `Declared::spread`). Приносит имплиситы сама операция: `throw :
/// e -> a` поднимает `a` в implicit-параметр (§4.1), и ветка честно
/// полиморфна по нему - `handler_type` разбирает тип операции телескопом, а не
/// по числу параметров метки.
///
/// Имя берётся из связывания: тело вправе назвать поднятое тем же именем, под
/// которым его подняли.
fn spread_branch(
    bound: &[Argument],
    written: Vec<ast::LamParam>,
    span: Span,
) -> Vec<ast::LamParam> {
    if !bound.iter().any(|argument| argument.implicit) {
        return written;
    }
    let mut found = Vec::with_capacity(bound.len());
    let mut rest = written.into_iter();
    for argument in bound {
        if argument.implicit {
            found.push(bind_as(ast::Name {
                text: Rc::clone(&argument.name),
                span,
            }));
            continue;
        }
        let Some(param) = rest.next() else {
            break;
        };
        found.push(param);
    }
    found.extend(rest);
    found
}

/// Имена, которые связывает паттерн.
fn binds_names(pattern: &Pattern, bound: &mut Vec<Symbol>) {
    match &pattern.kind {
        PatternKind::Name(name) => bound.push(Rc::clone(&name.text)),
        PatternKind::App { fields, .. } => {
            for field in fields {
                binds_names(field, bound);
            }
        }
        PatternKind::Tuple(items) => {
            for item in items {
                binds_names(item, bound);
            }
        }
        PatternKind::Wildcard | PatternKind::Lit(_) => {}
    }
}

/// Повторное имя переменной в клаузе.
///
/// Клауза `f x x = x` терму отвечает корректному - побеждает правое вхождение,
/// потому что индекс ищется от ближайшего связывания, - и ядро её принимает.
/// Значит поймать опечатку может только элаборация: написанное равенство
/// аргументов языком не выражается, и разбор по нему сравнением не становится.
fn repeated<'a>(pattern: &'a Pattern, seen: &mut Vec<&'a ast::Name>) -> Result<(), ElabError> {
    match &pattern.kind {
        PatternKind::Name(name) if !is_reference(&name.text) => {
            if let Some(first) = seen.iter().find(|earlier| earlier.text == name.text) {
                return Err(ElabError::RepeatedBinding {
                    name: Rc::clone(&name.text),
                    span: name.span,
                    first: first.span,
                });
            }
            seen.push(name);
        }
        PatternKind::App { fields, .. } => {
            for field in fields {
                repeated(field, seen)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Имя головы значения-типа: `Vect a n` даёт `Vect`.
fn head_name(ty: &Value) -> Option<&CoreName> {
    match ty {
        Value::Neutral(Head::Global(name, ..), _) => Some(name),
        _ => None,
    }
}

/// Аргументы применения в голове типа - в порядке написания.
fn arguments_of(ty: Option<&Value>) -> Vec<Rc<Value>> {
    match ty {
        Some(Value::Neutral(Head::Global(..), spine)) => spine
            .iter()
            .filter_map(|elim| match elim {
                Elim::App(argument) => Some(Rc::clone(argument)),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// Локальная переменная без спайна - её уровень.
fn variable(value: &Rc<Value>) -> Option<u32> {
    match &**value {
        Value::Neutral(Head::Local(Lvl(level)), spine) if spine.is_empty() => Some(*level),
        _ => None,
    }
}

/// Применено ли до конца: результат больше не функция.
///
/// Только по этому и различаются «передать значение аргументом» - что §3.3
/// разрешает - и «собрать над ним замыкание», что она запрещает.
fn saturated(ty: &Value) -> bool {
    !matches!(ty, Value::Pi(..))
}

/// Имя головы применения. `None` - голова не имя.
fn applied_head(expr: &Expr) -> Option<Symbol> {
    let mut head = expr;
    while let ExprKind::App(callee, _) = &head.kind {
        head = callee;
    }
    match &head.kind {
        ExprKind::Name(name) => Some(Rc::clone(&name.text)),
        _ => None,
    }
}

/// Имена определений, упомянутые термом.
fn constants(term: &Term, into: &mut Vec<CoreName>) {
    match term {
        Term::Const(name, _, _) => into.push(Rc::clone(name)),
        Term::App(callee, argument) => {
            constants(callee, into);
            constants(argument, into);
        }
        Term::Lam(_, _, body) => constants(body, into),
        Term::Pi(_, _, domain, _, codomain) => {
            constants(domain, into);
            constants(codomain, into);
        }
        Term::Let(_, _, ty, value, body) => {
            constants(ty, into);
            constants(value, into);
            constants(body, into);
        }
        Term::Project(record, _) => constants(record, into),
        Term::With(base, fields) => {
            constants(base, into);
            for (_, field) in fields.iter() {
                constants(field, into);
            }
        }
        Term::Object(fields) => {
            for (_, field) in fields.iter() {
                constants(field, into);
            }
        }
        Term::Case(case) => {
            constants(&case.scrutinee, into);
            constants(&case.motive, into);
            for branch in &case.branches {
                constants(&branch.body, into);
            }
        }
        Term::Var(_) | Term::Meta(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind => {}
        Term::Record(fields) | Term::Row(fields) => {
            for field in fields.fields.iter() {
                constants(&field.ty, into);
            }
        }
    }
}

/// Результат типа: то, что остаётся, когда сняты все связывания.
fn peeled(ty: &Term) -> Term {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    current.clone()
}
