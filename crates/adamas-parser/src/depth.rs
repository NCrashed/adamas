//! Предел вложенности: сколько узлов ядра встанет одно под другим (§10 вопрос 62).
//!
//! # Мера не та, что у разбора
//!
//! Спуск считает **свою** рекурсию: скобка стоит входа, а звена терму не даёт
//! вовсе. Потребителям дерева нужна другая величина - глубина того, что из
//! дерева получится, - и с первой она не совпадает ни в одну сторону. `f a b c`
//! набирается циклом и стоит одного входа, а даёт `App` по звену на аргумент;
//! `(((x)))` стоит шести входов и не даёт ни одного.
//!
//! Отсюда дефект, который этот проход закрывает: пределы, поставленные каждой
//! форме порознь, **складываются**. Сто двадцать скобок, в каждой по двести
//! аргументов, - вложенность разбора 120, длина всякого спайна 200, ни один
//! предел не нарушен, а терм глубиной в двадцать четыре тысячи звеньев, и
//! `check` срывается на нём в abort. То же давали три плоских списка, которым
//! предела не досталось вовсе: операторы блока, связывания одного `let` и имена
//! в одной группе.
//!
//! # Почему отдельным проходом
//!
//! Глубина узла известна только сверху, а длина плоского списка - только когда
//! он дочитан: разбирая первый аргумент, спуск ещё не знает, что за ним придёт
//! двести пятьдесят седьмой. Проход по готовому дереву знает и то и другое,
//! идёт явным стеком - то есть сам в предел не упирается - и стоит одного
//! обхода.
//!
//! # Правило разворота - по одному на форму
//!
//! Сколько звеньев ставит форма, знает элаборация, и здесь это повторено по
//! одному правилу на форму - тем же способом, что и в обратном проходе
//! маршрута. Разъехаться они могут только вместе с правилом, а `match` по
//! [`ExprKind`] исчерпывающий, поэтому новая форма заставит дописать и это.
//!
//! Списки при этом двух родов, и путать их нельзя. Одни разворачиваются в
//! цепочку - аргументы применения, имена группы, параметры лямбды, связывания
//! `let`, операторы блока, звенья цепочки операторов, **поля типа записи**, -
//! и каждый их элемент ставит звено. Другие собираются соседями - элементы
//! кортежа и списка, ветки `case`, конструкторы семейства, поля **значения**
//! записи - и стоят все на одной глубине.
//!
//! Запись показывает, что род списка читается не по скобкам, а по тому, что из
//! списка получится: `{ x : A, y : B }` - телескоп, где `B` живёт под `x`, а
//! `{ x = a, y = b }` - плоский набор значений. Один синтаксис, два рода.

use adamas_core::source::Span;

use crate::ast::{
    Binder, Block, Chain, Clause, Decl, DeclKind, Expr, ExprKind, LamParam, LamParamKind, Module,
    Pattern, PatternKind, StmtKind,
};
use crate::parser::{MAX_DEPTH, ParseError};

/// Узел дерева, которому осталось померить глубину.
enum Node<'a> {
    Expr(&'a Expr),
    Pattern(&'a Pattern),
    Decl(&'a Decl),
}

/// Работа прохода: узел и глубина, на которой он стоит.
type Pending<'a> = Vec<(Node<'a>, u32)>;

/// Проверяет, что ни один терм модуля не окажется глубже предела.
pub(crate) fn bounded(module: &Module) -> Result<(), ParseError> {
    let mut pending: Pending<'_> = module
        .decls
        .iter()
        .map(|decl| (Node::Decl(decl), 0))
        .collect();
    while let Some((node, depth)) = pending.pop() {
        match node {
            Node::Decl(decl) => decl_at(decl, depth, &mut pending)?,
            Node::Expr(expr) => expr_at(expr, depth, &mut pending)?,
            Node::Pattern(pattern) => pattern_at(pattern, depth, &mut pending)?,
        }
    }
    Ok(())
}

/// Ставит на путь `links` звеньев и отвечает получившейся глубиной.
///
/// `span` - форма целиком, а не её элемент: не помещается спайн, а не двести
/// пятьдесят седьмой аргумент, и показывать надо то, что не помещается.
fn deepen(depth: u32, links: usize, span: Span) -> Result<u32, ParseError> {
    let links = u32::try_from(links).unwrap_or(u32::MAX);
    let depth = depth.saturating_add(links);
    if depth > MAX_DEPTH {
        return Err(ParseError::TooDeep {
            limit: MAX_DEPTH,
            span,
        });
    }
    Ok(depth)
}

fn expr_at<'a>(expr: &'a Expr, depth: u32, pending: &mut Pending<'a>) -> Result<(), ParseError> {
    match &expr.kind {
        ExprKind::Name(_) | ExprKind::Lit(_) | ExprKind::Hole => {}
        // Row звено ставит одно - как стрелка, на которой она стоит; метки
        // соседи, и каждая живёт на той же глубине.
        ExprKind::Effectful { labels, body, .. } => {
            let inner = deepen(depth, 1, expr.span)?;
            pending.push((Node::Expr(body), inner));
            for label in labels {
                pending.extend(label.arguments.iter().map(|it| (Node::Expr(it), inner)));
            }
        }
        ExprKind::Using { body, .. } => pending.push((Node::Expr(body), depth)),
        // Тип записи - **телескоп**: тип поля живёт под предыдущими, и звено
        // ставит каждое (§4.2). Хвост звена не ставит - он переменная, а не
        // поле.
        ExprKind::RecordType(fields, _) => {
            let mut at = depth;
            for field in fields {
                at = deepen(at, 1, field.name.span)?;
                pending.push((Node::Expr(&field.ty), at));
            }
        }
        // Значение записи так не считается: зависимости в нём нет, поля -
        // соседи, и узел у них один плоский.
        ExprKind::Record(fields) => {
            let inner = deepen(depth, 1, expr.span)?;
            for (_, value) in fields {
                pending.push((Node::Expr(value), inner));
            }
        }
        ExprKind::Update(base, fields) => {
            let deeper = deepen(depth, 1, expr.span)?;
            pending.push((Node::Expr(base), deeper));
            for (_, value) in fields {
                pending.push((Node::Expr(value), deeper));
            }
        }
        ExprKind::Project(inner, _) => {
            let deeper = deepen(depth, 1, expr.span)?;
            pending.push((Node::Expr(inner), deeper));
        }
        ExprKind::App(..) => application(expr, depth, pending)?,
        // Применение типа - то же `App`, стрелка - `Pi` без имени: звено и там
        // и там одно.
        ExprKind::TypeApp(left, right) | ExprKind::Arrow(left, right) => {
            let inner = deepen(depth, 1, expr.span)?;
            pending.push((Node::Expr(left), inner));
            pending.push((Node::Expr(right), inner));
        }
        ExprKind::Pi { binders, codomain } => pi(binders, codomain, depth, expr.span, pending)?,
        ExprKind::Lam { params, body } => lam(params, body, depth, expr.span, pending)?,
        // Блок звена не ставит: его ставят операторы.
        ExprKind::Block(block) => block_at(block, depth, pending)?,
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let inner = deepen(depth, 1, expr.span)?;
            for part in [cond, then_branch, else_branch] {
                pending.push((Node::Expr(part), inner));
            }
        }
        // Ветки - соседи: разбор один, и каждая стоит под ним, а не под
        // предыдущей.
        ExprKind::Case { scrutinee, alts } => {
            let inner = deepen(depth, 1, expr.span)?;
            pending.push((Node::Expr(scrutinee), inner));
            for alt in alts {
                pending.push((Node::Pattern(&alt.pattern), inner));
                pending.push((Node::Expr(&alt.body), inner));
            }
        }
        // Элементы собирает конструктор, а не цепочка: они соседи.
        ExprKind::Tuple(items) | ExprKind::List(items) => {
            let inner = deepen(depth, 1, expr.span)?;
            pending.extend(items.iter().map(|item| (Node::Expr(item), inner)));
        }
        ExprKind::Chain(chain) => chain_at(chain, depth, expr.span, pending)?,
    }
    Ok(())
}

/// `f a b c` - звено `App` на аргумент; голова стоит под всеми.
fn application<'a>(
    expr: &'a Expr,
    depth: u32,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let mut arguments = Vec::new();
    let mut head = expr;
    while let ExprKind::App(callee, argument) = &head.kind {
        arguments.push(&**argument);
        head = callee;
    }
    let inner = deepen(depth, arguments.len(), expr.span)?;
    pending.push((Node::Expr(head), inner));
    // Последний аргумент собран первым и стоит выше всех.
    let mut at = depth;
    for argument in arguments {
        at += 1;
        pending.push((Node::Expr(argument), at));
    }
    Ok(())
}

/// `(q x y : A) (r z : B) -> C` - `Pi` на каждое имя; кодомен под всеми.
fn pi<'a>(
    binders: &'a [Binder],
    codomain: &'a Expr,
    depth: u32,
    span: Span,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let names = binders.iter().map(|binder| binder.names.len()).sum();
    let inner = deepen(depth, names, span)?;
    pending.push((Node::Expr(codomain), inner));
    // Тип группы элаборируется заново под каждым её именем, и глубже всех -
    // под последним.
    let mut at = depth;
    for binder in binders {
        for _ in &binder.names {
            at += 1;
        }
        if let Some(ty) = &binder.ty {
            pending.push((Node::Expr(ty), at));
        }
    }
    Ok(())
}

/// `\x y -> body` - `Lam` на каждый параметр.
fn lam<'a>(
    params: &'a [LamParam],
    body: &'a Expr,
    depth: u32,
    span: Span,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let inner = deepen(depth, params.len(), span)?;
    pending.push((Node::Expr(body), inner));
    let mut at = depth;
    for param in params {
        at += 1;
        match &param.kind {
            LamParamKind::Pattern(pattern) => pending.push((Node::Pattern(pattern), at)),
            // Тип параметра в терм лямбды не попадает - его несёт `Pi`
            // снаружи, - но написан он здесь, и мерить внутри него всё равно
            // надо.
            LamParamKind::Binder(binder) => {
                if let Some(ty) = &binder.ty {
                    pending.push((Node::Expr(ty), at));
                }
            }
        }
    }
    Ok(())
}

/// Блок: каждое связывание даёт `Let`, и всё, что за ним, стоит под ним.
fn block_at<'a>(block: &'a Block, depth: u32, pending: &mut Pending<'a>) -> Result<(), ParseError> {
    let mut at = depth;
    for stmt in &block.stmts {
        match &stmt.kind {
            StmtKind::Let(bindings) => {
                for binding in bindings {
                    at = deepen(at, 1, binding.span)?;
                    if let Some(ty) = &binding.ty {
                        pending.push((Node::Expr(ty), at));
                    }
                    pending.push((Node::Expr(&binding.body), at));
                    pending.extend(
                        binding
                            .params
                            .iter()
                            .map(|param| (Node::Pattern(param), at)),
                    );
                }
            }
            // Хвост блока - тело последнего `let`.
            StmtKind::Expr(expr) => pending.push((Node::Expr(expr), at)),
        }
    }
    Ok(())
}

/// Цепочка операторов: оператор - то же применение, поэтому звеньев два на
/// каждый.
fn chain_at<'a>(
    chain: &'a Chain,
    depth: u32,
    span: Span,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let inner = deepen(depth, chain.tail.len().saturating_mul(2), span)?;
    pending.push((Node::Expr(&chain.head), inner));
    // Последний оператор стоит снаружи, поэтому его операнд - выше всех.
    let mut at = depth;
    for (_, operand) in chain.tail.iter().rev() {
        at += 1;
        pending.push((Node::Expr(operand), at));
        at += 1;
    }
    Ok(())
}

fn pattern_at<'a>(
    pattern: &'a Pattern,
    depth: u32,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let (PatternKind::App { fields: inner, .. } | PatternKind::Tuple(inner)) = &pattern.kind else {
        return Ok(());
    };
    // Поля - соседи: разбор один на конструктор.
    let at = deepen(depth, 1, pattern.span)?;
    pending.extend(inner.iter().map(|field| (Node::Pattern(field), at)));
    Ok(())
}

fn decl_at<'a>(decl: &'a Decl, depth: u32, pending: &mut Pending<'a>) -> Result<(), ParseError> {
    match &decl.kind {
        DeclKind::Alias { params, body, .. } => {
            binder_terms(params, depth, pending);
            if let Some(body) = body {
                pending.push((Node::Expr(body), depth));
            }
        }
        DeclKind::Signature { ty: body, .. } => {
            pending.push((Node::Expr(body), depth));
        }
        DeclKind::Clauses { clauses, .. } => {
            for clause in clauses {
                clause_at(clause, depth, pending)?;
            }
        }
        DeclKind::Mutual(members) => {
            let inner = deepen(depth, 1, decl.span)?;
            for member in members {
                decl_at(member, inner, pending)?;
            }
        }
        DeclKind::Class(class) => {
            let inner = deepen(depth, 1, decl.span)?;
            pending.push((Node::Expr(&class.head), depth));
            binder_terms(&class.params, depth, pending);
            for superclass in &class.superclasses {
                pending.push((Node::Expr(superclass), depth));
            }
            for member in &class.members {
                decl_at(member, inner, pending)?;
            }
        }
        // Вложенность модуля считается как вложенность блока: член объявлен
        // глубже, и глубина у него на шаг больше.
        DeclKind::Module(module) => {
            let inner = deepen(depth, 1, decl.span)?;
            for ty in module.params.iter().filter_map(|it| it.ty.as_ref()) {
                pending.push((Node::Expr(ty), depth));
            }
            if let Some(ascription) = &module.ascription {
                pending.push((Node::Expr(ascription), depth));
            }
            if let Some(body) = &module.body {
                pending.push((Node::Expr(body), depth));
            }
            for member in &module.members {
                decl_at(member, inner, pending)?;
            }
        }
        DeclKind::Data(data) => {
            binder_terms(&data.params, depth, pending);
            if let Some(kind) = &data.kind {
                pending.push((Node::Expr(kind), depth));
            }
            // Конструкторы - соседи, и каждый начинает свой тип с нуля.
            pending.extend(
                data.constructors
                    .iter()
                    .map(|constructor| (Node::Expr(&constructor.ty), depth)),
            );
        }
        DeclKind::Resource(resource) => {
            binder_terms(&resource.params, depth, pending);
            pending.extend(
                resource
                    .members
                    .iter()
                    .map(|member| (Node::Decl(member), depth)),
            );
        }
    }
    Ok(())
}

/// Клауза: аргумент даёт лямбду, тело стоит под всеми.
fn clause_at<'a>(
    clause: &'a Clause,
    depth: u32,
    pending: &mut Pending<'a>,
) -> Result<(), ParseError> {
    let inner = deepen(depth, clause.patterns.len(), clause.span)?;
    pending.push((Node::Expr(&clause.body), inner));
    let mut at = depth;
    for pattern in &clause.patterns {
        at += 1;
        pending.push((Node::Pattern(pattern), at));
    }
    // Локальные определения - свои термы, а не продолжение этого.
    pending.extend(clause.wheres.iter().map(|local| (Node::Decl(local), depth)));
    Ok(())
}

/// Термы групп связываний - каждый со своей глубины.
///
/// Термов у связывания **два**, и оба написаны автором: тип и умолчание
/// (§4.1). Пропусти любой - и предел его не меряет: `type T (a = {f0 : Nat,
/// … })` роняло разбор в переполнение стека, ни разу не нарушив предела,
/// потому что глубина считалась только по типу.
fn binder_terms<'a>(binders: &'a [Binder], depth: u32, pending: &mut Pending<'a>) {
    for binder in binders {
        pending.extend(binder.ty.as_ref().map(|ty| (Node::Expr(ty), depth)));
        pending.extend(
            binder
                .default
                .as_ref()
                .map(|default| (Node::Expr(default), depth)),
        );
    }
}
