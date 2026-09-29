//! Связывания, которые никто не читает (§10 вопрос 218).
//!
//! Проход синтаксический: элаборация одно и то же выражение проходит не раз -
//! пробные проходы откатываются, - и отмечать употребления там значило бы
//! разбираться, какой из проходов настоящий. Здесь достаточно дерева: имя
//! связано, и в своей области видимости оно либо встречается, либо нет.
//!
//! Переменная паттерна клаузы не предупреждает: она стоит на позиции
//! сигнатуры, и `head n (VCons k x xs) = x` - обычный стиль, где имя называет
//! поле и непрочитанным. Параметры `let`-функции - те же клаузы. Прочие
//! связывания - `let`, лямбда, альтернатива `case`, ветка хендлера - пишутся
//! ради чтения, и непрочитанное там - оговорка. `_x` молчит везде.
//!
//! Заслонение не учитывается: `let x = 1` и ниже `\x -> x` засчитают внешнему
//! `x` употребление внутреннего. Ошибка от этого одна - предупреждения нет
//! там, где оно было бы, - и ложного предупреждения она не даёт.

use adamas_parser::ast::{
    Decl, DeclKind, Expr, ExprKind, LamParamKind, Name, Pattern, PatternKind, Stmt, StmtKind,
    Symbol,
};

use crate::expr::names_any;
use crate::warn::Warning;

/// Где связано имя, которое никто не читает, - подлежащим сообщения.
#[derive(Clone, Copy)]
enum Site {
    /// `let x = …`.
    Let,
    /// Параметр лямбды: `\x -> 0`.
    Lambda,
    /// Переменная паттерна альтернативы `case`: `Cons x xs -> xs`.
    Alt,
    /// Параметр ветки хендлера: `put s -> resume MkUnit`.
    Branch,
}

impl Site {
    fn what(self) -> &'static str {
        match self {
            Self::Let => "связывание `let`",
            Self::Lambda => "параметр лямбды",
            Self::Alt => "переменная альтернативы",
            Self::Branch => "параметр ветки хендлера",
        }
    }
}

/// Предупреждения о неиспользованных связываниях объявлений файла.
pub(crate) fn unused(decls: &[Decl]) -> Vec<Warning> {
    let mut found = Vec::new();
    for decl in decls {
        in_decl(decl, &mut found);
    }
    found
}

/// Молчит ли имя по соглашению: `_x` пишется ради того, чтобы не читать.
fn silenced(name: &Name) -> bool {
    name.text.starts_with('_')
}

fn in_decl(decl: &Decl, found: &mut Vec<Warning>) {
    match &decl.kind {
        DeclKind::Clauses { clauses, .. } => {
            for clause in clauses {
                in_clause(&clause.body, &clause.wheres, found);
            }
        }
        DeclKind::Mutual(decls) => decls.iter().for_each(|it| in_decl(it, found)),
        DeclKind::Module(module) => module.members.iter().for_each(|it| in_decl(it, found)),
        DeclKind::Class(class) => class.members.iter().for_each(|it| in_decl(it, found)),
        DeclKind::Resource(resource) => resource.members.iter().for_each(|it| in_decl(it, found)),
        _ => {}
    }
}

fn in_clause(body: &Expr, wheres: &[Decl], found: &mut Vec<Warning>) {
    in_expr(body, found);
    for it in wheres {
        in_decl(it, found);
    }
}

fn report(site: Site, name: Name, used: bool, found: &mut Vec<Warning>) {
    if !used && !silenced(&name) {
        found.push(Warning::UnusedBinding {
            what: site.what(),
            span: name.span,
            name: name.text,
        });
    }
}

/// Имена, которые паттерн связывает: строчные.
fn binders(pattern: &Pattern, into: &mut Vec<Name>) {
    match &pattern.kind {
        PatternKind::Name(name)
            if name
                .text
                .starts_with(|c: char| c.is_lowercase() || c == '_') =>
        {
            into.push(name.clone());
        }
        PatternKind::App { fields, .. } => fields.iter().for_each(|it| binders(it, into)),
        PatternKind::Tuple(items) => items.iter().for_each(|it| binders(it, into)),
        _ => {}
    }
}

fn in_expr(expr: &Expr, found: &mut Vec<Warning>) {
    match &expr.kind {
        ExprKind::Lam { params, body } => {
            for param in params {
                let mut bound = Vec::new();
                match &param.kind {
                    LamParamKind::Pattern(pattern) => binders(pattern, &mut bound),
                    LamParamKind::Binder(binder) => bound.extend(binder.names.iter().cloned()),
                }
                for name in bound {
                    let used = names_any(body, &[&name.text]);
                    report(Site::Lambda, name, used, found);
                }
            }
            in_expr(body, found);
        }
        ExprKind::Block(block) => in_block(&block.stmts, found),
        ExprKind::Case { scrutinee, alts } => {
            in_expr(scrutinee, found);
            for alt in alts {
                let mut bound = Vec::new();
                binders(&alt.pattern, &mut bound);
                for name in bound {
                    let used = names_any(&alt.body, &[&name.text]);
                    report(Site::Alt, name, used, found);
                }
                in_expr(&alt.body, found);
            }
        }
        ExprKind::Handle {
            computation,
            state,
            branches,
            ..
        } => {
            in_expr(computation, found);
            if let Some(state) = state {
                in_expr(state, found);
            }
            for branch in branches {
                for name in &branch.params {
                    let used = names_any(&branch.body, &[&name.text]);
                    report(Site::Branch, name.clone(), used, found);
                }
                in_expr(&branch.body, found);
            }
        }
        ExprKind::App(left, right)
        | ExprKind::TypeApp(left, right)
        | ExprKind::Arrow(left, right) => {
            in_expr(left, found);
            in_expr(right, found);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            in_expr(cond, found);
            in_expr(then_branch, found);
            in_expr(else_branch, found);
        }
        ExprKind::Using { body, .. } | ExprKind::Mask(body) | ExprKind::Project(body, _) => {
            in_expr(body, found);
        }
        ExprKind::Effectful { body, .. } => in_expr(body, found),
        ExprKind::Record(fields) => fields.iter().for_each(|(_, it)| in_expr(it, found)),
        ExprKind::Update(base, fields) => {
            in_expr(base, found);
            for (_, it) in fields {
                in_expr(it, found);
            }
        }
        ExprKind::Tuple(items) | ExprKind::List(items) => {
            for it in items {
                in_expr(it, found);
            }
        }
        ExprKind::Chain(chain) => {
            in_expr(&chain.head, found);
            chain.tail.iter().for_each(|(_, it)| in_expr(it, found));
        }
        ExprKind::Name(_)
        | ExprKind::Lit(_)
        | ExprKind::Hole
        | ExprKind::Pi { .. }
        | ExprKind::RecordType(..) => {}
    }
}

/// Блок: связывание видно операторам после себя.
fn in_block(stmts: &[Stmt], found: &mut Vec<Warning>) {
    for (at, stmt) in stmts.iter().enumerate() {
        let rest = &stmts[at + 1..];
        match &stmt.kind {
            StmtKind::Expr(expr) => in_expr(expr, found),
            StmtKind::Let(bindings) => {
                for (index, binding) in bindings.iter().enumerate() {
                    let later = &bindings[index + 1..];
                    let used = rest.iter().any(|it| stmt_mentions(it, &binding.name.text))
                        || later
                            .iter()
                            .any(|it| names_any(&it.body, &[&binding.name.text]));
                    report(Site::Let, binding.name.clone(), used, found);
                    if binding.params.is_empty() {
                        in_expr(&binding.body, found);
                    } else {
                        in_clause(&binding.body, &[], found);
                    }
                }
            }
        }
    }
}

fn stmt_mentions(stmt: &Stmt, name: &Symbol) -> bool {
    match &stmt.kind {
        StmtKind::Expr(expr) => names_any(expr, &[name]),
        StmtKind::Let(bindings) => bindings.iter().any(|it| {
            names_any(&it.body, &[name]) || it.ty.as_ref().is_some_and(|ty| names_any(ty, &[name]))
        }),
    }
}
