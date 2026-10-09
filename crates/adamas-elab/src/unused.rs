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
    self, Decl, DeclKind, Expr, ExprKind, LamParamKind, Name, Pattern, PatternKind, Stmt, StmtKind,
    Symbol,
};

use adamas_core::sig::{DefinitionKind, Signature};

use crate::expr::{
    CONS, DEFAULT_FLOAT, DEFAULT_INT, FROM_NAT, GRADE, NIL, SUCC, UNIT, ZERO, names_any,
};
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
            Self::Let => adamas_l10n::text!("unused-1"),
            Self::Lambda => adamas_l10n::text!("unused-2"),
            Self::Alt => adamas_l10n::text!("unused-3"),
            Self::Branch => adamas_l10n::text!("unused-4"),
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
        | ExprKind::Arrow(left, right)
        | ExprKind::Annotated(left, right) => {
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
        ExprKind::Guarded { guards, .. } => {
            for guard in guards {
                in_expr(&guard.cond, found);
                in_expr(&guard.body, found);
            }
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
        ExprKind::Section(section) => section.operand.iter().for_each(|it| in_expr(it, found)),
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

/// Имена из списков импорта, которые файл не употребляет (§10 вопрос 218).
///
/// Имя семейства открывает и его конструкторы, эффекта - и его операции
/// (§4.8), поэтому `import M (Bool)` употреблён, если в тексте стоит `True`.
/// Кого открыло имя, знает сигнатура: разбор этого не видит. Сам модуль,
/// импортированный без употреблённых имён, не предупреждает - инстансы
/// действуют на всю программу, и подключают его бывает ради них.
pub(crate) fn unused_imports(decls: &[Decl], signature: &Signature) -> Vec<Warning> {
    let mut found = Vec::new();
    for decl in decls {
        let DeclKind::Import(import) = &decl.kind else {
            continue;
        };
        let path = import.written();
        let head = format!("{path}.");
        for opened in &import.open {
            // `Unit` и `Mult` элаборация читает почти везде - вычисление есть
            // функция из `Unit`, - и по тексту этого не проследить.
            if [UNIT, GRADE].contains(&&*opened.text) {
                continue;
            }
            let sprouts = signature
                .lookup(&format!("{path}.{}", opened.text))
                .map(|definition| match &definition.kind {
                    DefinitionKind::Data { constructors, .. } => constructors.clone(),
                    DefinitionKind::Effect { operations, .. } => operations.clone(),
                    _ => Vec::new(),
                })
                .unwrap_or_default();
            let mut wanted: Vec<Symbol> = vec![opened.text.clone()];
            wanted.extend(
                sprouts
                    .iter()
                    .filter_map(|it| it.strip_prefix(&head).map(Symbol::from)),
            );
            let wanted: Vec<&Symbol> = wanted.iter().collect();
            let used = decls
                .iter()
                .filter(|it| !matches!(it.kind, DeclKind::Import(_)))
                .any(|it| decl_uses(it, &wanted));
            if !used {
                found.push(Warning::UnusedImport {
                    module: Symbol::from(path.as_str()),
                    name: opened.text.clone(),
                    span: opened.span,
                });
            }
        }
    }
    found
}

/// Употреблено ли в объявлении одно из имён - в типе, паттерне, выражении,
/// метке row, `using`, ветке хендлера или фикситете.
pub(crate) fn decl_uses(decl: &Decl, wanted: &[&Symbol]) -> bool {
    fn any<'e>(mut exprs: impl Iterator<Item = &'e Expr>, wanted: &[&Symbol]) -> bool {
        exprs.any(|it| uses(it, wanted))
    }
    let binders = |binders: &[ast::Binder]| {
        binders
            .iter()
            .filter_map(|it| it.ty.as_ref())
            .any(|it| uses(it, wanted))
    };
    match &decl.kind {
        DeclKind::Alias { params, body, .. } => {
            binders(params) || body.as_ref().is_some_and(|it| uses(it, wanted))
        }
        DeclKind::Signature { ty, .. } => uses(ty, wanted),
        DeclKind::Clauses { clauses, .. } => clauses.iter().any(|clause| {
            clause.patterns.iter().any(|it| pattern_uses(it, wanted))
                || uses(&clause.body, wanted)
                || clause.wheres.iter().any(|it| decl_uses(it, wanted))
        }),
        DeclKind::Data(data) => {
            binders(&data.params)
                || data.kind.as_ref().is_some_and(|it| uses(it, wanted))
                || any(data.constructors.iter().map(|it| &it.ty), wanted)
        }
        DeclKind::Module(module) => {
            binders(&module.params)
                || module.body.as_ref().is_some_and(|it| uses(it, wanted))
                || module
                    .ascription
                    .as_ref()
                    .is_some_and(|it| uses(it, wanted))
                || module.members.iter().any(|it| decl_uses(it, wanted))
        }
        DeclKind::Class(class) => {
            uses(&class.head, wanted)
                || binders(&class.params)
                || any(class.superclasses.iter(), wanted)
                || class.members.iter().any(|it| decl_uses(it, wanted))
        }
        DeclKind::Mutual(decls) => decls.iter().any(|it| decl_uses(it, wanted)),
        DeclKind::Resource(resource) => {
            binders(&resource.params) || resource.members.iter().any(|it| decl_uses(it, wanted))
        }
        DeclKind::Effect(effect) => {
            binders(&effect.params) || any(effect.operations.iter().map(|it| &it.ty), wanted)
        }
        DeclKind::Fixity(fixity) => fixity.operators.iter().any(|it| wanted.contains(&&it.text)),
        DeclKind::Extern(written) => uses(&written.ty, wanted),
        DeclKind::Export(written) => wanted.contains(&&written.name.text),
        DeclKind::Import(_) => false,
    }
}

fn pattern_uses(pattern: &Pattern, wanted: &[&Symbol]) -> bool {
    match &pattern.kind {
        PatternKind::Name(name) => wanted.contains(&&name.text),
        PatternKind::App { head, fields } => {
            wanted.contains(&&head.text) || fields.iter().any(|it| pattern_uses(it, wanted))
        }
        PatternKind::Tuple(items) => items.iter().any(|it| pattern_uses(it, wanted)),
        PatternKind::Wildcard | PatternKind::Lit(_) => false,
    }
}

fn label_uses(label: &ast::EffectLabel, wanted: &[&Symbol]) -> bool {
    wanted.contains(&&label.name.text) || label.arguments.iter().any(|it| uses(it, wanted))
}

/// Употребление в выражении - во всех позициях, где стоит написанное имя.
pub(crate) fn uses(expr: &Expr, wanted: &[&Symbol]) -> bool {
    let recur = |inner: &Expr| uses(inner, wanted);
    // Имена, которые форма читает по соглашению, не написав их (§4.1, §4.3):
    // `if` - разбор по `True`/`False`, литерал - `Zero`/`Succ`, умолчания и
    // `fromNat`, список - `Nil`/`Cons`.
    let implied = |names: &[&str]| wanted.iter().any(|it| names.contains(&&***it));
    match &expr.kind {
        ExprKind::Name(name) => wanted.contains(&&name.text),
        ExprKind::Lit(_) => implied(&[ZERO, SUCC, FROM_NAT, DEFAULT_INT, DEFAULT_FLOAT]),
        ExprKind::Hole => false,
        ExprKind::App(left, right)
        | ExprKind::TypeApp(left, right)
        | ExprKind::Arrow(left, right)
        | ExprKind::Annotated(left, right) => recur(left) || recur(right),
        ExprKind::Using { name, body } => wanted.contains(&&name.text) || recur(body),
        ExprKind::Lam { params, body } => {
            params.iter().any(|param| match &param.kind {
                LamParamKind::Pattern(pattern) => pattern_uses(pattern, wanted),
                LamParamKind::Binder(binder) => binder.ty.as_ref().is_some_and(recur),
            }) || recur(body)
        }
        ExprKind::Pi { binders, codomain } => {
            binders.iter().filter_map(|it| it.ty.as_ref()).any(recur) || recur(codomain)
        }
        ExprKind::Effectful { labels, body, .. } => {
            labels.iter().any(|it| label_uses(it, wanted)) || recur(body)
        }
        ExprKind::Block(block) => block.stmts.iter().any(|stmt| match &stmt.kind {
            StmtKind::Expr(inner) => recur(inner),
            StmtKind::Let(bindings) => bindings.iter().any(|it| {
                it.ty.as_ref().is_some_and(recur)
                    || it.params.iter().any(|param| pattern_uses(param, wanted))
                    || recur(&it.body)
            }),
        }),
        ExprKind::Handle {
            label,
            computation,
            state,
            branches,
            ..
        } => {
            label.as_deref().is_some_and(|it| label_uses(it, wanted))
                || recur(computation)
                || state.as_deref().is_some_and(recur)
                || branches
                    .iter()
                    .any(|it| wanted.contains(&&it.name.text) || recur(&it.body))
        }
        ExprKind::Mask(inner) | ExprKind::Project(inner, _) => recur(inner),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => implied(&["True", "False"]) || recur(cond) || recur(then_branch) || recur(else_branch),
        ExprKind::Guarded { guards, .. } => {
            implied(&["True", "False"])
                || guards
                    .iter()
                    .any(|guard| recur(&guard.cond) || recur(&guard.body))
        }
        ExprKind::Case { scrutinee, alts } => {
            recur(scrutinee)
                || alts
                    .iter()
                    .any(|alt| pattern_uses(&alt.pattern, wanted) || recur(&alt.body))
        }
        ExprKind::RecordType(fields, _) => fields.iter().any(|it| recur(&it.ty)),
        ExprKind::Record(fields) => fields.iter().any(|(_, value)| recur(value)),
        ExprKind::Update(base, fields) => {
            recur(base) || fields.iter().any(|(_, value)| recur(value))
        }
        ExprKind::Tuple(items) => items.iter().any(recur),
        ExprKind::List(items) => implied(&[NIL, CONS]) || items.iter().any(recur),
        ExprKind::Chain(chain) => {
            recur(&chain.head)
                || chain.tail.iter().any(|(operator, item)| {
                    wanted.contains(&&operator.text)
                        // `&&` и `||` строят `if` (§10 вопрос 208).
                        || (matches!(&*operator.text, "&&" | "||") && implied(&["True", "False"]))
                        || recur(item)
                })
        }
        // Секция `&&` и `||` - обычное применение: особой формы у неё нет.
        ExprKind::Section(section) => {
            wanted.contains(&&section.operator.text)
                || section.operand.as_deref().is_some_and(recur)
        }
    }
}
