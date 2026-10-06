//! Локальные определения (`where`) поднимаются на верхний уровень (§4.1,
//! решение 2026-10-06).
//!
//! # Почему подъёмом
//!
//! Единица объявления у ядра - определение верхнего уровня, и локальной
//! рекурсии оно не знает. Самый частый `where` - рекурсивный помощник `go`, и
//! сахар в `let` его бы не выразил. Подъём делает из локальной функции обычное
//! определение: рекурсия, взаимная рекурсия, тотальность и анализы видят его
//! тем же, чем видят всякое другое, а ядро не трогается.
//!
//! # Как
//!
//! Проход идёт по дереву до элаборации. Локальная функция `g` клаузы `f`
//! становится определением `f#g` - имя невыразимо в программе, как у словаря
//! инстанса, - чьи первые параметры - захваченные параметры клаузы, а дальше
//! написанная сигнатура `g`. Тип захваченного берётся из сигнатуры `f` по
//! позиции. Ссылки не переписываются: тело клаузы начинается с
//! `let g = f#g x …`, частичным применением к захваченному, и тем же `let`
//! начинается тело самого `f#g`, если оно зовёт себя или соседа. Захват
//! замкнут по соседям: зовёт `g` соседа `h` - захватывает и то, что нужно `h`.
//!
//! Значение без параметров не поднимается, а становится `let` в начале тела:
//! считается один раз, и сигнатура ему не нужна. Функция, которая его
//! называет, получает тот же `let` в начале своего тела.
//!
//! # Чего нет
//!
//! Захватывается параметр, написанный именем; поле конструктора в паттерне не
//! захватывается - имени у позиции нет, и передать её нечем. Тип захваченного
//! не вправе зависеть от другого параметра: переименовать связывание в чужом
//! типе этот проход не умеет. Обе границы - названный отказ.

use std::collections::HashSet;

use adamas_parser::ast::Binding;
use adamas_parser::ast::{
    Binder, Block, Clause, Decl, DeclKind, Expr, ExprKind, MultAnn, Name, Pattern, PatternKind,
    Stmt, StmtKind, Symbol, Visibility,
};

use crate::error::ElabError;
use crate::unused::{decl_uses, uses};

/// Объявления с поднятыми локальными определениями и отказы подъёма.
///
/// Определение, которое поднять нельзя, уходит в отказ, а его клаузы - из
/// списка: иначе элаборация отказала бы ему второй раз, общим текстом.
pub(crate) fn lifted(decls: &[Decl]) -> (Vec<Decl>, Vec<ElabError>) {
    let mut out = Vec::with_capacity(decls.len());
    let mut errors = Vec::new();
    let mut taken = HashSet::new();
    walk(decls, false, &mut out, &mut errors, &mut taken);
    (out, errors)
}

fn walk(
    decls: &[Decl],
    inside: bool,
    out: &mut Vec<Decl>,
    errors: &mut Vec<ElabError>,
    taken: &mut HashSet<Symbol>,
) {
    for decl in decls {
        match &decl.kind {
            DeclKind::Clauses { name, clauses }
                if clauses.iter().any(|it| !it.wheres.is_empty()) =>
            {
                let signature = match out.last() {
                    Some(Decl {
                        kind:
                            DeclKind::Signature {
                                name: written, ty, ..
                            },
                        ..
                    }) if written.text == name.text => Some(ty.clone()),
                    _ => None,
                };
                // Сигнатуры рядом нет - элаборация откажет так же, как без
                // `where`: «клаузы без сигнатуры».
                let Some(ty) = signature else {
                    out.push(decl.clone());
                    continue;
                };
                match lift(name, Some(&ty), clauses, taken) {
                    Ok(done) => {
                        let mut raised = Vec::new();
                        walk(&done.raised, true, &mut raised, errors, taken);
                        let own = Decl {
                            kind: DeclKind::Clauses {
                                name: name.clone(),
                                clauses: done.clauses,
                            },
                            span: decl.span,
                        };
                        if done.mutual && !inside {
                            let Some(signature) = out.pop() else {
                                unreachable!("сигнатура найдена последней выше")
                            };
                            raised.push(signature);
                            raised.push(own);
                            out.push(Decl {
                                kind: DeclKind::Mutual(raised),
                                span: decl.span,
                            });
                        } else {
                            // Поднятые встают **перед** сигнатурой: она
                            // спаривается со следующими за ней клаузами.
                            let at = out.len() - 1;
                            out.splice(at..at, raised);
                            out.push(own);
                        }
                    }
                    Err(error) => errors.push(error),
                }
            }
            DeclKind::Class(class) => {
                let (members, raised) = class_members(&class.members, errors, taken);
                out.extend(raised);
                let mut class = class.clone();
                class.members = members;
                out.push(Decl {
                    kind: DeclKind::Class(class),
                    span: decl.span,
                });
            }
            DeclKind::Mutual(members) => {
                let mut inner = Vec::new();
                walk(members, true, &mut inner, errors, taken);
                out.push(Decl {
                    kind: DeclKind::Mutual(inner),
                    span: decl.span,
                });
            }
            _ => out.push(decl.clone()),
        }
    }
}

/// Явный параметр сигнатуры: тип и кратность по позиции.
struct Param {
    mult: Option<MultAnn>,
    ty: Option<Expr>,
}

/// Явные параметры сигнатуры по порядку и имена, которыми она их связала.
fn telescope(ty: &Expr) -> (Vec<Param>, Vec<Symbol>) {
    let mut params = Vec::new();
    let mut names = Vec::new();
    let mut current = ty;
    loop {
        match &current.kind {
            ExprKind::Arrow(domain, codomain) => {
                params.push(Param {
                    mult: None,
                    ty: Some((**domain).clone()),
                });
                current = codomain;
            }
            ExprKind::Pi { binders, codomain } => {
                for binder in binders {
                    names.extend(binder.names.iter().map(|it| it.text.clone()));
                    if binder.visibility == Visibility::Explicit {
                        for _ in &binder.names {
                            params.push(Param {
                                mult: binder.mult,
                                ty: binder.ty.clone(),
                            });
                        }
                    }
                }
                current = codomain;
            }
            _ => return (params, names),
        }
    }
}

/// Локальное определение: сигнатура, если написана, и клаузы.
struct Local {
    name: Name,
    signature: Option<Expr>,
    clauses: Vec<Clause>,
}

impl Local {
    /// Функция поднимается, значение становится `let`.
    fn function(&self) -> bool {
        self.clauses.iter().any(|it| !it.patterns.is_empty())
    }

    /// Упоминает ли определение имя - в клаузах или в сигнатуре.
    fn mentions(&self, name: &Symbol) -> bool {
        let wanted = [name];
        let clauses = Decl {
            kind: DeclKind::Clauses {
                name: self.name.clone(),
                clauses: self.clauses.clone(),
            },
            span: self.name.span,
        };
        decl_uses(&clauses, &wanted) || self.signature.as_ref().is_some_and(|it| uses(it, &wanted))
    }
}

/// Итог подъёма одного определения.
struct Lifted {
    /// Поднятые определения: сигнатура и клаузы каждого.
    raised: Vec<Decl>,
    /// Клаузы самого определения без `where`.
    clauses: Vec<Clause>,
    /// Зовут ли поднятые определение или друг друга: тогда группа `mutual`.
    mutual: bool,
}

fn lift(
    owner: &Name,
    ty: Option<&Expr>,
    clauses: &[Clause],
    taken: &mut HashSet<Symbol>,
) -> Result<Lifted, ElabError> {
    let (params, bound) = ty.map_or_else(|| (Vec::new(), Vec::new()), telescope);
    let mut raised = Vec::new();
    let mut rewritten = Vec::with_capacity(clauses.len());
    let mut mutual = false;
    for clause in clauses {
        if clause.wheres.is_empty() {
            rewritten.push(clause.clone());
            continue;
        }
        let locals = grouped(&clause.wheres)?;
        // Параметры клаузы, написанные именем, - по позиции.
        let named: Vec<Option<&Name>> = clause
            .patterns
            .iter()
            .map(|pattern| match &pattern.kind {
                PatternKind::Name(name) if name.text.starts_with(char::is_lowercase) => Some(name),
                _ => None,
            })
            .collect();
        let needs = closure(&locals, &named);

        // Имена поднятых и то, чем их зовут.
        let mut calls: Vec<Option<(Name, Vec<Name>)>> = Vec::with_capacity(locals.len());
        for (index, local) in locals.iter().enumerate() {
            if !local.function() {
                calls.push(None);
                continue;
            }
            let mut text = format!("{}#{}", owner.text, local.name.text);
            while taken.contains(text.as_str()) {
                text.push('\'');
            }
            taken.insert(Symbol::from(text.as_str()));
            let lifted = Name {
                text: Symbol::from(text.as_str()),
                span: local.name.span,
            };
            let captured: Vec<Name> = named
                .iter()
                .flatten()
                .filter(|it| needs[index].contains(&it.text))
                .map(|it| (*it).clone())
                .collect();
            calls.push(Some((lifted, captured)));
        }

        for (index, local) in locals.iter().enumerate() {
            let Some((lifted, captured)) = &calls[index] else {
                continue;
            };
            let Some(signature) = &local.signature else {
                return Err(ElabError::LocalDefinition {
                    name: local.name.text.clone(),
                    why: "у функции нет сигнатуры, а поднятой на верхний уровень она нужна, \
                          как всякому определению"
                        .to_owned(),
                    span: local.name.span,
                });
            };
            let binders = captured_binders(owner, local, captured, &named, &params, &bound)?;
            let ty = if binders.is_empty() {
                signature.clone()
            } else {
                Expr {
                    span: signature.span,
                    kind: ExprKind::Pi {
                        binders,
                        codomain: Box::new(signature.clone()),
                    },
                }
            };
            mutual |= local.mentions(&owner.text)
                || locals.iter().enumerate().any(|(other, it)| {
                    other != index && it.function() && local.mentions(&it.name.text)
                });
            raised.extend(raised_decls(lifted, ty, local, captured, &locals, &calls));
        }

        rewritten.push(Clause {
            patterns: clause.patterns.clone(),
            body: prefixed(&clause.body, &locals, &calls),
            wheres: Vec::new(),
            span: clause.span,
        });
    }
    Ok(Lifted {
        raised,
        clauses: rewritten,
        mutual,
    })
}

/// Блок `where` по определениям: сигнатура и клаузы под одним именем.
fn grouped(wheres: &[Decl]) -> Result<Vec<Local>, ElabError> {
    let mut locals: Vec<Local> = Vec::new();
    for decl in wheres {
        match &decl.kind {
            DeclKind::Signature { name, ty, .. } => locals.push(Local {
                name: name.clone(),
                signature: Some(ty.clone()),
                clauses: Vec::new(),
            }),
            DeclKind::Clauses { name, clauses } => {
                match locals
                    .iter_mut()
                    .find(|it| it.name.text == name.text && it.clauses.is_empty())
                {
                    Some(local) => local.clauses.clone_from(clauses),
                    None => locals.push(Local {
                        name: name.clone(),
                        signature: None,
                        clauses: clauses.clone(),
                    }),
                }
            }
            _ => {
                return Err(ElabError::LocalDefinition {
                    name: Symbol::from("where"),
                    why: "в `where` пишутся только определения - сигнатуры и клаузы".to_owned(),
                    span: decl.span,
                });
            }
        }
    }
    for local in &locals {
        if local.clauses.is_empty() {
            return Err(ElabError::LocalDefinition {
                name: local.name.text.clone(),
                why: "у сигнатуры нет клауз".to_owned(),
                span: local.name.span,
            });
        }
        if !local.function() && (local.clauses.len() > 1 || !local.clauses[0].wheres.is_empty()) {
            return Err(ElabError::LocalDefinition {
                name: local.name.text.clone(),
                why: "значение без параметров пишется одной клаузой без своего `where`".to_owned(),
                span: local.name.span,
            });
        }
    }
    Ok(locals)
}

/// Какие параметры клаузы нужны каждому локальному определению - прямо или
/// через соседей, которых оно зовёт.
fn closure(locals: &[Local], named: &[Option<&Name>]) -> Vec<HashSet<Symbol>> {
    let mut needs: Vec<HashSet<Symbol>> = locals
        .iter()
        .map(|local| {
            named
                .iter()
                .flatten()
                .filter(|it| local.mentions(&it.text))
                .map(|it| it.text.clone())
                .collect()
        })
        .collect();
    loop {
        let mut grown = false;
        for index in 0..locals.len() {
            for (other, sibling) in locals.iter().enumerate() {
                if other == index || !locals[index].mentions(&sibling.name.text) {
                    continue;
                }
                let extra: Vec<Symbol> = needs[other]
                    .iter()
                    .filter(|it| !needs[index].contains(*it))
                    .cloned()
                    .collect();
                grown |= !extra.is_empty();
                needs[index].extend(extra);
            }
        }
        if !grown {
            return needs;
        }
    }
}

/// Тело с `let` в начале: по одному на каждое локальное определение, которое
/// оно называет, - прямо или через значение, которое называет.
///
/// Функции - частичным применением поднятого к захваченному, значения - своим
/// телом; функции идут первыми, потому что значение вправе их звать, а функция
/// значение берёт своим `let`.
fn prefixed(body: &Expr, locals: &[Local], calls: &[Option<(Name, Vec<Name>)>]) -> Expr {
    let mut wanted = vec![false; locals.len()];
    let mentioned = |expr: &Expr, name: &Symbol| uses(expr, &[name]);
    for (index, local) in locals.iter().enumerate() {
        wanted[index] = mentioned(body, &local.name.text);
    }
    // Значение тянет за собой то, что называет само.
    loop {
        let mut grown = false;
        for index in 0..locals.len() {
            if !wanted[index] || locals[index].function() {
                continue;
            }
            for (other, sibling) in locals.iter().enumerate() {
                if !wanted[other] && locals[index].mentions(&sibling.name.text) {
                    wanted[other] = true;
                    grown = true;
                }
            }
        }
        if !grown {
            break;
        }
    }
    let functions = locals.iter().enumerate().filter(|(_, it)| it.function());
    let values = locals.iter().enumerate().filter(|(_, it)| !it.function());
    let mut stmts: Vec<Stmt> = Vec::new();
    for (index, local) in functions.chain(values) {
        if !wanted[index] {
            continue;
        }
        let binding = match &calls[index] {
            Some((lifted, captured)) => {
                let head = Expr {
                    kind: ExprKind::Name(lifted.clone()),
                    span: local.name.span,
                };
                let applied = captured.iter().fold(head, |callee, argument| Expr {
                    span: local.name.span,
                    kind: ExprKind::App(
                        Box::new(callee),
                        Box::new(Expr {
                            kind: ExprKind::Name(argument.clone()),
                            span: local.name.span,
                        }),
                    ),
                });
                Binding {
                    mult: None,
                    name: local.name.clone(),
                    pattern: None,
                    params: Vec::new(),
                    ty: None,
                    body: applied,
                    span: local.name.span,
                }
            }
            None => Binding {
                mult: None,
                name: local.name.clone(),
                pattern: None,
                params: Vec::new(),
                ty: local.signature.clone(),
                body: local.clauses[0].body.clone(),
                span: local.name.span,
            },
        };
        stmts.push(Stmt {
            kind: StmtKind::Let(vec![binding]),
            span: local.name.span,
        });
    }
    if stmts.is_empty() {
        return body.clone();
    }
    let span = if let ExprKind::Block(block) = &body.kind {
        stmts.extend(block.stmts.iter().cloned());
        block.span
    } else {
        stmts.push(Stmt {
            kind: StmtKind::Expr(body.clone()),
            span: body.span,
        });
        body.span
    };
    Expr {
        kind: ExprKind::Block(Block { stmts, span }),
        span: body.span,
    }
}

/// Члены класса и инстанса: локальные определения метода поднимаются, а
/// поднятые встают перед самим объявлением - в теле класса места им нет.
///
/// Сигнатура метода есть у класса, а у инстанса её нет: тип пишет класс. Без
/// неё захватить параметр нечем, и такой захват - названный отказ.
fn class_members(
    members: &[Decl],
    errors: &mut Vec<ElabError>,
    taken: &mut HashSet<Symbol>,
) -> (Vec<Decl>, Vec<Decl>) {
    let mut kept: Vec<Decl> = Vec::with_capacity(members.len());
    let mut raised = Vec::new();
    for decl in members {
        let DeclKind::Clauses { name, clauses } = &decl.kind else {
            kept.push(decl.clone());
            continue;
        };
        if clauses.iter().all(|it| it.wheres.is_empty()) {
            kept.push(decl.clone());
            continue;
        }
        let signature = match kept.last() {
            Some(Decl {
                kind:
                    DeclKind::Signature {
                        name: written, ty, ..
                    },
                ..
            }) if written.text == name.text => Some(ty.clone()),
            _ => None,
        };
        match lift(name, signature.as_ref(), clauses, taken) {
            Ok(done) => {
                walk(&done.raised, true, &mut raised, errors, taken);
                kept.push(Decl {
                    kind: DeclKind::Clauses {
                        name: name.clone(),
                        clauses: done.clauses,
                    },
                    span: decl.span,
                });
            }
            Err(error) => errors.push(error),
        }
    }
    (kept, raised)
}

/// Связывания захваченных параметров в сигнатуре поднятого: имя - из клаузы,
/// тип и кратность - из сигнатуры владельца по позиции.
fn captured_binders(
    owner: &Name,
    local: &Local,
    captured: &[Name],
    named: &[Option<&Name>],
    params: &[Param],
    bound: &[Symbol],
) -> Result<Vec<Binder>, ElabError> {
    let refused = |why: String| ElabError::LocalDefinition {
        name: local.name.text.clone(),
        why,
        span: local.name.span,
    };
    let others: Vec<&Symbol> = bound.iter().collect();
    let mut binders = Vec::with_capacity(captured.len());
    for name in captured {
        let position = named
            .iter()
            .position(|it| it.is_some_and(|it| it.text == name.text))
            .unwrap_or(usize::MAX);
        let Some(Param {
            mult,
            ty: Some(param),
        }) = params.get(position)
        else {
            return Err(refused(format!(
                "захватывает `{}`, а у этой позиции нет типа в сигнатуре `{}`",
                name.text, owner.text
            )));
        };
        if uses(param, &others) {
            return Err(refused(format!(
                "захватывает `{}`, чей тип зависит от другого параметра; передайте его \
                 аргументом",
                name.text
            )));
        }
        binders.push(Binder {
            visibility: Visibility::Explicit,
            mult: *mult,
            names: vec![name.clone()],
            factors: Vec::new(),
            grade: None,
            ty: Some(param.clone()),
            default: None,
            span: name.span,
        });
    }
    Ok(binders)
}

/// Сигнатура и клаузы поднятого: захваченные параметры - первыми паттернами.
fn raised_decls(
    lifted: &Name,
    ty: Expr,
    local: &Local,
    captured: &[Name],
    locals: &[Local],
    calls: &[Option<(Name, Vec<Name>)>],
) -> [Decl; 2] {
    let clauses = local
        .clauses
        .iter()
        .map(|inner| Clause {
            patterns: captured
                .iter()
                .map(|it| Pattern {
                    kind: PatternKind::Name(it.clone()),
                    span: it.span,
                })
                .chain(inner.patterns.iter().cloned())
                .collect(),
            body: prefixed(&inner.body, locals, calls),
            wheres: inner.wheres.clone(),
            span: inner.span,
        })
        .collect();
    [
        Decl {
            kind: DeclKind::Signature {
                name: lifted.clone(),
                ty,
                attributes: Vec::new(),
            },
            span: local.name.span,
        },
        Decl {
            kind: DeclKind::Clauses {
                name: lifted.clone(),
                clauses,
            },
            span: local.name.span,
        },
    ]
}
