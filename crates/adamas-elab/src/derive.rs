//! Вывод инстансов: `deriving (Eq, Ord, Show)` последней строкой блока `data`
//! (§4.6).
//!
//! Вывод - **синтаксическое** раскрытие, как и обещанный §4.6 макрос: за
//! объявлением семейства встаёт обычное объявление инстанса, собранное из
//! дерева конструкторов, и дальше оно идёт той же элаборацией и той же
//! проверкой, что написанное руками. Макросов в языке пока нет, поэтому
//! выводимы три класса, а не «всякий, у которого есть `derive_X`»; переезд на
//! макросы автора не заденет - написанное им не меняется.
//!
//! # Имена - квалифицированные
//!
//! Тело инстанса ссылается на прелюдию **полными** именами (`Prelude.eq`,
//! `Prelude.True`) и ветвится `case`, а не `if`: программа вправе объявить
//! свою `Bool` (так делает `eval/zlib`), и голое `True` либо `if` по
//! соглашению о `Bool` связались бы с ней. Голова инстанса пишет класс так,
//! как его написал автор в `deriving`: квалифицированное имя класса голова не
//! принимает.
//!
//! # Чего не выводится
//!
//! Семейство с индексами (конструктор отвечает не `T a b`), стёртое поле и
//! семейство внутри `mutual` - отказ с названной причиной, а не догадка.
//! Поле, у типа которого инстанса нет, отвергается обычной проверкой
//! порождённого инстанса: «инстанс `Eq (UInt64 -> UInt64)` не найден».

use std::rc::Rc;

use adamas_core::source::Span;
use adamas_parser::ast::{
    Alt, Binder, ClassDecl, Clause, Data, Decl, DeclKind, Expr, ExprKind, Lit, LitKind, Mult, Name,
    Pattern, PatternKind, Visibility,
};

use crate::error::ElabError;

/// Объявления с раскрытым `deriving`. `None` - раскрывать нечего, и копия не
/// нужна: подавляющее большинство файлов `deriving` не пишет.
pub(crate) fn expanded(decls: &[Decl]) -> Option<(Vec<Decl>, Vec<ElabError>)> {
    if !decls.iter().any(derives) {
        return None;
    }
    let mut out = Vec::with_capacity(decls.len());
    let mut failed = Vec::new();
    for decl in decls {
        out.push(decl.clone());
        match &decl.kind {
            DeclKind::Data(data) => {
                for class in &data.deriving {
                    match instance(data, class) {
                        Ok(derived) => out.push(derived),
                        Err(error) => failed.push(error),
                    }
                }
            }
            DeclKind::Mutual(members) => {
                for member in members {
                    if let DeclKind::Data(data) = &member.kind {
                        for class in &data.deriving {
                            failed.push(refusal(class, adamas_l10n::text!("derive-mutual")));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Some((out, failed))
}

/// Пишет ли объявление `deriving` - своё или у члена `mutual`.
fn derives(decl: &Decl) -> bool {
    match &decl.kind {
        DeclKind::Data(data) => !data.deriving.is_empty(),
        DeclKind::Mutual(members) => members.iter().any(derives),
        _ => false,
    }
}

fn refusal(class: &Name, why: &'static str) -> ElabError {
    ElabError::Deriving {
        class: Rc::clone(&class.text),
        why,
        span: class.span,
    }
}

/// Конструктор, каким его видит вывод: имя и число явных полей.
struct Shape {
    name: Name,
    fields: usize,
}

/// Инстанс класса `class` для семейства `data`.
fn instance(data: &Data, class: &Name) -> Result<Decl, ElabError> {
    let method = match &*class.text {
        "Eq" => "eq",
        "Ord" => "compare",
        "Show" => "show",
        _ => return Err(refusal(class, adamas_l10n::text!("derive-class"))),
    };
    if data.kind.is_some() {
        return Err(refusal(class, adamas_l10n::text!("derive-indexed")));
    }
    let params: Vec<&Name> = data
        .params
        .iter()
        .flat_map(|binder| binder.names.iter())
        .collect();
    let shapes = data
        .constructors
        .iter()
        .map(|constructor| shape(data, &params, class, &constructor.name, &constructor.ty))
        .collect::<Result<Vec<_>, _>>()?;
    let at = Builder { span: class.span };
    let clauses = match method {
        "eq" => at.equality(&shapes),
        "compare" => at.ordering(&shapes),
        _ => at.showing(&shapes),
    };
    // Голова: класс над семейством, применённым к своим параметрам, и
    // констрейнт того же класса на каждом типовом параметре (§4.6).
    let applied = params.iter().fold(at.var(&data.name.text), |head, param| {
        at.app(head, at.var(&param.text))
    });
    let goal = at.app(at.var(&class.text), applied);
    let constraints: Vec<Binder> = data
        .params
        .iter()
        .filter(|binder| typal(binder))
        .flat_map(|binder| binder.names.iter())
        .map(|param| Binder {
            visibility: Visibility::Implicit,
            mult: None,
            names: vec![at.name("_")],
            factors: Vec::new(),
            grade: None,
            ty: Some(at.app(at.var(&class.text), at.var(&param.text))),
            default: None,
            span: class.span,
        })
        .collect();
    let head = if constraints.is_empty() {
        goal
    } else {
        at.expr(ExprKind::Pi {
            binders: constraints,
            codomain: Box::new(goal),
        })
    };
    Ok(Decl {
        kind: DeclKind::Class(ClassDecl {
            coherent: false,
            instance: true,
            name: None,
            head,
            params: Vec::new(),
            superclasses: Vec::new(),
            members: vec![Decl {
                kind: DeclKind::Clauses {
                    name: at.name(method),
                    clauses,
                },
                span: class.span,
            }],
        }),
        span: class.span,
    })
}

/// Типовый ли параметр: без аннотации либо `Type`. Параметр другого сорта
/// (`n : Nat`) в констрейнты не идёт (§4.6).
fn typal(binder: &Binder) -> bool {
    match &binder.ty {
        None => true,
        Some(ty) => matches!(&ty.kind, ExprKind::Name(name) if &*name.text == "Type"),
    }
}

/// Явные поля конструктора и проверка, что отвечает он самим семейством.
fn shape(
    data: &Data,
    params: &[&Name],
    class: &Name,
    name: &Name,
    ty: &Expr,
) -> Result<Shape, ElabError> {
    let mut fields = 0;
    let mut current = ty;
    loop {
        match &current.kind {
            ExprKind::Arrow(_, codomain) => {
                fields += 1;
                current = codomain;
            }
            ExprKind::Pi { binders, codomain } => {
                for binder in binders {
                    if binder.visibility != Visibility::Explicit {
                        continue;
                    }
                    if binder.mult.is_some_and(|it| it.mult == Mult::Zero) {
                        return Err(refusal(class, adamas_l10n::text!("derive-erased")));
                    }
                    fields += binder.names.len();
                }
                current = codomain;
            }
            _ => break,
        }
    }
    // Ответ - само семейство над своими параметрами по порядку: `T a b`.
    let mut arguments = Vec::new();
    let mut head = current;
    while let ExprKind::App(callee, argument) = &head.kind {
        arguments.push(argument);
        head = callee;
    }
    arguments.reverse();
    let plain = matches!(&head.kind, ExprKind::Name(it) if it.text == data.name.text)
        && arguments.len() == params.len()
        && arguments.iter().zip(params).all(
            |(argument, param)| matches!(&argument.kind, ExprKind::Name(it) if it.text == param.text),
        );
    if !plain {
        return Err(refusal(class, adamas_l10n::text!("derive-indexed")));
    }
    Ok(Shape {
        name: name.clone(),
        fields,
    })
}

/// Сборщик узлов дерева: всё порождённое стоит на спане класса в `deriving`
/// - туда и укажет отказ проверки.
struct Builder {
    span: Span,
}

impl Builder {
    fn name(&self, text: &str) -> Name {
        Name {
            text: Rc::from(text),
            span: self.span,
        }
    }

    fn expr(&self, kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: self.span,
        }
    }

    fn var(&self, text: &str) -> Expr {
        self.expr(ExprKind::Name(self.name(text)))
    }

    fn app(&self, callee: Expr, argument: Expr) -> Expr {
        self.expr(ExprKind::App(Box::new(callee), Box::new(argument)))
    }

    fn call(&self, function: &str, arguments: Vec<Expr>) -> Expr {
        arguments
            .into_iter()
            .fold(self.var(function), |callee, argument| {
                self.app(callee, argument)
            })
    }

    fn text(&self, content: &str) -> Expr {
        self.expr(ExprKind::Lit(Lit {
            kind: LitKind::Str,
            text: Rc::from(format!("\"{content}\"").as_str()),
            span: self.span,
        }))
    }

    fn pattern(&self, kind: PatternKind) -> Pattern {
        Pattern {
            kind,
            span: self.span,
        }
    }

    /// `C x1 … xn` либо `C _ … _`.
    fn constructed(&self, shape: &Shape, prefix: Option<&str>) -> Pattern {
        let fields = (0..shape.fields)
            .map(|at| match prefix {
                Some(prefix) => {
                    self.pattern(PatternKind::Name(self.name(&format!("{prefix}{at}"))))
                }
                None => self.pattern(PatternKind::Wildcard),
            })
            .collect();
        self.pattern(PatternKind::App {
            head: shape.name.clone(),
            fields,
        })
    }

    fn constant(&self, text: &str) -> Pattern {
        self.pattern(PatternKind::App {
            head: self.name(text),
            fields: Vec::new(),
        })
    }

    fn case(&self, scrutinee: Expr, alts: Vec<(Pattern, Expr)>) -> Expr {
        self.expr(ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            alts: alts
                .into_iter()
                .map(|(pattern, body)| Alt {
                    pattern,
                    body,
                    span: self.span,
                })
                .collect(),
        })
    }

    fn clause(&self, patterns: Vec<Pattern>, body: Expr) -> Clause {
        Clause {
            patterns,
            body,
            wheres: Vec::new(),
            span: self.span,
        }
    }

    /// `eq`: равны одноимённые конструкторы с попарно равными полями.
    fn equality(&self, shapes: &[Shape]) -> Vec<Clause> {
        let mut clauses: Vec<Clause> = shapes
            .iter()
            .map(|shape| {
                let body = (0..shape.fields)
                    .rev()
                    .fold(self.var("Prelude.True"), |rest, at| {
                        self.case(
                            self.call(
                                "Prelude.eq",
                                vec![self.var(&format!("x{at}")), self.var(&format!("y{at}"))],
                            ),
                            vec![
                                (self.constant("Prelude.True"), rest),
                                (self.constant("Prelude.False"), self.var("Prelude.False")),
                            ],
                        )
                    });
                self.clause(
                    vec![
                        self.constructed(shape, Some("x")),
                        self.constructed(shape, Some("y")),
                    ],
                    body,
                )
            })
            .collect();
        if shapes.len() > 1 {
            clauses.push(self.clause(
                vec![
                    self.pattern(PatternKind::Wildcard),
                    self.pattern(PatternKind::Wildcard),
                ],
                self.var("Prelude.False"),
            ));
        }
        clauses
    }

    /// `compare`: сперва порядок конструкторов в объявлении, затем поля
    /// лексикографически - как у Haskell.
    fn ordering(&self, shapes: &[Shape]) -> Vec<Clause> {
        let mut clauses: Vec<Clause> = shapes
            .iter()
            .map(|shape| {
                let body = (0..shape.fields)
                    .rev()
                    .fold(self.var("Prelude.EQ"), |rest, at| {
                        self.case(
                            self.call(
                                "Prelude.compare",
                                vec![self.var(&format!("x{at}")), self.var(&format!("y{at}"))],
                            ),
                            vec![
                                (self.constant("Prelude.EQ"), rest),
                                (
                                    self.pattern(PatternKind::Name(self.name("order"))),
                                    self.var("order"),
                                ),
                            ],
                        )
                    });
                self.clause(
                    vec![
                        self.constructed(shape, Some("x")),
                        self.constructed(shape, Some("y")),
                    ],
                    body,
                )
            })
            .collect();
        for (left, first) in shapes.iter().enumerate() {
            for (right, second) in shapes.iter().enumerate() {
                if left == right {
                    continue;
                }
                let answer = if left < right {
                    "Prelude.LT"
                } else {
                    "Prelude.GT"
                };
                clauses.push(self.clause(
                    vec![
                        self.constructed(first, None),
                        self.constructed(second, None),
                    ],
                    self.var(answer),
                ));
            }
        }
        clauses
    }

    /// `show`: имя конструктора и поля через пробел, составное поле - в
    /// скобках (`Prelude.showArg`), как печатает `adamas eval`.
    fn showing(&self, shapes: &[Shape]) -> Vec<Clause> {
        shapes
            .iter()
            .map(|shape| {
                let mut parts = vec![self.text(&shape.name.text)];
                for at in 0..shape.fields {
                    parts.push(self.text(" "));
                    parts.push(self.call("Prelude.showArg", vec![self.var(&format!("x{at}"))]));
                }
                let body = parts
                    .into_iter()
                    .rev()
                    .reduce(|rest, part| self.call("Prelude.combine", vec![part, rest]))
                    .unwrap_or_else(|| self.text(""));
                self.clause(vec![self.constructed(shape, Some("x"))], body)
            })
            .collect()
    }
}
