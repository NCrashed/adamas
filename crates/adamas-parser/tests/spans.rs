//! Спаны дерева: два свойства на любом разобранном файле.
//!
//! Спан узла начинается на первой его лексеме и кончается на последней
//! (заголовок [`adamas_parser::parser`], «Спаны»). Отсюда проверяемое: спан
//! ребёнка лежит внутри спана родителя, и ни один спан не начинается и не
//! кончается пробелом.
//!
//! Два свойства ловят два разных класса ошибок, и каждый уже случался. Узел,
//! забывший часть своего текста, - клауза без блока `where`: её спан
//! перестаёт вмещать спаны локальных определений. Узел, прихвативший чужой, -
//! объявление, кончающееся виртуальной границей блока: та стоит в позиции
//! токена, который блок закрыл, то есть следующего объявления, и вложенность
//! этого не замечает - замечает пробел на конце.

use adamas_core::source::Span;
use adamas_parser::ast::{
    Binder, Binding, Block, Clause, Data, Decl, DeclKind, Expr, ExprKind, LamParamKind, Module,
    Name, Pattern, PatternKind, Resource, Stmt, StmtKind,
};
use adamas_parser::parse;
use proptest::prelude::*;

/// Обход дерева, собирающий все расхождения: разбирать один тест приятнее по
/// полному списку, чем по первому попавшемуся.
struct Spans<'a> {
    text: &'a str,
    problems: Vec<String>,
}

impl Spans<'_> {
    /// Проверяет оба свойства разом. Через неё проходит спан каждого узла -
    /// ровно один раз, в роли `inner`.
    fn inside(&mut self, what: &str, outer: Span, inner: Span) {
        if inner.start() < outer.start() || inner.end() > outer.end() {
            self.problems
                .push(format!("{what} {inner:?} не внутри {outer:?}"));
        }
        let Some(written) = self.text.get(inner.start()..inner.end()) else {
            self.problems
                .push(format!("{what} {inner:?} режет текст не по границам"));
            return;
        };
        if written.trim() != written {
            self.problems
                .push(format!("{what} {inner:?} прихватил пробел: {written:?}"));
        }
    }

    fn module(&mut self, file: Span, module: &Module) {
        self.inside("модуль", file, module.span);
        for decl in &module.decls {
            self.decl(module.span, decl);
        }
    }

    fn decl(&mut self, parent: Span, decl: &Decl) {
        self.inside("объявление", parent, decl.span);
        let at = decl.span;
        match &decl.kind {
            DeclKind::Alias { name, body } => {
                self.name(at, name);
                self.expr(at, body);
            }
            DeclKind::Signature { name, ty } => {
                self.name(at, name);
                self.expr(at, ty);
            }
            DeclKind::Clauses { name, clauses } => {
                self.name(at, name);
                for clause in clauses {
                    self.clause(at, clause);
                }
            }
            DeclKind::Data(data) => self.data(at, data),
            DeclKind::Resource(resource) => self.resource(at, resource),
        }
    }

    fn data(&mut self, at: Span, data: &Data) {
        self.name(at, &data.name);
        for param in &data.params {
            self.binder(at, param);
        }
        if let Some(kind) = &data.kind {
            self.expr(at, kind);
        }
        for constructor in &data.constructors {
            self.inside("конструктор", at, constructor.span);
            self.name(constructor.span, &constructor.name);
            self.expr(constructor.span, &constructor.ty);
        }
    }

    fn resource(&mut self, at: Span, resource: &Resource) {
        self.name(at, &resource.name);
        for param in &resource.params {
            self.binder(at, param);
        }
        for member in &resource.members {
            self.decl(at, member);
        }
    }

    fn clause(&mut self, parent: Span, clause: &Clause) {
        self.inside("клауза", parent, clause.span);
        let at = clause.span;
        for pattern in &clause.patterns {
            self.pattern(at, pattern);
        }
        self.expr(at, &clause.body);
        for local in &clause.wheres {
            self.decl(at, local);
        }
    }

    fn binder(&mut self, parent: Span, binder: &Binder) {
        self.inside("связывание", parent, binder.span);
        let at = binder.span;
        if let Some(mult) = binder.mult {
            self.inside("кратность", at, mult.span);
        }
        for name in &binder.names {
            self.name(at, name);
        }
        if let Some(ty) = &binder.ty {
            self.expr(at, ty);
        }
    }

    fn expr(&mut self, parent: Span, expr: &Expr) {
        self.inside("выражение", parent, expr.span);
        let at = expr.span;
        match &expr.kind {
            ExprKind::Name(name) => self.name(at, name),
            ExprKind::Lit(lit) => self.inside("литерал", at, lit.span),
            ExprKind::Hole => {}
            ExprKind::RecordType(fields) => {
                for field in fields {
                    self.name(at, &field.name);
                    self.expr(at, &field.ty);
                }
            }
            ExprKind::Record(fields) => {
                for (name, value) in fields {
                    self.name(at, name);
                    self.expr(at, value);
                }
            }
            ExprKind::Update(base, fields) => {
                self.expr(at, base);
                for (name, value) in fields {
                    self.name(at, name);
                    self.expr(at, value);
                }
            }
            ExprKind::Project(record, name) => {
                self.expr(at, record);
                self.name(at, name);
            }
            ExprKind::App(left, right)
            | ExprKind::TypeApp(left, right)
            | ExprKind::Arrow(left, right) => {
                self.expr(at, left);
                self.expr(at, right);
            }
            ExprKind::Lam { params, body } => {
                for param in params {
                    self.inside("параметр", at, param.span);
                    match &param.kind {
                        LamParamKind::Pattern(pattern) => self.pattern(param.span, pattern),
                        LamParamKind::Binder(binder) => self.binder(param.span, binder),
                    }
                }
                self.expr(at, body);
            }
            ExprKind::Pi { binders, codomain } => {
                for binder in binders {
                    self.binder(at, binder);
                }
                self.expr(at, codomain);
            }
            ExprKind::Block(block) => self.block(at, block),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr(at, cond);
                self.expr(at, then_branch);
                self.expr(at, else_branch);
            }
            ExprKind::Case { scrutinee, alts } => {
                self.expr(at, scrutinee);
                for alt in alts {
                    self.inside("ветка", at, alt.span);
                    self.pattern(alt.span, &alt.pattern);
                    self.expr(alt.span, &alt.body);
                }
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                for item in items {
                    self.expr(at, item);
                }
            }
            ExprKind::Chain(chain) => {
                self.expr(at, &chain.head);
                for (operator, operand) in &chain.tail {
                    self.name(at, operator);
                    self.expr(at, operand);
                }
            }
        }
    }

    fn block(&mut self, parent: Span, block: &Block) {
        self.inside("блок", parent, block.span);
        for stmt in &block.stmts {
            self.stmt(block.span, stmt);
        }
    }

    fn stmt(&mut self, parent: Span, stmt: &Stmt) {
        self.inside("оператор", parent, stmt.span);
        match &stmt.kind {
            StmtKind::Let(bindings) => {
                for binding in bindings {
                    self.binding(stmt.span, binding);
                }
            }
            StmtKind::Expr(expr) => self.expr(stmt.span, expr),
        }
    }

    fn binding(&mut self, parent: Span, binding: &Binding) {
        self.inside("связывание `let`", parent, binding.span);
        let at = binding.span;
        if let Some(mult) = binding.mult {
            self.inside("кратность", at, mult.span);
        }
        self.name(at, &binding.name);
        for param in &binding.params {
            self.pattern(at, param);
        }
        if let Some(ty) = &binding.ty {
            self.expr(at, ty);
        }
        self.expr(at, &binding.body);
    }

    fn pattern(&mut self, parent: Span, pattern: &Pattern) {
        self.inside("паттерн", parent, pattern.span);
        let at = pattern.span;
        match &pattern.kind {
            PatternKind::Name(name) => self.name(at, name),
            PatternKind::Wildcard => {}
            PatternKind::Lit(lit) => self.inside("литерал", at, lit.span),
            PatternKind::App { head, fields } => {
                self.name(at, head);
                for field in fields {
                    self.pattern(at, field);
                }
            }
            PatternKind::Tuple(items) => {
                for item in items {
                    self.pattern(at, item);
                }
            }
        }
    }

    fn name(&mut self, parent: Span, name: &Name) {
        self.inside("имя", parent, name.span);
    }
}

/// Расхождения на этом тексте; пустой список - свойство держится. Текст, не
/// разобравшийся вовсе, расхождений не даёт: проверять нечего.
fn problems(text: &str) -> Vec<String> {
    let Ok(module) = parse(text) else {
        return Vec::new();
    };
    let mut spans = Spans {
        text,
        problems: Vec::new(),
    };
    spans.module(Span::new(0, text.len()), &module);
    spans.problems
}

/// Формы, у каждой из которых свой способ посчитать спан.
const FORMS: &[&str] = &[
    "map : (a -> b) -> Vect n a -> Vect n b\nmap f Nil = Nil\nmap f (Cons x xs) = Cons (f x) xs\n",
    "data Vect : (0 n : Nat) -> Type -> Type where\n  Nil  : Vect 0 a\n  Cons : a -> Vect n a\n",
    "data Void : Type\nf = 1\n",
    "resource File where\n  drop h = closeFile h\n\nf = 1\n",
    "f x = y\n  where\n    y = g x\n",
    "f x =\n  y\n  where\n    z = 1\n",
    "counter =\n  let n = get\n  put (n + 1)\n  n\n",
    "f x = case x of\n  Cons y ys -> y\n  Nil       -> zero\n",
    "f = \\(0 a : Type) x -> x\ng = \\() -> get\n",
    "f = g (-42)\nh = x - 42\nk = a + b * c\n",
    "f = (a, b, c)\ng = [1, 2, 3]\nh = ((a))\n",
];

#[test]
fn spans_of_every_form_nest() {
    for text in FORMS {
        assert_eq!(problems(text), Vec::<String>::new(), "на {text:?}");
    }
}

proptest! {
    /// То же свойство на всём, что вообще разбирается.
    #[test]
    fn spans_of_a_parsed_tree_nest(text in r"[a-z=(){}\[\]:,\n ]{0,120}") {
        let found = problems(&text);
        prop_assert!(found.is_empty(), "{found:?}");
    }
}
