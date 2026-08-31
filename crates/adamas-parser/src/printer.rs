//! Обратная печать: дерево -> исходник, который снова разбирается (§9 Фаза 2).
//!
//! Не путать с [`crate::ast::dump`]: тот показывает форму дерева s-выражениями
//! и в язык не целится, этот обязан выдать текст, который разберётся обратно в
//! то же дерево.
//!
//! # Печать каноническая
//!
//! Авторское форматирование не сохраняется - решение записано в decision log
//! 2026-08-25 вместе с выбором AST против lossless CST. Отсюда договор, который
//! проверяется тестами: **`parse(print(m))` даёт `m` с точностью до спанов**, и
//! `print` идемпотентна. Не сохраняются: переносы строк, выравнивание пробелами,
//! лишние скобки. Сохраняется всё, что несёт дерево, включая написание литерала
//! (`0xff` не превращается в `255`).
//!
//! Комментариев печать не выводит: их в дереве нет, они лежат отдельной
//! таблицей ([`crate::token::Comment`]). `adamas fmt` (§7.1) обязан их
//! сохранять, и таблица заведена ровно для этого, но привязка комментария к
//! узлу - отдельная работа, а round-trip дерева от неё не зависит. Переносов
//! строк печать тоже не делает: длинное применение печатается одной строкой.
//!
//! # Что печать предполагает о дереве
//!
//! Договор держится на деревьях, которые даёт [`crate::parse`]. У собранного
//! руками дерева исходника может не быть вовсе: пустой список веток у `case`,
//! пустой блок операторов, лямбда без параметров записываются в языке ничем,
//! и печать выдаст для них текст, который обратно не разберётся. Проверок на
//! это нет намеренно - они защищали бы от того, чего разбор не строит.
//!
//! # Скобки
//!
//! Ставятся по приоритетам (`Prec`), а не по тому, где они стояли в
//! исходнике: узла у скобок нет. Форма с блоком - исключение: в скобки её не
//! взять, под скобкой layout выключен (§10 вопрос 55). Скобки ей и не нужны:
//! разбор пропускает её только туда, где за ней на строке ничего не стоит
//! (§4.1, [`crate::ast::contains_block`]), а там приоритет позиции ей не
//! грозит.
//!
//! # Отступы
//!
//! Шаг - два пробела; связывания `let` выравниваются по первому, то есть на
//! ширину самого `let`. Тело определения печатается блоком **тогда и только
//! тогда**, когда блоком его несёт дерево: `f = e` и `f =` с телом-блоком из
//! одного оператора - разные деревья, и печать обязана их различать.
//!
//! Два решения принимаются по **напечатанному**, а не по форме дерева:
//! отступ `where` (тело заняло больше строки - `where` встаёт на колонку
//! определения) и пустая строка между объявлениями (ставится, если хотя бы
//! одно из соседних заняло больше строки). Предсказывать форму вывода по
//! дереву значило бы держать второй экземпляр логики печати рядом с первым.

use crate::ast::{
    Alt, Binder, Binding, Block, Chain, Clause, Constructor, Data, Decl, DeclKind, Expr, ExprKind,
    LamParam, LamParamKind, Lit, Module, ModuleDecl, Name, Pattern, PatternKind, Resource, Stmt,
    StmtKind, Visibility, contains_block,
};
use crate::lexer::is_operator;

/// Шаг отступа.
const STEP: usize = 2;

/// Ширина `let ` - на неё выравниваются связывания второго и дальше.
const LET_WIDTH: usize = 4;

/// Приоритет позиции: узел слабее её - берётся в скобки.
///
/// Уровни повторяют слои спуска ([`crate::parser`]): выражение, цепочка
/// операторов, применение, атом.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    /// Всё, что тянется вправо до упора: стрелка, лямбда, `if`, `case`, блок.
    Lowest,
    /// Цепочка операторов.
    Chain,
    /// Применение.
    App,
    /// Атом: имя, литерал, дырка, кортеж, список.
    Atom,
}

impl Expr {
    /// Насколько крепко узел держится без скобок.
    fn prec(&self) -> Prec {
        match self.kind {
            ExprKind::Name(_)
            | ExprKind::Lit(_)
            | ExprKind::Hole
            | ExprKind::Tuple(_)
            | ExprKind::RecordType(..)
            | ExprKind::Record(_)
            | ExprKind::Project(..)
            | ExprKind::Update(..)
            | ExprKind::List(_) => Prec::Atom,
            ExprKind::App(..) | ExprKind::TypeApp(..) => Prec::App,
            ExprKind::Chain(_) => Prec::Chain,
            ExprKind::Lam { .. }
            | ExprKind::Using { .. }
            | ExprKind::Pi { .. }
            | ExprKind::Arrow(..)
            | ExprKind::Block(_)
            | ExprKind::If { .. }
            | ExprKind::Case { .. } => Prec::Lowest,
        }
    }
}

/// Печатает файл. Результат кончается переводом строки; пустой файл даёт
/// пустую строку.
#[must_use]
pub fn print(module: &Module) -> String {
    let mut printer = Printer {
        out: String::new(),
        indent: 0,
    };
    printer.module(module);
    printer.out
}

/// Состояние печати: текст и отступ текущей строки.
struct Printer {
    out: String,
    indent: usize,
}

impl Printer {
    fn push(&mut self, text: &str) {
        self.out.push_str(text);
    }

    /// Начинает новую строку с текущим отступом.
    fn line(&mut self) {
        if !self.out.is_empty() {
            self.out.push('\n');
        }
        for _ in 0..self.indent {
            self.out.push(' ');
        }
    }

    /// Печатает то, что идёт глубже на `step`.
    fn nested(&mut self, step: usize, body: impl FnOnce(&mut Self)) {
        self.indent += step;
        body(self);
        self.indent -= step;
    }

    // --- объявления ------------------------------------------------------

    fn module(&mut self, module: &Module) {
        let mut previous_is_tall = false;
        for (index, decl) in module.decls.iter().enumerate() {
            let text = rendered(decl);
            let tall = text.contains('\n');
            if index > 0 {
                self.out.push('\n');
                // Пустая строка - когда хотя бы одно из соседних объявлений
                // заняло больше строки: список коротких определений остаётся
                // списком. Сигнатуру от её клауз не отделяем и тогда: они об
                // одном.
                if (tall || previous_is_tall) && !attached(&module.decls[index - 1], decl) {
                    self.out.push('\n');
                }
            }
            self.out.push_str(&text);
            previous_is_tall = tall;
        }
        if !self.out.is_empty() {
            self.out.push('\n');
        }
    }

    /// Блок членов под ключевым словом, каждый со своей строки.
    fn block_of<T>(&mut self, items: &[T], mut each: impl FnMut(&mut Self, &T)) {
        self.nested(STEP, |printer| {
            for item in items {
                printer.line();
                each(printer, item);
            }
        });
    }

    fn decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Alias { name, params, body } => {
                self.push("type ");
                self.push(&name.text);
                for param in params {
                    self.push(" ");
                    self.binder(param);
                }
                if let Some(body) = body {
                    self.push(" = ");
                    self.expr(body, Prec::Lowest);
                }
            }
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                for attribute in attributes {
                    self.push("@");
                    self.push(&attribute.text);
                    self.line();
                }
                self.decl_name(name);
                self.push(" : ");
                self.expr(ty, Prec::Lowest);
            }
            DeclKind::Clauses { name, clauses } => {
                for (index, clause) in clauses.iter().enumerate() {
                    if index > 0 {
                        self.line();
                    }
                    self.clause(name, clause);
                }
            }
            DeclKind::Data(data) => self.data(data),
            DeclKind::Module(module) => self.module_decl(module),
            DeclKind::Mutual(members) => {
                self.push("mutual");
                self.block_of(members, Self::decl);
            }
            DeclKind::Class(class) => {
                if class.coherent {
                    self.push("coherent ");
                }
                self.push(if class.instance {
                    "instance "
                } else {
                    "class "
                });
                if let Some(name) = &class.name {
                    self.decl_name(name);
                    self.push(" : ");
                }
                self.expr(&class.head, Prec::Lowest);
                for (index, superclass) in class.superclasses.iter().enumerate() {
                    self.push(if index == 0 { " when " } else { ", " });
                    self.expr(superclass, Prec::Lowest);
                }
                self.push(" where");
                self.block_of(&class.members, Self::decl);
            }
            DeclKind::Resource(resource) => self.resource(resource),
        }
    }

    fn clause(&mut self, name: &Name, clause: &Clause) {
        self.decl_name(name);
        for pattern in &clause.patterns {
            self.push(" ");
            self.pattern(pattern, true);
        }
        self.push(" =");
        let body = self.out.len();
        self.body(&clause.body);
        if clause.wheres.is_empty() {
            return;
        }
        // Однострочное тело - `where` на шаг вглубь, его члены ещё на шаг.
        // Тело, занявшее больше строки, кончается открытым блоком - веток или
        // операторов, - и `where` с отступом попал бы внутрь: блок веток
        // закрывает только офсайд. На колонке определения `where` закрывает
        // всё открытое и присоединяется к клаузе (§4.1 правило 2).
        let step = if self.out[body..].contains('\n') {
            0
        } else {
            STEP
        };
        self.nested(step, |printer| {
            printer.line();
            printer.push("where");
            printer.block_of(&clause.wheres, Self::decl);
        });
    }

    fn module_decl(&mut self, module: &ModuleDecl) {
        self.push(if module.signature {
            "module type "
        } else {
            "module "
        });
        self.decl_name(&module.name);
        for param in &module.params {
            self.push(" ");
            self.binder(param);
        }
        if let Some(ascription) = &module.ascription {
            self.push(if module.sealed { " :> " } else { " : " });
            self.expr(ascription, Prec::Lowest);
        }
        if let Some(body) = &module.body {
            self.push(" = ");
            self.expr(body, Prec::Lowest);
            return;
        }
        self.push(" where");
        self.block_of(&module.members, Self::decl);
    }

    fn data(&mut self, data: &Data) {
        if data.unique {
            self.push("unique ");
        }
        self.push("data ");
        self.decl_name(&data.name);
        for param in &data.params {
            self.push(" ");
            self.binder(param);
        }
        if let Some(kind) = &data.kind {
            self.push(" : ");
            self.expr(kind, Prec::Lowest);
        }
        // Без конструкторов `where` не пишется: пустого блока layout не делает,
        // а семейство без конструкторов - законный пустой тип.
        if !data.constructors.is_empty() {
            self.push(" where");
            self.block_of(&data.constructors, Self::constructor);
        }
    }

    fn constructor(&mut self, constructor: &Constructor) {
        self.decl_name(&constructor.name);
        self.push(" : ");
        self.expr(&constructor.ty, Prec::Lowest);
    }

    fn resource(&mut self, resource: &Resource) {
        self.push("resource ");
        self.decl_name(&resource.name);
        for param in &resource.params {
            self.push(" ");
            self.binder(param);
        }
        self.push(" where");
        self.block_of(&resource.members, Self::decl);
    }

    /// Имя в позиции объявления: оператор пишется в скобках (§4.4).
    fn decl_name(&mut self, name: &Name) {
        if is_operator(&name.text) {
            self.push("(");
            self.push(&name.text);
            self.push(")");
        } else {
            self.push(&name.text);
        }
    }

    // --- тела и операторы -------------------------------------------------

    /// Тело после `=`. Блоком печатается ровно тогда, когда блок несёт дерево.
    fn body(&mut self, expr: &Expr) {
        if let ExprKind::Block(block) = &expr.kind {
            self.block_of(&block.stmts, Self::stmt);
        } else {
            self.push(" ");
            self.expr(expr, Prec::Lowest);
        }
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let(bindings) => {
                self.push("let ");
                self.nested(LET_WIDTH, |printer| {
                    for (index, binding) in bindings.iter().enumerate() {
                        if index > 0 {
                            printer.line();
                        }
                        printer.binding(binding);
                    }
                });
            }
            StmtKind::Expr(expr) => self.expr(expr, Prec::Lowest),
        }
    }

    fn binding(&mut self, binding: &Binding) {
        if let Some(mult) = binding.mult {
            self.push(&mult.mult.to_string());
            self.push(" ");
        }
        self.push(&binding.name.text);
        for param in &binding.params {
            self.push(" ");
            self.pattern(param, true);
        }
        if let Some(ty) = &binding.ty {
            self.push(" : ");
            self.expr(ty, Prec::Lowest);
        }
        self.push(" =");
        self.body(&binding.body);
    }

    // --- выражения --------------------------------------------------------

    fn expr(&mut self, expr: &Expr, position: Prec) {
        // Форму с блоком в скобки не взять, и они ей не нужны: разбор
        // пропускает её только в хвост конструкции - см. заголовок модуля.
        let parenthesised =
            (expr.prec() < position || needs_sign_guard(expr, position)) && !contains_block(expr);
        if parenthesised {
            self.push("(");
        }
        self.expr_kind(expr);
        if parenthesised {
            self.push(")");
        }
    }

    fn expr_kind(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => self.push(&name.text),
            ExprKind::Lit(lit) => self.push(&lit.text),
            ExprKind::Hole => self.push("_"),
            ExprKind::Using { name, body } => {
                self.push("using ");
                self.push(&name.text);
                self.push(" ");
                self.expr(body, Prec::Lowest);
            }
            ExprKind::RecordType(fields, tail) => {
                self.push("{");
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&field.name.text);
                    self.push(" : ");
                    self.expr(&field.ty, Prec::Lowest);
                }
                if let Some(tail) = tail {
                    self.push(" | ");
                    self.push(&tail.text);
                }
                self.push("}");
            }
            ExprKind::Record(fields) => {
                self.push("{");
                for (index, (name, value)) in fields.iter().enumerate() {
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&name.text);
                    self.push(" = ");
                    self.expr(value, Prec::Lowest);
                }
                self.push("}");
            }
            ExprKind::Update(base, fields) => {
                self.push("{");
                self.expr(base, Prec::Lowest);
                self.push(" | ");
                for (index, (name, value)) in fields.iter().enumerate() {
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&name.text);
                    self.push(" = ");
                    self.expr(value, Prec::Lowest);
                }
                self.push("}");
            }
            ExprKind::Project(inner, name) => {
                self.expr(inner, Prec::Atom);
                self.push(".");
                self.push(&name.text);
            }
            ExprKind::App(..) | ExprKind::TypeApp(..) => self.spine(expr),
            ExprKind::Lam { params, body } => {
                self.push("\\");
                for (index, param) in params.iter().enumerate() {
                    if index > 0 {
                        self.push(" ");
                    }
                    self.lam_param(param);
                }
                self.push(" -> ");
                self.expr(body, Prec::Lowest);
            }
            ExprKind::Pi { binders, codomain } => {
                for binder in binders {
                    self.binder(binder);
                    self.push(" ");
                }
                self.push("-> ");
                self.expr(codomain, Prec::Lowest);
            }
            ExprKind::Arrow(domain, codomain) => {
                // Стрелка правоассоциативна, поэтому скобки нужны только слева.
                self.expr(domain, Prec::Chain);
                self.push(" -> ");
                self.expr(codomain, Prec::Lowest);
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.conditional(cond, then_branch, else_branch),
            ExprKind::Case { scrutinee, alts } => {
                self.push("case ");
                self.expr(scrutinee, Prec::Chain);
                self.push(" of");
                self.block_of(alts, Self::alt);
            }
            ExprKind::Tuple(items) => self.sequence("(", items, ")"),
            ExprKind::List(items) => self.sequence("[", items, "]"),
            ExprKind::Chain(chain) => self.chain(chain),
        }
    }

    /// Спайн применения - циклом, а не спуском.
    ///
    /// Аргументы разбор набирает циклом, предел вложенности на них не
    /// тратится, и спайн бывает глубже любого дерева, которое даёт вложенность
    /// скобок. Рекурсия по нему упиралась бы в стек - и упиралась: тысячи
    /// аргументов роняли печать.
    fn spine(&mut self, expr: &Expr) {
        let mut arguments = Vec::new();
        let mut head = expr;
        loop {
            match &head.kind {
                ExprKind::App(callee, argument) => {
                    arguments.push((" ", argument));
                    head = callee;
                }
                ExprKind::TypeApp(callee, argument) => {
                    arguments.push((" @", argument));
                    head = callee;
                }
                _ => break,
            }
        }
        self.expr(head, Prec::App);
        for (separator, argument) in arguments.iter().rev() {
            self.push(separator);
            self.expr(argument, Prec::Atom);
        }
    }

    /// Блок операторов вне позиции тела. Разбор такого дерева не порождает -
    /// блок открывают только `=` и `let`, - и ветка здесь ради того, чтобы
    /// `match` оставался исчерпывающим без заглушки.
    fn block(&mut self, block: &Block) {
        self.block_of(&block.stmts, Self::stmt);
    }

    fn conditional(&mut self, cond: &Expr, then_branch: &Expr, else_branch: &Expr) {
        self.push("if ");
        self.expr(cond, Prec::Chain);
        // Ветка «да» с блоком внутри займёт больше строки, и `else`,
        // напечатанный следом, уехал бы в этот блок: закрыть его может только
        // начало строки левее. Поэтому такой `if` печатается в три строки, а
        // обычный - в одну.
        if contains_block(then_branch) {
            // `then` и `else` отбиваются на шаг: они продолжают член блока, а
            // не начинают новый (§4.1 правило 2), но читаться должны как части
            // одного `if`, а не как продолжение чего попало.
            self.nested(STEP, |printer| {
                printer.line();
                printer.push("then ");
                printer.expr(then_branch, Prec::Lowest);
                printer.line();
                printer.push("else ");
                printer.expr(else_branch, Prec::Lowest);
            });
            return;
        }
        self.push(" then ");
        self.expr(then_branch, Prec::Lowest);
        self.push(" else ");
        self.expr(else_branch, Prec::Lowest);
    }

    fn alt(&mut self, alt: &Alt) {
        self.pattern(&alt.pattern, false);
        self.push(" -> ");
        self.expr(&alt.body, Prec::Lowest);
    }

    fn chain(&mut self, chain: &Chain) {
        self.expr(&chain.head, Prec::App);
        for (operator, operand) in &chain.tail {
            self.push(" ");
            self.push(&operator.text);
            self.push(" ");
            self.expr(operand, Prec::App);
        }
    }

    fn sequence(&mut self, open: &str, items: &[Expr], close: &str) {
        self.push(open);
        for (index, item) in items.iter().enumerate() {
            if index > 0 {
                self.push(", ");
            }
            self.expr(item, Prec::Lowest);
        }
        self.push(close);
    }

    fn lam_param(&mut self, param: &LamParam) {
        match &param.kind {
            LamParamKind::Pattern(pattern) => self.pattern(pattern, true),
            LamParamKind::Binder(binder) => self.binder(binder),
        }
    }

    // --- связывания и паттерны --------------------------------------------

    fn binder(&mut self, binder: &Binder) {
        // Параметр без скобок - тот, у которого нечего в них писать.
        if let (Visibility::Explicit, None, None, [name]) = (
            binder.visibility,
            binder.mult,
            binder.ty.as_ref(),
            binder.names.as_slice(),
        ) {
            self.push(&name.text);
            return;
        }
        let (open, close) = match binder.visibility {
            Visibility::Explicit => ("(", ")"),
            Visibility::Implicit => ("{", "}"),
        };
        self.push(open);
        if let Some(mult) = binder.mult {
            self.push(&mult.mult.to_string());
            self.push(" ");
        }
        for (index, name) in binder.names.iter().enumerate() {
            if index > 0 {
                self.push(" ");
            }
            self.push(&name.text);
        }
        if let Some(ty) = &binder.ty {
            self.push(" : ");
            self.expr(ty, Prec::Lowest);
        }
        self.push(close);
    }

    /// `atom` - позиция аргумента, где конструктор с полями требует скобок.
    fn pattern(&mut self, pattern: &Pattern, atom: bool) {
        match &pattern.kind {
            PatternKind::Name(name) => self.push(&name.text),
            PatternKind::Wildcard => self.push("_"),
            PatternKind::Lit(Lit { text, .. }) => self.push(text),
            PatternKind::App { head, fields } => {
                let parenthesised = atom && !fields.is_empty();
                if parenthesised {
                    self.push("(");
                }
                self.push(&head.text);
                for field in fields {
                    self.push(" ");
                    self.pattern(field, true);
                }
                if parenthesised {
                    self.push(")");
                }
            }
            PatternKind::Tuple(items) => {
                self.push("(");
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        self.push(", ");
                    }
                    self.pattern(item, false);
                }
                self.push(")");
            }
        }
    }
}

/// Печатает объявление отдельно.
///
/// Нужна ли перед ним пустая строка, зависит от того, заняло ли оно больше
/// строки, - а это видно только после печати.
fn rendered(decl: &Decl) -> String {
    let mut printer = Printer {
        out: String::new(),
        indent: 0,
    };
    printer.decl(decl);
    printer.out
}

/// Идут ли объявления вплотную, без пустой строки между ними.
fn attached(previous: &Decl, next: &Decl) -> bool {
    match (&previous.kind, &next.kind) {
        (DeclKind::Signature { name, .. }, DeclKind::Clauses { name: defined, .. }) => {
            name.text == defined.text
        }
        _ => false,
    }
}

/// Нужны ли скобки отрицательному литералу.
///
/// Знак принадлежит литералу только там, где начинается операнд (§4.1, решение
/// от 2026-08-25): в `f -42` тот же знак читается как вычитание. Скобки
/// поэтому ставятся всюду, кроме позиций, которые печать печатает с
/// [`Prec::Lowest`], - там операнд и так начинается заново: после `=`, `,`,
/// `then`, `->`. Дерева они не меняют нигде, кроме позиции аргумента, но
/// `x + -42` читается опечаткой, а стоят они два знака.
fn needs_sign_guard(expr: &Expr, position: Prec) -> bool {
    position > Prec::Lowest && matches!(&expr.kind, ExprKind::Lit(lit) if lit.text.starts_with('-'))
}
