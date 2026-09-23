//! Что написано под курсором (§7.2: hover и переход к определению).
//!
//! # Почему по дереву, а не по `origins`
//!
//! Таблица [`Signature::origin`] заведена трек E волны 1 Фазы 7 под DWARF, и
//! потолок мелкости у неё - определение: имя знает **первую клаузу**, а не
//! место, где написано. Под редактор она мала дважды. Во-первых, кладут в неё
//! только определения с клаузами: на корпусе позицию знают **1230 имён из
//! 3436**, а семейства, конструкторы, эффекты и операции не знают ни одного.
//! Во-вторых, она есть только у принятой программы, а буфер в редакторе
//! перестаёт проверяться на первом же недописанном слове.
//!
//! Дерево даёт и то и другое: имя каждого объявления лежит в нём со своим
//! спаном, и живёт дерево с момента, когда текст **разобрался**, - то есть
//! переход к определению работает на буфере, который проверку не проходит.
//!
//! # Чего дерево не даёт
//!
//! Типов подвыражений. У [`adamas_core::term::Term`] спанов нет, узел его
//! держится на 48 байтах (`a_term_node_stays_within_its_measured_width`), и
//! добрать их значило бы дописать спан к 1611 упоминаниям конструкторов
//! `Term::` в 28 файлах пяти крейтов. Поэтому тип отдаётся **имени**, а не
//! выражению, и берётся он из сигнатуры.
//!
//! Счёт, на котором решение стоит (137 принятых фикстур корпуса, 22 478
//! идентификаторов): имя верхнего уровня - 13 072, член модуля коротким
//! именем - 1 121, имя, занятое языком (§4.11), - 1 571, сорт - 182. Итого
//! **71 %** написанных имён получают тип из сигнатуры. Остаток - 6 532 - это
//! локальные связывания и поля записей; они распознаются как локальные (то
//! есть hover не выдаёт за них чужой тип), но своего типа сегодня не имеют.

use std::rc::Rc;

use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_parser::ast::{
    self, Block, Clause, Decl, DeclKind, Expr, ExprKind, LamParamKind, Module, Pattern,
    PatternKind, Stmt, StmtKind, Symbol,
};

use crate::expr::is_reference;

/// Связано ли имя чем-то написанным рядом.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bound {
    /// Связано локально: лямбдой, паттерном, `let`, связыванием телескопа.
    Local,
    /// Свободно - разрешается сигнатурой, примитивами или сортами.
    Free,
}

/// Имя под курсором вместе с тем, что о нём знает дерево.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cursor {
    /// Как написано.
    pub text: Symbol,
    /// Где написано - это и подсвечивает редактор.
    pub span: Span,
    /// Связано локально или свободно.
    pub bound: Bound,
    /// Где связано, если связано локально. У объявления верхнего уровня
    /// `None`: его место ищет [`declaration`] по всему дереву.
    pub binder: Option<Span>,
    /// Модули, внутри которых имя написано; внешний первым.
    pub within: Vec<Symbol>,
    /// Объявление, в чьём **написанном типе** стоит курсор.
    ///
    /// Нужно свободным именам типа: `map : (a -> b) -> List a -> List b`
    /// поднимает `a` и `b` в implicit-параметры (§4.1), связывания в тексте у
    /// них нет, а в элаборированном типе `map` они стоят первыми `Pi`.
    pub owner: Option<Symbol>,
}

impl Cursor {
    /// Префикс квалификации - то, что [`crate::expr::qualified_in`] называет
    /// окружением.
    fn enclosing(&self) -> Option<String> {
        (!self.within.is_empty()).then(|| {
            self.within
                .iter()
                .map(|it| &**it)
                .collect::<Vec<_>>()
                .join(".")
        })
    }

    /// Полное имя объявления, в чьём типе стоит курсор.
    fn owning(&self) -> Option<String> {
        let owner = self.owner.as_ref()?;
        Some(match self.enclosing() {
            Some(prefix) => format!("{prefix}.{owner}"),
            None => owner.to_string(),
        })
    }
}

/// Имя под курсором. `None` - курсор не на имени.
///
/// Смещение байтовое и полуоткрытое: `offset` внутри `[start, end)` имени.
/// Позиция сразу за именем принадлежит следующему знаку, а не ему.
///
/// Исходник нужен затем, что имя группы клауз лежит в дереве **однажды**, а
/// написано на каждой клаузе: второе и последующие его вхождения опознаются
/// сверкой с текстом (см. [`Search::clauses`]).
#[must_use]
pub fn at(source: &str, module: &Module, offset: usize) -> Option<Cursor> {
    let mut search = Search {
        source,
        offset,
        scope: Vec::new(),
        within: Vec::new(),
        owner: None,
        found: None,
    };
    search.decls(&module.decls);
    search.found
}

/// Под каким именем сигнатура знает то, что под курсором.
///
/// Правило разрешения - то же, каким его читает элаборация
/// ([`crate::expr::qualified_in`]): сначала члены объемлющих модулей, изнутри
/// наружу, затем имя как написано. Локальное связывание сигнатуре не
/// принадлежит вовсе, и для него ответ `None`.
#[must_use]
pub fn resolved(signature: &Signature, cursor: &Cursor) -> Option<Symbol> {
    if cursor.bound == Bound::Local {
        return None;
    }
    crate::expr::qualified_in(signature, cursor.enclosing().as_deref(), &cursor.text).or_else(
        || {
            signature
                .lookup(&cursor.text)
                .map(|_| Rc::clone(&cursor.text))
        },
    )
}

/// Строка «имя : тип» - одна на терминал и на редактор.
///
/// Тип печатает [`adamas_core::term::Term`] - тот же принтер, которым типы
/// показывают сообщения об отказе. Второй записи типа в проекте нет, и заводить
/// её ради редактора значило бы завести пару, которая разъедется. Совпадение
/// проверяется прогоном: `crates/adamas-cli/tests/hover.rs` запускает
/// `adamas check --type` **процессом** и сверяет с тем, что ушло бы в
/// подсказку.
///
/// Имя берётся уже разрешённым: квалификацию модулем знает [`resolved`], а
/// терминалу её пишут руками.
#[must_use]
pub fn described(signature: &Signature, name: &str) -> Option<String> {
    if let Some(definition) = signature.lookup(name) {
        return Some(format!("{name} : {}", definition.ty));
    }
    // Порядок тот же, каким читает имя элаборация: объявленное заслоняет
    // занятое языком, а занятое языком не переобъявить (§4.11).
    if let Some(prim) = adamas_core::prim::Prim::named(name) {
        let ty = adamas_core::check::prim_scheme(signature, prim);
        return Some(format!("{name} : {ty}"));
    }
    if name == "Type" || name == "Effect" {
        return Some(format!("{name} - сорт (§3.2, §3.4)"));
    }
    None
}

/// Что показать над курсором. `None` - типа у этого имени сегодня нет.
///
/// Четыре источника, в том же порядке, в каком читает имя элаборация:
/// сигнатура, имя, занятое языком (§4.11), сорт, поднятый implicit написанного
/// типа (§4.1). Локальное связывание не даёт типа ни по одному из них - и
/// **не выдаётся за одноимённое определение**: на корпусе таких заслонений 37.
#[must_use]
pub fn shown(signature: &Signature, cursor: &Cursor) -> Option<String> {
    if cursor.bound == Bound::Local {
        return None;
    }
    let name = resolved(signature, cursor).unwrap_or_else(|| Rc::clone(&cursor.text));
    described(signature, &name).or_else(|| lifted(signature, cursor))
}

/// Тип implicit-параметра, поднятого из написанного типа (§4.1).
///
/// Подъём сохраняет написанное имя, поэтому связывание находится по нему же:
/// `map : (a -> b) -> …` даёт `map : {0 a : Type u0} -> {0 b : Type u1} -> …`,
/// и `a` под курсором - первое `Pi` с этим именем.
fn lifted(signature: &Signature, cursor: &Cursor) -> Option<String> {
    let mut ty = &signature.lookup(&cursor.owning()?)?.ty;
    while let adamas_core::term::Term::Pi(_, name, domain, _, codomain) = ty {
        if **name == *cursor.text {
            return Some(format!("{} : {domain}", cursor.text));
        }
        ty = codomain;
    }
    None
}

/// Где в этом файле объявлено имя, видимое изнутри модулей `within`.
///
/// Порядок тот же, что у разрешения: члены объемлющих модулей изнутри наружу,
/// затем верхний уровень. Сигнатура предпочитается клаузам - `f : A -> B`
/// говорит читателю больше, чем первая строка тела.
#[must_use]
pub fn declaration(module: &Module, text: &str, within: &[Symbol]) -> Option<Span> {
    let mut sites = Vec::new();
    collect(&module.decls, &mut Vec::new(), &mut sites);
    for depth in (0..=within.len()).rev() {
        let prefix = &within[..depth];
        let found = sites
            .iter()
            .filter(|site| &*site.text == text && site.within == prefix)
            .min_by_key(|site| u8::from(!site.declaring));
        if let Some(site) = found {
            return Some(site.span);
        }
    }
    None
}

/// Определения, **написанные в этом файле**: имя сигнатуры и место, где оно
/// написано.
///
/// Нужно подсказкам §7.2: вердикт `@noalloc` и переиспользование ячейки
/// показываются над функцией, а «над функцией» есть место в **этом** тексте.
/// Взять его у [`Signature::origin`] нельзя, и это не мелочь: таблица позиций
/// файла не несёт, а сигнатура одна на программу - место имени из
/// подключённого модуля нарисовалось бы по чужому тексту и подчеркнуло
/// случайную строку (ровно то, что запрещает §7.2). Дерево же принадлежит
/// буферу по построению.
///
/// Отдаются только **определения значений** - то, у чего бывает тело: семейства,
/// конструкторы, метки эффектов и операции своего вердикта аллокации не имеют.
/// Имя разрешается лестницей объемлющих модулей, как его читает элаборация
/// ([`crate::expr::qualified_in`]), но **без** ступени импорта: имя, которого в
/// сигнатуре нет, чужим не подменяется - буфер бывает проверен наполовину, и
/// подсказка от чужого определения была бы ложью.
#[must_use]
pub fn definitions(signature: &Signature, module: &Module) -> Vec<(Symbol, Span)> {
    let mut sites = Vec::new();
    collect(&module.decls, &mut Vec::new(), &mut sites);
    let mut found = Vec::new();
    for site in sites {
        if !site.declaring || !site.value {
            continue;
        }
        let mut resolved = None;
        for depth in (1..=site.within.len()).rev() {
            let prefix: Vec<&str> = site.within[..depth].iter().map(|it| &**it).collect();
            let full: Symbol = Rc::from(format!("{}.{}", prefix.join("."), site.text).as_str());
            if signature.lookup(&full).is_some() {
                resolved = Some(full);
                break;
            }
        }
        let name = resolved.or_else(|| signature.lookup(&site.text).map(|_| Rc::clone(&site.text)));
        if let Some(name) = name {
            found.push((name, site.span));
        }
    }
    found
}

/// Объявленное имя: где написано и объявление ли это (против клаузы).
struct Site {
    text: Symbol,
    span: Span,
    within: Vec<Symbol>,
    /// Сигнатура, семейство, конструктор - против группы клауз.
    declaring: bool,
    /// Определение значения - то, у чего бывает тело. Семейство, конструктор,
    /// метка эффекта и операция сюда не идут: вердикта аллокации у них нет, а
    /// подсказка над ними была бы подсказкой ни о чём ([`definitions`]).
    value: bool,
}

/// Собирает объявленные имена вместе с модулем, которому они принадлежат.
fn collect(decls: &[Decl], within: &mut Vec<Symbol>, out: &mut Vec<Site>) {
    for decl in decls {
        let mut put = |name: &ast::Name, declaring: bool, value: bool| {
            out.push(Site {
                text: Rc::clone(&name.text),
                span: name.span,
                within: within.clone(),
                declaring,
                value,
            });
        };
        match &decl.kind {
            DeclKind::Signature { name, .. } => put(name, true, true),
            DeclKind::Alias { name, .. } => put(name, true, false),
            DeclKind::Extern(declared) => put(&declared.name, true, true),
            // Экспорт имени не объявляет: он называет уже объявленное, как
            // клауза называет свою сигнатуру.
            DeclKind::Export(exported) => put(&exported.name, false, false),
            DeclKind::Clauses { name, .. } => put(name, false, true),
            DeclKind::Data(data) => {
                put(&data.name, true, false);
                for constructor in &data.constructors {
                    put(&constructor.name, true, false);
                }
            }
            DeclKind::Effect(effect) => {
                put(&effect.name, true, false);
                for operation in &effect.operations {
                    put(&operation.name, true, false);
                }
            }
            DeclKind::Resource(resource) => {
                put(&resource.name, true, false);
                collect(&resource.members, within, out);
            }
            DeclKind::Module(module) => {
                put(&module.name, true, false);
                within.push(Rc::clone(&module.name.text));
                collect(&module.members, within, out);
                within.pop();
            }
            // Методы класса - имена верхнего уровня: `eq` зовётся без
            // квалификации, а словарь выбирает разрешение. Члены инстанса
            // наоборот невыразимы (`Eqv#Nat.eq`), и ссылаться на них некому,
            // поэтому в указатель они не идут.
            DeclKind::Class(class) => {
                if let Some(name) = &class.name {
                    put(name, true, false);
                }
                if !class.instance {
                    collect(&class.members, within, out);
                }
            }
            DeclKind::Mutual(inner) => collect(inner, within, out),
            // Импорт своих имён не объявляет: он приносит чужие, и объявлены
            // они в том файле, откуда пришли.
            DeclKind::Fixity(_) | DeclKind::Import(_) => {}
        }
    }
}

/// Обход дерева с окружением: что связано в точке, где стоит курсор.
struct Search<'a> {
    /// Текст файла - за именами, которых в дереве нет.
    source: &'a str,
    offset: usize,
    /// Локальные связывания, внешние первыми.
    scope: Vec<(Symbol, Span)>,
    /// Модули, внутри которых идёт обход.
    within: Vec<Symbol>,
    /// Объявление, чей написанный тип обходится сейчас.
    owner: Option<Symbol>,
    found: Option<Cursor>,
}

/// Покрывает ли спан смещение.
fn covers(span: Span, offset: usize) -> bool {
    span.start() <= offset && offset < span.end()
}

impl Search<'_> {
    /// Готов ли ответ: дальше обходить незачем.
    fn done(&self) -> bool {
        self.found.is_some()
    }

    /// Имя в позиции ссылки.
    fn refer(&mut self, name: &ast::Name) {
        if self.done() || !covers(name.span, self.offset) {
            return;
        }
        let local = self
            .scope
            .iter()
            .rev()
            .find(|(text, _)| *text == name.text)
            .map(|(_, span)| *span);
        self.found = Some(Cursor {
            text: Rc::clone(&name.text),
            span: name.span,
            bound: if local.is_some() {
                Bound::Local
            } else {
                Bound::Free
            },
            binder: local,
            within: self.within.clone(),
            owner: self.owner.clone(),
        });
    }

    /// Имя в позиции объявления верхнего уровня: оно и есть своё место.
    fn declare(&mut self, name: &ast::Name) {
        self.declare_at(name, name.span);
    }

    /// То же, но имя написано в другом месте, чем помнит дерево.
    fn declare_at(&mut self, name: &ast::Name, span: Span) {
        if self.done() || !covers(span, self.offset) {
            return;
        }
        self.found = Some(Cursor {
            text: Rc::clone(&name.text),
            span,
            bound: Bound::Free,
            binder: None,
            within: self.within.clone(),
            owner: self.owner.clone(),
        });
    }

    /// Группа клауз: имя написано перед каждой, а в дереве лежит однажды.
    ///
    /// Второе и последующие вхождения восстанавливаются по тексту: спан клаузы
    /// начинается с её левой части, и если там стоит ровно это имя - оно и
    /// написано. Сверка с исходником нужна, потому что инфиксная клауза
    /// (`x + y = …`) начинается не с имени, а с первого аргумента.
    fn clauses(&mut self, name: &ast::Name, clauses: &[Clause]) {
        self.declare(name);
        for clause in clauses {
            if self.done() {
                return;
            }
            let start = clause.span.start();
            let end = start + name.text.len();
            if start != name.span.start() && self.source.get(start..end) == Some(&name.text) {
                self.declare_at(name, Span::new(start, end));
            }
            self.clause(clause);
        }
    }

    /// Имя в позиции локального связывания.
    fn bind(&mut self, name: &ast::Name) {
        if !self.done() && covers(name.span, self.offset) {
            self.found = Some(Cursor {
                text: Rc::clone(&name.text),
                span: name.span,
                bound: Bound::Local,
                binder: Some(name.span),
                within: self.within.clone(),
                owner: self.owner.clone(),
            });
        }
        self.scope.push((Rc::clone(&name.text), name.span));
    }

    /// Связывание именем, которого в тексте нет: `resume`, `state` (§3.4).
    fn bind_implied(&mut self, text: &str, span: Span) {
        self.scope.push((Rc::from(text), span));
    }

    fn decls(&mut self, decls: &[Decl]) {
        for decl in decls {
            if self.done() {
                return;
            }
            self.decl(decl);
        }
    }

    fn decl(&mut self, decl: &Decl) {
        let depth = self.scope.len();
        match &decl.kind {
            DeclKind::Alias { name, params, body } => {
                self.declare(name);
                self.binders(params);
                if let Some(body) = body {
                    self.expr(body);
                }
            }
            DeclKind::Signature {
                name,
                ty,
                attributes,
            } => {
                self.declare(name);
                for attribute in attributes {
                    self.refer(attribute);
                }
                self.typed(name, ty);
            }
            DeclKind::Extern(declared) => {
                self.declare(&declared.name);
                for attribute in &declared.attributes {
                    self.refer(attribute);
                }
                self.typed(&declared.name, &declared.ty);
            }
            DeclKind::Export(exported) => self.refer(&exported.name),
            DeclKind::Clauses { name, clauses } => self.clauses(name, clauses),
            DeclKind::Data(data) => {
                self.declare(&data.name);
                if let Some(kind) = &data.kind {
                    self.expr(kind);
                }
                self.binders(&data.params);
                for constructor in &data.constructors {
                    self.declare(&constructor.name);
                    self.typed(&constructor.name, &constructor.ty);
                }
            }
            DeclKind::Effect(effect) => {
                self.declare(&effect.name);
                self.binders(&effect.params);
                for operation in &effect.operations {
                    self.declare(&operation.name);
                    self.typed(&operation.name, &operation.ty);
                }
            }
            DeclKind::Resource(resource) => {
                self.declare(&resource.name);
                self.binders(&resource.params);
                self.decls(&resource.members);
            }
            DeclKind::Module(module) => {
                self.declare(&module.name);
                self.binders(&module.params);
                if let Some(ascription) = &module.ascription {
                    self.expr(ascription);
                }
                if let Some(body) = &module.body {
                    self.expr(body);
                }
                self.within.push(Rc::clone(&module.name.text));
                self.decls(&module.members);
                self.within.pop();
            }
            DeclKind::Class(class) => {
                if let Some(name) = &class.name {
                    self.declare(name);
                }
                self.expr(&class.head);
                self.binders(&class.params);
                for superclass in &class.superclasses {
                    self.expr(superclass);
                }
                self.decls(&class.members);
            }
            DeclKind::Mutual(inner) => self.decls(inner),
            DeclKind::Fixity(fixity) => {
                for operator in &fixity.operators {
                    self.refer(operator);
                }
            }
            // Имена импорта - ссылки: путь называет чужой файл, открытое имя -
            // его член, и связывания здесь нет ни одного.
            DeclKind::Import(import) => {
                for opened in &import.open {
                    self.refer(opened);
                }
            }
        }
        self.scope.truncate(depth);
    }

    /// Написанный тип объявления: свободные имена в нём подняты в
    /// implicit-параметры этого объявления (§4.1).
    fn typed(&mut self, name: &ast::Name, ty: &Expr) {
        let outer = self.owner.replace(Rc::clone(&name.text));
        self.expr(ty);
        self.owner = outer;
    }

    /// Группы связываний телескопа: тип каждой видит предыдущие.
    fn binders(&mut self, binders: &[ast::Binder]) {
        for binder in binders {
            if self.done() {
                return;
            }
            if let Some(ty) = &binder.ty {
                self.expr(ty);
            }
            if let Some(default) = &binder.default {
                self.expr(default);
            }
            for name in binder.names.iter().chain(&binder.factors) {
                self.bind(name);
            }
        }
    }

    fn clause(&mut self, clause: &Clause) {
        let depth = self.scope.len();
        for pattern in &clause.patterns {
            self.pattern(pattern);
        }
        self.expr(&clause.body);
        self.decls(&clause.wheres);
        self.scope.truncate(depth);
    }

    /// Паттерн: заглавное имя разбирает, строчное связывает (§4.1).
    fn pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                if is_reference(&name.text) {
                    self.refer(name);
                } else {
                    self.bind(name);
                }
            }
            PatternKind::Wildcard | PatternKind::Lit(_) => {}
            PatternKind::App { head, fields } => {
                self.refer(head);
                for field in fields {
                    self.pattern(field);
                }
            }
            PatternKind::Tuple(fields) => {
                for field in fields {
                    self.pattern(field);
                }
            }
        }
    }

    fn block(&mut self, block: &Block) {
        let depth = self.scope.len();
        for stmt in &block.stmts {
            if self.done() {
                break;
            }
            self.stmt(stmt);
        }
        self.scope.truncate(depth);
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.expr(expr),
            // Связывание видит предыдущие, но не себя: рекурсивных `let` в
            // §4.1 нет, взаимная рекурсия пишется `mutual` (§4.8).
            StmtKind::Let(bindings) => {
                for binding in bindings {
                    let depth = self.scope.len();
                    for param in &binding.params {
                        self.pattern(param);
                    }
                    if let Some(ty) = &binding.ty {
                        self.expr(ty);
                    }
                    self.expr(&binding.body);
                    self.scope.truncate(depth);
                    self.bind(&binding.name);
                }
            }
        }
    }

    fn label(&mut self, label: &ast::EffectLabel) {
        self.refer(&label.name);
        for argument in &label.arguments {
            self.expr(argument);
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "ветвь на форму выражения: разложение по помощникам прячет то, что обход полон"
    )]
    fn expr(&mut self, expr: &Expr) {
        if self.done() {
            return;
        }
        match &expr.kind {
            ExprKind::Name(name) => self.refer(name),
            ExprKind::Lit(_) | ExprKind::Hole => {}
            ExprKind::App(left, right)
            | ExprKind::TypeApp(left, right)
            | ExprKind::Arrow(left, right) => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Using { name, body } => {
                self.refer(name);
                self.expr(body);
            }
            ExprKind::Lam { params, body } => {
                let depth = self.scope.len();
                for param in params {
                    match &param.kind {
                        LamParamKind::Pattern(pattern) => self.pattern(pattern),
                        LamParamKind::Binder(binder) => self.binders(std::slice::from_ref(binder)),
                    }
                }
                self.expr(body);
                self.scope.truncate(depth);
            }
            ExprKind::Pi { binders, codomain } => {
                let depth = self.scope.len();
                self.binders(binders);
                self.expr(codomain);
                self.scope.truncate(depth);
            }
            ExprKind::Effectful { labels, tail, body } => {
                for label in labels {
                    self.label(label);
                }
                if let Some(tail) = tail {
                    self.refer(tail);
                }
                self.expr(body);
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::Handle {
                label,
                computation,
                state,
                branches,
                ..
            } => {
                if let Some(label) = label {
                    self.label(label);
                }
                self.expr(computation);
                if let Some(state) = state {
                    self.expr(state);
                }
                for branch in branches {
                    let depth = self.scope.len();
                    // Имя ветки - операция эффекта либо `return`; связыванием
                    // оно не является.
                    self.refer(&branch.name);
                    for param in &branch.params {
                        self.bind(param);
                    }
                    if &*branch.name.text != crate::expr::RETURN {
                        self.bind_implied("resume", branch.span);
                    }
                    if state.is_some() {
                        self.bind_implied("state", branch.span);
                    }
                    self.expr(&branch.body);
                    self.scope.truncate(depth);
                }
            }
            ExprKind::Mask(inner) => self.expr(inner),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr(cond);
                self.expr(then_branch);
                self.expr(else_branch);
            }
            ExprKind::Case { scrutinee, alts } => {
                self.expr(scrutinee);
                for alt in alts {
                    let depth = self.scope.len();
                    self.pattern(&alt.pattern);
                    self.expr(&alt.body);
                    self.scope.truncate(depth);
                }
            }
            // Поля типа записи - телескоп: тип поля видит предыдущие (§4.2).
            ExprKind::RecordType(fields, tail) => {
                let depth = self.scope.len();
                for field in fields {
                    self.expr(&field.ty);
                    self.bind(&field.name);
                }
                if let Some(tail) = tail {
                    self.refer(tail);
                }
                self.scope.truncate(depth);
            }
            ExprKind::Record(fields) => {
                for (name, value) in fields {
                    self.refer(name);
                    self.expr(value);
                }
            }
            ExprKind::Project(record, name) => {
                self.expr(record);
                self.refer(name);
            }
            ExprKind::Update(base, fields) => {
                self.expr(base);
                for (name, value) in fields {
                    self.refer(name);
                    self.expr(value);
                }
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Chain(chain) => {
                self.expr(&chain.head);
                for (operator, operand) in &chain.tail {
                    self.refer(operator);
                    self.expr(operand);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Bound, at, resolved, shown};

    /// Курсор на первом вхождении подстроки.
    fn found(source: &str, needle: &str) -> super::Cursor {
        let module = adamas_parser::parse(source).expect("фикстура разбирается");
        let offset = source.find(needle).expect("подстрока в фикстуре есть");
        at(source, &module, offset).expect("под курсором имя")
    }

    const NAT: &str = "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n";

    /// §4.1: заглавное имя в паттерне разбирает, строчное связывает. Правило
    /// лексическое, и берётся оно у той же функции, что и у элаборации.
    #[test]
    fn case_distinguishes_a_pattern_binding_from_a_constructor() {
        let source = format!("{NAT}\nf : Nat -> Nat\nf (Succ n) = n\n");
        assert_eq!(found(&source, "Succ n)").bound, Bound::Free, "конструктор");
        assert_eq!(found(&source, "n) = n").bound, Bound::Local, "связывание");
    }

    /// Член модуля, названный коротким именем изнутри, разрешается в то же
    /// имя, под которым его знает сигнатура (§4.8).
    #[test]
    fn a_member_resolves_through_its_module() {
        let source = format!(
            "{NAT}\nmodule M where\n  один : Nat\n  один = Succ Zero\n\n  два : Nat\n  два = Succ один\n"
        );
        let cursor = found(&source, "один\n");
        assert_eq!(cursor.within.len(), 1, "курсор внутри модуля");
        let signature = crate::analyze(&source)
            .signature
            .expect("программа принята");
        assert_eq!(
            resolved(&signature, &cursor).as_deref(),
            Some("M.один"),
            "короткое имя изнутри модуля - это `M.один`"
        );
        assert_eq!(shown(&signature, &cursor).as_deref(), Some("M.один : Nat"));
    }

    /// Резумпция связана формой хендлера, а не текстом (§3.4): имени `resume`
    /// в ветке не написано, но связано оно.
    #[test]
    fn a_handler_branch_binds_its_resumption() {
        let source = format!(
            "{NAT}\neffect Ask where\n  ask : Nat\n\n\
             спросить : Nat\nспросить = handle ask with\n  ask -> resume Zero\n"
        );
        assert_eq!(found(&source, "resume Zero").bound, Bound::Local);
    }

    /// Поле типа записи видно следующим полям, но не наружу (§4.2).
    #[test]
    fn a_record_field_scopes_over_the_later_fields() {
        let source = "type Пара = { первое : Type, второе : первое }\n";
        assert_eq!(found(source, "первое }").bound, Bound::Local);
    }
}
