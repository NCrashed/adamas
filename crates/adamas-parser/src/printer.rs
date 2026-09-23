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
//! Переносов строк печать не делает: длинное применение печатается одной
//! строкой.
//!
//! # Комментарии
//!
//! [`print`] их не выводит - в дереве их нет, и round-trip дерева от них не
//! зависит. Выводит [`formatted`], которой отдают таблицу
//! ([`crate::token::Comment`]) вместе с исходником; на ней стоит `adamas fmt`
//! (§7.1).
//!
//! Место комментария решается **по исходнику**, а не по дереву, и правило одно:
//! комментарий встаёт над первым членом, который начинается позже него, -
//! ровно та привязка, которую лексер записывает в таблицу («комментарий в этом
//! языке пишется над тем, что поясняет»). Исключение одно: комментарий, стоящий
//! на строке уже напечатанного члена и отделённый от него только пробелами,
//! остаётся хвостом этой строки.
//!
//! Отсюда цена, которую печать платит **намеренно**. Комментарий внутри члена,
//! перед которым нет своей строки вывода - скажем, посреди переносимого
//! применения, - выносится наверх, к следующему члену: своей позиции у него в
//! каноническом выводе нет. Внутренность блочного комментария не трогается
//! вовсе: перевыравнивать чужие строки печать не берётся, и от этого
//! идемпотентность не зависит.
//!
//! Из авторских пустых строк сохраняется одна: та, что отделяет комментарий от
//! следующего комментария или от члена. Без неё шапка файла приклеивалась бы к
//! первому объявлению. Пустые строки между объявлениями по-прежнему
//! канонические - их печать ставит сама.
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

use adamas_core::source::Span;

use crate::ast::{
    Alt, Binder, Binding, Block, Chain, Clause, Constructor, Data, Decl, DeclKind, EffectDecl,
    EffectLabel, Expr, ExprKind, ExternDecl, Grade, HandlerBranch, LamParam, LamParamKind, Lit,
    Module, ModuleDecl, Name, Operation, Pattern, PatternKind, Resource, Stmt, StmtKind,
    Visibility, contains_block,
};
use crate::lexer::is_operator;
use crate::token::Comment;

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
            // `mask` держится как применение: аргумент читается до того же
            // уровня, и в скобки его берут по тем же поводам.
            ExprKind::App(..) | ExprKind::TypeApp(..) | ExprKind::Mask(_) => Prec::App,
            ExprKind::Chain(_) => Prec::Chain,
            // Row связывает так же слабо, как стрелка, на которой написана.
            ExprKind::Effectful { .. }
            | ExprKind::Lam { .. }
            | ExprKind::Using { .. }
            | ExprKind::Pi { .. }
            | ExprKind::Arrow(..)
            | ExprKind::Block(_)
            | ExprKind::If { .. }
            | ExprKind::Case { .. }
            | ExprKind::Handle { .. } => Prec::Lowest,
        }
    }
}

/// Печатает файл. Результат кончается переводом строки; пустой файл даёт
/// пустую строку.
///
/// Комментарии не выводятся: их в дереве нет. Печать с комментариями -
/// [`formatted`].
#[must_use]
pub fn print(module: &Module) -> String {
    Printer::new(Comments::default()).print(module)
}

/// Печатает файл вместе с комментариями исходника - то, что делает
/// `adamas fmt` (§7.1).
///
/// `text` обязан быть тем самым исходником, из которого получены `module` и
/// `comments`: по нему читается написание комментария и то, стоял ли он на
/// строке кода. Готовый вход - [`crate::tokenize`] плюс [`crate::parser::parse`],
/// и собран он в [`crate::format`].
#[must_use]
pub fn formatted(text: &str, module: &Module, comments: &[Comment]) -> String {
    Printer::new(Comments::new(text, comments)).print(module)
}

/// Комментарии исходника, разложенные по порядку появления.
///
/// Курсор один на весь файл и идёт только вперёд: печать обходит дерево в
/// порядке исходника, и «следующий ещё не выведенный» - это ровно тот,
/// чьё место сейчас и решается. Курсор, а не поиск по каждому узлу: иначе
/// один и тот же комментарий мог бы выйти дважды или не выйти вовсе, а мера
/// `adamas fmt` - счёт комментариев до и после.
///
/// Пустой курсор ([`Comments::default`]) не отдаёт ничего: на нём стоит
/// [`print`], и весь код ниже для неё - вызовы, возвращающие `None`.
#[derive(Debug, Default)]
struct Comments<'a> {
    /// Исходник целиком.
    text: &'a str,
    /// Таблица комментариев в порядке появления.
    items: &'a [Comment],
    /// Первый ещё не выведенный.
    next: usize,
}

impl<'a> Comments<'a> {
    fn new(text: &'a str, items: &'a [Comment]) -> Self {
        Self {
            text,
            items,
            next: 0,
        }
    }

    /// Есть ли ещё не выведенные.
    fn pending(&self) -> bool {
        self.next < self.items.len()
    }

    /// Написание комментария. Хвостовые пробелы срезаются: у строчного они
    /// входят в спан, и без среза вывод получал бы их обратно каждым проходом.
    fn written(&self, comment: &Comment) -> &'a str {
        self.text[comment.span.start()..comment.span.end()].trim_end()
    }

    /// Следующий комментарий, если он начинается раньше `start`.
    ///
    /// Второй член ответа - была ли в исходнике пустая строка между этим
    /// комментарием и тем, что за ним следует (соседним комментарием или самим
    /// членом).
    fn before(&mut self, start: usize) -> Option<(&'a str, bool)> {
        let comment = self.items.get(self.next)?;
        if comment.span.start() >= start {
            return None;
        }
        self.next += 1;
        let follows = self
            .items
            .get(self.next)
            .map(|next| next.span.start())
            .filter(|&next| next < start)
            .unwrap_or(start);
        // Пустая строка - когда между ними **только** пробелы и переводов
        // строки хотя бы два. Без проверки на «только» кусок кода, который
        // печать вынесла в другое место, читался бы пустой строкой.
        let blank = self
            .text
            .get(comment.span.end()..follows)
            .is_some_and(|between| {
                between.trim().is_empty() && between.matches('\n').count() >= 2
            });
        Some((self.written(comment), blank))
    }

    /// Следующий комментарий, если он стоит на той же строке, что и конец уже
    /// напечатанного: между `after` и им только пробелы.
    ///
    /// Второй член ответа - конец этого комментария: следующий хвостовой
    /// меряется уже от него, иначе `f = 1 {- a -} -- b` терял бы вторую
    /// привязку на первой.
    fn trailing(&mut self, after: usize) -> Option<(&'a str, usize)> {
        let comment = self.items.get(self.next)?;
        let start = comment.span.start();
        if start < after {
            return None;
        }
        let between = self.text.get(after..start)?;
        if !between.chars().all(|ch| ch == ' ' || ch == '\t') {
            return None;
        }
        self.next += 1;
        Some((self.written(comment), comment.span.end()))
    }
}

/// Член блока, у которого печать спрашивает место в исходнике: по нему
/// решается, какой комментарий стоит над ним, а какой - хвостом его строки.
trait Placed {
    fn span(&self) -> Span;
}

macro_rules! placed {
    ($($ty:ty),* $(,)?) => {
        $(impl Placed for $ty {
            fn span(&self) -> Span {
                self.span
            }
        })*
    };
}

placed!(Decl, Stmt, Alt, Binding, Constructor, Operation, HandlerBranch);

/// Состояние печати: текст, отступ текущей строки и курсор комментариев.
#[derive(Debug)]
struct Printer<'a> {
    out: String,
    indent: usize,
    comments: Comments<'a>,
}

impl<'a> Printer<'a> {
    fn new(comments: Comments<'a>) -> Self {
        Self {
            out: String::new(),
            indent: 0,
            comments,
        }
    }

    fn print(mut self, module: &Module) -> String {
        self.module(module);
        self.out
    }

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

    // --- комментарии ------------------------------------------------------

    /// Выводит комментарии, стоящие перед `start`, каждый со своей строки.
    fn comments_before(&mut self, start: usize) {
        while let Some((written, blank)) = self.comments.before(start) {
            self.line();
            self.push(written);
            // Пустая строка перед следующей строкой вывода: её поставит `line`
            // того, что пойдёт дальше.
            if blank {
                self.out.push('\n');
            }
        }
    }

    /// Комментарии, оставшиеся на строке уже напечатанного члена: они идут
    /// хвостом этой строки, каждый со своим пробелом впереди.
    fn line_tail(&mut self, end: usize) -> String {
        let mut out = String::new();
        let mut end = end;
        while let Some((written, stop)) = self.comments.trailing(end) {
            out.push(' ');
            out.push_str(written);
            end = stop;
        }
        out
    }

    /// То же, дописанное прямо в вывод.
    fn comments_after(&mut self, end: usize) {
        let tail = self.line_tail(end);
        self.push(&tail);
    }

    /// Отдельной строкой печатает то, что уходит перед членом: сам член в
    /// [`Self::module`] печатается врозь, потому что пустая строка перед ним
    /// решается по напечатанному.
    fn detached_comments(&mut self, start: usize) -> String {
        let mut sub = Printer {
            out: String::new(),
            indent: self.indent,
            comments: std::mem::take(&mut self.comments),
        };
        sub.comments_before(start);
        self.comments = sub.comments;
        let mut out = sub.out;
        if !out.is_empty() {
            out.push('\n');
        }
        out
    }

    /// Комментарии после последнего объявления: привязаны они к `Eof`, и своей
    /// строки вывода у них нет - печатаются хвостом файла.
    fn trailing_comments(&mut self) {
        let limit = self.comments.text.len();
        while let Some((written, blank)) = self.comments.before(limit) {
            self.out.push_str(written);
            self.out.push('\n');
            if blank && self.comments.pending() {
                self.out.push('\n');
            }
        }
    }

    // --- объявления ------------------------------------------------------

    fn module(&mut self, module: &Module) {
        let mut previous_is_tall = false;
        for (index, decl) in module.decls.iter().enumerate() {
            // Комментарии над объявлением снимаются с курсора **до** печати
            // самого объявления: иначе их подобрал бы первый же член его блока.
            let leading = self.detached_comments(decl.span.start());
            let mut text = self.rendered(decl);
            // Объявление с комментарием над ним - высокое: без этого шапка
            // файла и пояснение к определению приклеивались бы к соседу
            // сверху.
            let tall = text.contains('\n') || !leading.is_empty();
            text.push_str(&self.line_tail(decl.span.end()));
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
            self.out.push_str(&leading);
            self.out.push_str(&text);
            previous_is_tall = tall;
        }
        if !self.out.is_empty() {
            self.out.push('\n');
        }
        self.trailing_comments();
    }

    /// Печатает объявление отдельно, тем же курсором комментариев.
    ///
    /// Нужна ли перед ним пустая строка, зависит от того, заняло ли оно больше
    /// строки, - а это видно только после печати.
    fn rendered(&mut self, decl: &Decl) -> String {
        let mut sub = Printer {
            out: String::new(),
            indent: 0,
            comments: std::mem::take(&mut self.comments),
        };
        sub.decl(decl);
        self.comments = sub.comments;
        sub.out
    }

    /// Блок членов под ключевым словом, каждый со своей строки.
    fn block_of<T: Placed>(&mut self, items: &[T], mut each: impl FnMut(&mut Self, &T)) {
        self.nested(STEP, |printer| {
            for item in items {
                printer.comments_before(item.span().start());
                printer.line();
                each(printer, item);
                printer.comments_after(item.span().end());
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
                        self.comments_before(clause.span.start());
                        self.line();
                    }
                    self.clause(name, clause);
                    self.comments_after(clause.span.end());
                }
            }
            DeclKind::Data(data) => self.data(data),
            DeclKind::Module(module) => self.module_decl(module),
            DeclKind::Import(import) => {
                self.push("import ");
                self.push(&import.written());
                if let Some(alias) = &import.alias {
                    self.push(" as ");
                    self.push(&alias.text);
                }
                for (index, name) in import.open.iter().enumerate() {
                    self.push(if index == 0 { " (" } else { ", " });
                    self.decl_name(name);
                }
                if !import.open.is_empty() {
                    self.push(")");
                }
            }
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
                for param in &class.params {
                    self.push(" ");
                    self.binder(param);
                }
                for (index, superclass) in class.superclasses.iter().enumerate() {
                    self.push(if index == 0 { " when " } else { ", " });
                    self.expr(superclass, Prec::Lowest);
                }
                self.push(" where");
                self.block_of(&class.members, Self::decl);
            }
            DeclKind::Extern(declared) => self.extern_decl(declared),
            DeclKind::Export(exported) => {
                self.push("export ");
                self.push(&exported.abi.text);
                self.push(" fn ");
                self.decl_name(&exported.name);
            }
            DeclKind::Resource(resource) => self.resource(resource),
            DeclKind::Effect(effect) => self.effect_decl(effect),
            DeclKind::Fixity(fixity) => {
                self.push(fixity.assoc.keyword());
                self.push(" ");
                self.push(&fixity.precedence.to_string());
                for (index, operator) in fixity.operators.iter().enumerate() {
                    self.push(if index == 0 { " " } else { ", " });
                    self.push(&operator.text);
                }
            }
        }
    }

    /// Чужой символ (§5.3): атрибуты строкой выше, дальше ABI, `fn` и тип.
    fn extern_decl(&mut self, declared: &ExternDecl) {
        for attribute in &declared.attributes {
            self.push("@");
            self.push(&attribute.text);
            self.line();
        }
        self.push("extern ");
        self.push(&declared.abi.text);
        self.push(" fn ");
        self.decl_name(&declared.name);
        self.push(" : ");
        self.expr(&declared.ty, Prec::Lowest);
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

    fn effect_decl(&mut self, effect: &EffectDecl) {
        self.push("effect ");
        self.decl_name(&effect.name);
        for param in &effect.params {
            self.push(" ");
            self.binder(param);
        }
        // Без операций `where` не пишется - по той же причине, что у семейства
        // без конструкторов: пустого блока layout не делает.
        if !effect.operations.is_empty() {
            self.push(" where");
            self.block_of(&effect.operations, Self::operation);
        }
    }

    fn operation(&mut self, operation: &Operation) {
        self.decl_name(&operation.name);
        self.push(" : ");
        self.expr(&operation.ty, Prec::Lowest);
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
                            printer.comments_before(binding.span.start());
                            printer.line();
                        }
                        printer.binding(binding);
                        printer.comments_after(binding.span.end());
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

    /// Односложная форма с одним подвыражением: `mask e`.
    /// Форма из ключевого слова и одного аргумента: `mask e`, `state s0`.
    ///
    /// Аргумент печатается в позиции **применения**, а не цепочки: читает его
    /// разбор ровно как применение, и закрывающего токена у формы нет. С
    /// позицией цепочки `mask (a + b)` печаталось как `mask a + b`, а это
    /// другая программа - первая отдаёт второму хендлеру обе операции, вторая
    /// только первую (ревью 2026-09-05). У `handle` та же форма читается
    /// полным выражением и закрыта хвостовым `with`, поэтому там позиция
    /// цепочки верна; скопирована она была оттуда.
    fn wrapped(&mut self, form: &str, inner: &Expr) {
        self.push(form);
        self.expr(inner, Prec::App);
    }

    fn expr_kind(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Name(name) => self.push(&name.text),
            ExprKind::Lit(lit) => self.push(&lit.text),
            ExprKind::Hole => self.push("_"),
            ExprKind::Mask(inner) => self.wrapped("mask ", inner),
            ExprKind::Effectful { .. } => self.effect_row(expr),
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
                self.written_fields(fields);
                self.push("}");
            }
            ExprKind::Update(base, fields) => {
                self.push("{");
                self.expr(base, Prec::Lowest);
                self.push(" | ");
                self.written_fields(fields);
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
            ExprKind::Handle {
                multi,
                label,
                computation,
                state,
                branches,
            } => self.handler(
                *multi,
                label.as_deref(),
                computation,
                state.as_deref(),
                branches,
            ),
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

    /// Написанные поля через запятую - у записи и у переопределения они одни.
    fn written_fields(&mut self, fields: &[(Name, Expr)]) {
        for (index, (name, value)) in fields.iter().enumerate() {
            if index > 0 {
                self.push(", ");
            }
            self.push(&name.text);
            self.push(" = ");
            self.expr(value, Prec::Lowest);
        }
    }

    fn handler(
        &mut self,
        multi: bool,
        label: Option<&EffectLabel>,
        computation: &Expr,
        state: Option<&Expr>,
        branches: &[HandlerBranch],
    ) {
        self.push(if multi { "handleMulti " } else { "handle " });
        if let Some(label) = label {
            self.push("@");
            let parens = !label.arguments.is_empty();
            if parens {
                self.push("(");
            }
            self.push(&label.name.text);
            for argument in &label.arguments {
                self.push(" ");
                self.expr(argument, Prec::Atom);
            }
            if parens {
                self.push(")");
            }
            self.push(" ");
        }
        self.expr(computation, Prec::Chain);
        self.push(" with");
        // Состояние идёт первым членом: оно относится к хендлеру целиком, а не
        // к какой-то из веток.
        self.nested(STEP, |printer| {
            if let Some(state) = state {
                printer.comments_before(state.span.start());
                printer.line();
                printer.push("state ");
                // Позиция применения, а не цепочки: начальное состояние
                // читается разбором как применение, и `state (x + x)`
                // печаталось как `state x + x`, что обратно не разбирается.
                printer.expr(state, Prec::App);
                printer.comments_after(state.span.end());
            }
            for branch in branches {
                printer.comments_before(branch.span.start());
                printer.line();
                printer.handler_branch(branch);
                printer.comments_after(branch.span.end());
            }
        });
    }

    fn handler_branch(&mut self, branch: &HandlerBranch) {
        self.decl_name(&branch.name);
        for param in &branch.params {
            self.push(" ");
            self.push(&param.text);
        }
        self.push(" -> ");
        self.expr(&branch.body, Prec::Lowest);
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

    /// `{State Int | e} A` - row перед типом (§3.4).
    fn effect_row(&mut self, expr: &Expr) {
        let ExprKind::Effectful { labels, tail, body } = &expr.kind else {
            return;
        };
        let tail = tail.as_ref();
        self.push("{");
        for (position, label) in labels.iter().enumerate() {
            if position > 0 {
                self.push(", ");
            }
            self.push(&label.name.text);
            for argument in &label.arguments {
                self.push(" ");
                self.expr(argument, Prec::Atom);
            }
        }
        if let Some(tail) = tail {
            self.push(" | ");
            self.push(&tail.text);
        }
        self.push("} ");
        self.expr(body, Prec::Lowest);
    }

    fn binder(&mut self, binder: &Binder) {
        // Параметр без скобок - тот, у которого нечего в них писать.
        if let (Visibility::Explicit, None, None, None, [name]) = (
            binder.visibility,
            binder.mult,
            binder.ty.as_ref(),
            binder.default.as_ref(),
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
            // Остальные части выражения кратности стоят сразу за первым именем
            // и только там: `(q * r z : a)`, `(q + r z : a)` (§10 вопрос 41).
            // Знак выбирает [`Grade::written`] - смешанное печатается так,
            // чтобы обратно прочиталось смешанным.
            if index == 0 {
                for (position, factor) in binder.factors.iter().enumerate() {
                    self.push(Grade::written(binder.grade, position));
                    self.push(&factor.text);
                }
            }
        }
        if let Some(ty) = &binder.ty {
            self.push(" : ");
            self.expr(ty, Prec::Lowest);
        }
        if let Some(default) = &binder.default {
            self.push(" = ");
            self.expr(default, Prec::Lowest);
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
