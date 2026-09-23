//! `adamas doc`: документация по видимому снаружи интерфейсу (§7.1, §4.8).
//!
//! # Что попадает в вывод
//!
//! Объявление попадает в документацию, если выполнено **и то и другое**: оно
//! видно снаружи и над ним написан блок `-- |`.
//!
//! Видимость спрашивается у сигнатуры, а не у формы записи: `:>` ставит на
//! поднятое имя флаг сокрытия (§4.8), и член запечатанного модуля сверх его
//! сигнатуры снаружи не пишется вовсе. Различение это в языке есть и его надо
//! уважать - иначе `doc` рассказывал бы читателю про имена, написать которые
//! тот не вправе.
//!
//! Маркер спрашивается затем, что комментарий над объявлением документацией
//! **не является**. Счёт по корпусу (лог 2026-09-23): 1056 комментариев над
//! 5240 объявлениями, и документация среди них - примерно один блок из семи.
//! Без маркера вывод состоял бы из ожидаемых ответов прогона, истории правок и
//! ссылок в §10.
//!
//! Отсюда и ответ на вопрос «а где же остальные имена»: у необъявленного
//! интерфейса документации нет, и придумывать её из сигнатуры `doc` не станет.
//! Пустой раздел печатается вместе со счётом - читателю видно, что модуль
//! прочитан, а сказать о нём автор ничего не написал.
//!
//! # Чего нет
//!
//! **Документации у модуля целиком.** Блок `-- |`, не примыкающий ни к какому
//! объявлению, сегодня не значит ничего: форма для «это про файл» в языке не
//! решена, а выдумывать её `doc` не вправе (§4 - предмет владельца). Шапка
//! файла поэтому в вывод не попадает, и это названная граница, а не упущение.
//!
//! # Формат
//!
//! Markdown на стандартный вывод. Выбран за то, что читается и глазами, и
//! grep'ом, и любым просмотрщиком; HTML потребовал бы шаблонов и файлов рядом,
//! а простой текст потерял бы разницу между заголовком и телом. Куда его
//! положить, решает тот, кто запустил, - `doc` ничего не пишет на диск.

use std::path::Path;

use adamas_core::sig::Signature;
use adamas_elab::program::{Program, Unit};
use adamas_parser::ast::{self, DeclKind};
use adamas_parser::token::Comment;

/// Печатает документацию программы и отдаёт её текст.
///
/// # Errors
///
/// То же, что у `adamas check`: файл не читается, программа не разбирается либо
/// не проходит проверку. Документировать непроверенную программу значило бы
/// печатать типы, которых у неё нет.
pub(crate) fn run(path: &Path) -> anyhow::Result<String> {
    let opened = crate::project::opened(path)?;
    let program = crate::project::analyzed(&opened.entry, opened.sources.as_ref())?;
    let text = rendered(&program, &opened.store);
    print!("{text}");
    Ok(text)
}

/// Документация программы целиком.
///
/// Зависимости пропускаются: их исходники лежат в хранилище (§7.3), автору не
/// принадлежат и документируются у себя. Проверяется это путём файла, а не
/// списком имён: путь известен и тогда, когда модуль подключён транзитивно.
fn rendered(program: &Program, store: &Path) -> String {
    let mut out = String::new();
    for unit in &program.units {
        if Path::new(unit.file.name()).starts_with(store) {
            continue;
        }
        out.push_str(&documented(program, unit));
    }
    out
}

/// Раздел одного файла.
fn documented(program: &Program, unit: &Unit) -> String {
    let Some(module) = unit.module.as_ref() else {
        return String::new();
    };
    let Some(signature) = program.signature.as_ref() else {
        return String::new();
    };
    let text = unit.file.text();
    let comments = match adamas_parser::tokenize(text) {
        Ok(tokens) => tokens.comments,
        // Текст, который не лексится, не разобрался бы и в дерево, а дерево
        // здесь есть. Случай поэтому невозможен, но падать на нём нечего:
        // документации без комментариев просто нет.
        Err(_) => Vec::new(),
    };
    let title = unit.path.as_deref().map_or_else(
        || format!("Файл `{}`", unit.file.name()),
        |path| format!("Модуль `{path}`"),
    );
    let within: Vec<String> = unit.path.clone().into_iter().collect();
    let mut entries = Vec::new();
    members(
        &module.decls,
        &Scope {
            signature,
            text,
            comments: &comments,
            file: within.len(),
            within,
        },
        &mut entries,
    );
    let mut out = format!("# {title}\n\n");
    if entries.is_empty() {
        out.push_str("Документированных имён нет.\n\n");
        return out;
    }
    for entry in entries {
        out.push_str(&entry);
        out.push('\n');
    }
    out
}

/// Что известно при обходе объявлений одного уровня.
struct Scope<'a> {
    signature: &'a Signature,
    text: &'a str,
    comments: &'a [Comment],
    /// Сегменты квалификации: путь файла, затем имена объемлющих модулей.
    within: Vec<String>,
    /// Сколько первых сегментов приходится на путь **файла**.
    ///
    /// Заголовок раздела пишет имя так, как его напишет читатель, а путь файла
    /// он уже прочитал в заголовке раздела: внутри `Std.Order` пишется
    /// `compare`, а член вложенного модуля - `Counting.start`.
    file: usize,
}

impl Scope<'_> {
    /// Квалифицированное имя члена этого уровня - то, под которым его знает
    /// сигнатура (§4.8).
    fn qualified(&self, name: &str) -> String {
        if self.within.is_empty() {
            return name.to_owned();
        }
        format!("{}.{name}", self.within.join("."))
    }

    /// Имя так, как его пишет читатель этого файла.
    fn written_as(&self, name: &str) -> String {
        let path = &self.within[self.file.min(self.within.len())..];
        if path.is_empty() {
            return name.to_owned();
        }
        format!("{}.{name}", path.join("."))
    }

    /// Тот же уровень, углублённый в модуль.
    fn inside(&self, name: &str) -> Scope<'_> {
        let mut within = self.within.clone();
        within.push(name.to_owned());
        Scope {
            signature: self.signature,
            text: self.text,
            comments: self.comments,
            within,
            file: self.file,
        }
    }

    /// Запись об имени, если оно видно снаружи и документировано.
    ///
    /// Заголовок - **написанное**, а не элаборированное. Ядерный тип у `add`
    /// звучит `(ω _ : Nat) -> {| e0} (ω _ : Nat) -> {| e0} Nat`, и он верен, но
    /// отвечает на другой вопрос: что знает компилятор. Читателю документации
    /// нужен интерфейс в той записи, в какой он сам его напишет, - `Nat -> Nat
    /// -> Nat`. Ядерный показывают наведение и `adamas check --type`, и они
    /// остаются единственным его источником.
    ///
    /// Берётся он из исходника **срезом по спану**, а не вторым принтером:
    /// написанное уже написано, и печатать его заново незачем.
    fn entry(
        &self,
        name: &str,
        span: adamas_core::source::Span,
        written: &Written<'_>,
    ) -> Option<String> {
        let qualified = self.qualified(name);
        if self
            .signature
            .lookup(&qualified)
            .is_some_and(|it| it.hidden)
        {
            return None;
        }
        let said = adamas_parser::docs::attached(self.text, self.comments, span)?;
        let shown = self.written_as(name);
        let headline = match written {
            Written::Ty(ty) => format!("{shown} : {}", self.slice(ty.span)),
            Written::Form(word) => format!("{word} {shown}"),
        };
        Some(format!("## `{headline}`\n\n{said}\n"))
    }

    /// Кусок исходника одной строкой: написанный тип бывает перенесён, а
    /// заголовок раздела однострочен.
    fn slice(&self, span: adamas_core::source::Span) -> String {
        self.text[span.start()..span.end()]
            .split_whitespace()
            .collect::<Vec<&str>>()
            .join(" ")
    }
}

/// Чем назвать имя в заголовке раздела.
enum Written<'a> {
    /// Написанным типом: `add : Nat -> Nat -> Nat`.
    Ty(&'a ast::Expr),
    /// Словом формы: `data Nat`, `effect State`. Так пишутся те, у кого
    /// написанного типа нет вовсе - семейство, эффект, алиас, модуль, класс.
    Form(&'static str),
}

/// Объявления одного уровня в порядке написания.
///
/// Порядок именно написанный: §4.8 задаёт ordered scoping, и документация,
/// переставившая имена по алфавиту, показала бы читателю не тот файл, который
/// он открыл.
fn members(decls: &[ast::Decl], scope: &Scope<'_>, out: &mut Vec<String>) {
    for decl in decls {
        match &decl.kind {
            // Сигнатура, а не клаузы: документация пишется над написанным
            // типом. У определения без сигнатуры типа в тексте нет вовсе.
            DeclKind::Signature { name, ty, .. } => {
                out.extend(scope.entry(&name.text, decl.span, &Written::Ty(ty)));
            }
            DeclKind::Alias { name, .. } => {
                out.extend(scope.entry(&name.text, decl.span, &Written::Form("type")));
            }
            DeclKind::Extern(written) => {
                out.extend(scope.entry(&written.name.text, decl.span, &Written::Ty(&written.ty)));
            }
            // Семейство и эффект документируются вместе со своим
            // представлением: конструкторы и операции - имена программы, и
            // писать их автор вправе.
            DeclKind::Data(data) => {
                out.extend(scope.entry(&data.name.text, decl.span, &Written::Form("data")));
                for constructor in &data.constructors {
                    out.extend(scope.entry(
                        &constructor.name.text,
                        constructor.span,
                        &Written::Ty(&constructor.ty),
                    ));
                }
            }
            DeclKind::Effect(effect) => {
                out.extend(scope.entry(&effect.name.text, decl.span, &Written::Form("effect")));
                for operation in &effect.operations {
                    out.extend(scope.entry(
                        &operation.name.text,
                        operation.span,
                        &Written::Ty(&operation.ty),
                    ));
                }
            }
            DeclKind::Resource(resource) => {
                out.extend(scope.entry(&resource.name.text, decl.span, &Written::Form("resource")));
                members(&resource.members, scope, out);
            }
            DeclKind::Class(class) => {
                let word = if class.instance { "instance" } else { "class" };
                out.extend(
                    class
                        .name
                        .iter()
                        .filter_map(|it| scope.entry(&it.text, decl.span, &Written::Form(word))),
                );
                members(&class.members, scope, out);
            }
            DeclKind::Module(module) => {
                let word = if module.signature {
                    "module type"
                } else {
                    "module"
                };
                out.extend(scope.entry(&module.name.text, decl.span, &Written::Form(word)));
                members(&module.members, &scope.inside(&module.name.text), out);
            }
            // Группа взаимной рекурсии квалификации не добавляет: её члены
            // стоят на том же уровне, что и она сама (§4.8).
            DeclKind::Mutual(group) => members(group, scope, out),
            DeclKind::Clauses { .. }
            | DeclKind::Import(_)
            | DeclKind::Fixity(_)
            | DeclKind::Export(_) => {}
        }
    }
}
