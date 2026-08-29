//! Отказ в текст, который читает автор программы.
//!
//! Ядро отдаёт отказ значениями - термы, кратности, телескоп, кадры (§10
//! вопрос 49а), - и печатает их аварийным принтером на индексах де Брёйна: он
//! рассчитан на снапшоты уровня ядра, где имён взять неоткуда. Здесь из тех же
//! значений собирается сообщение человеку, и разница ровно в двух вещах.
//!
//! **Переменные названы.** Индекс `#1` в тексте связать с телескопом читатель
//! может только счётом, а имена в телескопе уже есть - и связывания самого
//! терма их несут тоже. Подстановка идёт по стеку: имена, введённые внутри
//! терма, ближе, чем телескоп вокруг него.
//!
//! **Дырки перенумерованы локально.** Идентификатор дырки сквозной по прогону,
//! поэтому `?5` в сообщении зависит от того, сколько дырок завели соседние
//! объявления. Правка соседа сдвигала бы номер, а с ним и снапшот, ничего не
//! говоря о самой ошибке.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

use adamas_core::check::{Frame, TypeError};
use adamas_core::level::{Level, LevelMeta};
use adamas_core::pattern::PatternError;
use adamas_core::source::{Location, SourceFile, Span};
use adamas_core::term::{Binder, Case, Fields, Index, Name, Term};

use crate::error::{ElabError, Names};

/// Сообщение целиком: позиция, строка исходника с подчёркиванием, телескоп и
/// путь до места отказа.
#[must_use]
pub fn report(file: &SourceFile, error: &ElabError) -> String {
    let mut out = located(file, error.span(), &message(error));
    if let ElabError::DetachedSignature { signature, .. } = error {
        out.push('\n');
        out.push_str(&located(file, *signature, "сигнатура написана здесь"));
    }
    if let Some(core) = error.core() {
        out.push_str(&explain(core, error.names().unwrap_or(&Names::default())));
    }
    out
}

/// Позиция, строка исходника и подчёркивание под фрагментом.
///
/// Отдельно от [`report`], потому что тем же способом показывается отказ
/// разбора: у него спан есть с самого начала, а ошибка своя.
#[must_use]
pub fn located(file: &SourceFile, span: Span, message: &str) -> String {
    let Some(Location { line, column }) = file.location(span.start()) else {
        return format!("{}: {message}", file.name());
    };
    let source = file.line_text(line).unwrap_or_default();
    // Ширина - в символах: спан меряется байтами, а колонка и отступ под
    // кареткой - скалярами Unicode, и на юникодном имени каретки уезжали
    // вправо.
    let width = file
        .snippet(span)
        .map_or(1, |text| text.chars().count())
        .max(1);
    let (source, column, width) = clip(source, column, width);
    format!(
        "{}:{line}:{column}: {message}\n  {source}\n  {}{}",
        file.name(),
        " ".repeat(column - 1),
        "^".repeat(width),
    )
}

/// Текст отказа. У отказа ядра он собирается заново - с именами и локальными
/// номерами дырок.
fn message(error: &ElabError) -> String {
    match error.core() {
        Some(core) => {
            let mut kind = core.kind.clone();
            let mut naming = Naming::of(core);
            naming.rewrite(&mut kind);
            match error {
                // Сборка клауз оборачивает отказ ядра своей фразой, и она
                // остаётся: споткнулась на типе именно она.
                ElabError::Clauses { error, .. }
                    if matches!(**error, PatternError::IllTypedType { .. }) =>
                {
                    format!("тип определения не является типом: {kind}")
                }
                _ => kind.to_string(),
            }
        }
        None => error.to_string(),
    }
}

/// Телескоп точки отказа и пройденный путь.
///
/// Телескоп показывается всегда: связывания, введённые проверкой, автору иначе
/// неоткуда взять - в тексте на месте отказа видно только имя. Путь объясняет,
/// **почему** подчёркнуто именно это место, и когда маршрут уходит в структуру,
/// порождённую элаборацией, он остаётся единственным указанием, куда смотреть.
fn explain(error: &TypeError, names: &Names) -> String {
    let mut out = String::new();
    let naming = Naming::of(error);
    let context = error.context();
    if !context.is_empty() {
        out.push_str("\n  в контексте:");
        for (depth, binding) in context.iter().enumerate() {
            let index = context.len() - depth - 1;
            let mut ty = binding.ty.clone();
            // Типы телескопа прочитаны обратно в контексте целиком, а не
            // каждый в своём начале: индекс в них тот же, что и в термах
            // сообщения.
            naming.term(&mut ty, &mut Vec::new(), 0);
            let _ = write!(
                out,
                "\n    ({} {} : {ty})",
                binding.mult,
                naming.local(index)
            );
        }
    }
    let route = route(error, names);
    if !route.is_empty() {
        let _ = write!(out, "\n  путь: {}", route.join(" -> "));
    }
    out
}

/// Маршрут словами.
///
/// Номер члена и номер конструктора заменяются именами: ядру они не нужны, а
/// читателю номер не говорит ничего - тем более что группа сегодня всегда из
/// одного члена, и «#0» в ней постоянно.
///
/// Номер конструктора считается **внутри** члена, поэтому пройденный член
/// запоминается: маршрут идёт снаружи внутрь, и `MemberType` приходит раньше
/// своего `Constructor`.
fn route(error: &TypeError, names: &Names) -> Vec<String> {
    let mut member = None;
    error
        .path()
        .map(|frame| {
            if let Frame::MemberType(index) | Frame::MemberBody(index) = frame {
                member = Some(index);
            }
            step(frame, member, names)
        })
        .collect()
}

/// Один кадр словами; имени нет - остаётся номер, который знает ядро.
fn step(frame: Frame, member: Option<u32>, names: &Names) -> String {
    let found = match frame {
        Frame::MemberType(index) => names.member(index).map(|name| format!("тип `{name}`")),
        Frame::MemberBody(index) => names.member(index).map(|name| format!("тело `{name}`")),
        Frame::Constructor(index) => member
            .and_then(|member| names.constructor(member, index))
            .map(|name| format!("конструктор `{name}`")),
        _ => None,
    };
    found.unwrap_or_else(|| frame.to_string())
}

/// Окно вокруг подчёркнутого фрагмента.
///
/// Строка бывает любой длины - спайн применения в тысячу аргументов пишется в
/// одну, - и печатать её целиком значит спрятать сообщение под ней.
fn clip(source: &str, column: usize, width: usize) -> (String, usize, usize) {
    const WINDOW: usize = 100;
    let chars: Vec<char> = source.chars().collect();
    if chars.len() <= WINDOW {
        return (
            source.to_owned(),
            column,
            width.min(chars.len() + 1 - column),
        );
    }
    let start = column.saturating_sub(WINDOW / 2).min(chars.len() - WINDOW);
    let end = (start + WINDOW).min(chars.len());
    let mut clipped = String::new();
    if start > 0 {
        clipped.push_str("...");
    }
    clipped.extend(&chars[start..end]);
    if end < chars.len() {
        clipped.push_str("...");
    }
    let shift = if start > 0 { start - 3 } else { 0 };
    (clipped, column - shift, width.min(end + 1 - column))
}

/// Имена телескопа и локальные номера дырок для одного сообщения.
struct Naming {
    /// Имена связываний телескопа, изнутри наружу: индекс де Брёйна - позиция.
    context: Vec<Name>,
    /// Дырка в порядке первой встречи.
    metas: HashMap<u32, u32>,
}

impl Naming {
    fn of(error: &TypeError) -> Self {
        let context = error.context();
        let mut names: Vec<Name> = Vec::with_capacity(context.len());
        for (depth, binding) in context.iter().enumerate().rev() {
            let index = context.len() - depth - 1;
            // Имя, которого автор не писал, остаётся индексом: `_` не
            // отличает одно связывание от другого (§10 вопрос 69). Повтор
            // имени - тоже: заслонённое видно по индексу.
            let taken = names.iter().any(|earlier| **earlier == *binding.name);
            names.push(if &*binding.name == "_" || taken {
                Name::from(format!("#{index}").as_str())
            } else {
                Rc::clone(&binding.name)
            });
        }
        Self {
            context: names,
            metas: HashMap::new(),
        }
    }

    /// Имя связывания телескопа по индексу де Брёйна.
    fn local(&self, index: usize) -> Name {
        self.context
            .get(index)
            .cloned()
            .unwrap_or_else(|| Name::from(format!("#{index}").as_str()))
    }

    /// Подставляет имена и локальные номера во все части сообщения.
    fn rewrite(&mut self, kind: &mut adamas_core::error::ErrorKind) {
        let (terms, levels, metas) = kind.parts_mut();
        // Части одного сообщения нумеруются вместе: `?0` в ожидаемом типе и
        // `?0` в полученном - одна дырка.
        let mut ordered = Vec::new();
        for term in terms {
            collect_term(term, &mut ordered);
        }
        for level in &*levels {
            collect_level(level, &mut ordered);
        }
        for meta in &*metas {
            push(&mut ordered, **meta);
        }
        for meta in ordered {
            let next = u32::try_from(self.metas.len()).unwrap_or(u32::MAX);
            self.metas.entry(meta.0).or_insert(next);
        }

        let (terms, levels, metas) = kind.parts_mut();
        for term in terms {
            self.term(term, &mut Vec::new(), 0);
        }
        for level in levels {
            self.level(level);
        }
        for meta in metas {
            *meta = LevelMeta(self.metas.get(&meta.0).copied().unwrap_or(meta.0));
        }
    }

    /// Переменные терма - именами, дырки - локальными номерами.
    ///
    /// `bound` - имена связываний, введённых внутри самого терма; они ближе
    /// телескопа. `outer` - сколько связываний телескопа стоит под термом: у
    /// типа из телескопа это его собственная позиция, у терма сообщения - ноль.
    fn term(&self, term: &mut Term, bound: &mut Vec<Name>, outer: usize) {
        match term {
            // Ряд и запись переписываются одинаково, но **собираются каждый
            // своим узлом**: `Row` - значение сорта `Row ℓ`, и назвать его
            // записью значит соврать о том, что не сошлось. Хвост при этом
            // стоит на исходной глубине, а не под полями: открытый ряд
            // зависимостей не имеет (§4.2).
            Term::Record(fields) | Term::Row(fields) => {
                let mut written = Vec::with_capacity(fields.len());
                for (index, field) in fields.iter().enumerate() {
                    let mut ty = field.ty.as_ref().clone();
                    self.term(&mut ty, bound, outer + index);
                    written.push(renamed(field, ty));
                }
                let tail = fields.tail.as_ref().map(|tail| {
                    let mut tail = tail.as_ref().clone();
                    self.term(&mut tail, bound, outer);
                    Rc::new(tail)
                });
                let rebuilt = Fields {
                    fields: written.into(),
                    tail,
                };
                *term = match term {
                    Term::Row(_) => Term::Row(rebuilt),
                    _ => Term::Record(rebuilt),
                };
            }
            Term::Object(fields) => {
                let mut written = Vec::with_capacity(fields.len());
                for (name, value) in fields.iter() {
                    let mut value = value.as_ref().clone();
                    self.term(&mut value, bound, outer);
                    written.push((Rc::clone(name), Rc::new(value)));
                }
                *term = Term::Object(written.into());
            }
            Term::With(base, fields) => {
                let mut inner = base.as_ref().clone();
                self.term(&mut inner, bound, outer);
                *base = Rc::new(inner);
                let mut written = Vec::with_capacity(fields.len());
                for (name, value) in fields.iter() {
                    let mut value = value.as_ref().clone();
                    self.term(&mut value, bound, outer);
                    written.push((Rc::clone(name), Rc::new(value)));
                }
                *fields = written.into();
            }
            Term::Project(record, _) => {
                let mut inner = record.as_ref().clone();
                self.term(&mut inner, bound, outer);
                *record = Rc::new(inner);
            }
            Term::Var(Index(index)) => {
                let index = *index as usize;
                let name = match bound.len().checked_sub(index + 1) {
                    Some(position) => bound[position].clone(),
                    None => self.local(index - bound.len() + outer),
                };
                *term = Term::Const(name, Rc::from([]));
            }
            // Дырка своего имени не имеет и переименованию не подлежит:
            // печатается она номером, а номер локализует `Naming` отдельно.
            Term::Meta(_) => {}
            Term::Universe(level) | Term::RowKind(level) => self.level(level),
            Term::Const(_, levels) => *levels = self.levels(levels),
            Term::App(callee, argument) => {
                self.term(Rc::make_mut(callee), bound, outer);
                self.term(Rc::make_mut(argument), bound, outer);
            }
            Term::Lam(_, name, body) => {
                let name = name.clone();
                self.under(bound, name, |naming, bound| {
                    naming.term(Rc::make_mut(body), bound, outer);
                });
            }
            // Аргументы меток row стоят под тем же контекстом, что домен:
            // связывание `Pi` вводится только для кодомена.
            Term::Pi(Binder { .. }, name, domain, row, codomain) => {
                self.term(Rc::make_mut(domain), bound, outer);
                *row = row.map(|argument| {
                    let mut argument = argument.clone();
                    self.term(&mut argument, bound, outer);
                    argument
                });
                let name = name.clone();
                self.under(bound, name, |naming, bound| {
                    naming.term(Rc::make_mut(codomain), bound, outer);
                });
            }
            Term::Let(_, name, ty, value, body) => {
                self.term(Rc::make_mut(ty), bound, outer);
                self.term(Rc::make_mut(value), bound, outer);
                let name = name.clone();
                self.under(bound, name, |naming, bound| {
                    naming.term(Rc::make_mut(body), bound, outer);
                });
            }
            Term::Case(case) => {
                let case: &mut Case = Rc::make_mut(case);
                case.levels = self.levels(&case.levels);
                self.term(Rc::make_mut(&mut case.scrutinee), bound, outer);
                self.term(Rc::make_mut(&mut case.motive), bound, outer);
                for branch in &mut case.branches {
                    self.term(Rc::make_mut(&mut branch.body), bound, outer);
                }
            }
        }
    }

    fn under(&self, bound: &mut Vec<Name>, name: Name, body: impl FnOnce(&Self, &mut Vec<Name>)) {
        bound.push(name);
        body(self, bound);
        bound.pop();
    }

    fn levels(&self, levels: &Rc<[Level]>) -> Rc<[Level]> {
        levels
            .iter()
            .map(|level| {
                let mut level = level.clone();
                self.level(&mut level);
                level
            })
            .collect()
    }

    fn level(&self, level: &mut Level) {
        match level {
            Level::Meta(meta) => {
                *meta = LevelMeta(self.metas.get(&meta.0).copied().unwrap_or(meta.0));
            }
            Level::Succ(inner) => self.level(Rc::make_mut(inner)),
            Level::Max(left, right) => {
                self.level(Rc::make_mut(left));
                self.level(Rc::make_mut(right));
            }
            Level::Zero | Level::Var(_) => {}
        }
    }
}

/// Дырки терма в порядке появления в тексте.
fn collect_term(term: &Term, ordered: &mut Vec<LevelMeta>) {
    match term {
        Term::Record(fields) | Term::Row(fields) => {
            for field in fields.iter() {
                collect_term(&field.ty, ordered);
            }
            if let Some(tail) = &fields.tail {
                collect_term(tail, ordered);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                collect_term(value, ordered);
            }
        }
        Term::With(base, fields) => {
            collect_term(base, ordered);
            for (_, value) in fields.iter() {
                collect_term(value, ordered);
            }
        }
        Term::Project(record, _) => collect_term(record, ordered),
        // Дырка терма своих уровней не носит: они в её типе, а он живёт
        // отдельно.
        Term::Var(_) | Term::Meta(_) => {}
        Term::Universe(level) | Term::RowKind(level) => collect_level(level, ordered),
        Term::Const(_, levels) => {
            for level in levels.iter() {
                collect_level(level, ordered);
            }
        }
        Term::App(left, right) => {
            collect_term(left, ordered);
            collect_term(right, ordered);
        }
        Term::Lam(_, _, body) => collect_term(body, ordered),
        Term::Pi(_, _, domain, row, codomain) => {
            collect_term(domain, ordered);
            collect_term(codomain, ordered);
            for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                collect_term(argument, ordered);
            }
        }
        Term::Let(_, _, ty, value, body) => {
            collect_term(ty, ordered);
            collect_term(value, ordered);
            collect_term(body, ordered);
        }
        Term::Case(case) => {
            for level in case.levels.iter() {
                collect_level(level, ordered);
            }
            collect_term(&case.scrutinee, ordered);
            collect_term(&case.motive, ordered);
            for branch in &case.branches {
                collect_term(&branch.body, ordered);
            }
        }
    }
}

fn collect_level(level: &Level, ordered: &mut Vec<LevelMeta>) {
    match level {
        Level::Meta(meta) => push(ordered, *meta),
        Level::Succ(inner) => collect_level(inner, ordered),
        Level::Max(left, right) => {
            collect_level(left, ordered);
            collect_level(right, ordered);
        }
        Level::Zero | Level::Var(_) => {}
    }
}

fn push(ordered: &mut Vec<LevelMeta>, meta: LevelMeta) {
    if !ordered.contains(&meta) {
        ordered.push(meta);
    }
}

/// Поле записи с переписанным типом - именование его не трогает.
fn renamed(field: &adamas_core::term::Field, ty: Term) -> adamas_core::term::Field {
    adamas_core::term::Field {
        name: Rc::clone(&field.name),
        mult: field.mult,
        ty: Rc::new(ty),
    }
}
