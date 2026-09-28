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

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

use adamas_core::check::{Frame, TypeError};
use adamas_core::level::{Level, LevelMeta};
use adamas_core::pattern::PatternError;
use adamas_core::row::{Row, RowMeta, Tail};
use adamas_core::source::{Location, SourceFile, Span};
use adamas_core::term::{Args, Binder, Case, Fields, Index, Name, Term, TermMeta};

use crate::diag::{Diagnostic, Related};
use crate::error::{ElabError, Names};

/// Сообщение целиком: позиция, строка исходника с подчёркиванием, телескоп и
/// путь до места отказа.
///
/// Части собирает [`Diagnostic`], печатает - [`Diagnostic::rendered`]: тот же
/// текст уходит в редактор, и собран он обязан быть один раз.
#[must_use]
pub fn report(file: &SourceFile, error: &ElabError) -> String {
    Diagnostic::of_error(error).rendered(file)
}

/// Хвост сообщения: телескоп точки отказа и пройденный путь. Пуст, если
/// отказало не ядро.
pub(crate) fn detail(error: &ElabError) -> String {
    error.core().map_or_else(String::new, |core| {
        explain(core, error.names().unwrap_or(&Names::default()))
    })
}

/// Прочие места того же отказа.
pub(crate) fn related(error: &ElabError) -> Vec<Related> {
    match error {
        ElabError::DetachedSignature { signature, .. } => vec![Related {
            span: *signature,
            message: "сигнатура написана здесь".to_owned(),
        }],
        _ => Vec::new(),
    }
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

/// Первая строка сообщения - та, что стоит после позиции. У отказа ядра она
/// собирается заново: с именами и локальными номерами дырок.
pub(crate) fn headline(error: &ElabError) -> String {
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
/// **почему** подчёркнуто именно это место, - в тех кадрах, у которых есть имя
/// (см. [`route`]).
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

/// Маршрут словами - только кадры, у которых есть имя.
///
/// Номер члена и номер конструктора заменяются именами: ядру они не нужны, а
/// читателю номер не говорит ничего.
///
/// Анонимные кадры - тело лямбды, аргумент применения, номер ветви - позиции
/// в терме ядра, а не в тексте: лямбд параметров клаузы и неявных аргументов
/// автор не писал, а ветвь нумеруется по конструктору. Место они уточняли,
/// пока каретка была грубой; перевод маршрута в спан делает это сам, и в
/// тексте они оставались пересказом элаборатора (§10 вопрос 217). Остаётся
/// то, чего каретка не передаёт: отказ в типе, а не в теле, и в каком
/// конструкторе. Одиночное «тело `f`» - то же, что файл и строка, и не
/// печатается.
///
/// Номер конструктора считается **внутри** члена, поэтому пройденный член
/// запоминается: маршрут идёт снаружи внутрь, и `MemberType` приходит раньше
/// своего `Constructor`.
fn route(error: &TypeError, names: &Names) -> Vec<String> {
    let mut member = None;
    let mut only_body = true;
    let steps: Vec<String> = error
        .path()
        .filter_map(|frame| {
            if let Frame::MemberType(index) | Frame::MemberBody(index) = frame {
                member = Some(index);
            }
            let found = step(frame, member, names)?;
            only_body &= matches!(frame, Frame::MemberBody(_));
            Some(found)
        })
        .collect();
    if only_body && steps.len() <= 1 {
        return Vec::new();
    }
    steps
}

/// Один кадр словами; кадра без имени в тексте нет.
fn step(frame: Frame, member: Option<u32>, names: &Names) -> Option<String> {
    match frame {
        Frame::MemberType(index) => names.member(index).map(|name| format!("тип `{name}`")),
        Frame::MemberBody(index) => names.member(index).map(|name| format!("тело `{name}`")),
        Frame::Constructor(index) => member
            .and_then(|member| names.constructor(member, index))
            .map(|name| format!("{} `{name}`", names.inner())),
        _ => None,
    }
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
    /// Дырки термов - в том же счёте, но нумеруются при печати: у них свой
    /// ряд идентификаторов, и общий ключ смешал бы дырку терма с дыркой
    /// уровня.
    holes: RefCell<HashMap<u32, u32>>,
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
            holes: RefCell::default(),
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
        let (terms, levels, metas, rows) = kind.parts_mut();
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
            push(&mut ordered, meta.0);
        }
        for row in &*rows {
            collect_row(row, &mut ordered);
        }
        for meta in ordered {
            let next = u32::try_from(self.metas.len()).unwrap_or(u32::MAX);
            self.metas.entry(meta).or_insert(next);
        }

        let (terms, levels, metas, rows) = kind.parts_mut();
        for term in terms {
            self.term(term, &mut Vec::new(), 0);
        }
        for level in levels {
            self.level(level);
        }
        for meta in metas {
            *meta = LevelMeta(self.metas.get(&meta.0).copied().unwrap_or(meta.0));
        }
        for row in rows {
            *row = self.row(row, &mut Vec::new(), 0);
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
                let rebuilt = self.fields(fields, bound, outer);
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
                *term = Term::Const(name, Rc::from([]), Args::none());
            }
            // Сорт `Effect` своего имени не имеет: ни имён, ни уровней.
            Term::EffectKind | Term::Prim(_) => {}
            Term::Universe(level) | Term::RowKind(level) => self.level(level),
            Term::Const(_, levels, args) => {
                *levels = self.levels(levels);
                // Нулевые уровни - то, что автор и написал бы, если бы писал
                // уровни: `List{0} Int32` пересказывает инстанциацию, а не
                // программу. Ненулевой или невыведенный показывается весь -
                // там уровень и есть то, что не сошлось (§10 вопрос 217).
                if levels.iter().all(|level| *level == Level::Zero) {
                    *levels = Rc::from([]);
                }
                *args = Args::new(
                    args.row_args()
                        .iter()
                        .map(|row| self.row(row, bound, outer))
                        .collect::<Vec<_>>(),
                    args.mult_args().to_vec(),
                );
            }
            // Дырка, применённая к переменным, - это дырка в контексте места,
            // где её завели: спайн пересказывает контекст, который напечатан
            // ниже, и `(?542) ds b ds x i` читается как выражение программы
            // (§10 вопрос 217). Печатается она одним номером.
            Term::App(..) if contextual(term).is_some() => {
                let meta = contextual(term).unwrap_or(TermMeta(0));
                *term = Term::Meta(self.hole(meta));
            }
            Term::App(callee, argument) => {
                self.term(Rc::make_mut(callee), bound, outer);
                self.term(Rc::make_mut(argument), bound, outer);
            }
            Term::Meta(meta) => *term = Term::Meta(self.hole(*meta)),
            Term::Lam(_, name, body) => {
                let name = name.clone();
                self.under(bound, name, |naming, bound| {
                    naming.term(Rc::make_mut(body), bound, outer);
                });
            }
            // Аргументы меток row стоят под связыванием стрелки наравне с
            // кодоменом, поэтому и имена им раздаются там же: иначе `{Alloc r}`
            // печаталось бы чужим именем.
            Term::Pi(Binder { .. }, name, domain, row, codomain) => {
                self.term(Rc::make_mut(domain), bound, outer);
                let name = name.clone();
                self.under(bound, name, |naming, bound| {
                    *row = naming.row(row, bound, outer);
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

    /// Локальный номер дырки терма - в порядке печати, после дырок уровней.
    fn hole(&self, meta: TermMeta) -> TermMeta {
        let mut holes = self.holes.borrow_mut();
        let next = u32::try_from(self.metas.len() + holes.len()).unwrap_or(u32::MAX);
        TermMeta(*holes.entry(meta.0).or_insert(next))
    }

    fn under(&self, bound: &mut Vec<Name>, name: Name, body: impl FnOnce(&Self, &mut Vec<Name>)) {
        bound.push(name);
        body(self, bound);
        bound.pop();
    }

    /// Телескоп полей: тип следующего стоит под предыдущими, поэтому глубина
    /// растёт вместе с ними. Хвост при этом стоит на исходной: открытый ряд
    /// зависимостей не имеет (§4.2).
    fn fields(&self, fields: &Fields, bound: &mut Vec<Name>, outer: usize) -> Fields {
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
        Fields {
            fields: written.into(),
            tail,
        }
    }

    /// Row с локализованными номерами - и в аргументах меток, и в хвосте.
    fn row(&self, row: &Row<Term>, bound: &mut Vec<Name>, outer: usize) -> Row<Term> {
        let mapped = row.map(|argument| {
            let mut argument = argument.clone();
            self.term(&mut argument, bound, outer);
            argument
        });
        let tail = match mapped.tail() {
            Some(Tail::Meta(RowMeta(meta))) => Some(Tail::Meta(RowMeta(
                self.metas.get(&meta).copied().unwrap_or(meta),
            ))),
            other => other,
        };
        Row::closing(mapped.labels().iter().cloned(), tail)
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
fn collect_term(term: &Term, ordered: &mut Vec<u32>) {
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
        Term::Var(_) | Term::Meta(_) | Term::EffectKind | Term::Prim(_) => {}
        Term::Universe(level) | Term::RowKind(level) => collect_level(level, ordered),
        Term::Const(_, levels, _) => {
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
            collect_row(row, ordered);
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

/// Дырки row: аргументы меток термами, хвост - своим номером.
///
/// Счётчик хранилища один на все сорта, поэтому номер дырки-row с номером
/// дырки уровня не столкнётся, и локализовать их можно вместе.
fn collect_row(row: &Row<Term>, ordered: &mut Vec<u32>) {
    for argument in row.labels().iter().flat_map(|label| &label.arguments) {
        collect_term(argument, ordered);
    }
    if let Some(Tail::Meta(RowMeta(meta))) = row.tail() {
        push(ordered, meta);
    }
}

fn collect_level(level: &Level, ordered: &mut Vec<u32>) {
    match level {
        Level::Meta(meta) => push(ordered, meta.0),
        Level::Succ(inner) => collect_level(inner, ordered),
        Level::Max(left, right) => {
            collect_level(left, ordered);
            collect_level(right, ordered);
        }
        Level::Zero | Level::Var(_) => {}
    }
}

fn push(ordered: &mut Vec<u32>, meta: u32) {
    if !ordered.contains(&meta) {
        ordered.push(meta);
    }
}

/// Поле записи с переписанным типом - именование его не трогает.
fn renamed(field: &adamas_core::term::Field, ty: Term) -> adamas_core::term::Field {
    adamas_core::term::Field {
        name: Rc::clone(&field.name),
        mult: field.mult,
        shape: field.shape,
        ty: Rc::new(ty),
    }
}

/// Дырка, применённая к одним переменным: её спайн - контекст места, где её
/// завели.
fn contextual(term: &Term) -> Option<TermMeta> {
    match term {
        Term::App(callee, argument) if matches!(**argument, Term::Var(_)) => contextual(callee),
        Term::Meta(meta) => Some(*meta),
        _ => None,
    }
}
