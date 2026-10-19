//! `adamas repl`: строка за строкой, ответ машиной (§7.1).
//!
//! # Сессия - накопленный текст
//!
//! Сессия есть текст файла: загруженный исходник и следом всё принятое из
//! ввода. Ввод, который разбирается объявлениями, дописывается к тексту, если
//! текст **целиком** после этого проходит проверку; иначе отказ печатается, а
//! текст остаётся прежним. Прочий ввод - выражение: оно вычисляется временным
//! определением `it` в конце текста и в текст не попадает.
//!
//! Каждый ввод проходит программу заново, вместе с прелюдией: элаборация не
//! инкрементальна, и сессия этим расплачивается - около 0,1 с на ввод в
//! release-сборке. Взамен у сессии нет своей семантики: что принято в ней, то
//! принято и файлом из того же текста - ordered scoping (§4.8), импорт посреди
//! текста, отказ повторного объявления. Последний виден сильнее всего:
//! переобъявить имя, как в `GHCi`, нельзя.
//!
//! # Выражение
//!
//! `it : _` и тело выражением. Если так не проходит, а программа подключила
//! `Std.IO`, пробуется `it : {Console, Files, Foreign} _`, и тогда вход
//! исполняется под `Std.IO.run` - так же, как `main` у `adamas eval`. Отказ
//! печатается от первой, чистой попытки: вторая только догадка.
//!
//! Предупреждений сессия не печатает. Половина их здесь ложна: имя, только что
//! импортированное, «нигде не употребляется», а литерал `1 + 2` берёт
//! умолчание на каждом вводе. Полный их список даёт `adamas check`.
//!
//! # Где отказ
//!
//! Место отказа называется в строках **ввода**, а не накопленного текста:
//! строка 40 сессии человеку ничего не говорит. Выражение в тексте стоит под
//! `it =` со сдвигом на два пробела, и позиция пересчитывается обратно.

use std::io::{BufRead as _, IsTerminal as _};
use std::path::{Path, PathBuf};

use adamas_core::sig::Signature;
use adamas_core::source::{SourceFile, Span};
use adamas_core::term::PRINT_DEPTH;
use adamas_elab::program::{Program, Sources};

/// Приглашение к вводу и к продолжению.
const PROMPT: &str = "λ> ";
const MORE: &str = " | ";

/// Сдвиг строк выражения под `it =`.
const INDENT: usize = 2;

/// Row второй попытки: метки, которые гасит `Std.IO.run`.
const IO_ROW: &str = "{Std.IO.Console, Std.IO.Files, Std.IO.Foreign} _";

/// Сессия: откуда модули, с чем линковать, накопленный текст.
struct Session {
    /// Откуда подключаются модули.
    sources: Box<dyn Sources>,
    /// Секция `[link]` проекта (§5.3): машина ищет чужие символы там же, где
    /// их найдёт компоновщик.
    link: adamas_pkg::manifest::Link,
    /// Имя, которым подписан текст.
    name: String,
    /// Загруженное: к нему возвращает `:reset`.
    loaded: String,
    /// Текст сессии.
    text: String,
    /// Сигнатура принятого текста.
    signature: Signature,
}

/// Ввод на своём месте в тексте: по нему позиция отказа идёт обратно.
struct Placed {
    /// Текст сессии вместе с вводом.
    text: String,
    /// Где в нём начинается первая строка ввода.
    start: usize,
    /// На сколько сдвинута каждая строка.
    indent: usize,
    /// Ввод как написан; каждая строка с переводом.
    input: String,
}

impl Placed {
    /// Смещение в тексте - смещение во вводе. `None` - место до ввода.
    fn back(&self, offset: usize) -> Option<usize> {
        let mut placed = self.start;
        let mut written = 0;
        for line in self.input.split_inclusive('\n') {
            let end = placed + self.indent + line.len();
            if offset < end {
                let within = offset.checked_sub(placed)?.saturating_sub(self.indent);
                return Some(written + within);
            }
            placed = end;
            written += line.len();
        }
        (offset >= self.start).then_some(written)
    }

    /// Спан во вводе. `None` - хотя бы край его лежит до ввода.
    fn span(&self, span: Span) -> Option<Span> {
        Some(Span::new(self.back(span.start())?, self.back(span.end())?))
    }
}

/// Что прочитано.
enum Read {
    /// Ввод: строки до конца формы.
    Input(String),
    /// Ввод сброшен - Ctrl-C.
    Dropped,
    /// Конец ввода.
    End,
}

/// Откуда строки: редактор в терминале либо поток как есть.
enum Lines {
    /// Терминал: история, стрелки, поиск.
    Editor(Box<rustyline::DefaultEditor>, Option<PathBuf>),
    /// Не терминал: приглашений нет, строки читаются подряд.
    Plain(std::io::StdinLock<'static>),
}

impl Lines {
    fn opened() -> anyhow::Result<Self> {
        if !std::io::stdin().is_terminal() {
            return Ok(Self::Plain(std::io::stdin().lock()));
        }
        let mut editor = rustyline::DefaultEditor::new()?;
        let history = history();
        if let Some(path) = &history {
            // Истории ещё нет - первый запуск, а не отказ.
            let _ = editor.load_history(path);
        }
        Ok(Self::Editor(Box::new(editor), history))
    }

    /// Строка без перевода. `Ok(None)` - конец ввода, `Err(())` - Ctrl-C.
    fn line(&mut self, prompt: &str) -> anyhow::Result<Result<Option<String>, ()>> {
        match self {
            Self::Editor(editor, _) => match editor.readline(prompt) {
                Ok(line) => Ok(Ok(Some(line))),
                Err(rustyline::error::ReadlineError::Interrupted) => Ok(Err(())),
                Err(rustyline::error::ReadlineError::Eof) => Ok(Ok(None)),
                Err(error) => Err(error.into()),
            },
            Self::Plain(stdin) => {
                let mut line = String::new();
                if stdin.read_line(&mut line)? == 0 {
                    return Ok(Ok(None));
                }
                let trimmed = line.trim_end_matches(['\n', '\r']).len();
                line.truncate(trimmed);
                Ok(Ok(Some(line)))
            }
        }
    }

    /// Форма целиком: строки, пока ввод не кончен ([`unfinished`]) либо не
    /// пришла пустая строка.
    ///
    /// Команда посреди ввода в несколько строк его кончает и читается
    /// следующей - `held`: `let x = 3`, за которым `:t x`, иначе уходил бы
    /// продолжением выражения. Только строка без отступа: внутри блока строку
    /// вправе начинать оператор `::`.
    fn read(&mut self, held: &mut Option<String>) -> anyhow::Result<Read> {
        let mut input = String::new();
        loop {
            let prompt = if input.is_empty() { PROMPT } else { MORE };
            let line = match held
                .take()
                .map_or_else(|| self.line(prompt), |it| Ok(Ok(Some(it))))?
            {
                Ok(Some(line)) => line,
                Ok(None) if input.is_empty() => return Ok(Read::End),
                Ok(None) => break,
                Err(()) => return Ok(Read::Dropped),
            };
            if line.trim().is_empty() {
                if input.is_empty() {
                    continue;
                }
                break;
            }
            if input.is_empty() && line.trim_start().starts_with(':') {
                input = line;
                break;
            }
            if line.starts_with(':') {
                *held = Some(line);
                break;
            }
            input.push_str(&line);
            input.push('\n');
            if !unfinished(&input, &line) {
                break;
            }
        }
        if let Self::Editor(editor, _) = self {
            let _ = editor.add_history_entry(input.trim_end());
        }
        Ok(Read::Input(input))
    }
}

impl Drop for Lines {
    fn drop(&mut self) {
        if let Self::Editor(editor, Some(path)) = self {
            if let Some(dir) = path.parent() {
                let _ = std::fs::create_dir_all(dir);
            }
            // История - удобство: не записалась, и сессия от этого не хуже.
            let _ = editor.save_history(path);
        }
    }
}

/// Файл истории: `$XDG_STATE_HOME/adamas/history`, по умолчанию под
/// `~/.local/state`.
fn history() -> Option<PathBuf> {
    let state = std::env::var_os("XDG_STATE_HOME")
        .filter(|it| !it.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|it| PathBuf::from(it).join(".local/state")))?;
    Some(state.join("adamas").join("history"))
}

/// Ждёт ли ввод продолжения.
///
/// Четыре случая. Строка с отступом - внутри блока, и конец блока виден
/// только по пустой строке. Последнее объявление - сигнатура: клаузы идут
/// следом. Строка кончается словом, открывающим блок, либо начинается с
/// `let`, чьё тело - на следующей строке: пустой блок разбирается, и
/// разбор их не отличит. Отказ разбора стоит в самом конце ввода: `1 +`.
fn unfinished(input: &str, last: &str) -> bool {
    use adamas_parser::token::TokenKind;

    if last.starts_with([' ', '\t']) {
        return true;
    }
    if let Ok(lexed) = adamas_parser::lexer::lex(last) {
        let kinds: Vec<TokenKind> = lexed
            .tokens
            .iter()
            .map(|it| it.kind)
            .filter(|it| *it != TokenKind::Eof)
            .collect();
        let opens = matches!(
            kinds.last(),
            Some(
                TokenKind::Where
                    | TokenKind::With
                    | TokenKind::Of
                    | TokenKind::Mutual
                    | TokenKind::Let
                    | TokenKind::Then
                    | TokenKind::Else
                    | TokenKind::Equals
                    | TokenKind::Arrow
            )
        );
        if opens || kinds.first() == Some(&TokenKind::Let) {
            return true;
        }
    }
    let read = reading(input);
    read.signature || read.refused.is_some_and(|it| it >= input.trim_end().len())
}

/// Выражение определением `name : ty` в конце текста.
fn wrapped(text: &str, input: &str, name: &str, ty: &str) -> Placed {
    let mut placed = joined(text);
    placed.push_str(&[name, " : ", ty, "\n", name, " =\n"].concat());
    let start = placed.len();
    for line in input.lines() {
        placed.push_str(&" ".repeat(INDENT));
        placed.push_str(line);
        placed.push('\n');
    }
    Placed {
        text: placed,
        start,
        indent: INDENT,
        input: normalized(input),
    }
}

/// Текст с пустой строкой в конце: за ней - новое объявление.
fn joined(text: &str) -> String {
    let mut joined = text.to_owned();
    if !joined.is_empty() {
        if !joined.ends_with('\n') {
            joined.push('\n');
        }
        joined.push('\n');
    }
    joined
}

/// Ввод, где каждая строка кончается переводом.
fn normalized(input: &str) -> String {
    input.lines().flat_map(|line| [line, "\n"]).collect()
}

/// Есть ли у прохода отказ.
fn refused(program: &Program) -> bool {
    program.signature.is_none()
        || program
            .diagnostics
            .iter()
            .any(|it| it.diagnostic.severity == adamas_elab::Severity::Error)
}

impl Session {
    /// Сессия над программой по пути, либо пустая над текущим каталогом.
    fn opened(path: Option<&Path>) -> anyhow::Result<Self> {
        let Some(path) = path else {
            let mut session = Self {
                sources: Box::new(adamas_elab::program::Directory::new(Path::new("."))),
                link: adamas_pkg::manifest::Link::default(),
                name: adamas_l10n::tr!("cli-repl-session"),
                loaded: String::new(),
                text: String::new(),
                signature: Signature::default(),
            };
            session.reset()?;
            return Ok(session);
        };
        let opened = crate::project::opened(path)?;
        let text = std::fs::read_to_string(&opened.entry).map_err(|error| {
            anyhow::Error::new(error).context(adamas_l10n::tr!(
                "cli-cannot-read",
                path = opened.entry.display()
            ))
        })?;
        let mut session = Self {
            sources: opened.sources,
            link: opened.link,
            name: opened.entry.display().to_string(),
            loaded: text,
            text: String::new(),
            signature: Signature::default(),
        };
        session.reset()?;
        Ok(session)
    }

    /// Назад к загруженному. Загруженное не проходит - отказ печатается, и
    /// сессия начинается с пустого текста: модули проекта ей по-прежнему видны.
    fn reset(&mut self) -> anyhow::Result<()> {
        let program = self.analyzed(&self.loaded);
        if !refused(&program) {
            self.text.clone_from(&self.loaded);
            self.signature = program.signature.unwrap_or_default();
            return Ok(());
        }
        if !self.loaded.is_empty() {
            eprintln!("{}", rendered(&program, None));
            eprintln!(
                "{}",
                adamas_l10n::tr!("cli-repl-started-empty", name = self.name)
            );
        }
        let program = self.analyzed("");
        let accepted = !refused(&program);
        let Some(signature) = program.signature.filter(|_| accepted) else {
            anyhow::bail!("{}", adamas_l10n::tr!("cli-no-signature", name = self.name));
        };
        self.text.clear();
        self.signature = signature;
        Ok(())
    }

    fn analyzed(&self, text: &str) -> Program {
        let file = SourceFile::new(self.name.clone(), text.to_owned());
        adamas_elab::program::analyze(file, self.sources.as_ref())
    }

    /// Объявления: дописываются, если текст с ними проходит.
    fn declare(&mut self, input: &str) -> Result<(), String> {
        let mut text = joined(&self.text);
        let placed = Placed {
            start: text.len(),
            indent: 0,
            input: normalized(input),
            text: {
                text.push_str(&normalized(input));
                text
            },
        };
        let program = self.analyzed(&placed.text);
        if refused(&program) {
            return Err(rendered(&program, Some(&placed)));
        }
        self.signature = program.signature.unwrap_or_default();
        self.text = placed.text;
        Ok(())
    }

    /// Имя под выражение: `it`, если оно не занято ни текстом, ни самим
    /// вводом - иначе `it` во вводе значило бы само определение.
    fn fresh(&self, input: &str) -> String {
        let written: Vec<&str> = adamas_parser::lexer::lex(input)
            .map(|lexed| {
                lexed
                    .tokens
                    .iter()
                    .filter(|it| it.kind == adamas_parser::token::TokenKind::Ident)
                    .map(|it| &input[it.span.start()..it.span.end()])
                    .collect()
            })
            .unwrap_or_default();
        let mut name = String::from("it");
        while self.signature.lookup(&name).is_some()
            || self.signature.written(&name).is_some()
            || written.contains(&name.as_str())
        {
            name.push('\'');
        }
        name
    }

    /// Выражение, прошедшее проверку: его определение и программа с ним.
    fn checked(&self, input: &str, effects: bool) -> Result<(String, Signature), String> {
        let name = self.fresh(input);
        let placed = wrapped(&self.text, input, &name, "_");
        let program = self.analyzed(&placed.text);
        if !refused(&program) {
            return Ok((name, program.signature.unwrap_or_default()));
        }
        if effects && self.signature.lookup("Std.IO.run").is_some() {
            let io = self.analyzed(&wrapped(&self.text, input, &name, IO_ROW).text);
            if !refused(&io) {
                return Ok((name, io.signature.unwrap_or_default()));
            }
        }
        Err(rendered(&program, Some(&placed)))
    }

    /// Значение выражения. `None` - печатать нечего: ответ - единица.
    fn evaluate(&self, input: &str) -> anyhow::Result<Option<String>> {
        let (name, signature) = self
            .checked(input, true)
            .map_err(|it| anyhow::anyhow!(it))?;
        let entry = crate::project::entry(&signature, &name)?;
        let answer = adamas_interp::run_linked(
            &signature,
            &entry.term,
            adamas_interp::Linkage::new(&self.link.libraries, &self.link.paths),
        )?;
        Ok(entry
            .printed
            .then(|| answer.printed(Some(PRINT_DEPTH)).to_string()))
    }

    /// Тип имени, а если это не имя - выражения.
    ///
    /// Имя - объявленным типом, тем же, что печатает `adamas check --type` и
    /// показывает hover: выражение `map` инстанцировало бы его неявные
    /// параметры дырками.
    fn typed(&self, input: &str) -> anyhow::Result<String> {
        let name = input.trim();
        let resolved = self
            .signature
            .written(name)
            .map_or_else(|| name.to_owned(), ToString::to_string);
        if let Some(shown) = adamas_elab::cursor::described(&self.signature, &resolved) {
            return Ok(shown);
        }
        let (it, signature) = self
            .checked(input, false)
            .map_err(|it| anyhow::anyhow!(it))?;
        let shown = adamas_elab::cursor::described(&signature, &it).unwrap_or_default();
        let ty = shown.split_once(" : ").map_or(shown.as_str(), |(_, ty)| ty);
        Ok(format!("{name} : {ty}"))
    }

    /// Что делать с вводом.
    fn entered(&mut self, input: &str) -> anyhow::Result<Flow> {
        if let Some(command) = input.trim().strip_prefix(':') {
            return self.command(command);
        }
        if declares(input) {
            self.declare(input).map_err(|it| anyhow::anyhow!(it))?;
        } else if let Some(answer) = self.evaluate(input)? {
            println!("{answer}");
        }
        Ok(Flow::Go)
    }

    fn command(&mut self, command: &str) -> anyhow::Result<Flow> {
        let (word, rest) = command
            .split_once(char::is_whitespace)
            .unwrap_or((command, ""));
        let rest = rest.trim();
        match word {
            "q" | "quit" => return Ok(Flow::Stop),
            "h" | "help" | "?" => println!("{}", adamas_l10n::tr!("cli-repl-help")),
            "r" | "reset" => self.reset()?,
            "t" | "type" if !rest.is_empty() => println!("{}", self.typed(rest)?),
            "l" | "load" if !rest.is_empty() => *self = Self::opened(Some(Path::new(rest)))?,
            "t" | "type" | "l" | "load" => {
                anyhow::bail!("{}", adamas_l10n::tr!("cli-repl-argument", command = word));
            }
            _ => anyhow::bail!("{}", adamas_l10n::tr!("cli-repl-unknown", command = word)),
        }
        Ok(Flow::Go)
    }
}

/// Идти дальше или кончить.
enum Flow {
    Go,
    Stop,
}

/// Объявления ли ввод.
///
/// Разбирается объявлениями - объявления. Не разбирается ни так, ни
/// выражением - чьим отказом отвечать, решает место: какой разбор прошёл
/// дальше, тот и имелся в виду. `f x = x +` дальше идёт объявлением, `1 +` -
/// выражением.
fn declares(input: &str) -> bool {
    reading(input).declares
}

/// Как ввод разбирается.
struct Reading {
    /// Объявлениями, а не выражением.
    declares: bool,
    /// Где отказ разбора во вводе. `None` - разобрался.
    refused: Option<usize>,
    /// Последнее объявление - сигнатура без клауз.
    signature: bool,
}

fn reading(input: &str) -> Reading {
    let declared = match adamas_parser::parse(input) {
        Ok(module) => {
            return Reading {
                declares: !module.decls.is_empty(),
                refused: None,
                signature: matches!(
                    module.decls.last().map(|it| &it.kind),
                    Some(adamas_parser::ast::DeclKind::Signature { .. })
                ),
            };
        }
        Err(error) => error.span().start(),
    };
    let placed = wrapped("", input, "it", "_");
    let expressed = match adamas_parser::parse(&placed.text) {
        Ok(_) => None,
        Err(error) => Some(placed.back(error.span().start()).unwrap_or(0)),
    };
    let further = expressed.is_some_and(|it| it < declared);
    Reading {
        declares: further,
        refused: if further { Some(declared) } else { expressed },
        signature: false,
    }
}

/// Отказы прохода, каждый на своём тексте: ввода, если место в нём, иначе -
/// файла, которому принадлежит.
fn rendered(program: &Program, placed: Option<&Placed>) -> String {
    let input = adamas_l10n::tr!("cli-repl-input");
    program
        .diagnostics
        .iter()
        .filter(|it| it.diagnostic.severity == adamas_elab::Severity::Error)
        .map(|located| {
            let moved = placed.filter(|_| located.unit == 0).and_then(|placed| {
                let mut diagnostic = located.diagnostic.clone();
                diagnostic.span = placed.span(diagnostic.span)?;
                for related in &mut diagnostic.related {
                    related.span = placed.span(related.span)?;
                }
                Some(diagnostic.rendered(&SourceFile::new(input.clone(), placed.input.clone())))
            });
            moved.unwrap_or_else(|| program.rendered(located))
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Сессия до конца ввода либо `:quit`.
///
/// # Errors
///
/// Программа по пути не открывается либо терминал не читается. Отказ на
/// вводе сессию не кончает: он печатается, и сессия ждёт следующего.
pub(crate) fn run(path: Option<&Path>) -> anyhow::Result<()> {
    let mut lines = Lines::opened()?;
    if matches!(lines, Lines::Editor(..)) {
        println!(
            "{}",
            adamas_l10n::tr!("cli-repl-banner", version = env!("CARGO_PKG_VERSION"))
        );
    }
    let mut session = Session::opened(path)?;
    let mut held = None;
    loop {
        let input = match lines.read(&mut held)? {
            Read::Input(input) => input,
            Read::Dropped => continue,
            Read::End => return Ok(()),
        };
        match session.entered(&input) {
            Ok(Flow::Go) => {}
            Ok(Flow::Stop) => return Ok(()),
            Err(error) => eprintln!("{}", crate::reported(&error)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_position_in_the_session_maps_back_to_the_input() {
        let placed = wrapped("x : Int\nx = 1\n", "let y = 2\ny + z\n", "it", "_");
        let z = placed.text.rfind('z').expect("z на месте");
        let back = placed.back(z).expect("в пределах ввода");
        assert_eq!(&placed.input[back..=back], "z");
        assert_eq!(placed.back(0), None, "заголовок `it` не ввод");
    }

    #[test]
    fn input_is_read_as_declarations_or_an_expression() {
        assert!(declares("f : Int -> Int\nf x = x\n"));
        assert!(declares("data T = A | B\n"));
        assert!(declares("f x = x +\n"));
        assert!(!declares("1 + 2\n"));
        assert!(!declares("1 +\n"));
        assert!(!declares("map (\\x -> x) [1]\n"));
    }

    #[test]
    fn an_open_form_waits_for_more_lines() {
        assert!(unfinished("f : Int -> Int\n", "f : Int -> Int"));
        assert!(unfinished("case xs of\n", "case xs of"));
        assert!(unfinished("let x = 3\n", "let x = 3"));
        assert!(unfinished("case xs of\n  Nil -> 0\n", "  Nil -> 0"));
        assert!(!unfinished("1 + 2\n", "1 + 2"));
        assert!(!unfinished("f : Int -> Int\nf x = x\n", "f x = x"));
        assert!(unfinished("1 +\n", "1 +"));
        assert!(unfinished("f x =\n", "f x ="));
        assert!(!unfinished("let x = 3\nx * 2\n", "x * 2"));
    }
}
