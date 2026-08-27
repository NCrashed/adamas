//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use adamas_core::check::TypeError;
use adamas_core::source::{Location, SourceFile, Span};
use anyhow::Context as _;
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(name = "adamas", version, about = "Adamas compiler driver", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Разобрать исходник, элаборировать и проверить типы (§7.1).
    Check {
        /// Путь к файлу `.adamas`.
        path: PathBuf,
    },
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().command {
        Command::Check { path } => check(&path),
    }
}

fn check(path: &Path) -> anyhow::Result<()> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("не удалось прочитать {}", path.display()))?;
    let file = SourceFile::new(path.display().to_string(), text);

    // Текст → дерево. Ошибка лексики, layout'а и разбора несёт спан.
    let module = match adamas_parser::parse(file.text()) {
        Ok(module) => module,
        Err(error) => anyhow::bail!("{}", report(&file, error.span(), &error.to_string())),
    };

    // Дерево → термы ядра и следом проверка типов: элаборация не в TCB, она
    // отдаёт терм, а корректность его устанавливает `check` (§3).
    let signature = match adamas_elab::elaborate(&module) {
        Ok(signature) => signature,
        Err(error) => {
            let mut message = report(&file, error.span(), &error.to_string());
            if let Some(core) = error.core() {
                message.push_str(&explain(core));
            }
            anyhow::bail!("{message}")
        }
    };

    println!("{}: проверено, объявлений {}", file.name(), signature.len());
    Ok(())
}

/// Телескоп и маршрут отказа ядра.
///
/// Ядро отдаёт их значениями - `Term`, кратности, кадры (§10 вопрос 49а), - а
/// строку из них делает эта функция: рендеринг живёт вне ядра.
///
/// Телескоп показывается всегда: связывания, введённые проверкой, автору
/// иначе неоткуда взять - в тексте на месте отказа видно только имя. Маршрут
/// показывается тоже, и в первую очередь затем, что объясняет, **почему**
/// подчёркнуто именно это место; когда маршрут ушёл в структуру, порождённую
/// элаборацией, подчёркнуто объявление целиком, и маршрут - единственное, что
/// говорит, куда внутри него смотреть.
fn explain(error: &TypeError) -> String {
    let mut out = String::new();
    let context = error.context();
    if !context.is_empty() {
        out.push_str("\n  в контексте:");
        for (depth, binding) in context.iter().enumerate() {
            // Имя `_` носят связывания, которых автор не называл: аргумент
            // безымянной стрелки, поле конструктора. Различить их можно только
            // позицией, и она же связывает строку с индексом в терме.
            let name = if &*binding.name == "_" {
                format!("#{}", context.len() - depth - 1)
            } else {
                binding.name.to_string()
            };
            let _ = write!(out, "\n    ({} {name} : {})", binding.mult, binding.ty);
        }
    }
    let route: Vec<String> = error.path().map(|frame| frame.to_string()).collect();
    if !route.is_empty() {
        let _ = write!(out, "\n  путь: {}", route.join(" → "));
    }
    out
}

/// Сообщение с позицией и строкой исходника.
fn report(file: &SourceFile, span: Span, message: &str) -> String {
    let Some(Location { line, column }) = file.location(span.start()) else {
        return format!("{}: {message}", file.name());
    };
    let source = file.line_text(line).unwrap_or_default();
    let width = span
        .len()
        .max(1)
        .min(source.chars().count().saturating_sub(column - 1).max(1));
    format!(
        "{}:{line}:{column}: {message}\n  {source}\n  {}{}",
        file.name(),
        " ".repeat(column - 1),
        "^".repeat(width),
    )
}
