//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.

use std::path::{Path, PathBuf};

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
        Err(error) => anyhow::bail!("{}", report(&file, error.span(), &error.to_string())),
    };

    println!("{}: проверено, объявлений {}", file.name(), signature.len());
    Ok(())
}

/// Сообщение с позицией и строкой исходника.
///
/// Полноценный рендеринг - отдельный срез: ошибка ядра пока доносит «что», но
/// не «где» внутри объявления (§10 вопрос 49б), поэтому подчёркивается спан
/// того, что элаборировалось, а не подтерма.
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
