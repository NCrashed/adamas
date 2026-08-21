//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только каркас `check`: разбор аргументов, загрузка
//! исходника, вывод.

use std::path::PathBuf;

use adamas_core::source::SourceFile;
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
    /// Загрузить исходник и проверить типы (§7.1).
    ///
    /// В Фазе 0 выполняется только загрузка: type checker — Фаза 1 (§9).
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

fn check(path: &std::path::Path) -> anyhow::Result<()> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("не удалось прочитать {}", path.display()))?;
    let file = SourceFile::new(path.display().to_string(), text);

    println!(
        "{}: {} bytes, {} lines",
        file.name(),
        file.len(),
        file.line_count()
    );
    eprintln!("check: type checker не реализован — Фаза 1 (§9), проверка не выполнена");
    Ok(())
}
