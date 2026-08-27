//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.

use std::path::{Path, PathBuf};

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
        Err(error) => anyhow::bail!(
            "{}",
            adamas_elab::located(&file, error.span(), &error.to_string())
        ),
    };

    // Дерево → термы ядра и следом проверка типов: элаборация не в TCB, она
    // отдаёт терм, а корректность его устанавливает `check` (§3).
    let signature = match adamas_elab::elaborate(&module) {
        Ok(signature) => signature,
        Err(error) => anyhow::bail!("{}", adamas_elab::report(&file, &error)),
    };

    println!("{}: проверено, объявлений {}", file.name(), signature.len());
    Ok(())
}
