//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.

use std::path::{Path, PathBuf};

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::source::SourceFile;
use adamas_core::term::Term;
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
    /// Проверить и вычислить определение до нормальной формы (§9 Фаза 5).
    Eval {
        /// Путь к файлу `.adamas`.
        path: PathBuf,
        /// Что вычислять. По умолчанию `main`.
        #[arg(default_value = "main")]
        name: String,
    },
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().command {
        Command::Check { path } => {
            let (file, signature) = checked(&path)?;
            println!("{}: проверено, объявлений {}", file.name(), signature.len());
            Ok(())
        }
        Command::Eval { path, name } => evaluate(&path, &name),
    }
}

/// Вычисляет определение и печатает нормальную форму.
///
/// Это **нормализация**, а не исполнение: стирания нет, поэтому стёртые
/// аргументы видны в ответе, а эффекты не производятся - их производит
/// evidence, которой пока нет. Наблюдать построенный терм этого довольно, и
/// ради наблюдения оно и заведено (§9 Фаза 5, первый пункт).
fn evaluate(path: &Path, name: &str) -> anyhow::Result<()> {
    let (_, signature) = checked(path)?;
    let Some(definition) = signature.lookup(name) else {
        anyhow::bail!("определение `{name}` не найдено");
    };
    let Some(body) = &definition.body else {
        anyhow::bail!("у `{name}` нет тела: постулат вычислять нечем");
    };
    // Параметры подставляются нулём и пустой row. Выбор назван: подъём даёт
    // row-параметр всякой написанной сигнатуре, поэтому требовать нулевой
    // арности значило бы не вычислять почти ничего, а вычисление идёт над
    // одним экземпляром - что и требуется, чтобы посмотреть на терм.
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    let body = body.substitute_levels(&levels).substitute_rows(&rows);
    println!("{}", adamas_core::conv::evaluated(&signature, &body));
    Ok(())
}

/// Разбор, элаборация и проверка типов - общая половина обеих команд.
fn checked(path: &Path) -> anyhow::Result<(SourceFile, adamas_core::sig::Signature)> {
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

    Ok((file, signature))
}
