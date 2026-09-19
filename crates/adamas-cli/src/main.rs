//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.
//!
//! # `check --type`
//!
//! §7.2 обещает, что в редакторе видно то же, что в терминале, и трек A волны 1
//! Фазы 9 это исполнил для диагностики. У hover'а обещание то же, но проверить
//! его было нечем: типов `adamas check` не печатал вовсе, а типы в сообщениях
//! об отказе — инстанцированные местом использования, то есть не те. `--type`
//! печатает объявленный тип тем же вызовом, каким его отдаёт hover, и тем
//! самым переводит обещание из слов в прогон (`tests/hover.rs`).

use std::path::{Path, PathBuf};

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::source::SourceFile;
use adamas_core::term::{PRINT_DEPTH, Term};
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
        /// Напечатать тип имени вместо счёта объявлений (§7.2). Можно повторять.
        #[arg(long, value_name = "ИМЯ")]
        r#type: Vec<String>,
    },
    /// Проверить и исполнить определение (§9 Фаза 5).
    Eval {
        /// Путь к файлу `.adamas`.
        path: PathBuf,
        /// Что вычислять. По умолчанию `main`.
        #[arg(default_value = "main")]
        name: String,
        /// Печатать ответ целиком, без среза по глубине.
        #[arg(long)]
        full: bool,
    },
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().command {
        Command::Check { path, r#type } => {
            let (file, signature) = checked(&path)?;
            if r#type.is_empty() {
                println!("{}: проверено, объявлений {}", file.name(), signature.len());
                return Ok(());
            }
            for name in &r#type {
                let Some(shown) = adamas_elab::cursor::described(&signature, name) else {
                    anyhow::bail!("имя `{name}` сигнатуре неизвестно");
                };
                println!("{shown}");
            }
            Ok(())
        }
        Command::Eval { path, name, full } => evaluate(&path, &name, full),
    }
}

/// Исполняет определение и печатает значение.
///
/// Считает **машина** (`adamas-interp`), а не `conv::evaluated`: эффекты
/// производятся, хендлеры срабатывают. Стёртые аргументы в ответе не видны:
/// стирание сделано, и свидетель ему - `tests/golden/eval/erasure.adamas`.
///
/// Ответ печатается со срезом по глубине: вырожденно глубокое значение даёт
/// сотни килобайт текста, которых никто не читает. `--full` его снимает, и
/// снимает по-настоящему - печать не рекурсивна (§10 вопрос 93).
fn evaluate(path: &Path, name: &str, full: bool) -> anyhow::Result<()> {
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
    let answer = adamas_interp::run(&signature, &body)?;
    let depth = if full { None } else { Some(PRINT_DEPTH) };
    println!("{}", answer.printed(depth));
    Ok(())
}

/// Разбор, элаборация и проверка типов - общая половина обеих команд.
///
/// Сам проход делает [`adamas_elab::analyze`], и делает его же LSP-сервер:
/// текст в редакторе обязан совпадать с текстом в терминале, а держится это
/// тем, что путь один, а не тем, что две записи сообщения совпали.
/// Элаборация при этом не в TCB - она отдаёт терм, корректность его
/// устанавливает `check` (§3).
fn checked(path: &Path) -> anyhow::Result<(SourceFile, adamas_core::sig::Signature)> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("не удалось прочитать {}", path.display()))?;
    let file = SourceFile::new(path.display().to_string(), text);

    let analysis = adamas_elab::analyze(file.text());
    if let Some(error) = analysis.error() {
        anyhow::bail!("{}", error.rendered(&file));
    }
    for diagnostic in &analysis.diagnostics {
        eprintln!("{}", diagnostic.rendered(&file));
    }
    let signature = analysis
        .signature
        .ok_or_else(|| anyhow::anyhow!("{}: проход не отдал сигнатуры", file.name()))?;
    Ok((file, signature))
}
