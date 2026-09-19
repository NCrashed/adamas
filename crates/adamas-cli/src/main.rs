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
            let (name, files, signature) = checked(&path)?;
            if r#type.is_empty() {
                // Файлов больше одного - у программы есть импорты, и счёт
                // объявлений без счёта файлов говорил бы про неё неправду.
                if files > 1 {
                    println!(
                        "{name}: проверено, файлов {files}, объявлений {}",
                        signature.len()
                    );
                } else {
                    println!("{name}: проверено, объявлений {}", signature.len());
                }
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
    let (_, _, signature) = checked(path)?;
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
/// Проход идёт по **программе**, а не по файлу: `import` подключает соседние
/// файлы, и корень их поиска - каталог входного файла (§4.8, §7.3). Программа
/// из одного файла проходит тем же путём: подключать нечего, и область
/// видимости у неё пуста.
///
/// Отказ печатается вместе с исходником **того** файла, которому принадлежит
/// его спан: позиция в чужом файле, нарисованная по входному, указывала бы на
/// случайную строку.
///
/// Элаборация при этом не в TCB - она отдаёт терм, корректность его
/// устанавливает `check` (§3).
fn checked(path: &Path) -> anyhow::Result<(String, usize, adamas_core::sig::Signature)> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("не удалось прочитать {}", path.display()))?;
    let file = SourceFile::new(path.display().to_string(), text);
    let name = file.name().to_owned();
    let root = path.parent().unwrap_or_else(|| Path::new("."));
    let sources = adamas_elab::program::Directory::new(root);

    let program = adamas_elab::program::analyze(file, &sources);
    if let Some(located) = program.error() {
        anyhow::bail!("{}", program.rendered(located));
    }
    for diagnostic in &program.diagnostics {
        eprintln!("{}", program.rendered(diagnostic));
    }
    let files = program.units.len();
    let signature = program
        .signature
        .ok_or_else(|| anyhow::anyhow!("{name}: проход не отдал сигнатуры"))?;
    Ok((name, files, signature))
}
