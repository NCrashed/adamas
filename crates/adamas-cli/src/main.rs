//! Драйвер компилятора Adamas.
//!
//! §7.1 называет семь команд: `new`, `build`, `test`, `run`, `check`, `fmt`,
//! `doc`. Здесь пять - шестая и седьмая суть отдельные машины (форматтер языка
//! и генератор документации из doc-комментариев), и ни одной из них в проекте
//! нет. Сверх семи есть `eval`: он старше `run` и отличается от него
//! вычислителем - считает машина (`adamas-interp`), а не собранный код.
//!
//! Что где: [`project`] - какая это программа (вход, корни модулей, каталог
//! артефактов), [`scaffold`] - `new`, [`compile`] - `build` и `run`,
//! [`suite`] - `test`.
//!
//! # `check --type`
//!
//! §7.2 обещает, что в редакторе видно то же, что в терминале, и трек A волны 1
//! Фазы 9 это исполнил для диагностики. У hover'а обещание то же, но проверить
//! его было нечем: типов `adamas check` не печатал вовсе, а типы в сообщениях
//! об отказе — инстанцированные местом использования, то есть не те. `--type`
//! печатает объявленный тип тем же вызовом, каким его отдаёт hover, и тем
//! самым переводит обещание из слов в прогон (`tests/hover.rs`).

mod compile;
mod project;
mod scaffold;
mod suite;

use std::path::PathBuf;
use std::process::ExitCode;

use adamas_core::term::PRINT_DEPTH;
use clap::{Parser, Subcommand};

use compile::Backend;

#[derive(Debug, Parser)]
#[command(name = "adamas", version, about = "Adamas compiler driver", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Завести проект: манифест, вход и тесты (§7.1).
    New {
        /// Каталог под проект. Создаётся, если его нет.
        path: PathBuf,
        /// Имя пакета. По умолчанию - последний сегмент пути.
        #[arg(long, value_name = "ИМЯ")]
        name: Option<String>,
    },
    /// Разобрать исходник, элаборировать и проверить типы (§7.1).
    Check {
        /// Путь к файлу `.adamas`, каталогу проекта или его `adamas.toml`.
        path: PathBuf,
        /// Напечатать тип имени вместо счёта объявлений (§7.2). Можно повторять.
        #[arg(long, value_name = "ИМЯ")]
        r#type: Vec<String>,
    },
    /// Собрать программу в исполняемый файл (§7.1).
    Build {
        /// Путь к проекту, его `adamas.toml` или файлу `.adamas`.
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Чем идти от IR до объектника.
        #[arg(long, value_enum, default_value_t = Backend::default())]
        backend: Backend,
    },
    /// Собрать и запустить (§7.1).
    Run {
        /// Путь к проекту, его `adamas.toml` или файлу `.adamas`.
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Чем идти от IR до объектника.
        #[arg(long, value_enum, default_value_t = Backend::default())]
        backend: Backend,
    },
    /// Прогнать тесты проекта (§7.1).
    Test {
        /// Путь к проекту или его `adamas.toml`.
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Проверить и исполнить определение машиной (§9 Фаза 5).
    Eval {
        /// Путь к файлу `.adamas`, каталогу проекта или его `adamas.toml`.
        path: PathBuf,
        /// Что вычислять. По умолчанию `main`.
        #[arg(default_value = "main")]
        name: String,
        /// Печатать ответ целиком, без среза по глубине.
        #[arg(long)]
        full: bool,
    },
}

/// Код возврата, а не `anyhow::Result`: у `run` он приходит от запущенной
/// программы, а у `test` - от вердикта сюиты, и подменять их нулём значило бы
/// отвечать успехом на неуспех.
///
/// Печать отказа - **дословно** та, которой отвечал `Termination` у
/// `anyhow::Result`: `Error:` и отладочное представление с цепочкой причин.
/// Своя короче, и первый же прогон показал, чего она стоит: 98 записанных
/// отказов корпуса и сверка «редактор видит то же, что терминал» сверяются с
/// текстом целиком, вместе с этим словом.
fn main() -> ExitCode {
    match dispatch(Cli::parse().command) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("Error: {error:?}");
            ExitCode::FAILURE
        }
    }
}

fn dispatch(command: Command) -> anyhow::Result<ExitCode> {
    match command {
        Command::New { path, name } => {
            scaffold::create(&path, name.as_deref())?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Check { path, r#type } => {
            check(&path, &r#type)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Build { path, backend } => {
            compile::build(&path, backend)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Run { path, backend } => {
            let code = compile::run(&path, backend)?;
            Ok(ExitCode::from(u8::try_from(code).unwrap_or(1)))
        }
        Command::Test { path } => {
            let green = suite::run(&path)?;
            Ok(if green {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            })
        }
        Command::Eval { path, name, full } => {
            evaluate(&path, &name, full)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

/// Проверка типов: счёт объявлений либо тип названного имени.
fn check(path: &std::path::Path, wanted: &[String]) -> anyhow::Result<()> {
    let opened = project::opened(path)?;
    let checked = project::checked(&opened.entry, opened.sources.as_ref())?;
    if wanted.is_empty() {
        // Файлов больше одного - у программы есть импорты, и счёт объявлений
        // без счёта файлов говорил бы про неё неправду.
        if checked.files > 1 {
            println!(
                "{}: проверено, файлов {}, объявлений {}",
                checked.name,
                checked.files,
                checked.signature.len()
            );
        } else {
            println!(
                "{}: проверено, объявлений {}",
                checked.name,
                checked.signature.len()
            );
        }
        return Ok(());
    }
    for name in wanted {
        let Some(shown) = adamas_elab::cursor::described(&checked.signature, name) else {
            anyhow::bail!("имя `{name}` сигнатуре неизвестно");
        };
        println!("{shown}");
    }
    Ok(())
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
fn evaluate(path: &std::path::Path, name: &str, full: bool) -> anyhow::Result<()> {
    let opened = project::opened(path)?;
    let checked = project::checked(&opened.entry, opened.sources.as_ref())?;
    let body = project::body(&checked.signature, name)?;
    // Машина ищет чужой символ по тем же библиотекам, по которым его ищет
    // компоновщик (§5.3): секция `[link]` плюс стандартная C. Иначе `adamas
    // eval` и `adamas run` отвечали бы по-разному на одной и той же программе.
    let answer = adamas_interp::run_linked(
        &checked.signature,
        &body,
        adamas_interp::Linkage::new(&opened.link.libraries, &opened.link.paths),
    )?;
    let depth = if full { None } else { Some(PRINT_DEPTH) };
    println!("{}", answer.printed(depth));
    Ok(())
}
