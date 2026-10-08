//! Драйвер компилятора Adamas.
//!
//! §7.1 называет семь команд: `new`, `build`, `test`, `run`, `check`, `fmt`,
//! `doc`. Здесь шесть - нет `doc`: генератор документации отдельная машина, и
//! предмета у неё пока нет, потому что разновидности «док» у комментария в
//! языке не заведено. Сверх семи есть `eval`: он старше `run` и отличается от
//! него вычислителем - считает машина (`adamas-interp`), а не собранный код.
//!
//! Что где: [`project`] - какая это программа (вход, корни модулей, каталог
//! артефактов), [`scaffold`] - `new`, [`compile`] - `build` и `run`,
//! [`suite`] - `test`, [`fmt`] - `fmt`.
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
mod doc;
mod fmt;
mod project;
mod scaffold;
mod suite;

use std::path::PathBuf;
use std::process::ExitCode;

use adamas_core::term::PRINT_DEPTH;
use clap::{CommandFactory as _, FromArgMatches as _, Parser, Subcommand};

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
    /// Привести исходники к каноническому виду (§7.1, §7.4).
    Fmt {
        /// Файл `.adamas` либо каталог: тогда форматируется всё дерево под ним.
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Не писать, а назвать файлы, которые изменились бы.
        #[arg(long)]
        check: bool,
    },
    /// Напечатать документацию по видимому снаружи интерфейсу (§7.1, §4.8).
    Doc {
        /// Путь к файлу `.adamas`, каталогу проекта или его `adamas.toml`.
        #[arg(default_value = ".")]
        path: PathBuf,
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
    let cli = match Cli::from_arg_matches(&localized().get_matches()) {
        Ok(cli) => cli,
        Err(error) => error.exit(),
    };
    match dispatch(cli.command) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{}", reported(&error));
            ExitCode::FAILURE
        }
    }
}

/// Отказ драйвера на языке пользователя (§7.6): слово перед ним и заголовок
/// цепочки причин - из каталога. `{error:?}` у `anyhow` печатал их
/// по-английски при любой локали.
fn reported(error: &anyhow::Error) -> String {
    let mut text = adamas_l10n::tr!("cli-error", error = error.to_string());
    let mut causes = error.chain().skip(1).peekable();
    if causes.peek().is_some() {
        text.push_str("\n\n");
        text.push_str(adamas_l10n::text!("cli-caused-by"));
        for cause in causes {
            text.push_str("\n    ");
            text.push_str(&cause.to_string());
        }
    }
    text
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
        Command::Fmt { path, check } => {
            let green = fmt::run(&path, check)?;
            Ok(if green {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            })
        }
        Command::Doc { path } => {
            doc::run(&path)?;
            Ok(ExitCode::SUCCESS)
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
                "{}",
                adamas_l10n::tr!(
                    "cli-checked-files",
                    name = checked.name,
                    files = adamas_l10n::count(checked.files),
                    declarations =
                        adamas_l10n::count(declared(&checked.signature, &checked.prelude))
                )
            );
        } else {
            println!(
                "{}",
                adamas_l10n::tr!(
                    "cli-checked",
                    name = checked.name,
                    declarations =
                        adamas_l10n::count(declared(&checked.signature, &checked.prelude))
                )
            );
        }
        return Ok(());
    }
    for name in wanted {
        let Some(shown) = adamas_elab::cursor::described(&checked.signature, name) else {
            anyhow::bail!("{}", adamas_l10n::tr!("cli-unknown-name", name = name));
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
    let entry = project::entry(&checked.signature, name)?;
    // Машина ищет чужой символ по тем же библиотекам, по которым его ищет
    // компоновщик (§5.3): секция `[link]` плюс стандартная C. Иначе `adamas
    // eval` и `adamas run` отвечали бы по-разному на одной и той же программе.
    let answer = adamas_interp::run_linked(
        &checked.signature,
        &entry.term,
        adamas_interp::Linkage::new(&opened.link.libraries, &opened.link.paths),
    )?;
    let depth = if full { None } else { Some(PRINT_DEPTH) };
    if entry.printed {
        println!("{}", answer.printed(depth));
    }
    Ok(())
}

/// Сколько объявлений написано программой.
///
/// Прелюдные не входят: подключаются они неявно (§4.4), автор их не писал, и
/// счёт с ними говорил бы про программу неправду - у всякой она выросла бы на
/// одно и то же число. Считаются по записи загрузчика, а не по префиксу
/// `Prelude.`: класс и словарь инстанса префикса не носят.
fn declared(
    signature: &adamas_core::sig::Signature,
    prelude: &std::collections::HashSet<adamas_core::term::Name>,
) -> usize {
    signature
        .names()
        .into_iter()
        .filter(|name| !prelude.contains(name))
        .count()
}

/// Подкоманды и их аргументы: по ним справка берётся из каталога (§7.6).
///
/// Doc-комментарии выше - для читателя кода; человеку в терминале справка
/// приходит переводом `cli-help-<команда>` и `cli-help-<команда>-<аргумент>`.
const HELP: &[(&str, &[&str])] = &[
    ("new", &["path", "name"]),
    ("check", &["path", "type"]),
    ("build", &["path", "backend"]),
    ("run", &["path", "backend"]),
    ("fmt", &["path", "check"]),
    ("doc", &["path"]),
    ("test", &["path"]),
    ("eval", &["path", "name", "full"]),
];

/// Разбор аргументов со справкой на языке процесса.
fn localized() -> clap::Command {
    let text = |id: String| adamas_l10n::message(&id, &[]);
    let mut command = Cli::command().about(adamas_l10n::tr!("cli-help-about"));
    for (name, arguments) in HELP {
        command = command.mut_subcommand(*name, |mut sub| {
            sub = sub.about(text(format!("cli-help-{name}")));
            for argument in *arguments {
                sub = sub.mut_arg(*argument, |arg| {
                    let arg = arg.help(text(format!("cli-help-{name}-{argument}")));
                    // `ИМЯ` у `--name` и `--type`; позиционные называет clap.
                    if matches!(*argument, "name" | "type") && *name != "eval" {
                        arg.value_name(adamas_l10n::text!("cli-help-value-name"))
                    } else {
                        arg
                    }
                });
            }
            sub
        });
    }
    command
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Справка покрывает все подкоманды и аргументы, и у каждого есть текст в
    /// каталоге: иначе человек увидел бы идентификатор вместо фразы.
    #[test]
    fn every_command_and_argument_has_its_help_in_both_languages() {
        let command = Cli::command();
        let written: Vec<&str> = command
            .get_subcommands()
            .map(clap::Command::get_name)
            .collect();
        let listed: Vec<&str> = HELP.iter().map(|(name, _)| *name).collect();
        assert_eq!(written, listed, "подкоманды разошлись с перечнем справки");
        for (name, arguments) in HELP {
            let sub = command.find_subcommand(name).expect("подкоманда есть");
            let ids: Vec<String> = sub
                .get_arguments()
                .filter(|it| !matches!(it.get_id().as_str(), "help"))
                .map(|it| it.get_id().to_string())
                .collect();
            assert_eq!(ids, *arguments, "{name}: аргументы разошлись с перечнем");
            for lang in [adamas_l10n::Lang::Ru, adamas_l10n::Lang::En] {
                let ids = std::iter::once(format!("cli-help-{name}"))
                    .chain(arguments.iter().map(|it| format!("cli-help-{name}-{it}")));
                for id in ids {
                    assert_ne!(adamas_l10n::message_in(lang, &id, &[]), id, "{lang:?}");
                }
            }
        }
    }
}
