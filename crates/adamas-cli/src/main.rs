//! Драйвер компилятора Adamas.
//!
//! Полный набор команд (`new`, `build`, `test`, `run`, `check`, `fmt`, `doc`) —
//! §7.1. Пока есть только `check`.
//!
//! # Программа, а не файл
//!
//! Обе команды берут **входной** файл и разрешают его `import`'ы (§4.8):
//! корень поиска модулей — каталог этого файла, `Data.Map` — это
//! `<каталог>/Data/Map.adamas`.
//!
//! # Проект, а не файл
//!
//! Тем же аргументом принимается **каталог** проекта или путь к его
//! `adamas.toml`: тогда корни поиска берутся из манифеста, а git-зависимости
//! достаются и подключаются (§7.3, `adamas-pkg`).
//!
//! Написанный **файл** тоже ищет манифест - вверх по дереву, до ближайшего.
//! Решение это переигранное: сперва вверх не искалось вовсе, доводом «чужой
//! `adamas.toml` этажом выше молча меняет смысл проверки». Довод не выдержал
//! замера трека B: `adamas check tests/golden/project/Std/Order.adamas`
//! отвечал «модуль `Std.Base` не найден: искали `…/Std/Std/Base.adamas`», то
//! есть инструмент не проверял файл **собственного** проекта. Редактор тот же
//! корень берёт из `rootUri`; у терминала его взять неоткуда, кроме как из
//! манифеста. Корни при этом манифестные, а входом остаётся написанный файл -
//! спрашивали про него.
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
        /// Путь к файлу `.adamas`, каталогу проекта или его `adamas.toml`.
        path: PathBuf,
        /// Напечатать тип имени вместо счёта объявлений (§7.2). Можно повторять.
        #[arg(long, value_name = "ИМЯ")]
        r#type: Vec<String>,
    },
    /// Проверить и исполнить определение (§9 Фаза 5).
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

/// Откуда берутся входной файл и корни поиска модулей.
///
/// Три случая. Каталог или сам `adamas.toml` - проект целиком, и вход берётся
/// из манифеста. Файл **внутри** проекта - корни из манифеста, а входом
/// остаётся написанный файл. Файл вне всякого проекта - как раньше: корень
/// поиска есть его каталог.
///
/// # Errors
///
/// Манифест собран не так или зависимость не достаётся.
fn opened(path: &Path) -> anyhow::Result<(PathBuf, Box<dyn adamas_elab::program::Sources>)> {
    let named = if path.is_dir() {
        Some(path.to_path_buf())
    } else if path
        .file_name()
        .is_some_and(|it| it == adamas_pkg::manifest::MANIFEST)
    {
        Some(
            path.parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
        )
    } else {
        None
    };
    let entry = named.is_none().then(|| path.to_path_buf());
    let Some(dir) = named.or_else(|| enclosing(path)) else {
        let root = path.parent().unwrap_or_else(|| Path::new("."));
        return Ok((
            path.to_path_buf(),
            Box::new(adamas_elab::program::Directory::new(root)),
        ));
    };

    let project = adamas_pkg::Project::open(&dir)?;
    // Достача - действие, и молчать о нём нельзя: сборка, впервые клонирующая
    // репозиторий, отличается от той, что взяла готовый чекаут, только
    // временем, и человеку это надо видеть.
    for dependency in &project.resolved {
        if dependency.refreshed {
            eprintln!("{}: достаю {}", dependency.prefix, dependency.rev);
        }
    }
    if project.relocked {
        eprintln!("{}: обновлён", adamas_pkg::lock::LOCKFILE);
    }
    Ok((
        entry.unwrap_or_else(|| project.entry_file()),
        Box::new(project.sources),
    ))
}

/// Проект, внутри которого лежит файл: ближайший `adamas.toml` вверх по дереву.
///
/// Путь приводится к абсолютному: без этого `adamas check main.adamas` смотрел
/// бы ровно в текущий каталог и никуда выше. Файла нет - искать нечего, и
/// отказ «не удалось прочитать» скажет об этом лучше.
fn enclosing(file: &Path) -> Option<PathBuf> {
    let full = std::fs::canonicalize(file).ok()?;
    let mut at = full.parent()?;
    loop {
        if at.join(adamas_pkg::manifest::MANIFEST).is_file() {
            return Some(at.to_path_buf());
        }
        at = at.parent()?;
    }
}

/// Разбор, элаборация и проверка типов - общая половина обеих команд.
///
/// Проход идёт по **программе**, а не по файлу: `import` подключает соседние
/// файлы, и корень их поиска даёт [`opened`] - каталог входного файла или
/// манифест проекта (§4.8, §7.3). Программа из одного файла проходит тем же
/// путём: подключать нечего, и область видимости у неё пуста.
///
/// Отказ печатается вместе с исходником **того** файла, которому принадлежит
/// его спан: позиция в чужом файле, нарисованная по входному, указывала бы на
/// случайную строку.
///
/// Элаборация при этом не в TCB - она отдаёт терм, корректность его
/// устанавливает `check` (§3).
fn checked(path: &Path) -> anyhow::Result<(String, usize, adamas_core::sig::Signature)> {
    let (entry, sources) = opened(path)?;
    let text = std::fs::read_to_string(&entry)
        .with_context(|| format!("не удалось прочитать {}", entry.display()))?;
    let file = SourceFile::new(entry.display().to_string(), text);
    let name = file.name().to_owned();

    let program = adamas_elab::program::analyze(file, sources.as_ref());
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
