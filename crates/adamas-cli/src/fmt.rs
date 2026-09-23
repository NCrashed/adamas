//! `adamas fmt` - канонический вид исходника (§7.1, §7.4).
//!
//! Форматтер opinionated и **без конфигурации**: §7.4 называет `gofmt` и
//! `rustfmt` образцом, и настройка, которой нет, - половина того, ради чего
//! форматтер заводят. Всё, что он умеет и чего намеренно не делает, - заголовок
//! [`adamas_parser::printer`]; здесь только обход файлов и запись.
//!
//! # Отказ, а не догадка
//!
//! Неразобранный файл не форматируется: восстановления после ошибки у разбора
//! нет, а печатать половину дерева значит стереть вторую. Такой файл называется
//! вместе с позицией, остальные форматируются, и команда завершается неуспехом.
//!
//! # Пишется только изменённое
//!
//! Файл, уже стоящий в каноне, не переписывается: время правки - вход для
//! `make`, редактора и системы сборки, и трогать его без причины нельзя.

use std::path::{Path, PathBuf};

use adamas_core::source::SourceFile;
use anyhow::Context as _;

/// Расширение исходника языка.
const EXTENSION: &str = "adamas";

/// Что вышло из прохода.
pub(crate) struct Report {
    /// Сколько файлов прошло через форматтер.
    pub(crate) seen: usize,
    /// Какие файлы отличались от канона.
    pub(crate) changed: Vec<PathBuf>,
    /// Какие не разобрались - вместе с тем, что о них сказано.
    pub(crate) refused: Vec<String>,
}

impl Report {
    /// Всё ли в порядке: и разобралось, и (при `--check`) уже в каноне.
    fn green(&self, check: bool) -> bool {
        self.refused.is_empty() && (!check || self.changed.is_empty())
    }
}

/// Форматирует файл или всё дерево под каталогом.
///
/// `check` - не писать, а только сказать, что изменилось бы. Ответ - `true`,
/// когда команде нечего сообщить об отказе.
///
/// # Errors
///
/// Каталог не читается или файл не записывается. Неразобранный файл ошибкой
/// **не** является: о нём сообщается, а обход продолжается - иначе первый же
/// сломанный файл прятал бы состояние остальных.
pub(crate) fn run(path: &Path, check: bool) -> anyhow::Result<bool> {
    let files = gathered(path)?;
    let mut report = Report {
        seen: 0,
        changed: Vec::new(),
        refused: Vec::new(),
    };
    for file in files {
        let source = std::fs::read_to_string(&file)
            .with_context(|| format!("не удалось прочитать {}", file.display()))?;
        report.seen += 1;
        let Some(canonical) = formatted(&file, &source, &mut report) else {
            continue;
        };
        if canonical == source {
            continue;
        }
        report.changed.push(file.clone());
        if !check {
            std::fs::write(&file, &canonical)
                .with_context(|| format!("не удалось записать {}", file.display()))?;
        }
    }
    announce(&report, check);
    Ok(report.green(check))
}

/// Канонический вид файла либо `None` с записанным отказом.
fn formatted(path: &Path, source: &str, report: &mut Report) -> Option<String> {
    match adamas_parser::format(source) {
        Ok(canonical) => Some(canonical),
        Err(error) => {
            report.refused.push(located(path, source, &error));
            None
        }
    }
}

/// Отказ вместе с позицией: `файл:строка:колонка: что случилось`.
fn located(path: &Path, source: &str, error: &adamas_parser::Error) -> String {
    let file = SourceFile::new(path.display().to_string(), source.to_owned());
    let at = file
        .location(error.span().start())
        .map_or_else(String::new, |it| format!(":{}:{}", it.line, it.column));
    format!("{}{at}: {error}", path.display())
}

/// Что команда говорит человеку.
fn announce(report: &Report, check: bool) {
    for refusal in &report.refused {
        eprintln!("не форматируется: {refusal}");
    }
    for path in &report.changed {
        println!("{}", path.display());
    }
    let verb = if check {
        "не в каноне"
    } else {
        "переформатировано"
    };
    println!(
        "файлов {}, {verb} {}, отказов {}",
        report.seen,
        report.changed.len(),
        report.refused.len()
    );
}

/// Какие файлы форматировать: названный либо всё дерево под каталогом.
///
/// Обход каталога сортирован - иначе порядок отчёта зависел бы от файловой
/// системы, - и в скрытые каталоги не заходит. Тем же правилом мимо проходит
/// хранилище зависимостей (`.adamas`, §7.3): чужой исходник форматтеру не
/// принадлежит.
fn gathered(path: &Path) -> anyhow::Result<Vec<PathBuf>> {
    if !path.is_dir() {
        return Ok(vec![path.to_path_buf()]);
    }
    let mut found = Vec::new();
    walk(path, &mut found)?;
    found.sort();
    Ok(found)
}

fn walk(dir: &Path, found: &mut Vec<PathBuf>) -> anyhow::Result<()> {
    let entries = std::fs::read_dir(dir)
        .with_context(|| format!("не удалось прочитать каталог {}", dir.display()))?;
    for entry in entries {
        let path = entry
            .with_context(|| format!("не удалось прочитать каталог {}", dir.display()))?
            .path();
        let hidden = path
            .file_name()
            .and_then(std::ffi::OsStr::to_str)
            .is_some_and(|name| name.starts_with('.'));
        if path.is_dir() {
            if !hidden {
                walk(&path, found)?;
            }
        } else if path.extension().is_some_and(|it| it == EXTENSION) {
            found.push(path);
        }
    }
    Ok(())
}
