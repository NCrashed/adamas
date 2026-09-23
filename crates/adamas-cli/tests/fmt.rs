//! `adamas fmt` (§7.1): мера - прогон по всему корпусу.
//!
//! Форматтер - единственный инструмент, который пишет пользователю его же код
//! обратно, и ошибка в нём переписывает корпус молча. Поэтому проверяется он
//! не примерами, а корпусом целиком: `tests/golden/eval`, `programs`, `errors`
//! и многофайловый проект - те же файлы, на которых стоит milestone Фазы 2.
//!
//! Четыре меры, и каждая ловит своё:
//!
//! 1. **Идемпотентность.** Второй проход не меняет ничего. Без неё «канон»
//!    значит только «детерминированно».
//! 2. **Ни один комментарий не пропал.** Считается, а не осматривается: у
//!    форматтера, теряющего комментарий на редкой форме, вывод выглядит
//!    правдоподобно.
//! 3. **Ответы те же.** Сильнее идемпотентности и ловит другое: форматтер,
//!    стабильно печатающий **не ту** программу, идемпотентен. Первый же
//!    прогон этой меры нашёл смешанную кратность - печать превращала
//!    отвергаемое определение в проходящее.
//! 4. **Отказ, а не паника** на неразобранном.
//!
//! # Что в ответе сверяется дословно, а что нет
//!
//! Значение и счёт объявлений - дословно: их форматирование двигать не вправе.
//! У диагностики сверяется **текст сообщения** без позиции и без выписки из
//! исходника: строку и колонку форматирование двигает по построению, и
//! требовать их совпадения значило бы требовать, чтобы форматтер ничего не
//! менял.

use std::path::{Path, PathBuf};
use std::process::Command;

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус или окружение, и падать он должен громко"
)]
mod fixture {
    use super::{Command, Path, PathBuf};

    /// Корень корпуса.
    pub(crate) fn corpus() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/golden")
            .canonicalize()
            .unwrap()
    }

    /// Пустой каталог под один сценарий.
    pub(crate) fn scratch(case: &str) -> PathBuf {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("fmt")
            .join(case);
        if dir.exists() {
            std::fs::remove_dir_all(&dir).unwrap();
        }
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Копирует дерево целиком: корпус этой волной не переформатируется, и
    /// трогать его на диске нельзя - `golden.rs` читает те же файлы в момент
    /// своего теста.
    pub(crate) fn copied(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let at = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copied(&entry.path(), &at);
            } else {
                std::fs::copy(entry.path(), at).unwrap();
            }
        }
    }

    /// Все исходники под каталогом, в порядке имени.
    pub(crate) fn sources(root: &Path) -> Vec<PathBuf> {
        let mut found = Vec::new();
        walk(root, &mut found);
        found.sort();
        assert!(!found.is_empty(), "корпус {} пуст", root.display());
        found
    }

    fn walk(dir: &Path, found: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(&path, found);
            } else if path.extension().is_some_and(|it| it == "adamas") {
                found.push(path);
            }
        }
    }

    /// Запускает драйвер и отдаёт `(успех, stdout, stderr)` с путём,
    /// заменённым на имя файла: копия корпуса лежит в другом каталоге, и путь
    /// в ответе иначе отличался бы у всех.
    pub(crate) fn driven(command: &str, path: &Path) -> (bool, String, String) {
        let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
            .arg(command)
            .arg(path)
            .env_remove("RUST_BACKTRACE")
            .env_remove("RUST_LIB_BACKTRACE")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
        let full = path.display().to_string();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        (
            output.status.success(),
            stdout.replace(&full, &name),
            stderr.replace(&full, &name),
        )
    }

    /// Запускает `adamas fmt` и отдаёт `(успех, stdout, stderr)`.
    pub(crate) fn formatter(args: &[&str]) -> (bool, String, String) {
        let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
            .arg("fmt")
            .args(args)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(!stderr.contains("panicked"), "форматтер упал: {stderr}");
        (output.status.success(), stdout, stderr)
    }

    pub(crate) fn read(path: &Path) -> String {
        std::fs::read_to_string(path).unwrap()
    }
}

use fixture::{copied, corpus, driven, formatter, read, scratch, sources};

/// Фикстуры корпуса, которые не разбираются **по построению**: на них стоят
/// снапшоты отказов разбора. Форматировать их нечем, и форматтер обязан
/// сказать это словами.
const UNPARSED: &[&str] = &["variadic-off-the-boundary.adamas"];

/// Относительное имя фикстуры - им подписаны все сообщения ниже.
fn named(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Разбирается ли фикстура вообще.
fn parsed(path: &Path) -> bool {
    !UNPARSED.contains(
        &path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .as_ref(),
    )
}

/// Сколько комментариев несёт текст.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: сюда попадает только разобравшееся, и отказ здесь означает сломанный корпус"
)]
fn comments(text: &str) -> usize {
    adamas_parser::tokenize(text)
        .expect("разбор фикстуры удался")
        .comments
        .len()
}

/// Милестоун волны: форматтер проходит по корпусу, второй проход не меняет
/// ничего, и ни один комментарий не пропадает.
#[test]
fn the_whole_corpus_formats_twice_to_the_same_text() {
    let root = corpus();
    let mut formatted = 0usize;
    let mut before = 0usize;
    let mut after = 0usize;
    let mut refused = Vec::new();
    for path in sources(&root) {
        let source = read(&path);
        let name = named(&root, &path);
        let Ok(once) = adamas_parser::format(&source) else {
            refused.push(name);
            continue;
        };
        let twice = adamas_parser::format(&once)
            .unwrap_or_else(|error| panic!("{name}: отформатированное не разобралось: {error}"));
        assert_eq!(twice, once, "{name}: форматирование не идемпотентно");
        formatted += 1;
        before += comments(&source);
        after += comments(&once);
        assert_eq!(
            comments(&once),
            comments(&source),
            "{name}: комментарии потерялись"
        );
    }
    // Отказ ровно на тех, кто не разбирается по построению: список закрытый,
    // и новый отказ обязан стать видимым, а не раствориться в счёте.
    let expected: Vec<String> = sources(&root)
        .iter()
        .filter(|path| !parsed(path))
        .map(|path| named(&root, path))
        .collect();
    assert_eq!(refused, expected, "отказался не тот набор фикстур");
    // Пол на счёте: мера «комментарии не потерялись» ничего не стоит на
    // корпусе без комментариев.
    assert!(formatted > 250, "корпус съёжился: {formatted} файлов");
    assert!(before > 500, "корпус без комментариев: {before}");
    assert_eq!(before, after, "счёт комментариев разошёлся на корпусе");
    // Сам замер - на stderr: числа нужны отчёту, а вытащить их иначе можно
    // только правкой теста.
    eprintln!(
        "замер: файлов {formatted}, отказов {}, комментариев {before} -> {after}",
        refused.len()
    );
}

/// Ответ драйвера, разложенный на то, что форматирование двигать не вправе, и
/// то, что двигает законно.
#[derive(Debug, PartialEq, Eq)]
struct Answer {
    /// Прошла ли программа.
    ok: bool,
    /// Что напечатано на stdout: значение либо счёт объявлений.
    value: String,
    /// Тексты диагностики без позиций и без выписки из исходника.
    said: Vec<String>,
}

/// Сообщение диагностики без позиции: `имя.adamas:строка:колонка: текст`.
///
/// Строки выписки и каретки сюда не попадают - в них нет двоеточий позиции, -
/// и это намеренно: выписка есть кусок исходника, а его форматирование меняет.
fn message(line: &str) -> Option<&str> {
    let after = line.find(".adamas:")? + ".adamas:".len();
    let mut parts = line[after..].splitn(3, ':');
    let at_line = parts.next()?;
    let at_column = parts.next()?;
    let tail = parts.next()?;
    let numeric = |text: &str| !text.is_empty() && text.chars().all(|ch| ch.is_ascii_digit());
    (numeric(at_line) && numeric(at_column)).then(|| tail.trim())
}

fn answered(command: &str, path: &Path) -> Answer {
    let (ok, stdout, stderr) = driven(command, path);
    Answer {
        ok,
        value: stdout,
        said: stderr
            .lines()
            .filter_map(message)
            .map(str::to_owned)
            .collect(),
    }
}

/// Форматированный корпус - тот же корпус: ни одна программа не поменяла
/// смысла.
///
/// Мера сильнее идемпотентности. Форматтер, стабильно печатающий не ту
/// программу, идемпотентен; поймать его может только прогон того, что он
/// напечатал.
#[test]
fn the_formatted_corpus_answers_the_same() {
    let root = corpus();
    let copy = scratch("answers");
    copied(&root, &copy);
    let (_, _, stderr) = formatter(&[&copy.display().to_string()]);
    assert!(
        !stderr.contains("panicked"),
        "форматтер упал на корпусе: {stderr}"
    );
    let mut checked = 0usize;
    for path in sources(&root) {
        if !parsed(&path) {
            continue;
        }
        let relative = path.strip_prefix(&root).expect("фикстура лежит в корпусе");
        let mirror = copy.join(relative);
        // `eval` считает значение, `check` - объявления; корпус `eval` целиком
        // о значении, остальные о проверке.
        let command = if relative.starts_with("eval") {
            "eval"
        } else {
            "check"
        };
        let name = named(&root, &path);
        assert_eq!(
            answered(command, &mirror),
            answered(command, &path),
            "{name}: ответ изменился после форматирования"
        );
        checked += 1;
    }
    assert!(checked > 250, "сверено слишком мало: {checked}");
}

/// Многофайловый проект (§4.8): форматируется весь, и проверяется по-прежнему
/// целиком.
#[test]
fn the_project_of_ten_files_survives_formatting() {
    let case = scratch("project");
    let copy = case.join("project");
    copied(&corpus().join("project"), &copy);
    let (ok, stdout, stderr) = formatter(&[&copy.display().to_string()]);
    assert!(ok, "проект не отформатировался: {stderr}");
    assert!(
        stdout.contains("файлов 10"),
        "форматтер обязан назвать все файлы проекта: {stdout}"
    );
    let entry = copy.join("main.adamas");
    let (ok, stdout, _) = driven("check", &entry);
    assert!(ok, "проект отвергнут после форматирования");
    assert_eq!(
        stdout.trim_end(),
        "main.adamas: проверено, файлов 10, объявлений 99"
    );
}

/// Неразобранное не форматируется, и это названный отказ.
#[test]
fn an_unparsed_fixture_is_refused_by_name() {
    let case = scratch("refusal");
    let broken = case.join("broken.adamas");
    std::fs::write(&broken, "f = case\n").expect("фикстура записалась");
    let before = read(&broken);
    let (ok, _, stderr) = formatter(&[&broken.display().to_string()]);
    assert!(!ok, "отказ обязан быть неуспехом");
    assert!(
        stderr.contains("broken.adamas:") && stderr.lines().any(|line| message(line).is_some()),
        "отказ обязан назвать файл, место и причину: {stderr}"
    );
    assert_eq!(read(&broken), before, "сломанный файл трогать нельзя");
}

/// Сломанный файл не прячет остальных: обход идёт дальше.
#[test]
fn a_broken_file_does_not_hide_its_neighbours() {
    let case = scratch("neighbours");
    std::fs::write(case.join("broken.adamas"), "f = case\n").expect("записалось");
    std::fs::write(case.join("ok.adamas"), "f   =   1\n").expect("записалось");
    let (ok, stdout, _) = formatter(&[&case.display().to_string()]);
    assert!(!ok);
    assert!(stdout.contains("отказов 1"), "{stdout}");
    assert_eq!(
        read(&case.join("ok.adamas")),
        "f = 1\n",
        "сосед отформатирован"
    );
}

/// `--check` не пишет, но краснеет; уже канонический файл не переписывается.
#[test]
fn check_reports_without_writing() {
    let case = scratch("check");
    let path = case.join("askew.adamas");
    std::fs::write(&path, "f   =   1\n").expect("записалось");
    let (ok, stdout, _) = formatter(&["--check", &path.display().to_string()]);
    assert!(!ok, "файл не в каноне - команда обязана покраснеть");
    assert!(stdout.contains("не в каноне 1"), "{stdout}");
    assert_eq!(read(&path), "f   =   1\n", "--check писать не вправе");

    let (ok, stdout, _) = formatter(&[&path.display().to_string()]);
    assert!(ok);
    assert!(stdout.contains("переформатировано 1"), "{stdout}");
    assert_eq!(read(&path), "f = 1\n");

    let (ok, stdout, _) = formatter(&[&path.display().to_string()]);
    assert!(ok);
    assert!(
        stdout.contains("переформатировано 0"),
        "второй проход трогать нечего: {stdout}"
    );
}
