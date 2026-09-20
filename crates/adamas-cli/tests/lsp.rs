//! Текст в редакторе и текст в терминале - один текст.
//!
//! Обещание §7.2 буквально такое: ошибки видны inline «с тем же текстом, что
//! печатает терминал». Держится оно тем, что путь один
//! ([`adamas_elab::analyze`]), но «держится по построению» - не свидетель:
//! вторая запись сообщения заводится незаметно, и проект платил за такие пары
//! четырежды за две волны.
//!
//! Поэтому здесь **драйвер запускается процессом** на всём корпусе отказов, а
//! его вывод собирается обратно **из того, что ушло бы в редактор**: из
//! диапазона LSP и строки сообщения. Совпало - значит в редакторе нет ни
//! лишнего слова, ни потерянного, и подчёркивание стоит там же.
//!
//! Живёт в пакете драйвера, а не сервера: путь к бинарю `adamas` знает
//! `CARGO_BIN_EXE_adamas`, а его cargo определяет только тестам того пакета,
//! который этот бинарь объявляет.
//!
//! # Что этот прогон **не** ловит
//!
//! Перевод позиций, ошибочный одинаково в обе стороны: диапазон здесь и
//! разбирается, и собирается одним кодом. Это ловят записанные руками числа в
//! `crates/adamas-lsp/tests/protocol.rs`; разделение намеренное.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr as _;

use adamas_core::source::SourceFile;
use adamas_lsp::Encoding;
use adamas_lsp::lsp_types::{DiagnosticSeverity, Uri};

/// Корень корпуса.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус либо окружение, и падать он должен громко"
)]
mod harness {
    use super::{Command, Encoding, Path, PathBuf, SourceFile, Uri, corpus};
    use std::str::FromStr as _;

    /// Фикстуры директории в порядке имени.
    pub(crate) fn fixtures(kind: &str) -> Vec<PathBuf> {
        let dir = corpus().join(kind);
        let mut found: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
            .collect();
        found.sort();
        assert!(!found.is_empty(), "корпус {} пуст", dir.display());
        found
    }

    /// Запускает драйвер и отдаёт `(успех, stderr)` без пути к файлу: путь
    /// зависит от того, откуда запущен тест, а сравнение - не должно.
    pub(crate) fn driven(path: &Path) -> (bool, String) {
        let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
            .arg("check")
            .arg(path)
            // По той же причине, что в `golden.rs`: `anyhow` дописывает трейс,
            // когда переменная стоит в окружении, а у CI она стоит.
            .env_remove("RUST_BACKTRACE")
            .env_remove("RUST_LIB_BACKTRACE")
            .output()
            .unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        (
            output.status.success(),
            stderr.replace(&path.display().to_string(), &name),
        )
    }

    /// Текст фикстуры и её имя - так же, как их видит драйвер.
    pub(crate) fn source(path: &Path) -> SourceFile {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        SourceFile::new(name, std::fs::read_to_string(path).unwrap())
    }

    /// Диагностика того же файла в виде протокола - тем же вызовом, каким её
    /// шлёт сервер.
    ///
    /// Корень поиска модулей - каталог фикстуры, как у драйвера: иначе
    /// многофайловая фикстура проверялась бы не тем деревом.
    pub(crate) fn published(
        path: &Path,
        file: &SourceFile,
    ) -> Vec<adamas_lsp::lsp_types::Diagnostic> {
        let uri = Uri::from_str("file:///corpus.adamas").unwrap();
        let sources =
            adamas_lsp::project::Buffers::on_disk(path.parent().unwrap_or_else(|| Path::new(".")));
        adamas_lsp::diagnostics(&uri, file, Encoding::Utf16, &sources)
    }
}

use harness::{driven, fixtures, published, source};

/// Собирает терминальный вид из диагностики протокола.
///
/// Позиция берётся из диапазона LSP, а не из спана компилятора: иначе перевод
/// в проверке не участвовал бы вовсе. Первая строка сообщения - `headline`,
/// остаток - хвост, который в терминале печатается **после** каретки.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: диапазон, который не переводится обратно, - и есть искомая поломка"
)]
fn rebuilt(file: &SourceFile, found: &adamas_lsp::lsp_types::Diagnostic) -> String {
    let span = adamas_lsp::position::span(file, found.range, Encoding::Utf16)
        .expect("диапазон обязан переводиться обратно в спан");
    let (headline, detail) = match found.message.split_once('\n') {
        Some((headline, detail)) => (headline, format!("\n{detail}")),
        None => (found.message.as_str(), String::new()),
    };
    let mut out = adamas_elab::located(file, span, headline);
    for related in found.related_information.iter().flatten() {
        out.push('\n');
        out.push_str(&adamas_elab::located(
            file,
            adamas_lsp::position::span(file, related.location.range, Encoding::Utf16)
                .expect("диапазон связанного места обязан переводиться обратно"),
            &related.message,
        ));
    }
    out.push_str(&detail);
    out
}

/// Каждый отказ корпуса уходит в редактор тем же текстом и на то же место.
#[test]
fn every_refusal_reaches_the_editor_unchanged() {
    let mut checked = 0;
    for path in fixtures("errors") {
        let (passed, terminal) = driven(&path);
        assert!(!passed, "{} прошла, а не должна была", path.display());

        let file = source(&path);
        let found = published(&path, &file);
        assert_eq!(
            found.len(),
            1,
            "{}: сервер обязан отдать ровно один отказ, отдал {found:?}",
            path.display()
        );
        assert_eq!(found[0].severity, Some(DiagnosticSeverity::ERROR));
        assert_eq!(found[0].source.as_deref(), Some("adamas"));

        // `Error: ` дописывает `anyhow` на выходе драйвера; перевод строки -
        // `eprintln!`.
        let expected = format!("Error: {}\n", rebuilt(&file, &found[0]));
        assert_eq!(terminal, expected, "{}", path.display());
        checked += 1;
    }
    assert!(checked >= 98, "корпус отказов усох до {checked}");
}

/// Принятая программа не даёт редактору ни одного подчёркивания - ровно так
/// же, как не даёт их терминал.
#[test]
fn an_accepted_program_says_nothing() {
    for path in fixtures("programs") {
        let (passed, terminal) = driven(&path);
        assert!(passed, "{} отвергнута:\n{terminal}", path.display());
        let file = source(&path);
        let found = published(&path, &file);
        let mut expected = String::new();
        for it in &found {
            expected.push_str(&rebuilt(&file, it));
            expected.push('\n');
        }
        assert_eq!(terminal, expected, "{}", path.display());
    }
}

/// Предупреждение - третий исход, и корпус его не содержит ни разу.
///
/// Без этого случая путь `Severity::Warning` не проходился бы вовсе: 29
/// принятых программ корпуса молчат все до одной (проверено прогоном).
/// Позиция стоит после кириллицы, поэтому счёт байтами виден и здесь: до
/// имени `х` шесть байтов и пять кодовых единиц.
#[test]
fn a_warning_reaches_the_editor_too() {
    const SOURCE: &str = "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\n\
                          ф : {х : Nat} -> Nat -> Nat\nф n = n\n";
    let directory = std::env::temp_dir().join("adamas-lsp-warning");
    std::fs::create_dir_all(&directory).expect("каталог для фикстуры");
    let path = directory.join("warning.adamas");
    std::fs::write(&path, SOURCE).expect("фикстура пишется");

    let (passed, terminal) = driven(&path);
    assert!(passed, "программа обязана быть принята:\n{terminal}");

    let file = source(&path);
    let found = published(&path, &file);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].severity, Some(DiagnosticSeverity::WARNING));
    assert_eq!(
        found[0].range.start,
        adamas_lsp::lsp_types::Position::new(4, 5),
        "пять кодовых единиц UTF-16 до `х`, а байтов было бы шесть"
    );
    assert_eq!(terminal, format!("{}\n", rebuilt(&file, &found[0])));
}

/// Предупреждения без отказа: `analyze` не смешивает исходы.
#[test]
fn a_refusal_and_a_warning_do_not_mix() {
    let uri = Uri::from_str("file:///probe.adamas").expect("URI разбирается");
    let file = SourceFile::new("probe.adamas", "f = (\n");
    let sources = adamas_lsp::project::Buffers::on_disk(".");
    let found = adamas_lsp::diagnostics(&uri, &file, Encoding::Utf16, &sources);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].severity, Some(DiagnosticSeverity::ERROR));
}
