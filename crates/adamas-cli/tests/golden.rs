//! Golden-корпус: программы на Adamas проходят путь целиком.
//!
//! Milestone Фазы 2 - «программы парсятся, элаборируются, проходят
//! type-check», - и проверяется он тем же способом, каким его увидит человек:
//! файлом на диске и запуском драйвера. Строка внутри Rust-теста этого не
//! показывает, потому что её нельзя открыть и прочитать.
//!
//! Фикстуры лежат в корне (`tests/golden/`), а не в пакете: одни и те же файлы
//! читают несколько слоёв, и копии по крейтам разъехались бы. Ожидаемый вывод
//! ведётся `insta` - `cargo insta review` после осмысленной правки, а не руками.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Корень корпуса.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

/// Фикстуры директории в порядке имени: снапшоты не должны зависеть от того,
/// в каком порядке их отдала файловая система.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус, и падать он должен громко"
)]
fn fixtures(kind: &str) -> Vec<PathBuf> {
    let dir = corpus().join(kind);
    let mut found: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    found.sort();
    assert!(
        !found.is_empty(),
        "корпус {} пуст: milestone нечем показать",
        dir.display()
    );
    found
}

/// Запускает драйвер и отдаёт его вывод без пути к файлу: путь зависит от
/// того, откуда запущен тест, а снапшот - не должен.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn checked(path: &Path) -> (bool, String) {
    driven("check", path)
}

/// То же для вычисления: значение печатается на stdout.
fn evaluated(path: &Path) -> (bool, String) {
    driven("eval", path)
}

#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn driven(command: &str, path: &Path) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .arg(command)
        .arg(path)
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    let text = if output.status.success() {
        stdout
    } else {
        stderr
    };
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    (
        output.status.success(),
        text.replace(&path.display().to_string(), &name),
    )
}

/// Имя снапшота - имя фикстуры.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: у фикстуры есть имя по построению"
)]
fn name(path: &Path) -> String {
    path.file_stem().unwrap().to_string_lossy().into_owned()
}

#[test]
fn every_program_checks() {
    for path in fixtures("programs") {
        let (passed, text) = checked(&path);
        assert!(passed, "{} отвергнута:\n{text}", path.display());
        insta::assert_snapshot!(format!("programs-{}", name(&path)), text);
    }
}

/// Программа вычисляется, и значение её в снапшоте.
///
/// Это первый способ увидеть построенный терм: до сих пор о нём можно было
/// судить только по тому, отвергла его проверка типов или нет, а ревью Фазы 4
/// показало, что этого мало - пять его находок были «терм тихо неверен».
#[test]
fn every_program_evaluates() {
    for path in fixtures("eval") {
        let (passed, text) = evaluated(&path);
        assert!(passed, "{} не вычислилась:\n{text}", path.display());
        insta::assert_snapshot!(format!("eval-{}", name(&path)), text);
    }
}

// Имя корпуса в имени снапшота: фикстуры разных корпусов вправе называться
// одинаково, а снапшоты живут одной директорией. Пара «отказ и его проходящий
// сосед» под общим именем - приём корпуса, и без префикса он был невозможен.

/// Отвергнутое отвергается **и объясняется**: сообщение целиком в снапшоте,
/// потому что диагностика - обещание Фазы 2 наравне с проверкой типов.
#[test]
fn every_error_is_refused() {
    for path in fixtures("errors") {
        let (passed, text) = checked(&path);
        assert!(!passed, "{} прошла, а не должна была", path.display());
        insta::assert_snapshot!(format!("errors-{}", name(&path)), text);
    }
}
