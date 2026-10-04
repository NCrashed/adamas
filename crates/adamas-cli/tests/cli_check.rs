//! End-to-end проверка драйвера: программа проходит путь целиком.
//!
//! Это milestone Фазы 2, увиденный снаружи: «argv -> clap -> парсер ->
//! элаборация -> проверка типов -> код возврата».

use std::path::PathBuf;
use std::process::Command;

fn adamas() -> Command {
    Command::new(env!("CARGO_BIN_EXE_adamas"))
}

/// Кладёт исходник во временный файл. `CARGO_TARGET_TMPDIR` уникален для
/// пакета и чистится вместе с `target/`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn source(name: &str, text: &str) -> PathBuf {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("check");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path
}

const PROGRAM: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)
";

#[test]
fn a_correct_program_checks() {
    let path = source("good.adamas", PROGRAM);
    let output = adamas().arg("check").arg(&path).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    assert!(!stderr.contains("panicked"), "driver panicked: {stderr}");
    assert!(output.status.success(), "проверка не прошла: {stderr}");
    assert!(stdout.contains("проверено"), "unexpected stdout: {stdout}");
}

#[test]
fn a_refused_program_points_at_the_line() {
    // Спан у элаборации есть, и диагностика обязана им пользоваться: без
    // позиции сообщение «не конструктор» отправляет искать по всему файлу.
    let path = source(
        "bad.adamas",
        &format!("{PROGRAM}\nf : Nat -> Nat\nf Zeroo = Zero\n"),
    );
    let output = adamas().arg("check").arg(&path).output().unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    assert!(!stderr.contains("panicked"), "driver panicked: {stderr}");
    assert!(!output.status.success(), "отказ обязан быть ненулевым");
    assert!(stderr.contains("Zeroo"), "unhelpful error: {stderr}");
    assert!(stderr.contains(":10:"), "нет номера строки: {stderr}");
    assert!(stderr.contains('^'), "нет подчёркивания: {stderr}");
}

#[test]
fn a_syntax_error_is_reported_the_same_way() {
    let path = source("syntax.adamas", "f =\nx\n");
    let output = adamas().arg("check").arg(&path).output().unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    assert!(!stderr.contains("panicked"), "driver panicked: {stderr}");
    assert!(!output.status.success());
    assert!(stderr.contains("отступ"), "unexpected error: {stderr}");
}

/// Программа из двух файлов проходит драйвером (§4.8).
///
/// Свидетель парный: та же программа без `import` обязана быть отвергнута -
/// своего `Numbers.double` у входного файла нет. Без второй половины тест
/// проходил бы и при начисто сломанном разрешении имён между файлами.
#[test]
fn a_program_of_two_files_checks_and_evaluates() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("project");
    std::fs::create_dir_all(dir.join("Numbers")).unwrap();
    std::fs::write(
        dir.join("Numbers/Peano.adamas"),
        format!("{PROGRAM}\ndouble : Nat -> Nat\ndouble n = plus n n\n"),
    )
    .unwrap();
    let entry = dir.join("main.adamas");
    let text = "\
import Numbers.Peano as P

main : P.Nat
main = P.double (P.Succ P.Zero)
";
    std::fs::write(&entry, text).unwrap();

    let output = adamas().arg("check").arg(&entry).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    assert!(output.status.success(), "проверка не прошла: {stderr}");
    assert!(stdout.contains("файлов 2"), "неожиданный вывод: {stdout}");

    let output = adamas().arg("eval").arg(&entry).output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("Numbers.Peano.Succ"),
        "ответ собран не из подключённого файла: {stdout}"
    );

    // Вторая половина пары.
    std::fs::write(&entry, text.replace("import Numbers.Peano as P\n", "")).unwrap();
    let output = adamas().arg("check").arg(&entry).output().unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        !output.status.success(),
        "без импорта имя нашлось: {stderr}"
    );
}

/// Отказ внутри подключённого файла указывает на **него**, а не на входной.
#[test]
fn a_refusal_inside_an_imported_file_names_that_file() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("broken");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("Broken.adamas"),
        format!("{PROGRAM}\nf : Nat -> Nat\nf Zeroo = Zero\n"),
    )
    .unwrap();
    let entry = dir.join("uses.adamas");
    std::fs::write(&entry, "import Broken (Nat)\n").unwrap();

    let output = adamas().arg("check").arg(&entry).output().unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    assert!(!output.status.success());
    assert!(
        stderr.contains("Broken.adamas") && stderr.contains("Zeroo"),
        "отказ обязан назвать чужой файл и место в нём: {stderr}"
    );
}

/// Корень входного файла подключённому модулю не подключён (§4.8, §10 вопрос
/// 193): модуль, звавший `helper` входного файла, которого не объявлял и не
/// подключал, отвергается в **своём** файле. Прежде голое имя падало в общую
/// таблицу и находило корневое объявление, стоявшее выше строки `import`, -
/// библиотека не проверялась в одиночку, а перестановка объявления ниже
/// `import` роняла программу отказом в чужом файле.
#[test]
fn a_module_does_not_see_the_entry_root() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("leaky");
    std::fs::create_dir_all(dir.join("Leaky")).unwrap();
    std::fs::write(
        dir.join("Leaky").join("Uses.adamas"),
        "twice : Nat -> Nat\ntwice n = helper (helper n)\n",
    )
    .unwrap();
    let entry = dir.join("main.adamas");
    std::fs::write(
        &entry,
        format!(
            "{PROGRAM}\nhelper : Nat -> Nat\nhelper n = Succ n\n\nimport Leaky.Uses (twice)\n\nmain : Nat\nmain = twice Zero\n"
        ),
    )
    .unwrap();

    let output = adamas().arg("check").arg(&entry).output().unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    assert!(
        !output.status.success(),
        "модуль увидел корень входного файла"
    );
    assert!(
        stderr.contains("Uses.adamas") && stderr.contains("`Nat` не найдено"),
        "отказ обязан стоять в подключённом модуле: {stderr}"
    );
}

#[test]
fn missing_file_fails_without_panic() {
    let output = adamas()
        .arg("check")
        .arg("does-not-exist.adamas")
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    assert!(!output.status.success());
    assert!(!stderr.contains("panicked"), "driver panicked: {stderr}");
    assert!(
        stderr.contains("does-not-exist.adamas"),
        "unhelpful error: {stderr}"
    );
}
