//! `adamas repl` (§7.1): сессия прогоном, ввод потоком.
//!
//! Поток, а не терминал: редактор строк включается только на терминале, и
//! сверяется здесь то, что за ним, - разбор ввода, текст сессии, ответ
//! машины. Сверяется **вывод** целиком: код возврата у сессии нулевой и тогда,
//! когда на каждый ввод она отвечала отказом.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Каталог под один сценарий.
fn scratch(case: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("repl")
        .join(case);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Сессия над `args` с вводом `input`: `(stdout, stderr)`.
fn session(dir: &Path, args: &[&str], input: &str) -> (String, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .arg("repl")
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "сессия кончилась отказом");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn declarations_accumulate_and_expressions_are_answered() {
    let dir = scratch("accumulate");
    let (out, err) = session(
        &dir,
        &[],
        "1 + 2\n\
         double : Int -> Int\n\
         double x = x * 2\n\
         double 21\n\
         let x = 3\n\
         x * 2\n\
         case [5, 6] of\n\
         \x20 Nil -> 0\n\
         \x20 Cons y _ -> y\n\
         \n\
         map double [1, 2]\n",
    );
    assert_eq!(out, "3\n42\n6\n5\n[2, 4]\n");
    assert_eq!(err, "", "предупреждений сессия не печатает");
}

/// Отказ объявления текста не трогает: следующее объявление того же имени
/// проходит, как будто первого не было.
#[test]
fn a_refused_declaration_leaves_the_session_as_it_was() {
    let dir = scratch("refused");
    let (out, err) = session(
        &dir,
        &[],
        "f : Int -> Int\nf x = x + True\nf : Int -> Int\nf x = x + 1\nf 1\n",
    );
    assert_eq!(out, "2\n");
    assert!(err.starts_with("Ошибка: ввод:2:"), "{err}");
}

/// Место отказа - в строках ввода, а не накопленного текста.
#[test]
fn a_refusal_points_into_the_input() {
    let dir = scratch("points");
    let (_, err) = session(
        &dir,
        &[],
        "g : Int -> Int\ng x = x\ncase 1 of\n  0 -> g 1\n  _ -> nowhere\n\n",
    );
    assert!(err.contains("ввод:3:8: имя `nowhere` не найдено"), "{err}");
    assert!(
        err.contains("\n    _ -> nowhere\n         ^^^^^^^"),
        "{err}"
    );
}

/// Выражение с эффектом исполняется под `Std.IO.run`, если программа его
/// подключила: так же, как `main` у `adamas eval`.
#[test]
fn an_effectful_expression_runs_under_the_io_handler() {
    let dir = scratch("io");
    let (out, err) = session(&dir, &[], "import Std.IO (putLine)\nputLine \"hello\"\n");
    assert_eq!((out.as_str(), err.as_str()), ("hello\n", ""));
}

/// Файл загружается в сессию, `:reset` возвращает к нему, `:type` печатает
/// то же, что `adamas check --type`.
#[test]
fn a_loaded_file_is_the_start_of_the_session() {
    let dir = scratch("loaded");
    std::fs::write(
        dir.join("Shapes.adamas"),
        "data Shape where\n  Circle : Int -> Shape\n  Square : Int -> Shape\n\n\
         area : Shape -> Int\narea (Circle r) = 3 * r * r\narea (Square s) = s * s\n",
    )
    .unwrap();
    let (out, err) = session(
        &dir,
        &["Shapes.adamas"],
        "area (Square 4)\n\
         twice : Shape -> Int\n\
         twice s = 2 * area s\n\
         twice (Circle 1)\n\
         :type area\n\
         :t map\n\
         :reset\n\
         twice (Circle 1)\n\
         :quit\n\
         area (Square 1)\n",
    );
    let checked = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .args(["check", "Shapes.adamas", "--type", "area"])
        .current_dir(&dir)
        .output()
        .unwrap();
    let area = String::from_utf8_lossy(&checked.stdout);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[..2], ["16", "6"]);
    assert_eq!(lines[2], area.trim_end());
    assert!(lines[3].starts_with("map : "), "{out}");
    assert_eq!(lines.len(), 4, "после `:quit` ввод не читается: {out}");
    assert!(err.contains("имя `twice` не найдено"), "{err}");
}

#[test]
fn an_unknown_command_is_named() {
    let dir = scratch("command");
    let (out, err) = session(&dir, &[], ":frobnicate\n:type\n1\n");
    assert_eq!(out, "1\n");
    assert!(err.contains("команды `:frobnicate` нет"), "{err}");
    assert!(err.contains("`:type` ждёт аргумента"), "{err}");
}

/// Команда посреди ввода в несколько строк его кончает и выполняется
/// следующей: `let` ждёт тела на следующей строке, и `:type` прежде уходил
/// ему продолжением.
#[test]
fn a_command_ends_an_unfinished_input() {
    let dir = scratch("held");
    let (out, err) = session(&dir, &[], "let f = 1\n:type map\n2\n");
    let lines: Vec<&str> = out.lines().collect();
    assert!(
        lines.first().is_some_and(|it| it.starts_with("map : ")),
        "{out}"
    );
    assert_eq!(lines.get(1), Some(&"2"), "{out}");
    assert!(
        err.starts_with("Ошибка: "),
        "незаконченный `let` - отказ: {err}"
    );
}
