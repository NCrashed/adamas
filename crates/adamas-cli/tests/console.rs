//! Консоль `Std.IO` по-настоящему: стандартные ввод и вывод процесса (§4.4).
//!
//! Корпус `eval/` такую программу не берёт: сверка трёх вычислителей ждёт в
//! выводе один ответ, а здесь программа печатает сама. Поэтому сверка - здесь,
//! по точному выводу каждого: машина, C, LLVM.
//!
//! Различает свидетель дефекты, бывшие на пути. Литерал буфера C несёт
//! завершающий ноль, и печать его выдала бы `привет\n\0` - сравнивается вывод
//! целиком, байт в байт. Чтение у конца ввода обязано ответить `None`, а не
//! пустую строку: ввод пуст - ответ `100`, пустая строка - `0`. Терм входа,
//! собранный из тела `main`, а не из ссылки на него, терял у сборки весь вывод
//! литералов - машина при этом печатала верно.
//!
//! `main` эффектный: хендлер ставит драйвер (§10 вопрос 12), и stdout
//! принадлежит программе целиком - строка «собрано в» уходит в stderr, ответ
//! `Unit` не печатается.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Печатает приветствие, читает строку, отвечает её длиной.
const GREET: &str = "\
import Std.IO (Console, putLine, readLine)

main : {Console} UInt64
main =
  putLine \"привет\"
  let line : Option String = readLine
  case line of
    Some (MkString n _bytes) -> n
    None -> 100
";

/// Ответ - единица: весь смысл программы в её выводе.
const HELLO: &str = "\
import Std.IO (Console, putLine, readLine)

main : {Console} Unit
main =
  putLine \"Как тебя зовут?\"
  let name : Option String = readLine
  case name of
    Some n ->
      putStr \"Привет, \"
      putLine n
    None -> putLine \"Тишина.\"
";

/// Пустой каталог под один сценарий, с программой внутри.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn program(case: &str, text: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("console")
        .join(case);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.adamas");
    std::fs::write(&file, text).unwrap();
    file
}

/// Запуск драйвера с заданным стандартным вводом: `(успех, stdout, stderr)`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn driven(file: &Path, args: &[&str], input: &str) -> (bool, String, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .args(args)
        .arg(file)
        .current_dir(file.parent().unwrap())
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
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr,
    )
}

/// Машина, C и LLVM.
const EVALUATORS: [&[&str]; 3] = [&["eval"], &["run"], &["run", "--backend", "llvm"]];

#[test]
fn three_evaluators_print_and_read_the_same() {
    let file = program("three", GREET);
    for args in EVALUATORS {
        let (ok, stdout, stderr) = driven(&file, args, "мир\n");
        assert!(ok, "{args:?} не посчитал:\n{stderr}");
        assert_eq!(stdout, "привет\n6\n", "{args:?}: вывод не тот");
    }
}

#[test]
fn a_unit_answer_is_not_printed() {
    let file = program("hello", HELLO);
    for args in EVALUATORS {
        let (ok, stdout, stderr) = driven(&file, args, "мир\n");
        assert!(ok, "{args:?} не посчитал:\n{stderr}");
        assert_eq!(
            stdout, "Как тебя зовут?\nПривет, мир\n",
            "{args:?}: вывод не тот"
        );
    }
}

#[test]
fn the_end_of_input_is_none_rather_than_an_empty_line() {
    let file = program("eof", GREET);
    let (ok, stdout, stderr) = driven(&file, &["eval"], "");
    assert!(ok, "не посчитал:\n{stderr}");
    // Конец ввода - `None`: ответ 100, а не длина пустого.
    assert_eq!(stdout, "привет\n100\n");
    // Пустая строка - не конец ввода: она есть, и длина её ноль, а `Some`.
    let (ok, stdout, stderr) = driven(&file, &["eval"], "\n");
    assert!(ok, "не посчитал:\n{stderr}");
    assert_eq!(stdout, "привет\n0\n");
}
