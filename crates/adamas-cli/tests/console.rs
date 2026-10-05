//! Консоль `Std.IO` по-настоящему: стандартные ввод и вывод процесса (§4.4).
//!
//! Корпус `eval/` такую программу не берёт: сверка трёх вычислителей ждёт в
//! выводе один ответ, а здесь программа печатает сама. Поэтому сверка - здесь,
//! по точному выводу каждого: машина, C, LLVM.
//!
//! Различает свидетель два дефекта, бывших на пути. Литерал буфера C несёт
//! завершающий ноль, и печать его выдала бы `привет\n\0` - сравнивается вывод
//! целиком, байт в байт. Чтение у конца ввода обязано ответить `None`, а не
//! пустую строку: ввод пуст - ответ `100`, пустая строка - `0`.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Программа: печатает приветствие, читает строку, отвечает её длиной.
const GREET: &str = "\
import Std.IO (Console, putLine, readLine, runConsole, Foreign)

runForeign : {a : Type} -> ((ω u : Unit) -> {Foreign} a) -> a
runForeign k = handle @Foreign k with
  return v -> v

greet : (ω u : Unit) -> {Console} UInt64
greet u =
  putLine \"привет\"
  let line : Option String = readLine
  case line of
    Some (MkString n _bytes) -> n
    None -> 100

main : UInt64
main = runForeign (\\_u -> runConsole greet)
";

/// Пустой каталог под один сценарий, с программой внутри.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn program(case: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("console")
        .join(case);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("greet.adamas");
    std::fs::write(&file, GREET).unwrap();
    file
}

/// Запуск драйвера с заданным стандартным вводом: `(успех, stdout, stderr)`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn driven(file: &Path, args: &[&str], input: &str) -> (bool, Vec<u8>, String) {
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
    (output.status.success(), output.stdout, stderr)
}

/// Вывод программы: у `run` первой строкой драйвер называет собранное -
/// она к программе не относится.
fn printed(stdout: &[u8]) -> Vec<u8> {
    let text = stdout.to_vec();
    let first = text
        .iter()
        .position(|it| *it == b'\n')
        .map_or(text.len(), |at| at + 1);
    if String::from_utf8_lossy(&text[..first]).contains(": собрано в ") {
        text[first..].to_vec()
    } else {
        text
    }
}

#[test]
fn three_evaluators_print_and_read_the_same() {
    let file = program("three");
    for args in [
        &["eval"][..],
        &["run"][..],
        &["run", "--backend", "llvm"][..],
    ] {
        let (ok, stdout, stderr) = driven(&file, args, "мир\n");
        assert!(ok, "{args:?} не посчитал:\n{stderr}");
        assert_eq!(
            String::from_utf8_lossy(&printed(&stdout)),
            "привет\n6\n",
            "{args:?}: вывод не тот (байты: {:?})",
            printed(&stdout)
        );
    }
}

#[test]
fn the_end_of_input_is_none_rather_than_an_empty_line() {
    let file = program("eof");
    let (ok, stdout, stderr) = driven(&file, &["eval"], "");
    assert!(ok, "не посчитал:\n{stderr}");
    // Конец ввода - `None`: ответ 100, а не длина пустого.
    assert_eq!(String::from_utf8_lossy(&printed(&stdout)), "привет\n100\n");
    // Пустая строка - не конец ввода: она есть, и длина её ноль, а `Some`.
    let (ok, stdout, stderr) = driven(&file, &["eval"], "\n");
    assert!(ok, "не посчитал:\n{stderr}");
    assert_eq!(String::from_utf8_lossy(&printed(&stdout)), "привет\n0\n");
}
