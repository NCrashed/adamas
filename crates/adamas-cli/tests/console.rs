//! `Std.IO` по-настоящему: стандартные ввод и вывод процесса, файлы на диске
//! (§4.4).
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

/// Запуск драйвера с заданным стандартным вводом: `(код возврата, stdout,
/// stderr)`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn driven(file: &Path, args: &[&str], input: &str) -> (Option<i32>, String, String) {
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
        output.status.code(),
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
        let (code, stdout, stderr) = driven(&file, args, "мир\n");
        assert_eq!(code, Some(0), "{args:?} не посчитал:\n{stderr}");
        assert_eq!(stdout, "привет\n6\n", "{args:?}: вывод не тот");
    }
}

#[test]
fn a_unit_answer_is_not_printed() {
    let file = program("hello", HELLO);
    for args in EVALUATORS {
        let (code, stdout, stderr) = driven(&file, args, "мир\n");
        assert_eq!(code, Some(0), "{args:?} не посчитал:\n{stderr}");
        assert_eq!(
            stdout, "Как тебя зовут?\nПривет, мир\n",
            "{args:?}: вывод не тот"
        );
    }
}

#[test]
fn the_end_of_input_is_none_rather_than_an_empty_line() {
    let file = program("eof", GREET);
    let (code, stdout, stderr) = driven(&file, &["eval"], "");
    assert_eq!(code, Some(0), "не посчитал:\n{stderr}");
    // Конец ввода - `None`: ответ 100, а не длина пустого.
    assert_eq!(stdout, "привет\n100\n");
    // Пустая строка - не конец ввода: она есть, и длина её ноль, а `Some`.
    let (code, stdout, stderr) = driven(&file, &["eval"], "\n");
    assert_eq!(code, Some(0), "не посчитал:\n{stderr}");
    assert_eq!(stdout, "привет\n0\n");
}

/// Пишет файл, дописывает его тем же и считает строки.
const LINES: &str = "\
import Std.IO (Console, Files, IOError, Reading, Writing, putLine, reading, writing, appending, nextLine, emitLine)
import Std.Except (Except)

three : {Writing} Unit
three =
  emitLine \"раз\"
  emitLine \"два\"
  emitLine \"три\"

counting : UInt64 -> {Reading} UInt64
counting n =
  let line : Option String = nextLine
  case line of
    None -> n
    Some _line -> counting (addUInt64 n 1)

tally : {Reading} UInt64
tally = counting 0

main : {Console, Files, Except IOError} UInt64
main =
  writing \"out.txt\" three
  appending \"out.txt\" three
  putLine \"записано\"
  reading \"out.txt\" tally
";

/// Читает файл, которого нет.
const MISSING: &str = "\
import Std.IO (Console, Files, IOError, Reading, putLine, reading, nextLine)
import Std.Except (Except)

first : {Reading} UInt64
first =
  let line : Option String = nextLine
  case line of
    None -> 0
    Some _line -> 1

main : {Console, Files, Except IOError} UInt64
main =
  putLine \"до\"
  let n : UInt64 = reading \"нет.txt\" first
  putLine \"после\"
  n
";

#[test]
#[allow(
    clippy::unwrap_used,
    reason = "файл пишет программа: нет его - отказ свидетеля, а не окружения"
)]
fn files_are_written_appended_and_read() {
    let file = program("lines", LINES);
    let written = file.with_file_name("out.txt");
    for args in EVALUATORS {
        let (code, stdout, stderr) = driven(&file, args, "");
        assert_eq!(code, Some(0), "{args:?} не посчитал:\n{stderr}");
        assert_eq!(stdout, "записано\n6\n", "{args:?}: вывод не тот");
        // `writing` обрезает: прогон, идущий вторым, не находит строк первого.
        assert_eq!(
            std::fs::read_to_string(&written).unwrap(),
            "раз\nдва\nтри\nраз\nдва\nтри\n",
            "{args:?}: файл не тот"
        );
    }
}

#[test]
fn a_missing_file_ends_the_program_with_a_message() {
    let file = program("missing", MISSING);
    for args in EVALUATORS {
        let (code, stdout, stderr) = driven(&file, args, "");
        assert_eq!(code, Some(1), "{args:?}: код возврата не тот:\n{stderr}");
        // Отказ обрывает программу: «после» не печатается, ответа нет.
        assert_eq!(stdout, "до\n", "{args:?}: вывод не тот");
        assert!(
            stderr.contains("ошибка: не открывается файл нет.txt\n"),
            "{args:?}: сообщения нет:\n{stderr}"
        );
    }
}

/// Печатает строки файла по мере чтения: колбэк `reading` несёт и `Reading`,
/// и `Console` - метка сверх гасимой проходит насквозь.
const ECHO: &str = "\
import Std.IO (Console, Files, IOError, Reading, putLine, reading, nextLine)
import Std.Except (Except)

echoed : UInt64 -> {Reading, Console} UInt64
echoed n =
  let line : Option String = nextLine
  case line of
    None -> n
    Some s ->
      putLine s
      echoed (addUInt64 n 1)

shown : {Reading, Console} UInt64
shown = echoed 0

main : {Console, Files, Except IOError} UInt64
main = reading \"in.txt\" shown
";

#[test]
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn a_reading_callback_prints_to_the_console() {
    let file = program("echo", ECHO);
    std::fs::write(file.with_file_name("in.txt"), "α\nβ\n").unwrap();
    for args in EVALUATORS {
        let (code, stdout, stderr) = driven(&file, args, "");
        assert_eq!(code, Some(0), "{args:?} не посчитал:\n{stderr}");
        assert_eq!(stdout, "α\nβ\n2\n", "{args:?}: вывод не тот");
    }
}

/// Копирует файл построчно: `writing` внутри колбэка `reading`.
const COPY: &str = "\
import Std.IO (Console, Files, IOError, Reading, Writing, reading, writing, nextLine, emitLine)
import Std.Except (Except)

copying : UInt64 -> {Reading, Writing} UInt64
copying n =
  let line : Option String = nextLine
  case line of
    None -> n
    Some s ->
      emitLine s
      copying (addUInt64 n 1)

into : {Reading, Files, Except IOError} UInt64
into = writing \"out.txt\" (copying 0)

main : {Console, Files, Except IOError} UInt64
main = reading \"in.txt\" into
";

#[test]
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn a_file_is_copied_by_nesting_reading_and_writing() {
    let file = program("copy", COPY);
    std::fs::write(file.with_file_name("in.txt"), "α\nβ\n").unwrap();
    let copy = file.with_file_name("out.txt");
    for args in EVALUATORS {
        let _ = std::fs::remove_file(&copy);
        let (code, stdout, stderr) = driven(&file, args, "");
        assert_eq!(code, Some(0), "{args:?} не посчитал:\n{stderr}");
        assert_eq!(stdout, "2\n", "{args:?}: вывод не тот");
        assert_eq!(
            std::fs::read_to_string(&copy).unwrap(),
            "α\nβ\n",
            "{args:?}: копия не та"
        );
    }
}

#[test]
fn the_block_counters_stay_quiet_without_being_asked() {
    // Счётчики блоков печатаются по `ADAMAS_STATS`, и сюита ставит её себе
    // (`.cargo/config.toml`). Пользователь её не ставит - и его stderr чист.
    let file = program("quiet", HELLO);
    for args in &EVALUATORS[1..] {
        let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
            .args(*args)
            .arg(&file)
            .current_dir(file.parent().unwrap_or(Path::new(".")))
            .env_remove("ADAMAS_STATS")
            .stdin(Stdio::null())
            .output()
            .unwrap_or_else(|why| panic!("{args:?} не запустился: {why}"));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !stderr.contains("блоков выдано"),
            "{args:?}: счётчики без спроса:\n{stderr}"
        );
    }
    // С переменной - на месте: ею живут свидетели течи.
    let (_code, _stdout, stderr) = driven(&file, &["run"], "");
    assert!(stderr.contains("блоков выдано"), "счётчиков нет:\n{stderr}");
}
