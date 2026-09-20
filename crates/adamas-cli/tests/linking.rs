//! Секция `[link]` манифеста: проект собирается и **запускается** с чужой
//! библиотекой (§5.3, §7.1).
//!
//! # Почему библиотека своя, а не системная
//!
//! Системная ничего бы не показала: стандартную библиотеку C подключают сами
//! обе стороны - `cc` без единого ключа, машина по [`C_LIBRARY`]. Секция
//! наблюдаема ровно там, где без неё **не работает**, и потому здесь строится
//! настоящая разделяемая библиотека в каталоге проекта: без `-L` её не найдёт
//! компоновщик, без `-l` не найдёт символ, без обоих не найдёт `dlopen`.
//!
//! Собирается она тем же `cc`, каким собран рантайм, и на диске лежит там же,
//! где лежала бы чужая: `vendor/lib/libadamasprobe.so`.
//!
//! # Что здесь проверяется
//!
//! Четыре вещи, и каждая - прогон, а не разбор манифеста.
//!
//! 1. `adamas run` собирает C-путём, линкуется и печатает ответ.
//! 2. `adamas run --backend llvm` делает то же: секция обязана доехать до
//!    линковки объектника `.ll` наравне с `cc`.
//! 3. `adamas eval` отвечает **то же самое**: машина ищет символ по тем же
//!    библиотекам, что и компоновщик.
//! 4. Тот же проект **без** секции не собирается и не считается. Без этой
//!    половины тест был бы зелен и при начисто проигнорированной секции: в
//!    системных каталогах `libadamasprobe.so` нет, но убедиться в этом можно
//!    только отказом.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Чужая библиотека: две функции, и ответ у них такой, какого не даст ошибка.
///
/// `adamas_probe_scale` умножает на семь и прибавляет три: перепутанный порядок
/// аргументов, потерянный вызов или подставленный ноль меняют **число**.
const PROBE: &str = "\
#include <stdint.h>

static uint64_t stashed = 0u;

uint64_t adamas_probe_scale(uint64_t value) {
    return value * 7u + 3u;
}

uint64_t adamas_probe_blend(uint64_t left, uint64_t right) {
    return left * 100u + right;
}

/* Пара, которой наблюдается **`void`-символ**. Иначе он не наблюдаем ничем:
 * значения у него нет по построению, и пропущенный вызов молчит. Измерено
 * мутантом: ветвь `(long) -> void`, не зовущая ничего, не роняла ни одного
 * свидетеля, пока этой пары не было. */
void adamas_probe_stash(uint64_t value) {
    stashed = value;
}

uint64_t adamas_probe_fetch(void) {
    return stashed;
}
";

/// Имя библиотеки в написании `-l`: файл её - `libadamasprobe.so`.
const LIBRARY: &str = "adamasprobe";

/// Каталог библиотеки внутри проекта - относительный, как его пишет манифест.
const VENDOR: &str = "vendor/lib";

/// Программа: четыре чужих вызова четырёх разных форм, ответ - их арифметика.
///
/// `scale 6` даёт 45; `stash 45` кладёт его на чужой стороне, `fetch` достаёт
/// обратно; `blend 45 2` даёт 4502. Пропущенный `stash` - единственный из
/// четырёх, чьё отсутствие не видно **в нём самом**: значения у `void`-символа
/// нет. Видно оно в `fetch`, и потому пара стоит здесь целиком.
const MAIN: &str = "\
data Unit where
  MkUnit : Unit

effect Foreign

extern \"C\" fn adamas_probe_scale : UInt64 -> UInt64

extern \"C\" fn adamas_probe_blend : UInt64 -> UInt64 -> UInt64

extern \"C\" fn adamas_probe_stash : UInt64 -> Unit

extern \"C\" fn adamas_probe_fetch : UInt64

body : (ω u : Unit) -> {Foreign} UInt64
body u =
  let scaled : UInt64 = adamas_probe_scale 6
  let kept : Unit = adamas_probe_stash scaled
  let back : UInt64 = adamas_probe_fetch
  adamas_probe_blend back 2

main : UInt64
main = handle @Foreign body with
  return v -> v
";

/// Ответ программы.
const ANSWER: &str = "4502";

/// Пустой каталог под один сценарий.
fn scratch(case: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("linking")
        .join(case);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Кладёт файл, создавая каталоги по дороге.
fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// Компилятор C: тот же, которым собирает драйвер, если его назвали.
fn cc() -> Command {
    Command::new(
        std::env::var_os(adamas_codegen::native::CC_VARIABLE)
            .filter(|it| !it.is_empty())
            .unwrap_or_else(|| "cc".into()),
    )
}

/// Собирает чужую разделяемую библиотеку в каталоге проекта.
fn probe(dir: &Path) {
    let source = dir.join("probe.c");
    write(&source, PROBE);
    let object = dir.join(VENDOR).join(format!("lib{LIBRARY}.so"));
    std::fs::create_dir_all(object.parent().unwrap()).unwrap();
    let built = cc()
        .args(["-std=c11", "-O1", "-Wall", "-fPIC", "-shared"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "чужая библиотека не собралась:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    assert!(object.is_file(), "библиотеки нет: {}", object.display());
}

/// Проект с секцией `[link]` либо без неё.
fn project(dir: &Path, linked: bool) {
    let section = if linked {
        format!("\n[link]\nlibraries = [\"{LIBRARY}\"]\npaths = [\"{VENDOR}\"]\n")
    } else {
        String::new()
    };
    write(
        &dir.join("adamas.toml"),
        &format!("[package]\nname = \"app\"\n{section}"),
    );
    write(&dir.join("src/Main.adamas"), MAIN);
    probe(dir);
}

/// Запускает драйвер и отдаёт `(успех, stdout, stderr)`.
fn adamas(dir: &Path, args: &[&str]) -> (bool, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .args(args)
        .arg(dir)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    (output.status.success(), stdout, stderr)
}

/// Проект с `[link]` собирается, запускается и считается - тремя путями.
#[test]
fn a_project_links_against_a_foreign_library() {
    let dir = scratch("linked");
    project(&dir, true);

    let (ok, stdout, stderr) = adamas(&dir, &["run"]);
    assert!(ok, "C-путь не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == ANSWER),
        "C-путь посчитал не то:\n{stdout}"
    );

    let (ok, stdout, stderr) = adamas(&dir, &["run", "--backend", "llvm"]);
    assert!(ok, "путь LLVM не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == ANSWER),
        "путь LLVM посчитал не то:\n{stdout}"
    );

    let (ok, stdout, stderr) = adamas(&dir, &["eval"]);
    assert!(ok, "машина не посчитала:\n{stderr}\n{stdout}");
    assert_eq!(stdout, ANSWER, "машина посчитала не то");
}

/// Тот же проект без секции: ни сборки, ни ответа.
///
/// Вторая половина свидетеля выше. Без неё зелёный цвет означал бы только, что
/// `libadamasprobe.so` нашлась - а найтись она могла бы и сама.
#[test]
fn the_same_project_without_the_section_finds_nothing() {
    let dir = scratch("bare");
    project(&dir, false);

    let (ok, stdout, stderr) = adamas(&dir, &["build"]);
    assert!(!ok, "сборка без `[link]` обязана отказать:\n{stdout}");
    assert!(
        stderr.contains("adamas_probe_scale") || stderr.contains(LIBRARY),
        "отказ обязан назвать, чего не хватило:\n{stderr}"
    );

    let (ok, _, stderr) = adamas(&dir, &["eval"]);
    assert!(!ok, "машина без `[link]` обязана отказать");
    assert!(
        stderr.contains("adamas_probe_scale"),
        "отказ машины обязан назвать символ:\n{stderr}"
    );
}
