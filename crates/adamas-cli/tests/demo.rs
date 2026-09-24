//! Демо Фазы 9 проверяется прогоном: собирается, в каноне, документировано.
//!
//! # Чего этот прогон **не** делает
//!
//! Не запускает игру. Запуск требует либо экрана, либо драйвера `dummy` и
//! минуты кадров, а гейт - ни того, ни другого. Проверяется поэтому то, что
//! проверяемо без окна: программа **собирается обоими понижениями**, лежит в
//! каноне форматтера и несёт документацию.
//!
//! Граница названа, чтобы её не приняли за проверенность: ввод, столкновения и
//! счёт гейтом не исполняются. Исполняются они рукой, и это записано в
//! `docs/phase9-w5-trackD-notes.md`.
//!
//! # Копия модуля SDL
//!
//! Зависимостей по пути в манифесте нет - только git (§7.3), - поэтому демо
//! владеет своей копией `Sdl/Raw.adamas`, а корпус своей. Две копии расходятся
//! молча, и сторожит это `the_sdl_binding_has_not_drifted`: дешевле, чем ждать,
//! пока разойдутся.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Корень репозитория.
fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Каталог демо.
fn demo() -> PathBuf {
    root().join("demo/asteroids")
}

/// Запускает драйвер и отдаёт `(успех, вывод)`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn driven(args: &[&str]) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .args(args)
        .env_remove("RUST_BACKTRACE")
        .env_remove("RUST_LIB_BACKTRACE")
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    (
        output.status.success(),
        if output.status.success() {
            stdout
        } else {
            stderr
        },
    )
}

#[test]
fn the_demo_checks() {
    let (passed, text) = driven(&["check", &demo().display().to_string()]);
    assert!(passed, "демо не проверяется:\n{text}");
}

/// Собирается **обоими** понижениями, и это требование плана волны: демо
/// показывает язык, а не один его бэкенд.
#[test]
fn the_demo_builds_through_both_backends() {
    for backend in ["c", "llvm"] {
        let (passed, text) =
            driven(&["build", "--backend", backend, &demo().display().to_string()]);
        assert!(passed, "демо не собралось через {backend}:\n{text}");
    }
}

#[test]
fn the_demo_is_canonical() {
    let (passed, text) = driven(&["fmt", "--check", &demo().display().to_string()]);
    assert!(passed, "демо разошлось с каноном:\n{text}");
}

/// Демо документировано, и это не украшение: оно пишется для внешнего читателя,
/// а голая программа без рассказа показывает синтаксис, а не язык.
#[test]
fn the_demo_is_documented() {
    let (passed, text) = driven(&["doc", &demo().display().to_string()]);
    assert!(passed, "демо не документируется:\n{text}");
    let sections = text.lines().filter(|it| it.starts_with("## ")).count();
    assert!(
        sections >= 60,
        "документированных имён {sections} - для программы в тысячу строк это мало:\n{text}"
    );
}

/// Копия биндинга у демо и у корпуса совпадает побайтно.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отсутствие файла здесь означает сломанное дерево"
)]
#[test]
fn the_sdl_binding_has_not_drifted() {
    let theirs = std::fs::read_to_string(root().join("tests/golden/eval/Sdl/Raw.adamas")).unwrap();
    let ours = std::fs::read_to_string(demo().join("Sdl/Raw.adamas")).unwrap();
    assert_eq!(
        ours, theirs,
        "копии `Sdl/Raw.adamas` разошлись: зависимостей по пути нет, и держать их вместе больше нечем"
    );
}
