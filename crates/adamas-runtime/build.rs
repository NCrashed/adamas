//! Сборка C-рантайма и путь к его заголовку для потребителей.

use std::path::PathBuf;

/// Исходники рантайма в порядке слоёв: объекты, вектор, замыкания, кадры.
const SOURCES: [&str; 4] = ["c/object.c", "c/evidence.c", "c/closure.c", "c/frame.c"];

fn main() {
    let manifest = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap_or_default());
    let include = manifest.join("include");

    let mut build = cc::Build::new();
    build.std("c11").warnings(true).include(&include);
    // Обёртки gcc, добавляющие `-D_FORTIFY_SOURCE` (Nix и дистрибутивные),
    // без оптимизации выдают `#warning` о нём же на каждый файл - тридцать
    // строк, под которыми не видно `-Wall`. Снять определение нечем: обёртка
    // дописывает его после наших флагов. Гасится сам класс `#warning`, и
    // только там, где он весь состоит из этого сообщения.
    let msvc = std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc");
    if !msvc && std::env::var("OPT_LEVEL").as_deref() == Ok("0") {
        build.flag("-Wno-cpp");
    }
    for source in SOURCES {
        build.file(manifest.join(source));
    }
    build.compile("adamas_runtime");

    // Пересборка просится **на каждый** исходник поимённо. Первая же порция
    // мутантов выжила целиком именно здесь: `cc` о зависимостях не сообщает, а
    // одного `rerun-if-changed` довольно, чтобы cargo перестал следить за всем
    // остальным, - правка в `.c` не доезжала до теста вовсе.
    for source in SOURCES {
        println!(
            "cargo::rerun-if-changed={}",
            manifest.join(source).display()
        );
    }
    println!(
        "cargo::rerun-if-changed={}",
        include.join("adamas.h").display()
    );
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::metadata=include={}", include.display());
}
