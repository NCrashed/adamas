//! Пути, без которых порождённый C не собрать: заголовок рантайма, его
//! исходники и компилятор.
//!
//! Заголовок и список единиц трансляции приходят от `adamas-runtime` через
//! `links`-метаданные (`DEP_ADAMAS_RUNTIME_INCLUDE`, `DEP_ADAMAS_RUNTIME_UNITS`).
//! Каталог исходников угадывается рядом с заголовком - и это единственное
//! место, где раскладка чужого крейта угадывается; чтобы догадка не разъехалась
//! молча, наличие файлов проверяется здесь же.

use std::path::{Path, PathBuf};

fn main() {
    let Some(include) = std::env::var_os("DEP_ADAMAS_RUNTIME_INCLUDE") else {
        panic!("путь к заголовку приходит от `adamas-runtime`: он объявлен зависимостью");
    };
    let include = PathBuf::from(include);
    assert!(
        include.join("adamas.h").is_file(),
        "заголовок рантайма не найден в {}",
        include.display()
    );

    // Список единиц трансляции приходит **от рантайма** тем же путём, что путь
    // к заголовку: второй копией он разъезжался бы молча, и порождённый C
    // переставал бы линковаться на первом же новом слое.
    let Some(units) = std::env::var_os("DEP_ADAMAS_RUNTIME_UNITS") else {
        panic!("список исходников приходит от `adamas-runtime`: он объявлен зависимостью");
    };
    let units = units.to_string_lossy().into_owned();

    let sources = include.parent().unwrap_or(Path::new(".")).join("c");
    for source in units.split(',') {
        let path = sources.join(source);
        assert!(
            path.is_file(),
            "исходник рантайма {} не найден: раскладка крейта разъехалась",
            path.display()
        );
        println!("cargo::rerun-if-changed={}", path.display());
    }
    println!(
        "cargo::rerun-if-changed={}",
        include.join("adamas.h").display()
    );

    // Компилятор берётся тот же, каким `cc` собирает сам рантайм: в Nix-среде
    // он не `cc` из PATH.
    let compiler = cc::Build::new().get_compiler();

    println!(
        "cargo::rustc-env=ADAMAS_RUNTIME_INCLUDE={}",
        include.display()
    );
    println!(
        "cargo::rustc-env=ADAMAS_RUNTIME_SOURCES={}",
        sources.display()
    );
    println!("cargo::rustc-env=ADAMAS_RUNTIME_UNITS={units}");
    println!("cargo::rustc-env=ADAMAS_CC={}", compiler.path().display());
    println!("cargo::rerun-if-changed=build.rs");
}
