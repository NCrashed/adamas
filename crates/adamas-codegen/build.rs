//! Пути, без которых порождённый C не собрать: заголовок рантайма, его
//! исходники и компилятор.
//!
//! Заголовок и список единиц трансляции приходят от `adamas-runtime` через
//! `links`-метаданные (`DEP_ADAMAS_RUNTIME_INCLUDE`, `DEP_ADAMAS_RUNTIME_UNITS`).
//! Каталог исходников угадывается рядом с заголовком - и это единственное
//! место, где раскладка чужого крейта угадывается; чтобы догадка не разъехалась
//! молча, наличие файлов проверяется здесь же.
//!
//! Сверх путей отсюда же приезжает **текст** рантайма: таблица «имя файла -
//! содержимое», которую читает [`native`](../adamas_codegen/native/index.html).
//! Пути годятся тестам крейта - они и так бегут в дереве исходников, - а
//! драйверу `adamas build` нужен рантайм у **установленного** бинаря, где
//! дерева нет.

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

    embed(&include, &sources, &units);
}

/// Пишет в `OUT_DIR` литерал таблицы «имя - текст» со всем рантаймом.
///
/// `include_str!`, а не чтение с диска на прогоне: путь, записанный сборкой,
/// указывает в дерево исходников, а установленный `adamas` живёт от него
/// отдельно. Заголовок идёт первым - без него не соберётся ни одна единица.
fn embed(include: &Path, sources: &Path, units: &str) {
    let entry = |name: &str, path: &Path| {
        format!(
            "    ({name:?}, include_str!({:?})),\n",
            path.display().to_string()
        )
    };
    let mut text = String::from("&[\n");
    text.push_str(&entry("adamas.h", &include.join("adamas.h")));
    for source in units.split(',') {
        text.push_str(&entry(source, &sources.join(source)));
    }
    text.push_str("]\n");

    let Some(out) = std::env::var_os("OUT_DIR") else {
        panic!("`OUT_DIR` ставит cargo: без него таблицу рантайма некуда писать");
    };
    let path = PathBuf::from(out).join("runtime.rs");
    if let Err(why) = std::fs::write(&path, text) {
        panic!("таблица рантайма не записалась в {}: {why}", path.display());
    }
}
