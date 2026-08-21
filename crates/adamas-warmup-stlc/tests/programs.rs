//! Прогон подготовленных программ через весь конвейер.
//!
//! Acceptance criterion Фазы 0 (§9): "3-5 подготовленных example программ
//! парсятся, типизируются, исполняются корректно". Проверка снапшотом, а не
//! набором `assert_eq!`, потому что интересен не факт "не упало", а то, какие
//! именно типы выводятся - регрессия в обобщении меняет их молча.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use adamas_core::source::SourceFile;
use adamas_warmup_stlc::run;

#[test]
fn examples_typecheck_and_evaluate() {
    // Сбор списка живёт внутри теста, а не в помощнике: `expect` разрешён
    // clippy только в теле тестовой функции (clippy.toml).
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("директория с примерами существует")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "stlc"))
        .collect();
    // Порядок обхода директории не определён, а снапшот обязан быть стабилен.
    paths.sort();

    assert!(
        paths.len() >= 3,
        "§9 требует минимум три примера, найдено {}",
        paths.len()
    );

    let mut report = String::new();
    for path in paths {
        let name = path
            .file_name()
            .map_or_else(|| "?".to_owned(), |n| n.to_string_lossy().into_owned());
        let text = std::fs::read_to_string(&path).expect("пример читается");
        let file = SourceFile::new(name.clone(), text);

        match run(&file) {
            Ok(outcome) => {
                let _ = writeln!(report, "{name}");
                let _ = writeln!(report, "  тип:      {}", outcome.ty);
                let _ = writeln!(report, "  значение: {}\n", outcome.value);
            }
            Err(error) => panic!("{name} не прошла конвейер:\n{}", error.render(&file)),
        }
    }

    insta::assert_snapshot!(report);
}
