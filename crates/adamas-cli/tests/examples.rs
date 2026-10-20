//! Примеры из `docs/examples/` проверяются прогоном, а не чтением.
//!
//! # Зачем прогон
//!
//! Пример - это обещание, и обещание тем дороже, чем дольше оно не проверено.
//! Цена измерена на соседней стопке: примеры §5.3 за Фазу 8 правились **семь
//! раз**, и каждое расхождение с языком находилось прогоном, а не глазами.
//! Непроверяемая копия §4 расходится с оригиналом тем быстрее, чем она длиннее.
//!
//! Раньше `docs/examples/` был пуст **нарочно**, и довод в его `README` был
//! ровно этот. Волна 4 Фазы 9 довод не отменила - она сняла его условие:
//! примеры входят в гейт, поэтому протухнуть молча им больше нечем.
//!
//! # Чем этот свидетель ломается
//!
//! Проверок четыре, и каждая ловит свой род протухания.
//!
//! 1. **`check`** - пример разошёлся с языком и перестал проверяться.
//! 2. **`eval`** - пример проверяется, но считает не то. Ответ записан
//!    снапшотом: рассказ в комментариях называет числа, и молча разойтись с
//!    ними нельзя.
//! 3. **`doc`** - пример перестал быть документированным. Примеры пишутся для
//!    человека, и голый код без рассказа - это фикстура, которой место в
//!    `tests/golden/`.
//! 4. **`fmt --check`** - пример разошёлся с каноном. Показывать читателю
//!    запись, которую форматтер тут же перепишет, значит учить не тому.
//!
//! Плюс сам счёт: пустой каталог красит прогон. Иначе все четыре проверки были
//! бы зелены ровно тогда, когда примеров нет.
//!
//! # Проекты
//!
//! Каталог с манифестом - пример в масштабе программы (демо-компилятор Фазы
//! 9). Он проходит те же четыре проверки и ещё две, которых у файла нет: его
//! тесты (`adamas test`) проходят, а собранный через C и через LLVM бинарь
//! печатает то же, что машина. Файлам вторая не нужна - её держит корпус
//! (`agreement.rs`, `llvm.rs`), а проект в корпус не входит.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Каталог примеров.
fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/examples")
}

/// Примеры в порядке имени: снапшоты не должны зависеть от файловой системы.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное дерево, и падать он должен громко"
)]
fn fixtures() -> Vec<PathBuf> {
    let dir = examples();
    let mut found: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    found.sort();
    // Каталог, из которого примеры вынесли, обязан красить прогон: без этого
    // все проверки ниже зелены на пустом множестве.
    assert!(
        found.len() >= 4,
        "примеров осталось {}: язык показывают кратности, эффекты, регионы и FFI",
        found.len()
    );
    found
}

/// Запускает драйвер и отдаёт `(успех, вывод)` без пути к файлу.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn driven(command: &str, path: &Path, extra: &[&str]) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .arg(command)
        .arg(path)
        .args(extra)
        .env_remove("RUST_BACKTRACE")
        .env_remove("RUST_LIB_BACKTRACE")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    let text = if output.status.success() {
        stdout
    } else {
        stderr
    };
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    (
        output.status.success(),
        text.replace(&path.display().to_string(), &name),
    )
}

/// Имя примера - имя снапшота.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: у файла есть имя по построению"
)]
fn name(path: &Path) -> String {
    path.file_stem().unwrap().to_string_lossy().into_owned()
}

#[test]
fn every_example_checks() {
    for path in fixtures() {
        let (passed, text) = driven("check", &path, &[]);
        assert!(passed, "{} не проверяется:\n{text}", path.display());
    }
}

/// Ответ примера записан: рассказ в комментариях называет числа, и разойтись с
/// ними молча нельзя.
#[test]
fn every_example_computes_what_it_says() {
    for path in fixtures() {
        let (passed, text) = driven("eval", &path, &[]);
        assert!(passed, "{} не вычислился:\n{text}", path.display());
        insta::assert_snapshot!(format!("example-{}", name(&path)), text);
    }
}

/// Пример документирован: он пишется для человека, и голый код без рассказа -
/// это фикстура, а фикстурам место в `tests/golden/`.
#[test]
fn every_example_is_documented() {
    for path in fixtures() {
        let (passed, text) = driven("doc", &path, &[]);
        assert!(passed, "{} не документируется:\n{text}", path.display());
        let sections = text.lines().filter(|it| it.starts_with("## ")).count();
        assert!(
            sections >= 3,
            "{}: документированных имён {sections}, а пример пишется для человека",
            path.display()
        );
    }
}

/// Пример написан каноном: показывать запись, которую форматтер тут же
/// перепишет, значит учить не тому.
#[test]
fn every_example_is_canonical() {
    let (passed, text) = driven("fmt", &examples(), &["--check"]);
    assert!(passed, "примеры разошлись с каноном:\n{text}");
}

// --- проекты -------------------------------------------------------------

/// Проекты примеров: каталоги с манифестом, в порядке имени.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное дерево, и падать он должен громко"
)]
fn projects() -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = std::fs::read_dir(examples())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("adamas.toml").is_file())
        .collect();
    found.sort();
    // Тот же довод, что у файлов: проверки ниже зелены на пустом множестве.
    assert!(
        !found.is_empty(),
        "проектов не осталось: демо-компилятор Фазы 9 показывает язык в масштабе"
    );
    found
}

/// Копия проекта во временном каталоге: сборка пишет артефакты рядом с
/// манифестом, и в дереве репозитория им не место. Копия на каждый бэкенд -
/// прогоны идут параллельно.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn copied(project: &Path, case: &str) -> PathBuf {
    fn copy(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap();
            if name == ".adamas" {
                continue;
            }
            if path.is_dir() {
                copy(&path, &to.join(name));
            } else {
                std::fs::copy(&path, to.join(name)).unwrap();
            }
        }
    }
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("examples")
        .join(format!("{}-{case}", name(project)))
        .join(name(project));
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    copy(project, &dir);
    dir
}

#[test]
fn every_project_checks() {
    for path in projects() {
        let (passed, text) = driven("check", &path, &[]);
        assert!(passed, "{} не проверяется:\n{text}", path.display());
    }
}

/// Ответ проекта записан, как у файла.
#[test]
fn every_project_computes_what_it_says() {
    for path in projects() {
        let (passed, text) = driven("eval", &path, &[]);
        assert!(passed, "{} не вычислился:\n{text}", path.display());
        insta::assert_snapshot!(format!("project-{}", name(&path)), text);
    }
}

/// Тесты проекта (`src/Test.adamas`) проходят: проект показывает и то, как на
/// языке пишут проверки.
#[test]
fn every_project_passes_its_tests() {
    for path in projects() {
        let (passed, text) = driven("test", &path, &[]);
        assert!(passed, "{}: тесты не прошли:\n{text}", path.display());
        assert!(
            text.contains("отказов 0"),
            "{}: прогон тестов не назвал счёт:\n{text}",
            path.display()
        );
    }
}

#[test]
fn every_project_is_documented() {
    for path in projects() {
        let (passed, text) = driven("doc", &path, &[]);
        assert!(passed, "{} не документируется:\n{text}", path.display());
        let sections = text.lines().filter(|it| it.starts_with("## ")).count();
        assert!(
            sections >= 3,
            "{}: документированных имён {sections}",
            path.display()
        );
    }
}

/// Собранный проект отвечает то же, что машина, обоими бэкендами (§8).
#[test]
fn every_project_runs_as_it_evaluates() {
    for path in projects() {
        let (_, evaluated) = driven("eval", &path, &[]);
        for backend in ["c", "llvm"] {
            let dir = copied(&path, backend);
            let (passed, text) = driven("run", &dir, &["--backend", backend]);
            assert!(
                passed,
                "{} ({backend}) не собрался:\n{text}",
                path.display()
            );
            assert_eq!(
                text,
                evaluated,
                "{} ({backend}) разошёлся с машиной",
                path.display()
            );
        }
    }
}
