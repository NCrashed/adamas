//! `adamas new`/`build`/`run`/`test` (§7.1): каждая команда - прогоном.
//!
//! # Жанр подделки, от которого написан этот файл
//!
//! Команда, которая «отработала». Прогон, сверяющий код возврата с нулём,
//! зелен и тогда, когда команда не сделала ничего: волна 1 Фазы 9 поймала это
//! трижды подряд на упаковке расширения - `vsce` рапортовал успех, молча
//! упаковав пустоту. Поэтому здесь сверяется **результат**, а не код возврата:
//!
//! - `new` - что заведённый проект проверяется, собирается и тестируется;
//! - `build` - что собранный файл **запускается** и печатает то же, что
//!   `adamas eval`, то есть договор трёх вычислителей цел и в драйвере;
//! - `test` - что он **краснеет** на сломанном, и краснеет тремя разными
//!   способами: отказавший тест, тест не того типа, и тестов ноль.
//!
//! # Окружение
//!
//! Каждый запуск драйвера идёт с выключенной конфигурацией машины
//! (`GIT_CONFIG_GLOBAL`, `GIT_CONFIG_SYSTEM`). Трек C волны 2 поймал у себя
//! ровно это: фикстура подхватывала `commit.gpgsign` из `~/.gitconfig`
//! разработчика, и сюита была зелена по случайности - в другом прогоне
//! pinentry не ответил и дал шесть красных из шести.

use std::path::{Path, PathBuf};
use std::process::Command;

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
mod fixture {
    use super::{Command, Path, PathBuf};

    /// Пустой каталог под один сценарий.
    pub(crate) fn scratch(case: &str) -> PathBuf {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("commands")
            .join(case);
        if dir.exists() {
            std::fs::remove_dir_all(&dir).unwrap();
        }
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Драйвер, которому ничего не достаётся от машины.
    pub(crate) fn adamas() -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_adamas"));
        command
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("GIT_TERMINAL_PROMPT", "0");
        command
    }

    /// Запускает команду и отдаёт `(успех, stdout, stderr)`.
    pub(crate) fn run(command: &mut Command) -> (bool, String, String) {
        let output = command.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
        (output.status.success(), stdout, stderr)
    }

    /// Читает файл проекта.
    pub(crate) fn read(path: &Path) -> String {
        std::fs::read_to_string(path).unwrap()
    }

    /// Кладёт файл, создавая каталоги по дороге.
    pub(crate) fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    /// Корпус: `crates/adamas-cli` - два уровня от корня дерева.
    pub(crate) fn corpus() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/golden")
            .canonicalize()
            .unwrap()
    }

    /// Копирует дерево целиком: корпусный проект собирается **не в корпусе**,
    /// иначе прогон оставлял бы в дереве исходников `.adamas/` с объектниками.
    pub(crate) fn copied(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let at = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copied(&entry.path(), &at);
            } else {
                std::fs::copy(entry.path(), at).unwrap();
            }
        }
    }

    /// Запускает собранный файл и отдаёт то, что он напечатал на stdout.
    pub(crate) fn executed(binary: &Path) -> String {
        let output = Command::new(binary).output().unwrap();
        assert!(
            output.status.success(),
            "{}: прогон оборвался:\n{}",
            binary.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    }
}

use fixture::{adamas, copied, corpus, executed, read, run, scratch, write};

/// Милестоун трека: заведённый проект проверяется, собирается и тестируется.
///
/// Свидетель различающий по построению. `check` мог бы пройти и над пустым
/// файлом - поэтому сверяется счёт объявлений; `build` мог бы «отработать», не
/// породив ничего, - поэтому собранный файл **запускается**, и его ответ
/// сверяется с ответом машины; `test` мог бы уйти с нулём, не найдя ни одного
/// теста, - поэтому сверяется счёт тестов.
#[test]
fn a_new_project_checks_builds_runs_and_tests() {
    let case = scratch("new");
    let app = case.join("demo");
    let (ok, stdout, stderr) = run(adamas().arg("new").arg(&app));
    assert!(ok, "проект не завёлся: {stderr}");
    assert!(stdout.contains("demo"), "неожиданный вывод: {stdout}");

    // Раскладка - та, которую читает `Directory::file_of` при умолчаниях
    // манифеста: `root = "src"`, `entry = "Main"`, `test = "Test"`.
    for at in ["adamas.toml", "src/Main.adamas", "src/Test.adamas"] {
        assert!(app.join(at).is_file(), "{at} не положен");
    }

    let (ok, stdout, stderr) = run(adamas().arg("check").arg(&app));
    assert!(ok, "заготовка не проверилась: {stderr}");
    assert!(
        stdout.contains("объявлений 6"),
        "неожиданный вывод: {stdout}"
    );

    let (ok, expected, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "заготовка не посчиталась: {stderr}");
    assert_eq!(expected, "Succ (Succ (Succ (Succ Zero)))");

    let (ok, stdout, stderr) = run(adamas().arg("build").arg(&app));
    assert!(ok, "заготовка не собралась: {stderr}");
    let binary = app.join(".adamas/build/demo");
    assert!(binary.is_file(), "артефакта нет: {stdout}");
    assert_eq!(
        executed(&binary),
        expected,
        "собранное посчитало не то, что машина"
    );

    let (ok, stdout, stderr) = run(adamas().arg("run").arg(&app));
    assert!(ok, "заготовка не запустилась: {stderr}");
    assert!(stdout.contains(&expected), "`run` напечатал: {stdout}");

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(ok, "тесты заготовки не прошли: {stderr}\n{stdout}");
    assert!(
        stdout.contains("тестов 2, отказов 0"),
        "неожиданный вывод: {stdout}"
    );
}

/// Тесты заготовки считают **написанное в другом файле**, и ломается это
/// правкой того файла.
///
/// Без этой половины `adamas new` проверялся бы тем, что тесты зелены, - а
/// зелены они и у сюиты, которая ничего не спрашивает у программы. `Test`
/// не объявляет ни `Nat`, ни `plus`, ни `double`: всё приходит из `Main`.
#[test]
fn the_template_tests_reach_into_the_entry_module() {
    let case = scratch("reach");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));

    let entry = app.join("src/Main.adamas");
    let broken = read(&entry).replace("double n = plus n n", "double n = n");
    write(&entry, &broken);

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(!ok, "сломанный `double` не уронил тестов: {stdout}{stderr}");
    assert!(
        stdout.contains("testDoubleAddsToItself: ОТКАЗ"),
        "отказ обязан назвать тест: {stdout}"
    );
    assert!(
        stdout.contains("testPlusIsLeftNeutral: ok"),
        "уцелевший тест обязан остаться зелёным: {stdout}"
    );
    assert!(
        stdout.contains("тестов 2, отказов 1"),
        "неожиданный счёт: {stdout}"
    );
}

/// Собранный файл печатает то же, что машина, на **десятифайловой** программе.
///
/// Корпусный проект (трек B) для того и годится: во входном файле не объявлено
/// ни одного имени счёта, весь ответ собран из девяти модулей `Std/*`. Сломай
/// что-нибудь между понижением и линковкой - и ответы разойдутся.
#[test]
fn a_built_program_answers_what_the_machine_answers() {
    let case = scratch("corpus");
    let app = case.join("project");
    copied(&corpus().join("project"), &app);

    let (ok, expected, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "корпусный проект не посчитался: {stderr}");
    assert!(expected.contains("Std.Base.Cons"), "{expected}");

    let (ok, _, stderr) = run(adamas().arg("build").arg(&app));
    assert!(ok, "корпусный проект не собрался: {stderr}");
    assert_eq!(
        executed(&app.join(".adamas/build/project")),
        expected,
        "собранное посчитало не то, что машина"
    );
}

/// Второй бэкенд собирает **то же**, и это тот же договор, что у первого.
///
/// Правило отсутствия LLVM - одно на всех свидетелей LLVM-пути
/// (`adamas-codegen`, `tests/harness`): `ADAMAS_LLVM=absent` и ничего больше.
#[test]
fn both_backends_answer_the_same() {
    if std::env::var("ADAMAS_LLVM").is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим (ADAMAS_LLVM=absent): договор не проверялся");
        return;
    }
    let case = scratch("backends");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));

    let (ok, expected, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "заготовка не посчиталась: {stderr}");

    for backend in ["c", "llvm"] {
        let (ok, _, stderr) = run(adamas().arg("build").arg(&app).args(["--backend", backend]));
        assert!(ok, "{backend}: сборка отказала: {stderr}");
        assert_eq!(
            executed(&app.join(".adamas/build/demo")),
            expected,
            "{backend}: посчитал не то, что машина"
        );
    }
}

/// Цепочки LLVM нет - отказ **называет** инструмент, а не падает и не молчит.
///
/// `PATH` пуст, а `ADAMAS_LLVM_BIN` снят: в dev-shell он выставлен, и без
/// снятия прогон брал бы инструменты оттуда.
#[test]
fn a_missing_llvm_toolchain_is_refused_by_name() {
    let case = scratch("no-llvm");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));

    let (ok, _, stderr) = run(adamas()
        .env("PATH", "")
        .env_remove(adamas_codegen::llvm::TOOLS_VARIABLE)
        .arg("build")
        .arg(&app)
        .args(["--backend", "llvm"]));
    assert!(!ok, "сборка прошла без цепочки LLVM");
    assert!(stderr.contains("llvm-as"), "отказ обязан назвать: {stderr}");
}

/// Сюита без тестов - **отказ**, а не зелёный прогон.
///
/// Это и есть жанр «команда, которая отработала»: `adamas test`, ничего не
/// нашедший и ушедший с нулём, неотличим от того, что всё прогнал.
#[test]
fn a_suite_without_tests_is_refused() {
    let case = scratch("empty");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));

    let tests = app.join("src/Test.adamas");
    let text = read(&tests);
    let cut = text.find("testPlusIsLeftNeutral").expect("тесты заготовки");
    write(&tests, &text[..cut]);

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(!ok, "сюита без тестов прошла: {stdout}");
    assert!(
        stderr.contains("тестов нет ни одного"),
        "отказ обязан назвать причину: {stderr}"
    );
}

/// Тестового модуля нет - отказ называет, где его ждали.
#[test]
fn a_missing_test_module_is_refused_by_name() {
    let case = scratch("no-module");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));
    std::fs::remove_file(app.join("src/Test.adamas")).expect("тестовый модуль");

    let (ok, _, stderr) = run(adamas().arg("test").arg(&app));
    assert!(!ok, "сюита без модуля прошла");
    assert!(
        stderr.contains("Test.adamas"),
        "отказ обязан назвать файл: {stderr}"
    );
}

/// Определение с именем на `test` и типом не `Bool` - отказ, а не тихий
/// пропуск.
///
/// Пропущенный тест не отличается от прошедшего ничем, кроме отсутствия строки
/// в выводе, и это второй способ быть зелёным, ничего не сделав.
#[test]
fn a_test_that_is_not_boolean_is_refused() {
    let case = scratch("not-bool");
    let app = case.join("demo");
    run(adamas().arg("new").arg(&app));

    let tests = app.join("src/Test.adamas");
    let text = format!("{}\ntestCount : Nat\ntestCount = Zero\n", read(&tests));
    write(&tests, &text);

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(!ok, "тест не того типа прошёл молча: {stdout}");
    assert!(
        stderr.contains("testCount") && stderr.contains("`Bool`"),
        "отказ обязан назвать имя и тип: {stderr}"
    );
}

/// Тест вправе называться `Bool`'ом **из другого файла**: соглашение стоит на
/// имени типа, а не на том, кто его объявил (§4.3).
#[test]
fn a_test_may_use_a_boolean_from_another_module() {
    let case = scratch("imported-bool");
    let app = case.join("lib");
    write(
        &app.join(adamas_pkg::manifest::MANIFEST),
        "[package]\nname = \"lib\"\n",
    );
    write(
        &app.join("src/Main.adamas"),
        "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\nmain : Nat\nmain = Succ Zero\n",
    );
    write(
        &app.join("src/Std/Base.adamas"),
        "data Bool where\n  False : Bool\n  True : Bool\n",
    );
    write(
        &app.join("src/Test.adamas"),
        "import Std.Base (Bool, False, True)\n\ntestImported : Bool\ntestImported = True\n",
    );

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(ok, "чужой `Bool` не признан: {stderr}\n{stdout}");
    assert!(
        stdout.contains("testImported: ok") && stdout.contains("тестов 1, отказов 0"),
        "неожиданный вывод: {stdout}"
    );
}

/// Тестами считаются определения **входного файла** сюиты, а не всей её
/// программы: иначе `adamas test` отвечал бы за чужой код.
#[test]
fn tests_of_an_imported_module_are_not_run() {
    let case = scratch("own-only");
    let app = case.join("lib");
    write(
        &app.join(adamas_pkg::manifest::MANIFEST),
        "[package]\nname = \"lib\"\n",
    );
    write(
        &app.join("src/Main.adamas"),
        "data Bool where\n  False : Bool\n  True : Bool\n\nmain : Bool\nmain = True\n",
    );
    // Тест соседа заведомо красный: прогонись он - сюита покраснела бы.
    write(
        &app.join("src/Other.adamas"),
        "import Main (Bool, False, True)\n\ntestAlien : Bool\ntestAlien = False\n",
    );
    write(
        &app.join("src/Test.adamas"),
        "import Main (Bool, False, True)\nimport Other (testAlien)\n\ntestOwn : Bool\ntestOwn = True\n",
    );

    let (ok, stdout, stderr) = run(adamas().arg("test").arg(&app));
    assert!(ok, "чужой тест прогнан: {stderr}\n{stdout}");
    assert!(
        stdout.contains("тестов 1, отказов 0"),
        "неожиданный счёт: {stdout}"
    );
}

/// Непустой каталог не занимается: `adamas new` над чужой работой затёр бы её.
#[test]
fn new_refuses_a_non_empty_directory() {
    let case = scratch("occupied");
    let app = case.join("demo");
    write(&app.join("уже-лежит.txt"), "чужое\n");

    let (ok, _, stderr) = run(adamas().arg("new").arg(&app));
    assert!(!ok, "непустой каталог занят молча");
    assert!(stderr.contains("не пуст"), "{stderr}");
    assert!(
        !app.join(adamas_pkg::manifest::MANIFEST).exists(),
        "манифест положен вопреки отказу"
    );
}

/// Имя пакета называет файл артефакта, поэтому путём быть не вправе.
#[test]
fn new_refuses_a_name_that_is_a_path() {
    let case = scratch("bad-name");
    let (ok, _, stderr) = run(adamas()
        .arg("new")
        .arg(case.join("demo"))
        .args(["--name", "../sh"]));
    assert!(!ok, "путь в имени пакета прошёл");
    assert!(stderr.contains("не годится"), "{stderr}");
}
