//! Проект с git-зависимостью: достаётся, собирается, подключается (§7.3),
//! и повторная сборка из `adamas.lock` даёт то же (§7.1).
//!
//! # Почему без сети
//!
//! Источник зависимости - репозиторий, созданный `git init` в каталоге теста,
//! и адресуется он `file://`. Сверх того каждому запуску драйвера ставится
//! `GIT_ALLOW_PROTOCOL=file`: попробуй код сходить по `https`, `ssh` или
//! `git://` - git откажет («transport 'https' not allowed»), и тест покраснеет
//! от этого, а не от того, что сети не случилось.
//!
//! **Чего эта проверка не показывает.** Транспорт: HTTP-редиректы,
//! аутентификацию, `credential.helper`, `insteadOf`, серверные ограничения на
//! выборку произвольного коммита, прокси, таймауты и обрывы. Локальный
//! репозиторий проверяет **алгоритм** достачи - какой коммит выбран, когда
//! ходят к источнику, что попадает в замок, - и молчит обо всём, что делает
//! настоящая сеть.
//!
//! # Свидетель обязан различать
//!
//! «Повторная сборка даёт то же» зелено и при начисто не читаемом замке:
//! второй прогон берёт готовый чекаут просто потому, что он уже лежит.
//! Поэтому свидетель здесь - **мутант**: тег в репозитории-источнике
//! переставляется на другой коммит, и сборка обязана разойтись - с замком
//! прежний ответ, без замка новый.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Библиотека: считает `answer` и ничем не отличается от обычного проекта.
fn library(answer: &str) -> String {
    format!(
        "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\nanswer : Nat\nanswer = {answer}\n"
    )
}

/// Вход проекта. Имени счёта он не объявляет ни одного: сломанное разрешение
/// имён между пакетами роняет его целиком.
const MAIN: &str = "import Std.Prelude (Nat, answer)\n\nmain : Nat\nmain = answer\n";

/// Ответ при `answer = Succ Zero`.
const ONE: &str = "Std.Prelude.Succ Std.Prelude.Zero";
/// Ответ при `answer = Succ (Succ Zero)`.
const TWO: &str = "Std.Prelude.Succ (Std.Prelude.Succ Std.Prelude.Zero)";

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
            .join("project")
            .join(case);
        if dir.exists() {
            std::fs::remove_dir_all(&dir).unwrap();
        }
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Настоящий `git` - им строится фикстура, а не проверяется поведение.
    ///
    /// Конфигурация машины отключена целиком, и это не перестраховка. Первый
    /// прогон без этого упал на `commit.gpgsign = true` из `~/.gitconfig`:
    /// фикстура полезла подписывать коммит ключом разработчика, pinentry не
    /// ответил, и шесть тестов покраснели по причине, к пакетному менеджеру
    /// отношения не имеющей. Той же дорогой пришли бы `init.defaultBranch`,
    /// `core.hooksPath` и `url.insteadOf`.
    pub(crate) fn git(dir: &Path, args: &[&str]) -> String {
        let output = hermetic("git")
            .arg("-C")
            .arg(dir)
            .args([
                "-c",
                "user.name=test",
                "-c",
                "user.email=test@example.invalid",
            ])
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    /// Кладёт файл, создавая каталоги по дороге.
    pub(crate) fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    /// Репозиторий-источник с одним модулем `Std.Prelude`.
    pub(crate) fn source(dir: &Path, answer: &str) -> String {
        write(&dir.join("adamas.toml"), "[package]\nname = \"std\"\n");
        write(&dir.join("src/Std/Prelude.adamas"), &super::library(answer));
        git(dir, &["init", "-q", "."]);
        commit(dir, "первый")
    }

    /// Правит модуль и коммитит.
    pub(crate) fn commit(dir: &Path, message: &str) -> String {
        git(dir, &["add", "-A"]);
        git(dir, &["commit", "-q", "-m", message]);
        git(dir, &["rev-parse", "HEAD"])
    }

    /// Проект, зависящий от репозитория по написанному требованию.
    pub(crate) fn project(dir: &Path, source: &Path, want: &str, main: &str) {
        write(
            &dir.join("adamas.toml"),
            &format!(
                "[package]\nname = \"app\"\n\n[dependencies]\nStd = {{ git = \"file://{}\", {want} }}\n",
                source.display()
            ),
        );
        write(&dir.join("src/Main.adamas"), main);
    }

    /// Команда, которой ничего не достаётся от машины.
    ///
    /// `GIT_CONFIG_GLOBAL` и `GIT_CONFIG_SYSTEM` в `/dev/null` - `~/.gitconfig`
    /// и `/etc/gitconfig` не читаются ни фикстурой, ни `git`, которого зовёт
    /// драйвер. `GIT_ALLOW_PROTOCOL=file` - запрет выходить наружу, а не
    /// пожелание: транспорт, которого нет в списке, git отвергает сам.
    fn hermetic(program: &str) -> Command {
        let mut command = Command::new(program);
        command
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("GIT_ALLOW_PROTOCOL", "file")
            .env("GIT_TERMINAL_PROMPT", "0");
        command
    }

    /// Драйвер.
    pub(crate) fn adamas() -> Command {
        hermetic(env!("CARGO_BIN_EXE_adamas"))
    }

    /// Запускает команду и отдаёт `(успех, stdout, stderr)`.
    pub(crate) fn run(command: &mut Command) -> (bool, String, String) {
        let output = command.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
        (output.status.success(), stdout, stderr)
    }

    /// Текст замка.
    pub(crate) fn lock(app: &Path) -> String {
        std::fs::read_to_string(app.join("adamas.lock")).unwrap_or_default()
    }
}

use fixture::{adamas, commit, git, lock, project, run, scratch, source, write};

/// Зависимость по URL и коммиту достаётся, собирается и подключается.
///
/// Свидетель парный: та же программа без `import` обязана быть отвергнута.
/// Без второй половины тест проходил бы и при начисто сломанном разрешении
/// имён между пакетами - `main` не объявляет ни `Nat`, ни `answer`.
#[test]
fn a_dependency_by_url_and_commit_is_fetched_built_and_imported() {
    let case = scratch("by-rev");
    let repository = case.join("std");
    let rev = source(&repository, "Succ Zero");
    let app = case.join("app");
    project(&app, &repository, &format!("rev = \"{rev}\""), MAIN);

    let (ok, stdout, stderr) = run(adamas().arg("check").arg(&app));
    assert!(ok, "проверка не прошла: {stderr}");
    assert!(stdout.contains("файлов 2"), "неожиданный вывод: {stdout}");

    assert!(
        app.join(".adamas/checkout/Std").join(&rev).is_dir(),
        "чекаут не лежит под своим коммитом"
    );
    assert!(lock(&app).contains(&rev), "замок не записал коммит");

    let (ok, stdout, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "счёт не прошёл: {stderr}");
    assert_eq!(stdout, ONE, "ответ собран не из зависимости");

    // Вторая половина пары.
    write(
        &app.join("src/Main.adamas"),
        &MAIN.replace(MAIN.lines().next().unwrap(), ""),
    );
    let (ok, _, stderr) = run(adamas().arg("check").arg(&app));
    assert!(!ok, "без импорта имя нашлось: {stderr}");
}

/// Переставленный тег меняет сборку **только** без замка.
///
/// Это и есть различающий свидетель воспроизводимости: не «второй прогон дал
/// то же», а «второй прогон дал то же, хотя источник уже другой».
#[test]
fn a_moved_tag_changes_the_build_only_without_the_lockfile() {
    let case = scratch("moved-tag");
    let repository = case.join("std");
    let first = source(&repository, "Succ Zero");
    git(&repository, &["tag", "v1"]);
    let app = case.join("app");
    project(&app, &repository, "tag = \"v1\"", MAIN);

    let (ok, stdout, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "первая сборка не прошла: {stderr}");
    assert_eq!(stdout, ONE);
    assert!(lock(&app).contains(&first));

    // Мутант: тег в источнике переезжает на другой коммит.
    write(
        &repository.join("src/Std/Prelude.adamas"),
        &library("Succ (Succ Zero)"),
    );
    let second = commit(&repository, "второй");
    git(&repository, &["tag", "-f", "v1"]);
    assert_ne!(first, second);

    let (ok, stdout, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "сборка из замка не прошла: {stderr}");
    assert_eq!(stdout, ONE, "замок не удержал коммит");
    assert!(lock(&app).contains(&first), "замок переписан без спроса");

    std::fs::remove_file(app.join("adamas.lock")).expect("замок");
    let (ok, stdout, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "сборка без замка не прошла: {stderr}");
    assert_eq!(stdout, TWO, "без замка тег обязан разрешиться заново");
    assert!(lock(&app).contains(&second), "новый замок не записан");
}

/// Сборка из замка не зовёт `git` вовсе, а без замка - обязана.
///
/// Проверяется отсутствием `git` в `PATH`: счёт вызовов пришлось бы кому-то
/// вести, а пустой `PATH` отвечает на тот же вопрос без посредника. Пара
/// обязательна - без второй половины тест проходил бы и у сборки, которая
/// вообще ничего не достаёт.
#[test]
fn a_locked_rebuild_asks_git_for_nothing() {
    let case = scratch("no-git");
    let repository = case.join("std");
    source(&repository, "Succ Zero");
    git(&repository, &["tag", "v1"]);
    let app = case.join("app");
    project(&app, &repository, "tag = \"v1\"", MAIN);

    let (ok, _, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(ok, "первая сборка не прошла: {stderr}");

    let (ok, stdout, stderr) = run(adamas().env("PATH", "").arg("eval").arg(&app));
    assert!(ok, "сборка из замка потребовала git: {stderr}");
    assert_eq!(stdout, ONE);

    std::fs::remove_file(app.join("adamas.lock")).expect("замок");
    let (ok, _, stderr) = run(adamas().env("PATH", "").arg("eval").arg(&app));
    assert!(!ok, "без замка тег разрешился без git");
    assert!(stderr.contains("git"), "отказ обязан назвать git: {stderr}");
}

/// Тега, которого в репозитории нет, хватает на названный отказ, а не на
/// падение.
#[test]
fn an_unknown_tag_is_refused_by_name() {
    let case = scratch("no-tag");
    let repository = case.join("std");
    source(&repository, "Succ Zero");
    let app = case.join("app");
    project(&app, &repository, "tag = \"v9\"", MAIN);

    let (ok, _, stderr) = run(adamas().arg("eval").arg(&app));
    assert!(!ok, "несуществующий тег прошёл");
    assert!(
        stderr.contains("refs/tags/v9"),
        "отказ обязан назвать тег: {stderr}"
    );
}

/// Зависимость со своими зависимостями отвергается названной причиной.
///
/// Транзитивный граф требует правила «какой из двух коммитов одного
/// репозитория взять», а версий у git-зависимости нет (§7.3: реестра нет).
/// Молчаливое игнорирование чужого `[dependencies]` дало бы вместо этого
/// «модуль не найден» посреди чужого файла.
#[test]
fn a_transitive_dependency_is_refused_by_name() {
    let case = scratch("transitive");
    let repository = case.join("std");
    write(
        &repository.join("adamas.toml"),
        "[package]\nname = \"std\"\n\n[dependencies]\nOther = { git = \"file:///нет\", tag = \"v1\" }\n",
    );
    write(
        &repository.join("src/Std/Prelude.adamas"),
        &library("Succ Zero"),
    );
    git(&repository, &["init", "-q", "."]);
    let rev = commit(&repository, "первый");
    let app = case.join("app");
    project(&app, &repository, &format!("rev = \"{rev}\""), MAIN);

    let (ok, _, stderr) = run(adamas().arg("check").arg(&app));
    assert!(!ok, "транзитивная зависимость прошла молча");
    assert!(
        stderr.contains("транзитивные не поддержаны"),
        "отказ обязан назвать причину: {stderr}"
    );
}

/// Путь модуля идёт тому пакету, чей префикс его накрывает, - и больше никуда.
///
/// В чекауте лежит `Extra/Thing.adamas`, но префикс `Extra` в манифесте не
/// объявлен, поэтому модуль ищется у самого проекта и не находится. Это то же
/// свойство «явных зависимостей» §7.3, что трек A записал для неимпортированных
/// модулей, только на границе пакетов.
#[test]
fn a_module_outside_the_declared_prefix_is_looked_for_in_the_project() {
    let case = scratch("prefix");
    let repository = case.join("std");
    write(
        &repository.join("adamas.toml"),
        "[package]\nname = \"std\"\n",
    );
    write(
        &repository.join("src/Std/Prelude.adamas"),
        &library("Succ Zero"),
    );
    write(
        &repository.join("src/Extra/Thing.adamas"),
        "data Thing where\n  It : Thing\n",
    );
    git(&repository, &["init", "-q", "."]);
    let rev = commit(&repository, "первый");
    let app = case.join("app");
    project(
        &app,
        &repository,
        &format!("rev = \"{rev}\""),
        "import Extra.Thing (Thing)\n\nmain : Thing\nmain = It\n",
    );

    let (ok, _, stderr) = run(adamas().arg("check").arg(&app));
    assert!(!ok, "необъявленный префикс разрешился");
    assert!(
        stderr.contains("Extra/Thing.adamas"),
        "отказ обязан назвать, где искали: {stderr}"
    );
    assert!(
        !stderr.contains("checkout"),
        "искали в чекауте пакета, чей префикс не объявлен: {stderr}"
    );
}
