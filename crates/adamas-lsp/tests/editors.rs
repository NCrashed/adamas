//! Плагины редакторов гоняются **headless**, настоящими редакторами.
//!
//! §4 милестоуна волны: «скриншот и „я посмотрел“ свидетелями не считаются».
//! Поэтому здесь запускается не подобие редактора, а он сам: `nvim --headless`
//! с каталогом плагина в `runtimepath` и Electron `VSCodium` с
//! `--extensionTestsPath`. Диагностику оба отдают изнутри - из
//! `vim.diagnostic.get` и из `vscode.languages.getDiagnostics`.
//!
//! # Чего такой прогон **не** доказывает сам по себе
//!
//! Что редактор ответил - ещё не что он показал верное. Числа позиции здесь
//! записаны руками, а главное - у каждого редактора спрашивается **текст под
//! подчёркиванием**: кусок, который редактор сам вырезал из своего буфера по
//! полученному диапазону. Перевод позиций, ошибочный одинаково в обе стороны,
//! круговой проверке не виден (трек A измерил это мутантом «считать UTF-16
//! байтами»), а нарезке чужим кодом - виден: съехавший диапазон вырезает не то
//! слово.
//!
//! Тем же ценен и состав пары. Neovim держит колонки **в байтах** и переводит
//! из кодовых единиц протокола сам; VS Code меряет UTF-16 и хранит UTF-16. То
//! есть nvim замыкает перевод чужой реализацией, а VS Code проверяет тот
//! случай (UTF-16), который протокол берёт по умолчанию.
//!
//! # Что показали мутанты
//!
//! Два, и каждый убит **разным** подмножеством - то есть лишних прогонов тут
//! нет.
//!
//! *«UTF-16 считать байтами»* (`Encoding::units` -> `text.len()`) - тот самый,
//! к которому слепы оба round-trip'а трека A. Падают
//! `neovim_decodes_the_other_encodings…` и оба прогона VS Code; под
//! подчёркиванием у них оказывается `o Zero` вместо `Succ Zero Zero`.
//! `neovim_underlines…` при этом **зелен**: Neovim просит UTF-8, и на нём
//! мутация ничего не меняет.
//!
//! *«UTF-8 считать знаками»* (`text.len()` -> `text.chars().count()`) -
//! наоборот: падает один `neovim_underlines…`, с ` 😀 -} Succ ` под
//! подчёркиванием, а остальные три зелены.
//!
//! # Инструменты
//!
//! `ADAMAS_NVIM`, `ADAMAS_VSCODE`, `ADAMAS_VSCODE_CLI`, `ADAMAS_VSCE` - пути к
//! бинарям; их задаёт dev-shell (`flake.nix`). У VS Code их две, потому что
//! бинарей два: Electron держит extension host, CLI ставит `.vsix`, и
//! подменять одного другим нельзя ни в ту, ни в другую сторону.
//!
//! Значение `absent` - **объявленное** отсутствие
//! инструмента, то же правило, что у `ADAMAS_LLVM=absent`
//! (`.github/workflows/ci.yml`). Переменная, не заданная вовсе, роняет прогон:
//! молчаливый пропуск был бы обманчивым свидетелем.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// Фикстура корпуса, на которой байт, знак и кодовая единица UTF-16 дают три
/// разных числа.
const FIXTURE: &str = "position-past-multibyte.adamas";

/// Строка отказа, 0-based. То же число, что в `tests/protocol.rs`.
const LINE: u64 = 19;

/// Границы подчёркивания **в байтах** - так их отдаёт Neovim.
const BYTES: (u64, u64) = (26, 40);

/// Те же границы в кодовых единицах UTF-16 - так их отдаёт VS Code.
const UTF16: (u64, u64) = (18, 32);

/// Что обязано оказаться под подчёркиванием.
const UNDERLINED: &str = "Succ Zero Zero";

/// Строка последней строки фикстуры после правки.
const FIXED_LINE: &str = "двойка = {- 😀 -} Succ Zero";

/// Первая строка сообщения - та же, что печатает терминал.
const HEADLINE: &str = "ожидалась функция, получено значение типа `Nat`";

/// Корень репозитория.
fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Путь к инструменту или объявленное его отсутствие.
///
/// `None` только при `<VAR>=absent`. Пустое и незаданное - отказ: инструмент,
/// которого нет, обязан ронять прогон, а не молчать.
fn tool(variable: &str) -> Option<String> {
    match std::env::var(variable) {
        Ok(value) if value == "absent" => {
            eprintln!("{variable}=absent: редактор объявлен отсутствующим, прогон его не проверял");
            None
        }
        Ok(value) if !value.is_empty() => Some(value),
        _ => panic!("`{variable}` не задан, а в dev-shell он есть: редактор взять неоткуда"),
    }
}

/// Рабочий каталог одного прогона.
///
/// Под `CARGO_TARGET_TMPDIR`, а не под `/tmp`: путь обязан быть простым.
/// Измерено - в каталоге вида `/tmp/nix-shell.XXX/claude-1000/-home-…` `vsce`
/// молча отдаёт **пустой** список файлов и пакует `.vsix` без точки входа.
fn workspace(name: &str) -> PathBuf {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    root
}

/// Копия фикстуры в рабочем каталоге.
///
/// Копия, а не оригинал: прогон правит буфер, и промах автосохранения переписал
/// бы корпус.
fn fixture(into: &Path) -> PathBuf {
    let source = repo().join("tests/golden/errors").join(FIXTURE);
    let target = into.join(FIXTURE);
    std::fs::copy(&source, &target).unwrap();
    target
}

/// Прогон команды: вывод целиком, стандартный и ошибочный вместе.
fn output(command: &mut Command) -> (bool, String) {
    let done = command
        .output()
        .unwrap_or_else(|error| panic!("не запустился `{:?}`: {error}", command.get_program()));
    let mut text = String::from_utf8_lossy(&done.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&done.stderr));
    (done.status.success(), text)
}

/// Строки вида `КЛЮЧ=значение` из вывода драйвера.
///
/// Вывод целиком хранится рядом: редактор пишет в те же потоки свой лог, и
/// когда драйвер не сказал ничего, разбираться приходится именно по логу.
struct Said(Vec<(String, String)>, String);

impl Said {
    fn of(output: &str) -> Self {
        Self(
            output
                .lines()
                .filter_map(|line| line.split_once('='))
                .map(|(key, value)| (key.trim().to_owned(), value.to_owned()))
                .collect(),
            output.to_owned(),
        )
    }

    /// Значение ключа. Ключ обязан быть - его печатает драйвер.
    #[track_caller]
    fn get(&self, key: &str) -> &str {
        self.0.iter().find(|(name, _)| name == key).map_or_else(
            || panic!("драйвер не сказал `{key}`:\n{}", self.dump()),
            |(_, value)| value.as_str(),
        )
    }

    /// Все значения ключа: диагностик бывает и больше одной.
    fn all(&self, key: &str) -> Vec<Value> {
        self.0
            .iter()
            .filter(|(name, _)| name == key)
            .map(|(_, value)| serde_json::from_str(value).expect("драйвер печатает JSON"))
            .collect()
    }

    fn dump(&self) -> &str {
        &self.1
    }
}

/// Одна диагностика: на месте, под нужным словом, с тем же текстом.
///
/// `severity` параметром, потому что нумерации разные: у LSP и Neovim ошибка -
/// 1, у VS Code - 0.
#[track_caller]
fn check(found: &Value, bounds: (u64, u64), severity: u64) {
    assert_eq!(found["line"].as_u64(), Some(LINE), "{found}");
    assert_eq!(
        (found["start"].as_u64(), found["end"].as_u64()),
        (Some(bounds.0), Some(bounds.1)),
        "границы подчёркивания: {found}"
    );
    assert_eq!(
        found["underlined"].as_str(),
        Some(UNDERLINED),
        "редактор подчеркнул не то место: {found}"
    );
    assert_eq!(found["source"].as_str(), Some("adamas"), "{found}");
    assert_eq!(found["severity"].as_u64(), Some(severity), "{found}");
    assert_eq!(
        found["message"].as_str().and_then(|it| it.lines().next()),
        Some(HEADLINE),
        "текст - тот же, что печатает терминал: {found}"
    );
}

// ---------------------------------------------------------------- Neovim ----

/// Прогон Neovim.
///
/// `--clean` - без пользовательского конфига и чужих плагинов, но с обычной
/// загрузкой `plugin/` из `runtimepath`: проверяется ровно то, что лежит в
/// `editors/nvim`.
///
/// `encoding` задан - каталог плагина в `runtimepath` **не** кладётся, и клиента
/// поднимает сам драйвер. Иначе клиентов было бы два и диагностик тоже.
fn nvim(binary: &str, name: &str, encoding: Option<&str>) -> Said {
    let root = workspace(name);
    let fixture = fixture(&root);
    let driver = root.join("nvim.lua");
    std::fs::write(&driver, include_str!("editors/nvim.lua")).expect("драйвер пишется");

    let mut command = Command::new(binary);
    command.current_dir(&root).arg("--headless").arg("--clean");
    if encoding.is_none() {
        command.arg("--cmd").arg(format!(
            "set runtimepath^={}",
            repo().join("editors/nvim").display()
        ));
    }
    command
        .arg("-l")
        .arg(&driver)
        .env("ADAMAS_LSP_BIN", env!("CARGO_BIN_EXE_adamas-lsp"))
        .env("ADAMAS_FIXTURE", &fixture)
        .env("XDG_CONFIG_HOME", root.join("config"))
        .env("XDG_DATA_HOME", root.join("data"))
        .env("XDG_STATE_HOME", root.join("state"))
        .env_remove("ADAMAS_FORCE_ENCODING");
    if let Some(encoding) = encoding {
        command.env("ADAMAS_FORCE_ENCODING", encoding);
    }

    let (ok, text) = output(&mut command);
    assert!(ok, "nvim вышел с ошибкой:\n{text}");
    Said::of(&text)
}

/// Neovim подчёркивает то же место и тем же текстом, что печатает терминал.
///
/// Колонки здесь **байтовые** (26 и 40), и совпадение это не с нашим счётом: по
/// протоколу ушли кодовые единицы, а обратно в байты их перевёл сам Neovim.
#[test]
fn neovim_underlines_the_offending_expression() {
    let Some(binary) = tool("ADAMAS_NVIM") else {
        return;
    };
    let said = nvim(&binary, "nvim-default", None);

    assert_eq!(
        said.get("PLUGIN"),
        "true",
        "автокоманду ставит editors/nvim/plugin/adamas.lua; без неё прогон проверял бы драйвер"
    );
    assert_eq!(said.get("FT"), "adamas", "ftdetect привязал `.adamas`");
    assert_eq!(said.get("WAIT"), "true", "диагностика не пришла");
    assert_eq!(said.get("CLIENTS"), "1", "{}", said.dump());
    assert_eq!(said.get("CLIENT"), "adamas", "клиента поднял плагин");
    assert_eq!(
        said.get("ENCODING"),
        "utf-8",
        "Neovim просит UTF-8 первой, и сервер обязан уважить порядок клиента"
    );
    assert_eq!(said.get("COUNT"), "1", "{}", said.dump());

    check(&said.all("DIAG")[0], BYTES, 1);

    assert_eq!(said.get("EDITED"), FIXED_LINE, "правка что-то да меняет");
    assert_eq!(
        said.get("CLEARED"),
        "true",
        "исправленный буфер обязан гасить подчёркивание"
    );
}

/// То же на UTF-16 и UTF-32: перевод замыкается чужой реализацией.
///
/// Смысл именно в UTF-16 - это умолчание протокола и то, чем меряет VS Code, а
/// Neovim переводит его в байты **своим** кодом. UTF-32 рядом потому, что на
/// этой строке все три числа разные, и перепутать их нечем.
#[test]
fn neovim_decodes_the_other_encodings_back_to_the_same_bytes() {
    let Some(binary) = tool("ADAMAS_NVIM") else {
        return;
    };
    for encoding in ["utf-16", "utf-32"] {
        let said = nvim(&binary, &format!("nvim-{encoding}"), Some(encoding));
        assert_eq!(said.get("ENCODING"), encoding);
        assert_eq!(said.get("COUNT"), "1", "{}", said.dump());
        check(&said.all("DIAG")[0], BYTES, 1);
    }
}

// --------------------------------------------------------------- VS Code ----

/// Каталог расширения, готовый к запуску: исходники из `editors/vscode` плюс
/// поставленные `npm ci` зависимости.
fn extension(into: &Path) -> PathBuf {
    let source = repo().join("editors/vscode");
    assert!(
        source.join("node_modules/vscode-languageclient").is_dir(),
        "нет `editors/vscode/node_modules`: сделай `npm ci` в этом каталоге \
         (dev-shell делает это сам при входе)"
    );
    let target = into.join("extension");
    let (ok, text) = output(Command::new("cp").arg("-rL").arg(&source).arg(&target));
    assert!(ok, "копия расширения не сделалась:\n{text}");
    target
}

/// Прогон `VSCodium` с сюитой внутри extension host'а.
///
/// `xvfb-run`, потому что Electron без дисплея не поднимается вовсе. Бинарь -
/// **Electron**, а не CLI-обёртка `bin/codium`: обёртка отдаёт аргументы и
/// возвращается сразу, и прогон с ней зелен за секунду, ничего не проверив.
fn vscodium(
    binary: &str,
    root: &Path,
    fixture: &Path,
    exts: &Path,
    extra: &[String],
) -> (bool, Said) {
    let driver = root.join("suite.js");
    std::fs::write(&driver, include_str!("editors/suite.js")).expect("драйвер пишется");
    let user = root.join("user");
    std::fs::create_dir_all(user.join("User")).expect("каталог настроек создаётся");
    // Путь к серверу идёт настройкой `adamas.server.path` - тем же способом,
    // каким его задаёт человек. PATH сработал бы тоже, но не проверил бы, что
    // настройка расширения вообще читается.
    std::fs::write(
        user.join("User/settings.json"),
        format!(
            "{{ \"adamas.server.path\": {} }}",
            serde_json::to_string(env!("CARGO_BIN_EXE_adamas-lsp")).expect("путь сериализуется")
        ),
    )
    .expect("настройки пишутся");

    let (ok, text) = output(
        Command::new("xvfb-run")
            .arg("-a")
            .arg(binary)
            .args(extra)
            .arg(format!("--extensionTestsPath={}", driver.display()))
            .arg(format!("--user-data-dir={}", user.display()))
            .arg(format!("--extensions-dir={}", exts.display()))
            .args([
                "--disable-gpu",
                "--disable-updates",
                "--disable-workspace-trust",
                "--skip-welcome",
                "--skip-release-notes",
                "--no-sandbox",
            ])
            .current_dir(root)
            .env("ADAMAS_FIXTURE", fixture),
    );
    (ok, Said::of(&text))
}

/// VS Code подчёркивает то же место и тем же текстом, что печатает терминал.
///
/// Колонки здесь в кодовых единицах UTF-16 (18 и 32) - умолчание протокола.
/// Само по себе это круг: VS Code хранит UTF-16 и отдаёт UTF-16. Круг
/// разрывает `underlined` - текст, вырезанный редактором из своего буфера по
/// полученному диапазону.
#[test]
fn vscode_underlines_the_offending_expression() {
    let Some(binary) = tool("ADAMAS_VSCODE") else {
        return;
    };
    let root = workspace("vscode-dev");
    let fixture = fixture(&root);
    let extension = extension(&root);
    let exts = root.join("exts");
    std::fs::create_dir_all(&exts).expect("каталог расширений создаётся");
    let dev = format!("--extensionDevelopmentPath={}", extension.display());
    let (ok, said) = vscodium(&binary, &root, &fixture, &exts, std::slice::from_ref(&dev));
    assert!(ok, "сюита в редакторе отказала:\n{}", said.dump());

    assert_eq!(said.get("FOUND"), "true", "расширение не подхватилось");
    assert_eq!(said.get("ACTIVE"), "true", "{}", said.dump());
    assert_eq!(
        said.get("LANGUAGE"),
        "adamas",
        "`.adamas` не привязан к языку"
    );
    assert_eq!(said.get("COUNT"), "1", "{}", said.dump());

    // 0 - `DiagnosticSeverity.Error` в нумерации VS Code (в LSP это 1).
    check(&said.all("DIAG")[0], UTF16, 0);

    assert_eq!(said.get("EDITED"), "true", "правка не применилась");
    assert_eq!(
        said.get("AFTER_COUNT"),
        "0",
        "исправленный буфер обязан гасить подчёркивание"
    );
}

/// Упакованный `.vsix` ставится в редактор, и поставленное работает.
///
/// # Почему проверка именно такая
///
/// Ни «`vsce package` не отказал», ни «`--list-extensions` показывает
/// расширение» свидетелями не годятся, и это измерено, а не предположено.
/// Мутант - `vsce package --no-dependencies`: архив из четырёх файлов, без
/// `node_modules`. `vsce` печатает `DONE`, CLI печатает `was successfully
/// installed`, `--list-extensions` печатает `adamas-lang.adamas`. Всё зелено, а
/// расширение нерабочее: сюита на нём даёт `ACTIVATION_FAILED: Cannot find
/// module 'vscode-languageclient/node'` и `COUNT=0`. Поэтому последнее слово -
/// за прогоном сюиты на **поставленном** каталоге.
///
/// # Почему сюита идёт через `--extensionDevelopmentPath`
///
/// Режима «гонять тесты на установленном расширении» у VS Code нет: без
/// `--extensionDevelopmentPath` редактор не открывает окна и висит (измерено -
/// 120 с до обрыва, в логе только запуск хранилища). Поэтому путь указывает на
/// **распакованный `.vsix`** в каталоге расширений: код там тот, что уехал в
/// архив, а каталог создан установкой. `--extensions-dir` при этом пустой,
/// чтобы не осталось сомнений, откуда взят код.
#[test]
fn a_packaged_extension_works_after_install() {
    let (Some(binary), Some(cli), Some(vsce)) = (
        tool("ADAMAS_VSCODE"),
        tool("ADAMAS_VSCODE_CLI"),
        tool("ADAMAS_VSCE"),
    ) else {
        return;
    };
    let root = workspace("vscode-packaged");
    let fixture = fixture(&root);
    let extension = extension(&root);
    let vsix = root.join("adamas.vsix");

    let (ok, text) = output(
        Command::new(vsce)
            .arg("package")
            .arg("--out")
            .arg(&vsix)
            .current_dir(&extension),
    );
    assert!(ok, "`vsce package` отказал:\n{text}");

    // Ставит **CLI**, а не Electron: установка - работа командной строки, и
    // Electron её не делает. Измерено: Electron с `--install-extension`
    // открывает окно и висит; CLI ставит за доли секунды и дисплея не просит.
    let (ok, text) = output(
        Command::new(cli)
            .arg("--install-extension")
            .arg(&vsix)
            // Каталог настроек **свой**, а не тот, в котором пойдёт сюита:
            // CLI оставляет в нём сокет, и следующий запуск отказывается
            // словами «extension tests ... only supported if no other instance
            // is running». Общим у двух шагов должен быть каталог расширений,
            // а не каталог настроек.
            .arg(format!(
                "--user-data-dir={}",
                root.join("installer").display()
            ))
            .arg(format!("--extensions-dir={}", root.join("exts").display()))
            .arg("--no-sandbox")
            .current_dir(&root),
    );
    // Код возврата у CLI нулевой и на неудаче - он печатает `Failed Installing
    // Extensions` и уходит с нулём. Поэтому смотрим текст, а следом за ним -
    // на то, что установленное вообще поднимается.
    assert!(
        ok && !text.contains("Failed Installing"),
        "установка `.vsix` отказала:\n{text}"
    );

    // Каталог, который создала установка. Имя складывается из `publisher`,
    // `name` и `version`, но собирать его здесь второй раз значило бы записать
    // правило `vsce` ещё раз - берём то, что появилось.
    let installed = std::fs::read_dir(root.join("exts"))
        .expect("каталог расширений создан установкой")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("adamas-lang.adamas-"))
        })
        .expect("установка обязана оставить каталог расширения");

    let empty = root.join("empty");
    std::fs::create_dir_all(&empty).expect("пустой каталог расширений создаётся");
    let (ok, said) = vscodium(
        &binary,
        &root,
        &fixture,
        &empty,
        &[format!(
            "--extensionDevelopmentPath={}",
            installed.display()
        )],
    );
    assert!(ok, "сюита в редакторе отказала:\n{}", said.dump());
    assert_eq!(said.get("FOUND"), "true", "поставленного не видно");
    assert_eq!(
        said.get("ACTIVE"),
        "true",
        "поставленное не активировалось:\n{}",
        said.dump()
    );
    assert_eq!(
        said.get("FROM"),
        installed.to_str().expect("путь - UTF-8"),
        "код взят не из поставленного"
    );
    assert_eq!(said.get("COUNT"), "1", "{}", said.dump());
    check(&said.all("DIAG")[0], UTF16, 0);
}
