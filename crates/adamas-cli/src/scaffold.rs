//! `adamas new`: проект, который сразу проверяется, собирается и тестируется
//! (§7.1).
//!
//! # Что кладётся
//!
//! ```text
//! <имя>/
//!   adamas.toml        манифест (§7.3): одна секция `[package]`
//!   .gitignore         кеш зависимостей и артефакты сборки
//!   src/Main.adamas    вход программы
//!   src/Test.adamas    её тесты
//! ```
//!
//! Раскладка не выбрана, а **вынуждена**:
//! [`Directory::file_of`](adamas_elab::program::Directory::file_of) кладёт
//! модуль `Std.Prelude` в `<корень>/Std/Prelude.adamas`, и умолчания манифеста
//! (`root = "src"`, `entry = "Main"`, `test = "Test"`) дают ровно эти два
//! файла. Заготовка, разошедшаяся с этим правилом, не проверялась бы.
//!
//! # Чего здесь нет
//!
//! `git init` не зовётся. Cargo его зовёт, но за ним приезжает конфигурация
//! машины - `init.defaultBranch`, `core.hooksPath`, `commit.gpgsign`, - а
//! §7.1 репозитория от `new` не требует. `.gitignore` при этом кладётся: он
//! пригодится, когда репозиторий заведут руками, и ничего не запускает.
//!
//! # Заготовка обязана быть настоящей программой
//!
//! `main` считает, а не возвращает константу, и тест **сверяет** ответ. Иначе
//! `adamas new` проверялся бы тем, что файлы появились, - а появившийся файл и
//! неработающий проект различаются ровно тем, что первое не прогоняется.

use std::path::{Path, PathBuf};

use anyhow::Context as _;

/// Вход программы: унарная арифметика и `main`, который по ней считает.
const MAIN: &str = "\
-- Вход программы. `adamas run` соберёт её и запустит, `adamas eval` посчитает
-- интерпретатором, `adamas check` только проверит типы.

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> (1 m : Nat) -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

double : Nat -> Nat
double n = plus n n

main : Nat
main = double (Succ (Succ Zero))
";

/// Тесты: отдельная программа, подключающая вход как модуль.
const TEST: &str = "\
-- Тесты программы (§7.1). Тест - определение с именем на `test` и типом
-- `Bool`; `adamas test` считает его и требует `True`.
--
-- Вход подключается как обычный модуль: файл - это модуль (§4.8).

import Main (Nat, Zero, Succ, plus, double)

data Bool where
  False : Bool
  True : Bool

eqNat : Nat -> Nat -> Bool
eqNat Zero Zero = True
eqNat Zero (Succ m) = False
eqNat (Succ k) Zero = False
eqNat (Succ k) (Succ m) = eqNat k m

testPlusIsLeftNeutral : Bool
testPlusIsLeftNeutral = eqNat (plus Zero (Succ Zero)) (Succ Zero)

testDoubleAddsToItself : Bool
testDoubleAddsToItself = eqNat (double (Succ Zero)) (Succ (Succ Zero))
";

/// Что не попадает в репозиторий.
const IGNORE: &str = "\
# Кеш зависимостей и артефакты сборки (§7.3). Замок `adamas.lock` - наоборот,
# коммитится: он и есть воспроизводимость сборки.
/.adamas/
";

/// Заводит проект в написанном каталоге.
///
/// # Errors
///
/// Каталог занят непустым содержимым, имя не годится в имя пакета либо файл не
/// записывается.
pub(crate) fn create(path: &Path, name: Option<&str>) -> anyhow::Result<()> {
    let name = match name {
        Some(written) => written.to_owned(),
        None => derived(path)?,
    };
    // Проверяется **и** написанное ключом: манифест отверг бы его при первой же
    // команде, но заведён проект был бы уже.
    named(&name)?;
    if path.is_dir() && path.read_dir().is_ok_and(|mut it| it.next().is_some()) {
        anyhow::bail!("каталог {} не пуст", path.display());
    }

    let manifest = format!("[package]\nname = \"{name}\"\n");
    for (at, text) in [
        (
            PathBuf::from(adamas_pkg::manifest::MANIFEST),
            manifest.as_str(),
        ),
        (PathBuf::from(".gitignore"), IGNORE),
        (["src", "Main.adamas"].iter().collect(), MAIN),
        (["src", "Test.adamas"].iter().collect(), TEST),
    ] {
        let at = path.join(at);
        if let Some(parent) = at.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("не удалось создать {}", parent.display()))?;
        }
        std::fs::write(&at, text)
            .with_context(|| format!("не удалось записать {}", at.display()))?;
    }
    println!("{name}: заведён в {}", path.display());
    Ok(())
}

/// Имя пакета из последнего сегмента пути.
fn derived(path: &Path) -> anyhow::Result<String> {
    let Some(name) = path.file_name().map(|it| it.to_string_lossy().into_owned()) else {
        anyhow::bail!(
            "из пути {} не вывести имени пакета: напишите его ключом `--name`",
            path.display()
        );
    };
    Ok(name)
}

/// Годится ли строка в имя пакета.
///
/// Правило то же, каким его проверяет манифест: имя пакета называет файл
/// артефакта (`adamas build`), и `adamas new ./моя программа` иначе завёл бы
/// проект, который не собирается.
fn named(name: &str) -> anyhow::Result<()> {
    let ok = !name.is_empty()
        && name
            .chars()
            .all(|it| it.is_alphanumeric() || it == '_' || it == '-');
    if !ok {
        anyhow::bail!(
            "`{name}` не годится в имя пакета: буквы, цифры, `_` и `-`; другое задаёт `--name`"
        );
    }
    Ok(())
}
