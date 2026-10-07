//! Язык сообщений выбирается окружением (§7.6).
//!
//! Остальные тесты гоняются с `ADAMAS_LANG=ru` из `.cargo/config.toml`, и
//! снимки написаны по-русски. Здесь окружение задаётся явно и целиком: какая
//! переменная старше и что бывает с локалью, которой нет в каталогах.

use std::process::Command;

/// Отказ разбора: незакрытая скобка.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn refused(env: &[(&str, &str)]) -> String {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("language");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("unclosed.adamas");
    std::fs::write(&path, "main : Bool\nmain = (True\n").unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_adamas"));
    command.arg("check").arg(&path);
    for name in adamas_l10n::VARIABLES {
        command.env_remove(name);
    }
    command.envs(env.iter().copied());
    let output = command.output().unwrap();
    assert!(!output.status.success(), "незакрытая скобка принята");
    String::from_utf8(output.stderr).unwrap()
}

#[test]
fn the_locale_chooses_the_language() {
    assert!(refused(&[("LANG", "ru_RU.UTF-8")]).contains("незакрытая скобка"));
    assert!(refused(&[("LANG", "en_US.UTF-8")]).contains("unclosed bracket"));
}

#[test]
fn an_unknown_locale_falls_back_to_english() {
    assert!(
        refused(&[]).contains("unclosed bracket"),
        "без локали вовсе"
    );
    assert!(refused(&[("LANG", "de_DE.UTF-8")]).contains("unclosed bracket"));
    assert!(refused(&[("LANG", "C")]).contains("unclosed bracket"));
}

#[test]
fn the_posix_order_holds_and_our_variable_is_above_it() {
    let both = [("LC_ALL", "C"), ("LANG", "ru_RU.UTF-8")];
    assert!(
        refused(&both).contains("unclosed bracket"),
        "`LC_ALL` старше `LANG`"
    );
    let ours = [("ADAMAS_LANG", "ru"), ("LC_ALL", "en_US.UTF-8")];
    assert!(
        refused(&ours).contains("незакрытая скобка"),
        "`ADAMAS_LANG` старше всех"
    );
}
