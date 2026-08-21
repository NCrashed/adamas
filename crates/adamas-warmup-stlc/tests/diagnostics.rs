//! Как выглядят ошибки.
//!
//! Снапшот, а не набор проверок на подстроки: важно не то, что ошибка
//! случилась, а то, куда указывает спан и что написано пользователю. §7.4
//! требует хорошей диагностики "с самого начала, не потом починим" - снапшот
//! делает регресс в ней видимым.

use std::fmt::Write as _;

use adamas_core::source::SourceFile;
use adamas_warmup_stlc::run;

/// Каждый случай - отдельная стадия конвейера, чтобы в снапшоте было видно
/// все четыре класса ошибок сразу.
const BROKEN: &[(&str, &str)] = &[
    ("лексер", "1 @ 2"),
    ("парсер: нет `in`", "let x = 1"),
    ("парсер: сравнение неассоциативно", "1 < 2 < 3"),
    ("несвязанная переменная", "\\x -> y"),
    ("условие не Bool", "if 1 then 2 else 3"),
    ("ветки расходятся", "if true then 1 else false"),
    ("аргумент не того типа", "let f = \\n -> n + 1 in f true"),
    ("occurs check", "\\x -> x x"),
    ("применение не-функции", "1 2"),
    ("расходимость", "fix (\\f -> f)"),
];

#[test]
fn errors_point_at_the_right_place() {
    let mut report = String::new();

    for (label, source) in BROKEN {
        let file = SourceFile::new("broken.stlc", *source);
        let error = run(&file).expect_err("программа обязана быть отвергнута");
        let _ = writeln!(report, "== {label} ==");
        let _ = write!(report, "{}", error.render(&file));
        let _ = writeln!(report);
    }

    insta::assert_snapshot!(report);
}
