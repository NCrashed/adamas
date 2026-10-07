//! Каталоги полны и согласны между собой.
//!
//! Компилятор полноту перевода не проверяет: идентификатор - строка. Поэтому
//! здесь три сверки. Каталог разбирается Fluent без ошибок. Русский и
//! английский называют одни и те же сообщения с одними и теми же аргументами.
//! И всякий идентификатор, написанный в коде литералом `tr!(…)`, есть в
//! каталоге.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use adamas_l10n::CATALOGS;

use fluent_syntax::ast::{Entry, Expression, InlineExpression, Pattern, PatternElement};

/// Сообщения каталога: идентификатор и имена аргументов.
fn messages(text: &str, file: &str) -> BTreeMap<String, BTreeSet<String>> {
    let resource = fluent_syntax::parser::parse(text)
        .unwrap_or_else(|(_, errors)| panic!("{file} не разбирается: {errors:?}"));
    let mut found = BTreeMap::new();
    for entry in &resource.body {
        if let Entry::Message(message) = entry {
            let mut names = BTreeSet::new();
            if let Some(value) = &message.value {
                arguments(value, &mut names);
            }
            found.insert(message.id.name.to_owned(), names);
        }
    }
    found
}

fn arguments(pattern: &Pattern<&str>, names: &mut BTreeSet<String>) {
    for element in &pattern.elements {
        if let PatternElement::Placeable { expression } = element {
            expression_arguments(expression, names);
        }
    }
}

fn expression_arguments(expression: &Expression<&str>, names: &mut BTreeSet<String>) {
    match expression {
        Expression::Inline(inline) => inline_arguments(inline, names),
        Expression::Select { selector, variants } => {
            inline_arguments(selector, names);
            for variant in variants {
                arguments(&variant.value, names);
            }
        }
    }
}

fn inline_arguments(inline: &InlineExpression<&str>, names: &mut BTreeSet<String>) {
    match inline {
        InlineExpression::VariableReference { id } => {
            names.insert(id.name.to_owned());
        }
        InlineExpression::Placeable { expression } => expression_arguments(expression, names),
        _ => {}
    }
}

#[test]
fn both_languages_name_the_same_messages_with_the_same_arguments() {
    let mut all = BTreeSet::new();
    for (file, ru, en) in CATALOGS {
        let ru = messages(ru, &format!("ru/{file}"));
        let en = messages(en, &format!("en/{file}"));
        assert_eq!(
            ru.keys().collect::<Vec<_>>(),
            en.keys().collect::<Vec<_>>(),
            "{file}: каталоги называют разные сообщения"
        );
        for (id, names) in &ru {
            assert_eq!(names, &en[id], "{file}: `{id}` берёт разные аргументы");
            assert!(all.insert(id.clone()), "`{id}` объявлено дважды");
        }
    }
}

/// Идентификаторы `tr!(…)`, написанные в исходниках крейтов.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное дерево исходников"
)]
fn written() -> Vec<(String, String)> {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut found = Vec::new();
    let mut stack = vec![crates];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if !path.ends_with("target") {
                    stack.push(path);
                }
                continue;
            }
            if path.extension().is_none_or(|it| it != "rs") {
                continue;
            }
            let text = std::fs::read_to_string(&path).unwrap();
            for (at, _) in text.match_indices("tr!(\"") {
                // `include_str!("…")` кончается тем же.
                let before = text[..at].chars().next_back();
                if before.is_some_and(|it| it.is_alphanumeric() || it == '_') {
                    continue;
                }
                let rest = &text[at + 5..];
                let id = &rest[..rest.find('"').unwrap()];
                found.push((id.to_owned(), path.display().to_string()));
            }
        }
    }
    found
}

#[test]
fn every_written_identifier_is_in_the_catalog() {
    let known: BTreeSet<String> = CATALOGS
        .iter()
        .flat_map(|(file, ru, _)| messages(ru, file).into_keys())
        .collect();
    let written = written();
    assert!(
        written.len() > 20,
        "в коде найдено мало сообщений: {}",
        written.len()
    );
    for (id, file) in written {
        assert!(known.contains(&id), "{file}: `{id}` нет в каталоге");
    }
}

#[test]
fn a_count_chooses_the_russian_form() {
    let ru = |n| {
        adamas_l10n::message_in(
            adamas_l10n::Lang::Ru,
            "count-declarations",
            &[("count", adamas_l10n::count(n))],
        )
    };
    assert_eq!(ru(1), "1 объявление");
    assert_eq!(ru(3), "3 объявления");
    assert_eq!(ru(5), "5 объявлений");
    assert_eq!(ru(21), "21 объявление");
}
