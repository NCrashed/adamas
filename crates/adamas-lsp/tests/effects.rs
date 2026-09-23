//! Погашение эффекта в тексте: что снимает `handle` и кто снимет это (§3.4, §7.2).
//!
//! # Чем этот свидетель ломается
//!
//! Обе подсказки показывают то, чего в тексте нет, и обе врут по-своему.
//!
//! 1. **Метка хендлера.** `handle asked with …` не называет `Ask` нигде: метку
//!    `handle` берёт из первой ветки-операции. Назови подсказка не ту метку -
//!    и читатель пойдёт править не тот хендлер; заготовка поэтому держит
//!    **две** метки, а не одну, иначе перепутать было бы нечего.
//! 2. **Хендлеры операции.** Множество, а не один: `handle` берёт названное
//!    вычисление (§3.4), поэтому один `ask` вправе попасть в любой из
//!    хендлеров файла. Заготовка держит две штуки на одну метку - на одной
//!    подсказка была бы неотличима от механизма, который показывает первый
//!    попавшийся.
//! 3. **Пустое множество.** Метка, не гасимая в этом файле, уходит в ряд, и
//!    молчать о ней нельзя: молчание читается как «механизма нет». Заготовка
//!    держит такую метку рядом с гасимой.

use std::path::{Path, PathBuf};
use std::str::FromStr as _;

use adamas_core::source::SourceFile;
use adamas_lsp::lsp_types::{InlayHint, InlayHintLabel, Position, Range, Uri};
use adamas_lsp::{Document, Encoding, hints};

/// Корпус `tests/golden/eval/` - он же корень поиска подключаемых модулей.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Буфер, проверенный так же, как это делает сервер на уведомлении.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn checked(text: &str) -> (Uri, Document) {
    let uri = Uri::from_str("file:///corpus/effects.adamas").expect("URI заготовки");
    let mut document = Document::of(&uri, text.to_owned());
    let sources = adamas_elab::program::Directory::new(corpus());
    let mut program = adamas_elab::program::analyze(SourceFile::new(uri.as_str(), text), &sources);
    assert!(
        program.error().is_none(),
        "заготовка обязана проверяться: {:?}",
        program.error().map(|it| program.rendered(it))
    );
    document.absorb(&mut program);
    (uri, document)
}

/// Всё окно буфера.
fn whole() -> Range {
    Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: u32::MAX,
            character: 0,
        },
    }
}

/// Подсказка в одну строку; у части со ссылкой в строку попадает её строка.
fn rendered(hint: &InlayHint) -> String {
    let label = match &hint.label {
        InlayHintLabel::String(text) => text.clone(),
        InlayHintLabel::LabelParts(parts) => parts
            .iter()
            .map(|part| match &part.location {
                Some(at) => format!("{}@{}", part.value, at.range.start.line),
                None => part.value.clone(),
            })
            .collect::<String>(),
    };
    format!("{}:{} {label}", hint.position.line, hint.position.character)
}

/// Подсказки **про эффекты**: аллокационные отброшены по своим словам.
fn effects(uri: &Uri, document: &Document) -> Vec<String> {
    hints::hints(uri, document, whole(), Encoding::Utf16)
        .iter()
        .map(rendered)
        .filter(|it| it.contains("Ask") || it.contains("Shout"))
        .collect()
}

const SOURCE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

effect Ask where
  ask : Nat

effect Shout where
  shout : Nat -> Unit

asked : {Ask} Nat
asked = ask

loud : {Shout} Unit
loud = shout Zero

one : Nat
one = handle asked with
  return v -> v
  ask -> resume Zero

two : Nat
two = handle asked with
  return v -> v
  ask -> resume (Succ Zero)
";

#[test]
fn a_handler_says_which_label_it_discharges() {
    // Ни один из двух `handle` не пишет `Ask`: метка берётся из первой ветки.
    let (uri, document) = checked(SOURCE);
    let found = effects(&uri, &document);
    assert!(
        found.contains(&"20:6 Ask".to_owned()),
        "первый хендлер обязан назвать свою метку: {found:#?}"
    );
    assert!(
        found.contains(&"25:6 Ask".to_owned()),
        "второй тоже: {found:#?}"
    );
    assert!(
        !SOURCE.contains("handle @"),
        "заготовка обязана держать метку **ненаписанной**, иначе показывать нечего"
    );
}

#[test]
fn an_operation_names_every_handler_that_could_catch_it() {
    // Два хендлера на одну метку, и назван каждый - своим именем и своим
    // адресом. Один хендлер показал бы то же самое у механизма, который берёт
    // первый попавшийся.
    let (uri, document) = checked(SOURCE);
    let found = effects(&uri, &document);
    assert!(
        found.contains(&"14:8 Ask: one@20, two@25".to_owned()),
        "`ask` обязан назвать оба хендлера: {found:#?}"
    );
}

#[test]
fn a_label_that_leaves_in_the_row_says_so() {
    // `Shout` в этом файле не гасится. Молчание читалось бы как «механизма
    // нет», а не как «хендлера нет».
    let (uri, document) = checked(SOURCE);
    let found = effects(&uri, &document);
    assert!(
        found.contains(&"17:7 Shout: в ряд".to_owned()),
        "негасимая метка обязана сказать, что уходит в ряд: {found:#?}"
    );
}

#[test]
fn a_handler_branch_is_not_a_use_of_the_operation() {
    // `ask -> resume Zero` называет ветку, а не производит операцию, и
    // подсказки «кто это погасит» там нет: погашение здесь и происходит.
    // Различение это не выбор оформления - имя ветки в текст ответа не
    // элаборируется вовсе, - но записать его надо: без свидетеля оно
    // неотличимо от пробела.
    let (uri, document) = checked(SOURCE);
    let found = effects(&uri, &document);
    assert!(
        !found
            .iter()
            .any(|it| it.starts_with("22:2") || it.starts_with("27:2")),
        "ветка хендлера получила подсказку использования: {found:#?}"
    );
}

#[test]
fn the_whole_set_is_what_it_should_be() {
    // Множество целиком: пропажа подсказки заметна так же, как выдумка.
    let (uri, document) = checked(SOURCE);
    assert_eq!(
        effects(&uri, &document),
        [
            "14:8 Ask: one@20, two@25",
            "17:7 Shout: в ряд",
            "20:6 Ask",
            "25:6 Ask",
        ],
        "подсказки про эффекты целиком"
    );
}
