//! Жизнь ресурса в тексте: где взят и где закроется (§3.3, §7.2).
//!
//! # Чем этот свидетель ломается
//!
//! Подсказка о ресурсе врёт тремя разными способами, и каждый здесь свой тест.
//!
//! 1. **Сказать «закроется», где не закроется.** Связывание, расходуемое
//!    дальше, деструктора не получает - закрывает его тот, кто взял; и сам
//!    деструктор своего параметра не закрывает, иначе он звал бы себя. Оба
//!    случая стоят в заготовке рядом с закрываемым, и отличаются они от него
//!    ровно тем, чем должны.
//! 2. **Промолчать там, где закроется.** Обратная сторона той же проверки:
//!    множество подсказок сверяется **целиком**, поэтому пропажа заметна так
//!    же, как выдумка.
//! 3. **Соврать про порядок.** §3.3 обещает LIFO, и порядок этот наблюдаем:
//!    `eval/resource.adamas` различает `[1, 8, 9]` от `[1, 9, 8]`. Различить
//!    его можно только **двумя** деструкторами в одной точке, поэтому в
//!    заготовке есть пара.
//!
//! Позиции здесь в кодовых единицах UTF-16 и совпадают с байтами: латиница.

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
    let uri = Uri::from_str("file:///corpus/resources.adamas").expect("URI заготовки");
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

/// Подсказка в одну строку: место и подпись.
fn rendered(hint: &InlayHint) -> String {
    let label = match &hint.label {
        InlayHintLabel::String(text) => text.clone(),
        InlayHintLabel::LabelParts(parts) => parts
            .iter()
            .map(|part| part.value.clone())
            .collect::<String>(),
    };
    format!("{}:{} {label}", hint.position.line, hint.position.character)
}

/// Подсказки **про ресурсы**: аллокационные сюда не относятся и отброшены по
/// своим словам.
fn resources(uri: &Uri, document: &Document) -> Vec<String> {
    hints::hints(uri, document, whole(), Encoding::Utf16)
        .iter()
        .filter(|hint| {
            let text = rendered(hint);
            text.contains("resource") || text.contains("close")
        })
        .map(rendered)
        .collect()
}

/// Три формы разом: закрываемое связывание, расходуемое и пара под LIFO.
///
/// Заготовка одна на все проверки нарочно: формы обязаны различаться **внутри
/// одного прохода**, иначе свидетель зелен у механизма, который отвечает одно и
/// то же на всё.
const SOURCE: &str = "\
data Bool where
  False : Bool
  True : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

effect Log where
  note : Nat -> Unit

resource File where
  Open : File
  closeFile : (1 h : File) -> {Log} Bool
  closeFile h =
    note 9
    True

resource Sock where
  Bind : Sock
  closeSock : (1 s : Sock) -> {Log} Bool
  closeSock s =
    note 8
    True

plain : File -> {Log} Bool
plain h =
  note 1
  True

spent : File -> {Log} Bool
spent h = plain h

paired : File -> Sock -> {Log} Bool
paired h s =
  note 1
  True
";

#[test]
fn every_resource_binding_says_what_happens_to_it() {
    let (uri, document) = checked(SOURCE);
    assert_eq!(
        resources(&uri, &document),
        [
            // Параметр самого деструктора: `drop` внутри `drop` не вставляется.
            "17:12 resource, расходуется",
            "24:12 resource, расходуется",
            // Закрывается на выходе из тела - и вставка видна там, где её
            // сделает компилятор.
            "29:6 resource",
            "31:6 closeFile h",
            // Расходуется дальше: закроет тот, кто взял.
            "34:6 resource, расходуется",
            // Пара: оба взяты, оба закрываются в одной точке.
            "37:7 resource",
            "37:9 resource",
            "39:6 closeSock s, closeFile h",
        ],
        "подсказки целиком"
    );
}

#[test]
fn the_order_of_two_destructors_is_lifo() {
    // §3.3 обещает LIFO, и порядок наблюдаем: связанное позже закрывается
    // раньше. Отдельным тестом, а не только в списке выше: перепутанный
    // порядок - самая тихая из трёх поломок, и назвать её надо словами.
    let (uri, document) = checked(SOURCE);
    let found = resources(&uri, &document);
    let paired = found
        .iter()
        .find(|it| it.contains("closeSock"))
        .expect("пара обязана закрываться");
    assert!(
        paired.ends_with("closeSock s, closeFile h"),
        "связанное позже закрывается раньше: {paired}"
    );
}

#[test]
fn a_window_that_shows_nothing_says_nothing() {
    // Подсказки считаются по видимому куску: окно - требование протокола, а не
    // экономия. Без этой проверки `resources` мог бы отвечать целым файлом на
    // любой запрос, и цена подсказки перестала бы зависеть от окна.
    let (uri, document) = checked(SOURCE);
    let head = Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: 5,
            character: 0,
        },
    };
    let found: Vec<String> = hints::hints(&uri, &document, head, Encoding::Utf16)
        .iter()
        .map(rendered)
        .filter(|it| it.contains("resource") || it.contains("close"))
        .collect();
    assert!(
        found.is_empty(),
        "за окном подсказок быть не должно: {found:?}"
    );
}
