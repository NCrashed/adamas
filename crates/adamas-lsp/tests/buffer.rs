//! Что буфер помнит между запросами (§7.2).
//!
//! Подсказки §7.2 считаются по **сигнатуре**: `alloc::blame` читает вердикты,
//! `Signature::allocated_at` - места. До волны 3 Фазы 9 проход её строил и
//! выбрасывал, и всякий запрос, которому она нужна, проверял бы программу
//! заново - те же 45,8 мс, ради экономии которых буфер уже хранит дерево.
//!
//! # Почему прогон не через протокол
//!
//! Состояние сервера между запросами наблюдаемо только через запросы, а запрос
//! `inlayHint` - работа трека C. Поэтому свидетель берёт **тот же метод**,
//! каким сервер кладёт в буфер результат прохода ([`Document::absorb`]):
//! второго пути к этому состоянию нет, и обойти проверяемое здесь нечем.

use std::path::Path;
use std::str::FromStr as _;

use adamas_core::alloc;
use adamas_core::source::SourceFile;
use adamas_core::term::Name;
use adamas_lsp::Document;
use adamas_lsp::lsp_types::Uri;

/// Корпус `tests/golden/eval/` - он же корень поиска подключаемых модулей.
fn corpus() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Буфер, проверенный так же, как это делает сервер на уведомлении.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn checked(name: &str, text: &str) -> Document {
    let uri = Uri::from_str(&format!("file:///corpus/{name}")).expect("URI заготовки");
    let mut document = Document::of(&uri, text.to_owned());
    let sources = adamas_elab::program::Directory::new(corpus());
    let mut program = adamas_elab::program::analyze(SourceFile::new(uri.as_str(), text), &sources);
    document.absorb(&mut program);
    document
}

/// Заготовка: определение, аллоцирующее через соседа.
const SOURCE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

wrap : Nat -> Pair
wrap n = MkPair n n

reach : Nat -> Pair
reach n = wrap n

main : Nat
main = Zero
";

/// Буфер отвечает про аллокацию, не проверяя программу заново.
///
/// Свидетель - **текст под спаном**, а не наличие ответа: сигнатура, взятая от
/// чужого прохода, дала бы места, которые в этот текст не попадают.
#[test]
fn a_buffer_answers_where_it_allocates() {
    let document = checked("blame.adamas", SOURCE);
    let signature = document
        .signature()
        .expect("буфер обязан помнить сигнатуру прохода");

    let name: Name = "reach".into();
    let blame = alloc::blame(signature, &name).expect("`reach` аллоцирует через `wrap`");
    assert_eq!(
        blame.through().iter().map(|it| &**it).collect::<Vec<_>>(),
        ["wrap"]
    );

    let text = document.text();
    let at = |name: &str| {
        signature
            .allocated_at(name)
            .map(|spot| &text[spot.span.start()..spot.span.end()])
    };
    assert_eq!(at("reach"), Some("wrap n"), "звено показывает вызов");
    assert_eq!(
        at(blame.owner(&name)),
        Some("MkPair n n"),
        "конец цепочки показывает построение"
    );
}

/// Правка буфера снимает сигнатуру прошлого текста.
///
/// Без этого подсказка пережила бы текст, к которому относится, и указывала бы
/// в строки, которых больше нет, - худший из возможных исходов для §7.2, где
/// «подсказка, которая врёт, хуже отсутствующей».
#[test]
fn an_edit_drops_what_belonged_to_the_old_text() {
    let mut document = checked("stale.adamas", SOURCE);
    assert!(document.signature().is_some());
    assert!(document.module().is_some());
    // Тот же метод, каким сервер применяет `didChange`: синхронизация полная,
    // и правка - весь текст.
    document.retext("main : Nat\nmain = Zero\n".to_owned());
    assert!(
        document.signature().is_none(),
        "сигнатура прошлого текста описывает не этот буфер"
    );
    assert!(
        document.module().is_none(),
        "дерево прошлого текста описывает не этот буфер"
    );
}

/// Модуль, подтянутый проходом, переводится в файл.
///
/// Место аллокации приходит **путём модуля** (`sig::Spot`), а редактору нужен
/// URI. Без этой пары звено цепочки из подключённого файла показать нечем.
#[test]
fn a_buffer_translates_a_module_path_into_a_file() {
    let text = std::fs::read_to_string(corpus().join("library.adamas"))
        .unwrap_or_else(|error| panic!("фикстура корпуса обязана читаться: {error}"));
    let document = checked("library.adamas", &text);
    let signature = document
        .signature()
        .expect("буфер обязан помнить сигнатуру прохода");

    let mut translated = 0_usize;
    for name in signature.names() {
        let Some(spot) = signature.allocated_at(&name) else {
            continue;
        };
        let Some(module) = spot.module.as_deref() else {
            continue;
        };
        let file = document
            .file_of(module)
            .unwrap_or_else(|| panic!("`{name}` называет модуль `{module}`, а файла у него нет"));
        let written = std::fs::read_to_string(file)
            .unwrap_or_else(|error| panic!("файл модуля `{module}` обязан читаться: {error}"));
        let cut = written
            .get(spot.span.start()..spot.span.end())
            .unwrap_or_else(|| panic!("`{name}` режет `{module}` за концом текста"));
        assert!(
            !cut.trim().is_empty(),
            "`{name}` подчёркивает в `{module}` пустоту"
        );
        translated += 1;
    }
    assert!(
        translated > 0,
        "фикстура из нескольких файлов обязана дать место не во входном"
    );
}
