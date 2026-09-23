//! Что подсказка показывает читателю (§5.1, §7.2).
//!
//! # Свидетель сверяет подпись и место, а не наличие ответа
//!
//! Проверка «сервер вернул непустой список» зелена и тогда, когда список
//! бессмыслен. Здесь каждая подсказка сворачивается в строку вида
//! `строка:знак подпись`, и у части подписи, ведущей куда-то, в эту же строку
//! попадает её адрес. Перепутанный кадр маршрута, потерянное звено цепочки,
//! чужой файл в ссылке - всё это меняет строку, и меняет заметно.
//!
//! Позиции здесь **в кодовых единицах UTF-16**, и в заготовке `SOURCE` они
//! совпадают с байтами: латиница. Различение трёх счётов - работа прогона по
//! протоколу (`protocol.rs`), где в строке стоит `😀`.

use std::path::{Path, PathBuf};
use std::str::FromStr as _;

use adamas_core::source::SourceFile;
use adamas_lsp::lsp_types::{InlayHint, InlayHintLabel, Position, Range, Uri};
use adamas_lsp::{Document, Encoding, hints, position};

/// Корпус `tests/golden/eval/` - он же корень поиска подключаемых модулей.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Буфер, проверенный так же, как это делает сервер на уведомлении.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn checked(name: &str, text: &str) -> (Uri, Document) {
    let uri = Uri::from_str(&format!("file:///corpus/{name}")).expect("URI заготовки");
    let mut document = Document::of(&uri, text.to_owned());
    let sources = adamas_elab::program::Directory::new(corpus());
    let mut program = adamas_elab::program::analyze(SourceFile::new(uri.as_str(), text), &sources);
    document.absorb(&mut program);
    (uri, document)
}

/// Окно от строки `from` до строки `upto` включительно.
fn window(from: u32, upto: u32) -> Range {
    Range {
        start: Position {
            line: from,
            character: 0,
        },
        end: Position {
            line: upto + 1,
            character: 0,
        },
    }
}

/// Всё окно буфера: конец за последней строкой прижимается к концу текста.
fn whole() -> Range {
    window(0, u32::MAX - 1)
}

/// Подсказка в одну строку: место, подпись и адреса частей.
///
/// Адрес пишется вместе с **именем файла**: ссылка, уехавшая в чужой файл,
/// иначе была бы неотличима от своей.
fn rendered(hint: &InlayHint) -> String {
    let label = match &hint.label {
        InlayHintLabel::String(text) => text.clone(),
        InlayHintLabel::LabelParts(parts) => parts
            .iter()
            .map(|part| match &part.location {
                Some(at) => {
                    let file = at.uri.as_str().rsplit('/').next().unwrap_or_default();
                    format!(
                        "{}@{file}:{}:{}",
                        part.value, at.range.start.line, at.range.start.character
                    )
                }
                None => part.value.clone(),
            })
            .collect::<String>(),
    };
    format!("{}:{} {label}", hint.position.line, hint.position.character)
}

/// Подсказки буфера, свёрнутые в строки.
fn lines(uri: &Uri, document: &Document, range: Range) -> Vec<String> {
    hints::hints(uri, document, range, Encoding::Utf16)
        .iter()
        .map(rendered)
        .collect()
}

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

far : Nat -> Pair
far n = reach n

quiet : Nat -> Nat
quiet n = n

mirror : Pair -> Pair
mirror (MkPair a b) = MkPair b a
";

/// Ответ целиком: всё, что буфер показывает читателю, и ничего сверх.
///
/// Список сверяется **целым**, а не поиском нужной строки: лишняя подсказка -
/// такая же неправда, как пропущенная, и поиск её не увидит.
#[test]
fn the_whole_answer_is_what_the_reader_sees() {
    let (uri, document) = checked("hints.adamas", SOURCE);
    assert_eq!(
        lines(&uri, &document, whole()),
        [
            // Статус над объявлением: щелчок по слову `куча` ведёт туда, где
            // определение аллоцирует, а конец подписи называет источник.
            "7:0 куча@hints.adamas:8:9: MkPair",
            // Место внутри тела - само построение.
            "8:9 куча",
            // Цепочка в одно звено: `reach` зовёт `wrap`, и у звена свой адрес -
            // место, где аллоцирует **оно**.
            "10:0 куча@hints.adamas:11:10: wrap@hints.adamas:8:9 → MkPair",
            "11:10 куча",
            // Цепочка длиннее одного звена: на короткой первое и последнее
            // звено совпадают, и перепутать их нечем.
            "13:0 куча@hints.adamas:14:8: reach@hints.adamas:11:10 → wrap@hints.adamas:8:9 → \
             MkPair",
            "14:8 куча",
            // Вердикт написан `@noalloc`, а не «не аллоцирует»: это ответ
            // проверки, и область у него у́же машины (§10 вопрос 190).
            "16:0 @noalloc",
            // Две половины одного тела: вердикт кучи говорит «аллоцирует»
            // (Perceus'а нет), а форма кода reuse'у не мешает. Обе правда, и
            // обе показаны.
            "19:0 куча@hints.adamas:20:22: MkPair, reuse 1",
            "20:22 куча",
            "20:22 reuse",
        ]
    );
}

/// Над конструктором статуса нет - какой бы формой он ни был написан.
///
/// Конструктор `data` объявляется своей формой, а конструктор `resource` - той
/// же, что определение (`Shouted : Pair -> Loud`). Отбор по одному синтаксису
/// поэтому молчал бы над первым и говорил над вторым, и это не мелочь: `куча:
/// Shouted` над объявлением обещает читателю место, которого у конструктора
/// нет вовсе - аллоцирует **применение**, а не объявление.
///
/// Свидетель корпусный это и поймал; здесь он свёрнут в заготовку, где обе
/// формы стоят рядом.
#[test]
fn a_constructor_gets_no_status_in_either_syntax() {
    const RESOURCEFUL: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

resource Loud where
  Shouted : Pair -> Loud
  closeLoud : (1 l : Loud) -> Pair
  closeLoud (Shouted p) = p

main : Nat
main = Zero
";
    let (uri, document) = checked("resourceful.adamas", RESOURCEFUL);
    assert_eq!(
        lines(&uri, &document, whole()),
        ["9:2 @noalloc", "12:0 @noalloc"],
        "статус - только у двух определений, конструкторы молчат"
    );
}

/// Окно клиента ограничивает ответ.
///
/// Протокол просит подсказки **видимого** куска, и подсказка за его границей -
/// не щедрость, а нарушение: клиент рисует то, что попросил.
#[test]
fn the_window_bounds_the_answer() {
    let (uri, document) = checked("hints.adamas", SOURCE);
    assert_eq!(
        lines(&uri, &document, window(10, 11)),
        [
            "10:0 куча@hints.adamas:11:10: wrap@hints.adamas:8:9 → MkPair",
            "11:10 куча",
        ],
        "видны только подсказки двух строк, а адреса частей ведут и наружу"
    );
}

/// Буфер, который не проверился, молчит - и молчит **сразу**.
///
/// Подсказка от прошлого текста указывала бы в строки, которых больше нет.
/// Правка снимает сигнатуру (`Document::retext`), и до следующего прохода
/// показывать нечего.
#[test]
fn an_edited_buffer_says_nothing_until_it_is_checked_again() {
    let (uri, mut document) = checked("hints.adamas", SOURCE);
    assert!(!lines(&uri, &document, whole()).is_empty());
    document.retext(SOURCE.replace("wrap n = MkPair n n", "wrap n = MkPair n"));
    assert!(
        lines(&uri, &document, whole()).is_empty(),
        "сигнатура прошлого текста описывает не этот буфер"
    );
}

/// Звено, у которого места нет, названо, а не проглочено.
///
/// В цепочку попадает `Source::Call` определения **с телом**, а словарь
/// инстанса и значение функтора тело имеют, написанного выражения - нет. На
/// корпусе таких звеньев 12. Молчаливый пропуск дал бы цепочку с дыркой
/// посередине, а неработающий щелчок читатель принял бы за поломку редактора.
#[test]
fn a_link_without_a_place_is_named_not_swallowed() {
    let name = "class-multiplicity.adamas";
    let text = std::fs::read_to_string(corpus().join(name))
        .unwrap_or_else(|error| panic!("фикстура корпуса обязана читаться: {error}"));
    let (uri, document) = checked(name, &text);
    let found = lines(&uri, &document, whole());
    assert!(
        found.contains(
            &"34:0 куча@class-multiplicity.adamas:35:7: ‹Mappable#List› → запись".to_owned()
        ),
        "звено без места обязано быть названо: {found:?}"
    );
    let marked = hints::hints(&uri, &document, whole(), Encoding::Utf16)
        .into_iter()
        .filter_map(|hint| match hint.label {
            InlayHintLabel::LabelParts(parts) => Some(parts),
            InlayHintLabel::String(_) => None,
        })
        .flatten()
        .any(|part| part.value.starts_with('‹') && part.tooltip.is_some());
    assert!(marked, "у звена без места обязано быть объяснение");
}

/// Место из подключённого модуля в этот буфер не рисуется.
///
/// Сигнатура одна на программу, и мест в ней больше, чем строк в буфере: спан
/// чужого файла, нарисованный по этому тексту, подчеркнул бы случайную строку.
/// Свидетель сверяет список **целиком** - лишняя подсказка видна только так.
#[test]
fn a_place_from_an_imported_module_is_not_drawn_here() {
    let name = "library.adamas";
    let text = std::fs::read_to_string(corpus().join(name))
        .unwrap_or_else(|error| panic!("фикстура корпуса обязана читаться: {error}"));
    let (uri, document) = checked(name, &text);
    assert_eq!(
        lines(&uri, &document, whole()),
        [
            "41:0 @noalloc",
            "47:0 куча@library.adamas:48:7: запись",
            "48:7 куча",
        ],
        "трёх файлов программа, а подсказки - только у своего"
    );
}

/// Звено цепочки, живущее в другом файле, ведёт **в тот** файл.
///
/// Заготовка, а не фикстура корпуса: цепочка, пересекающая границу файла у
/// определения **входного** буфера, в корпусе сегодня не встречается (проверено
/// обходом - все семь таких цепочек живут целиком внутри подключённого
/// модуля). Ради этого случая [`adamas_core::sig::Spot`] и несёт путь модуля.
#[test]
fn a_link_in_another_file_points_into_that_file() {
    const BORROWED: &str = "\
import Cmp.Truth (Bool)
import Cmp.Words (isBig)

echo : UInt64 -> Bool
echo n = isBig n
";
    let (uri, document) = checked("borrowed.adamas", BORROWED);
    let found = lines(&uri, &document, whole());
    let status = found
        .iter()
        .find(|line| line.starts_with("3:0 "))
        .unwrap_or_else(|| panic!("статус над `echo` обязан быть: {found:?}"));
    assert!(
        status.contains("@Words.adamas:"),
        "звено обязано вести в свой файл, а не в этот: {status}"
    );
    assert!(
        status.contains("Cmp.Words.isBig@"),
        "звено обязано быть названо: {status}"
    );
}

/// Фикстуры корпуса по алфавиту.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанный корпус, и падать он должен громко"
)]
fn fixtures() -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = std::fs::read_dir(corpus())
        .expect("каталог корпуса обязан читаться")
        .map(|entry| entry.expect("запись каталога").path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    found.sort();
    found
}

/// Определение, аллоцирующее без места: как подсказка ведёт себя на нём.
///
/// Таких имён на корпусе **82** (замер трека A), и делятся они надвое, причём
/// по признаку, который решает и поведение подсказки.
///
/// *Тела нет* - постулат, `extern`. Место внутри тела взяться не может, потому
/// что тела нет; зато написано **объявление**, и статус стоит над ним. Он там и
/// нужен: чинить читателю нечего внутри, ответ - дописать `@noalloc` либо тело.
///
/// *Тело есть, а клауз нет* - значение модуля, словарь инстанса, запись,
/// которую собрала элаборация. Написанного объявления значения за ней нет
/// вовсе, и подсказке стоять негде. Молчание тут не пробел, а единственный
/// правдивый ответ; звено цепочки, наоборот, **названо**
/// ([`a_link_without_a_place_is_named_not_swallowed`]) - там подпись чужая, и
/// дырка в ней была бы видна.
///
/// Свидетель закрывает границу с обеих сторон: всякое имя без места, попавшее
/// под статус, обязано быть без тела, и оба множества обязаны быть непусты.
#[test]
fn a_definition_without_a_place_is_shown_by_whether_it_has_a_body() {
    let mut bodiless = 0_usize;
    let mut unwritten = 0_usize;
    for path in fixtures() {
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("файл корпуса обязан читаться: {error}"));
        let name = path
            .file_name()
            .and_then(|it| it.to_str())
            .unwrap_or_default();
        let (_, document) = checked(name, &text);
        let (Some(signature), Some(module)) = (document.signature(), document.module()) else {
            continue;
        };
        let written: Vec<_> = adamas_elab::cursor::definitions(signature, module)
            .into_iter()
            .map(|(it, _)| it)
            .collect();
        for full in signature.names() {
            let Some(definition) = signature.lookup(&full) else {
                continue;
            };
            if definition.allocates.is_none() || signature.allocated_at(&full).is_some() {
                continue;
            }
            if written.contains(&full) {
                assert!(
                    definition.body.is_none(),
                    "{name}: `{full}` написана, имеет тело и аллоцирует, а места не знает"
                );
                bodiless += 1;
            } else {
                unwritten += 1;
            }
        }
    }
    assert!(bodiless > 0, "постулаты в корпусе обязаны быть");
    assert!(
        unwritten > 0,
        "остаток без написанного объявления обязан быть непустым"
    );
}

/// На всём корпусе подсказка стоит на написанном, а не в пустоте.
///
/// Обе половины существенны. Позиция обязана переводиться обратно в смещение
/// **этого** текста - иначе клиент получил бы каретку за концом буфера. И под
/// ней обязан стоять знак, а не пробел: спан, нарисованный по чужому файлу,
/// садится в произвольное место, и середина отступа - самый частый исход.
///
/// **Конец непустой строки - законное место, и это уточнение, а не
/// послабление.** Подсказка волны 4 «сюда встанет деструктор» стоит за концом
/// тела (§3.3, §7.2), то есть ровно на переводе строки: место у неё такое по
/// существу - вставка происходит **после** написанного. Середина отступа и
/// пустая строка по-прежнему отвергаются, и именно их проверка и заводилась
/// ловить.
#[test]
fn every_hint_on_the_corpus_stands_on_written_text() {
    let mut counted = 0_usize;
    for path in fixtures() {
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("файл корпуса обязан читаться: {error}"));
        let name = path
            .file_name()
            .and_then(|it| it.to_str())
            .unwrap_or_default();
        let (uri, document) = checked(name, &text);
        let file = SourceFile::new(uri.as_str(), text.as_str());
        for hint in hints::hints(&uri, &document, whole(), Encoding::Utf16) {
            let offset = position::offset(&file, hint.position, Encoding::Utf16)
                .unwrap_or_else(|| panic!("{name}: подсказка {:?} вне буфера", hint.position));
            let standing = match text[offset..].chars().next() {
                None => true,
                Some('\n') => text[..offset]
                    .rsplit('\n')
                    .next()
                    .is_some_and(|line| !line.trim().is_empty()),
                Some(under) => !under.is_whitespace(),
            };
            assert!(
                standing,
                "{name}: подсказка {:?} стоит на пустоте",
                hint.position
            );
            counted += 1;
        }
    }
    // Число не сверяется точно - оно растёт с корпусом; проверяется, что
    // проверять было что: пустой обход зелен при любой поломке. Снято прогоном:
    // **2361** подсказка на 127 фикстурах у волны 3, **2854** у волны 4 -
    // прибавка есть жизнь ресурсов и погашение меток (§7.2).
    assert!(
        counted > 2500,
        "подсказок {counted} - было 2854, корпус не мог обеднеть"
    );
}
