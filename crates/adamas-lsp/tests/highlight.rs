//! Вхождения и область локального связывания (§7.2, §10 вопрос 198).
//!
//! §7.2 обещала подсветку «области региона», а регион пишет программа, и
//! отличить его от `Vect (0 n : Nat)` анализу нечем. Подсвечивается поэтому
//! область **всякого** локального связывания - и у `r` региона она ровно та,
//! где регион действителен.
//!
//! Свидетель различает связывания, а не написания: затенённое одноимённое
//! связывание обязано остаться без подсветки, иначе сервер подсвечивал бы
//! текст, а не область.

use adamas_core::source::SourceFile;
use adamas_lsp::Encoding;
use adamas_lsp::lsp_types::{DocumentHighlightKind, Position};

/// Позиция `nth`-го (с нуля) вхождения `needle` в тексте - строка и колонка
/// UTF-16, как их шлёт редактор.
fn at(text: &str, needle: &str, nth: usize) -> Position {
    let offset = text
        .match_indices(needle)
        .nth(nth)
        .map_or_else(|| panic!("`{needle}` #{nth} не найдено"), |(at, _)| at);
    let before = &text[..offset];
    let line = before.matches('\n').count();
    let column = before
        .rsplit('\n')
        .next()
        .unwrap_or_default()
        .encode_utf16()
        .count();
    Position::new(
        u32::try_from(line).unwrap_or(u32::MAX),
        u32::try_from(column).unwrap_or(u32::MAX),
    )
}

/// Подсвеченное: начало каждого диапазона и его вид, по порядку текста.
fn highlighted(text: &str, position: Position) -> Option<Vec<(Position, DocumentHighlightKind)>> {
    let file = SourceFile::new("подсветка.adamas", text);
    let mut found: Vec<_> = adamas_lsp::occurrences(&file, position, Encoding::Utf16)?
        .into_iter()
        .map(|it| {
            (
                it.range.start,
                it.kind.unwrap_or(DocumentHighlightKind::TEXT),
            )
        })
        .collect();
    found.sort_by_key(|(start, _)| (start.line, start.character));
    Some(found)
}

#[test]
fn a_parameter_lights_its_binder_and_every_use() {
    let text = "twice : UInt64 -> UInt64\ntwice x = addUInt64 x x\n";
    let found = highlighted(text, at(text, "x", 2)).expect("параметр - локальное связывание");
    assert_eq!(
        found,
        [
            (at(text, "x", 0), DocumentHighlightKind::WRITE),
            (at(text, "x", 1), DocumentHighlightKind::READ),
            (at(text, "x", 2), DocumentHighlightKind::READ),
        ]
    );
}

#[test]
fn a_shadowing_binder_has_its_own_scope() {
    // Внутренний `x` лямбды - другое связывание: подсветка внешнего его не
    // берёт, и наоборот.
    let text = "pick : UInt64 -> UInt64\npick x = (\\x -> x) x\n";
    let outer = highlighted(text, at(text, "x", 0)).expect("внешний");
    assert_eq!(
        outer.iter().map(|(at, _)| *at).collect::<Vec<_>>(),
        [at(text, "x", 0), at(text, "x", 3)]
    );
    let inner = highlighted(text, at(text, "x", 2)).expect("внутренний");
    assert_eq!(
        inner.iter().map(|(at, _)| *at).collect::<Vec<_>>(),
        [at(text, "x", 1), at(text, "x", 2)]
    );
}

#[test]
fn a_top_level_name_has_no_scope_to_light() {
    let text = "one : UInt64\none = 1\n\ntwo : UInt64\ntwo = one\n";
    assert_eq!(highlighted(text, at(text, "one", 2)), None);
}

#[test]
fn the_region_of_a_reference_is_the_scope_of_its_binder() {
    // Форма корпуса (`eval/region-allocates-and-reads`): `r` параметра клаузы
    // стоит в типе ссылки - там, где регион действителен.
    let text = "\
data Region where
  Home : Region

data Ref (0 r : Region) (a : Type) where
  MkRef : Ref r a

effect Alloc (0 r : Region) where
  allocIn : UInt64 -> Ref r UInt64

program : (0 r : Region) -> (ω u : UInt64) -> {Alloc r} Ref r UInt64
program r u =
  let p : Ref r UInt64 = allocIn u
  p
";
    let binder = at(text, "program r", 0);
    let binder = Position::new(binder.line, binder.character + 8);
    let found = highlighted(text, binder).expect("`r` клаузы - локальное связывание");
    assert_eq!(
        found.iter().map(|(at, _)| *at).collect::<Vec<_>>(),
        [binder, at(text, "Ref r UInt64 =", 0).with_offset(4)],
        "подсвечено: {found:?}"
    );
}

/// Сдвиг позиции вправо - для имени внутри найденного куска.
trait Shifted {
    fn with_offset(self, by: u32) -> Self;
}

impl Shifted for Position {
    fn with_offset(self, by: u32) -> Self {
        Position::new(self.line, self.character + by)
    }
}
