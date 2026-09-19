//! Байтовые смещения компилятора в позиции LSP и обратно.
//!
//! Спан ядра - полуинтервал байтовых смещений ([`adamas_core::source::Span`]).
//! Позиция LSP - строка и **номер кодовой единицы** внутри строки, причём
//! единица зависит от кодировки, о которой клиент и сервер договариваются в
//! `initialize`. Умолчание протокола - UTF-16.
//!
//! # Почему это не мелочь
//!
//! Три счёта совпадают ровно на латинице. `двойка` - шесть знаков, шесть
//! единиц UTF-16 и **двенадцать** байтов; `😀` - один знак, **две** единицы
//! UTF-16 и четыре байта. Исходники проекта несут русские комментарии, то есть
//! строка, где все три числа различны, встречается обыденно, а тест на чисто
//! латинском файле зелен при любой поломке перевода.
//!
//! Свидетель - `tests/golden/errors/position-past-multibyte.adamas`: до места
//! отказа на его последней строке 26 байтов, 18 единиц UTF-16 и 17 знаков. Три
//! разных числа одной позиции различают все три прочтения сразу.

use adamas_core::source::{Location, SourceFile, Span};
use lsp_types::{Position, PositionEncodingKind, Range};

/// Чем клиент меряет позицию внутри строки.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Encoding {
    /// Байты UTF-8.
    Utf8,
    /// Кодовые единицы UTF-16 - умолчание протокола.
    #[default]
    Utf16,
    /// Скалярные значения Unicode.
    Utf32,
}

impl Encoding {
    /// Имя кодировки в протоколе.
    #[must_use]
    pub fn kind(self) -> PositionEncodingKind {
        match self {
            Self::Utf8 => PositionEncodingKind::UTF8,
            Self::Utf16 => PositionEncodingKind::UTF16,
            Self::Utf32 => PositionEncodingKind::UTF32,
        }
    }

    /// Кодировка по имени из протокола. Неизвестное имя - `None`.
    #[must_use]
    pub fn of(kind: &PositionEncodingKind) -> Option<Self> {
        match kind.as_str() {
            "utf-8" => Some(Self::Utf8),
            "utf-16" => Some(Self::Utf16),
            "utf-32" => Some(Self::Utf32),
            _ => None,
        }
    }

    /// Сколько единиц занимает один знак.
    fn width(self, ch: char) -> usize {
        match self {
            Self::Utf8 => ch.len_utf8(),
            Self::Utf16 => ch.len_utf16(),
            Self::Utf32 => 1,
        }
    }

    /// Сколько единиц занимает кусок текста.
    fn units(self, text: &str) -> usize {
        match self {
            Self::Utf8 => text.len(),
            Self::Utf16 => text.chars().map(char::len_utf16).sum(),
            Self::Utf32 => text.chars().count(),
        }
    }
}

/// Байтовое смещение в позицию LSP.
///
/// `None`, если смещение выходит за файл или режет знак: и то и другое -
/// внутренний баг, но валиться на нём сервер не вправе (§7.4).
#[must_use]
pub fn position(file: &SourceFile, offset: usize, encoding: Encoding) -> Option<Position> {
    let location = file.location(offset)?;
    let start = file.offset(Location::new(location.line, 1))?;
    let prefix = file.text().get(start..offset)?;
    Some(Position {
        line: u32::try_from(location.line - 1).ok()?,
        character: u32::try_from(encoding.units(prefix)).ok()?,
    })
}

/// Позиция LSP в байтовое смещение.
///
/// Колонка за концом строки прижимается к её концу, а колонка внутри
/// суррогатной пары - к началу знака: так велит спецификация, и без этого
/// правки от клиента, считающего иначе, резали бы UTF-8.
#[must_use]
pub fn offset(file: &SourceFile, position: Position, encoding: Encoding) -> Option<usize> {
    let line = usize::try_from(position.line).ok()?.checked_add(1)?;
    let start = file.offset(Location::new(line, 1))?;
    let wanted = usize::try_from(position.character).ok()?;
    let rest = file.text().get(start..)?;
    let mut units = 0usize;
    for (index, ch) in rest.char_indices() {
        if ch == '\n' || units + encoding.width(ch) > wanted {
            return Some(start + index);
        }
        units += encoding.width(ch);
    }
    Some(file.text().len())
}

/// Спан в диапазон LSP.
///
/// Смещение, которое не переводится, заменяется началом файла: сообщение с
/// уехавшей кареткой лучше, чем упавший сервер.
#[must_use]
pub fn range(file: &SourceFile, span: Span, encoding: Encoding) -> Range {
    let start = position(file, span.start(), encoding).unwrap_or_default();
    let end = position(file, span.end(), encoding).unwrap_or(start);
    Range { start, end }
}

/// Диапазон LSP в спан.
#[must_use]
pub fn span(file: &SourceFile, range: Range, encoding: Encoding) -> Option<Span> {
    let start = offset(file, range.start, encoding)?;
    let end = offset(file, range.end, encoding)?;
    Some(Span::new(start.min(end), start.max(end)))
}

#[cfg(test)]
mod tests {
    use super::{Encoding, offset, position, range, span};
    use adamas_core::source::{SourceFile, Span};
    use lsp_types::{Position, Range};
    use proptest::prelude::*;

    /// Числа записаны руками, а не посчитаны тем же кодом: перевод, ошибочный
    /// одинаково в обе стороны, круговой проверке не виден.
    #[test]
    fn three_encodings_disagree_past_a_multibyte_line() {
        let text = "двойка = {- 😀 -} Succ Zero Zero";
        let file = SourceFile::new("t.adamas", text);
        let at = text.find("Succ").expect("`Succ` в строке есть");
        assert_eq!(at, 26, "байтов до места отказа");
        assert_eq!(
            position(&file, at, Encoding::Utf8),
            Some(Position::new(0, 26))
        );
        assert_eq!(
            position(&file, at, Encoding::Utf16),
            Some(Position::new(0, 18))
        );
        assert_eq!(
            position(&file, at, Encoding::Utf32),
            Some(Position::new(0, 17))
        );
    }

    #[test]
    fn line_number_counts_lines_not_bytes() {
        let file = SourceFile::new("t.adamas", "ох\nох\nx");
        let at = file.text().find('x').expect("`x` в тексте есть");
        assert_eq!(
            position(&file, at, Encoding::Utf16),
            Some(Position::new(2, 0))
        );
    }

    #[test]
    fn column_past_the_end_clamps_to_the_line() {
        let file = SourceFile::new("t.adamas", "аб\nв");
        assert_eq!(
            offset(&file, Position::new(0, 99), Encoding::Utf16),
            Some(4)
        );
        assert_eq!(
            offset(&file, Position::new(1, 99), Encoding::Utf16),
            Some(7)
        );
    }

    /// Колонка внутри суррогатной пары округляется вниз: иначе смещение
    /// разрезало бы знак, и `SourceFile::location` вернул бы `None`.
    #[test]
    fn column_inside_a_surrogate_pair_rounds_down() {
        let file = SourceFile::new("t.adamas", "a😀b");
        assert_eq!(offset(&file, Position::new(0, 1), Encoding::Utf16), Some(1));
        assert_eq!(offset(&file, Position::new(0, 2), Encoding::Utf16), Some(1));
        assert_eq!(offset(&file, Position::new(0, 3), Encoding::Utf16), Some(5));
    }

    #[test]
    fn span_survives_the_round_trip() {
        let text = "двойка = {- 😀 -} Succ Zero Zero";
        let file = SourceFile::new("t.adamas", text);
        let at = text.find("Succ").expect("`Succ` в строке есть");
        let source = Span::new(at, at + "Succ Zero Zero".len());
        for encoding in [Encoding::Utf8, Encoding::Utf16, Encoding::Utf32] {
            let there = range(&file, source, encoding);
            assert_eq!(span(&file, there, encoding), Some(source), "{encoding:?}");
        }
    }

    #[test]
    fn range_of_a_multibyte_span_is_written_out() {
        let text = "двойка = {- 😀 -} Succ Zero Zero";
        let file = SourceFile::new("t.adamas", text);
        let at = text.find("Succ").expect("`Succ` в строке есть");
        assert_eq!(
            range(&file, Span::new(at, at + 14), Encoding::Utf16),
            Range::new(Position::new(0, 18), Position::new(0, 32))
        );
    }

    proptest! {
        /// Смещение -> позиция -> смещение не теряет информации ни в одной из
        /// трёх кодировок.
        #[test]
        fn offset_round_trips(text in "(?s)[a-zа-я\u{1F600}\n ]{0,60}") {
            let file = SourceFile::new("prop.adamas", text.clone());
            for encoding in [Encoding::Utf8, Encoding::Utf16, Encoding::Utf32] {
                for at in 0..=text.len() {
                    if !text.is_char_boundary(at) {
                        continue;
                    }
                    let there = position(&file, at, encoding).expect("граница знака переводится");
                    prop_assert_eq!(offset(&file, there, encoding), Some(at), "{:?}", encoding);
                }
            }
        }
    }
}
