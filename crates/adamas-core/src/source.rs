//! Позиции в исходном тексте — нижний слой диагностики (§7.4).
//!
//! Смещения байтовые (`usize`): их отдаёт лексер. Позиции — 1-based строка и
//! колонка в Unicode scalar values: их читает человек.

/// Полуоткрытый диапазон байтовых смещений `[start, end)` внутри одного файла.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// Создаёт спан из границ `[start, end)`.
    ///
    /// `start > end` — баг вызывающего, а не легальный вход: спан «поедет» на
    /// чужой фрагмент, и диагностика укажет не туда. В debug-сборке это ловит
    /// ассерт; в release границы нормализуются, чтобы арифметика по спану
    /// осталась осмысленной, но полагаться на нормализацию не следует.
    #[must_use]
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(start <= end, "перевёрнутый спан: {start} > {end}");
        Self {
            start: start.min(end),
            end: start.max(end),
        }
    }

    /// Пустой спан в точке `offset`.
    #[must_use]
    pub fn at(offset: usize) -> Self {
        Self {
            start: offset,
            end: offset,
        }
    }

    /// Начало диапазона (включительно).
    #[must_use]
    pub fn start(self) -> usize {
        self.start
    }

    /// Конец диапазона (не включительно).
    #[must_use]
    pub fn end(self) -> usize {
        self.end
    }

    /// Длина в байтах.
    #[must_use]
    pub fn len(self) -> usize {
        self.end - self.start
    }

    /// Пуст ли диапазон.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Наименьший спан, покрывающий оба. Используется при сборке спана
    /// узла AST из спанов его детей.
    #[must_use]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Содержит ли спан смещение.
    #[must_use]
    pub fn contains(self, offset: usize) -> bool {
        self.start <= offset && offset < self.end
    }
}

/// Позиция в файле: 1-based номер строки и 1-based номер колонки в символах.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Location {
    /// Номер строки, начиная с единицы.
    pub line: usize,
    /// Номер колонки в Unicode scalar values, начиная с единицы.
    pub column: usize,
}

impl Location {
    /// Создаёт позицию.
    #[must_use]
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Исходный файл с предпосчитанной таблицей начал строк.
///
/// Таблица считается один раз при загрузке, дальше перевод
/// `offset -> Location` — бинарный поиск по ней.
#[derive(Clone, Debug)]
pub struct SourceFile {
    name: String,
    text: String,
    /// Байтовое смещение начала каждой строки. Всегда непусто: `[0, ...]`.
    line_starts: Vec<usize>,
}

impl SourceFile {
    /// Загружает файл в память и считает таблицу начал строк.
    ///
    /// Разделителем строк считается `\n`; `\r` перед ним трактуется как часть
    /// содержимого строки и отбрасывается только в [`SourceFile::line_text`].
    #[must_use]
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> Self {
        let text = text.into();
        let mut line_starts = vec![0];
        line_starts.extend(text.match_indices('\n').map(|(index, _)| index + 1));
        Self {
            name: name.into(),
            text,
            line_starts,
        }
    }

    /// Имя файла в том виде, в каком его показывают в диагностике.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Полный текст файла.
    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Размер файла в байтах.
    #[must_use]
    pub fn len(&self) -> usize {
        self.text.len()
    }

    /// Пуст ли файл.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.text.is_empty()
    }

    /// Количество строк. Файл, оканчивающийся на `\n`, имеет пустую последнюю
    /// строку, и она считается.
    #[must_use]
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// Переводит байтовое смещение в позицию.
    ///
    /// Возвращает `None`, если смещение выходит за пределы файла или не
    /// попадает на границу символа. Смещение, равное длине файла, валидно —
    /// это позиция end-of-file.
    #[must_use]
    pub fn location(&self, offset: usize) -> Option<Location> {
        if offset > self.text.len() || !self.text.is_char_boundary(offset) {
            return None;
        }
        // Индекс последней строки, начало которой не превышает offset.
        let line_index = self.line_starts.partition_point(|&start| start <= offset) - 1;
        let line_start = self.line_starts[line_index];
        let column = self.text[line_start..offset].chars().count() + 1;
        Some(Location::new(line_index + 1, column))
    }

    /// Переводит позицию в байтовое смещение — операция, обратная
    /// [`SourceFile::location`].
    ///
    /// Колонки нумеруют символы строки вместе с её терминатором, поэтому у
    /// каждого валидного смещения ровно одно имя. Позиция сразу за концом
    /// строки — это `1:1` следующей строки, и своей колонки у неё нет;
    /// исключение — последняя строка, где такая позиция означает конец файла.
    ///
    /// Возвращает `None` для несуществующей строки, нулевых `line`/`column`
    /// и колонки за пределами строки.
    #[must_use]
    pub fn offset(&self, location: Location) -> Option<usize> {
        if location.line == 0 || location.column == 0 {
            return None;
        }
        let line_index = location.line - 1;
        let line_start = *self.line_starts.get(line_index)?;
        let line_end = self.line_end(line_index);
        // Терминатора у последней строки нет, поэтому точку вставки в её конце
        // (она же end-of-file) надо назвать отдельной колонкой.
        let eof = (line_index + 1 == self.line_starts.len()).then_some(line_end);

        self.text[line_start..line_end]
            .char_indices()
            .map(|(index, _)| line_start + index)
            .chain(eof)
            .nth(location.column - 1)
    }

    /// Текст строки без завершающих `\n` и `\r`. `line` — 1-based.
    #[must_use]
    pub fn line_text(&self, line: usize) -> Option<&str> {
        let line_index = line.checked_sub(1)?;
        let start = *self.line_starts.get(line_index)?;
        let end = self.line_end(line_index);
        Some(
            self.text[start..end]
                .trim_end_matches('\n')
                .trim_end_matches('\r'),
        )
    }

    /// Фрагмент текста под спаном. `None`, если спан выходит за границы файла
    /// или режет символ.
    #[must_use]
    pub fn snippet(&self, span: Span) -> Option<&str> {
        self.text.get(span.start()..span.end())
    }

    /// Байтовое смещение конца строки — начало следующей или конец файла.
    fn line_end(&self, line_index: usize) -> usize {
        self.line_starts
            .get(line_index + 1)
            .copied()
            .unwrap_or(self.text.len())
    }
}

#[cfg(test)]
mod tests {
    use super::{Location, SourceFile, Span};
    use proptest::prelude::*;

    #[test]
    fn empty_file_has_one_line() {
        let file = SourceFile::new("empty.adamas", "");
        assert_eq!(file.line_count(), 1);
        assert_eq!(file.location(0), Some(Location::new(1, 1)));
        assert_eq!(file.line_text(1), Some(""));
    }

    #[test]
    fn trailing_newline_creates_empty_last_line() {
        let file = SourceFile::new("t.adamas", "ab\n");
        assert_eq!(file.line_count(), 2);
        assert_eq!(file.location(3), Some(Location::new(2, 1)));
        assert_eq!(file.line_text(2), Some(""));
    }

    #[test]
    fn columns_count_characters_not_bytes() {
        // «λ» занимает два байта, «привет» — по два байта на символ.
        let file = SourceFile::new("t.adamas", "λ привет\nx");
        let offset = file.text().find('п').unwrap();
        assert_eq!(file.location(offset), Some(Location::new(1, 3)));
    }

    #[test]
    fn location_rejects_offsets_inside_a_character() {
        let file = SourceFile::new("t.adamas", "λ");
        assert_eq!(file.location(1), None);
        assert_eq!(file.location(2), Some(Location::new(1, 2)));
        assert_eq!(file.location(3), None);
    }

    #[test]
    fn crlf_is_stripped_from_line_text() {
        let file = SourceFile::new("t.adamas", "a\r\nb");
        assert_eq!(file.line_text(1), Some("a"));
        assert_eq!(file.line_text(2), Some("b"));
    }

    #[test]
    fn offset_past_line_end_does_not_alias_next_line() {
        let file = SourceFile::new("t.adamas", "ab\ncd\n");
        // Колонка 3 — сам терминатор, точка вставки в конце строки.
        assert_eq!(file.offset(Location::new(1, 3)), Some(2));
        // Колонка 4 уже называется как 2:1, второго имени у неё нет.
        assert_eq!(file.offset(Location::new(1, 4)), None);
        assert_eq!(file.offset(Location::new(2, 1)), Some(3));
    }

    #[test]
    fn offset_names_end_of_file() {
        let file = SourceFile::new("t.adamas", "ab\ncd\n");
        assert_eq!(file.offset(Location::new(3, 1)), Some(6));
        assert_eq!(file.offset(Location::new(3, 2)), None);
        assert_eq!(file.offset(Location::new(4, 1)), None);
    }

    #[test]
    fn span_merge_covers_both() {
        let merged = Span::new(10, 12).merge(Span::new(3, 5));
        assert_eq!(merged, Span::new(3, 12));
    }

    proptest! {
        /// Ключевое свойство: перевод смещения в позицию и обратно не теряет
        /// информации. Ломается — ломается вся привязка диагностики к тексту.
        #[test]
        fn location_offset_round_trip(text in "(?s).{0,200}") {
            let file = SourceFile::new("prop.adamas", text.clone());
            for offset in 0..=text.len() {
                if !text.is_char_boundary(offset) {
                    continue;
                }
                let location = file.location(offset).expect("boundary offset resolves");
                prop_assert_eq!(file.offset(location), Some(offset));
            }
        }

        /// Обратное направление: разные позиции не могут указывать на одно
        /// смещение. Без этого колонка за концом строки тихо становится
        /// вторым именем для `1:1` следующей.
        #[test]
        fn offset_location_round_trip(text in "(?s).{0,200}") {
            let file = SourceFile::new("prop.adamas", text);
            for line in 1..=file.line_count() {
                // +3 к длине видимого текста строки: хватает, чтобы выйти за
                // терминатор и за точку вставки, какими бы они ни были.
                let width = file.line_text(line).map_or(0, |text| text.chars().count());
                for column in 1..=width + 3 {
                    let location = Location::new(line, column);
                    if let Some(offset) = file.offset(location) {
                        prop_assert_eq!(file.location(offset), Some(location));
                    }
                }
            }
        }

        /// Спан, собранный из двух других, покрывает оба.
        #[test]
        fn merge_is_a_cover(a in 0usize..1000, b in 0usize..1000, c in 0usize..1000, d in 0usize..1000) {
            let left = Span::new(a.min(b), a.max(b));
            let right = Span::new(c.min(d), c.max(d));
            let merged = left.merge(right);
            prop_assert!(merged.start() <= left.start() && merged.start() <= right.start());
            prop_assert!(merged.end() >= left.end() && merged.end() >= right.end());
        }
    }
}
