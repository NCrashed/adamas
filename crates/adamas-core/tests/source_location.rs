//! Разрешение позиций в многострочном исходнике.
//!
//! Проверяет цепочку `Span -> Location -> строка текста` в том виде, в каком
//! её увидит рендерер диагностики.

use std::fmt::Write as _;

use adamas_core::source::{Location, SourceFile, Span};

const SAMPLE: &str = "id : (0 a : Type) -> a -> a\nid x = x\n\nλ-строка с юникодом\n";

fn show(location: Option<Location>) -> String {
    location.map_or_else(|| "?".to_owned(), |l| l.to_string())
}

fn render(file: &SourceFile, spans: &[Span]) -> String {
    // Запись в String инфаллибельна.
    let mut out = String::new();
    let _ = writeln!(
        out,
        "file: {} ({} bytes, {} lines)",
        file.name(),
        file.len(),
        file.line_count()
    );
    for span in spans {
        let _ = writeln!(
            out,
            "[{}..{}] {} -> {} {:?}",
            span.start(),
            span.end(),
            show(file.location(span.start())),
            show(file.location(span.end())),
            file.snippet(*span),
        );
    }
    for line in 1..=file.line_count() {
        let _ = writeln!(out, "line {line}: {:?}", file.line_text(line));
    }
    out
}

#[test]
fn multiline_rendering() {
    let file = SourceFile::new("sample.adamas", SAMPLE);
    let unicode_line = file.text().find('λ').expect("sample contains λ");
    let spans = [
        Span::new(0, 2),
        Span::new(5, 17),
        Span::new(28, 36),
        // Спан целиком на строке с многобайтовыми символами.
        Span::new(unicode_line, unicode_line + "λ-строка".len()),
        // Спан, режущий λ пополам: обе координаты и фрагмент должны быть None.
        Span::new(unicode_line, unicode_line + 1),
        // Позиция end-of-file.
        Span::at(file.len()),
    ];
    insta::assert_snapshot!(render(&file, &spans));
}
