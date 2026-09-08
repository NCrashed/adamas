//! Шов между ядром и эмиттером проверяется, а не обещается.
//!
//! Требование Фазы 7 (`docs/phase7-plan.md`, «Промежуточное представление
//! обязано нести факты уникальности») даёт ему проверяемую форму: если эмиттер
//! тянется к термам ядра, шва нет. Здесь исходник эмиттера читается и
//! спрашивается на упоминание ядра.
//!
//! Тест текстовый, и это его граница: он видит имена, а не зависимости. Обойти
//! его можно - но не случайно, а только дописав слой пересылки, и такой слой
//! виден в ревью.

/// Исходник эмиттера целиком.
const EMITTER: &str = include_str!("../src/emit_c.rs");

/// Исходник представления целиком.
const REPRESENTATION: &str = include_str!("../src/ir.rs");

/// Исходник печати целиком.
const PRINTER: &str = include_str!("../src/print.c");

/// Эмиттер C не читает термов ядра.
#[test]
fn the_c_emitter_does_not_read_core_terms() {
    for forbidden in ["adamas_core::term", "adamas_core::sig", "Term", "Signature"] {
        assert!(
            !EMITTER.contains(forbidden),
            "эмиттер упоминает `{forbidden}`: шва между ядром и текстом C нет"
        );
    }
}

/// Представление не читает термов ядра тоже: факты приходят от понижения.
#[test]
fn the_representation_does_not_read_core_terms() {
    for forbidden in ["adamas_core::term", "adamas_core::sig", "Term", "Signature"] {
        assert!(
            !REPRESENTATION.contains(forbidden),
            "представление упоминает `{forbidden}`: оно копия ядра, а не шов"
        );
    }
}

/// Срез печати у обоих вычислителей один.
///
/// Число живёт в `print.c`, а не тянется из ядра: тянуться значило бы дать
/// эмиттеру читать ядро, чего шов и не даёт. Ценой второй записи числа - и
/// цена оплачена здесь. Тест не заменяет свидетеля на глубоком ответе
/// (`agreement.rs`), а называет расхождение своим именем: там оно вылезет
/// разошедшимися строками, здесь - разошедшимся числом.
#[test]
fn both_printers_cut_at_the_same_depth() {
    let written = format!(
        "#define ADAMAS_PRINT_DEPTH {}L",
        adamas_core::term::PRINT_DEPTH
    );
    assert!(
        PRINTER.contains(&written),
        "печать понижения режет не на `{}`: договор с `adamas eval` держится глубиной",
        adamas_core::term::PRINT_DEPTH
    );
}

/// Кратность до эмиттера доезжает: факты - не украшение документации.
#[test]
fn the_representation_carries_the_facts() {
    for required in ["mult", "unique", "region", "present"] {
        assert!(
            REPRESENTATION.contains(required),
            "у представления нет поля `{required}`: Фазе 7 нечего будет прочитать"
        );
    }
}
