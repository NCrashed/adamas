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

/// Исходник вставки RC целиком.
const PERCEUS: &str = include_str!("../src/perceus.rs");

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

/// Вставка RC живёт по ту же сторону шва, что и представление.
///
/// Требование Фазы 7 прямое: LLVM-бэкенд обязан получить RC **вставленным**.
/// Читай этот проход термы ядра - и вставлять пришлось бы дважды, каждому
/// эмиттеру заново.
#[test]
fn the_reference_counting_pass_does_not_read_core_terms() {
    for forbidden in ["adamas_core::term", "adamas_core::sig", "Term", "Signature"] {
        assert!(
            !PERCEUS.contains(forbidden),
            "вставка RC упоминает `{forbidden}`: она по ту сторону шва"
        );
    }
}

/// Эмиттер RC не изобретает: он печатает узлы, а не решает, где считать.
///
/// Различить это чтением исходника всё-таки можно. Всякий вызов счётчика в
/// эмиттере стоит либо на **связывании IR** (`v{…}` - значит его назвал узел),
/// либо на **слоте замыкания** (`adamas_closure_get(self, …)` - трамплин, то
/// есть C-ABI, которого в IR нет вовсе). Третьего места быть не должно: оно
/// означало бы собственное мнение эмиттера о владении, и LLVM-эмиттер Фазы 7
/// остался бы без него.
///
/// Граница у теста та же, что у соседей: он видит текст. Обойти его можно,
/// собрав имя по кускам, - но не случайно.
#[test]
fn the_c_emitter_does_not_invent_reference_counting() {
    let counting = [
        "adamas_dup(",
        "adamas_drop_value(",
        "adamas_reclaim_value(",
        "adamas_reuse(",
    ];
    for line in EMITTER.lines() {
        for called in counting {
            assert!(
                !line.contains(called)
                    || line.contains("(v{")
                    || line.contains("adamas_closure_get(self"),
                "`{called}` в эмиттере не на узле и не на слоте замыкания: {}",
                line.trim()
            );
        }
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

/// RC - узлы представления, а не приём печати.
#[test]
fn the_representation_carries_the_reference_counting() {
    for required in ["Dup {", "Drop {", "Reclaim {", "reuse:"] {
        assert!(
            REPRESENTATION.contains(required),
            "у представления нет `{required}`: Фаза 7 получила бы понижение без RC"
        );
    }
}
