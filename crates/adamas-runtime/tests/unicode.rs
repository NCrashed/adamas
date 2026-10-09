//! Таблицы Юникода рантайма (`c/unicode.c`) порождены из стандартной
//! библиотеки Rust и сверяются с ней здесь (§4.4).
//!
//! Функции символа - `charClass`, `charToUpper`, `charToLower` - машина
//! считает через `char` Rust (`adamas_core::prim::char_class`), а собранная
//! программа - по этим таблицам. Договор трёх вычислителей требует одного
//! ответа, то есть одной версии Юникода: файл обязан быть ровно тем, что
//! порождает этот тест. Разошёлся - тест красный; переписать файл:
//!
//! ```sh
//! ADAMAS_REGENERATE=1 cargo test -p adamas-runtime --test unicode
//! ```

use std::fmt::Write as _;
use std::path::PathBuf;

/// Отрезки кодов, на которых свойство истинно.
fn ranges(holds: impl Fn(char) -> bool) -> Vec<(u32, u32)> {
    let mut found: Vec<(u32, u32)> = Vec::new();
    for code in 0..=0x10_FFFF_u32 {
        let Some(symbol) = char::from_u32(code) else {
            continue;
        };
        if !holds(symbol) {
            continue;
        }
        match found.last_mut() {
            Some((_, hi)) if *hi + 1 == code => *hi = code,
            _ => found.push((code, code)),
        }
    }
    found
}

/// Пары «символ - его простое отображение», где оно не он сам.
fn mapping<I: Iterator<Item = char>>(map: impl Fn(char) -> I) -> Vec<(u32, u32)> {
    (0..=0x10_FFFF_u32)
        .filter_map(char::from_u32)
        .filter_map(|symbol| {
            let mapped = adamas_core::prim::simple(symbol, map(symbol));
            (mapped != u32::from(symbol)).then_some((u32::from(symbol), mapped))
        })
        .collect()
}

fn table(out: &mut String, name: &str, rows: &[(u32, u32)]) {
    let _ = writeln!(
        out,
        "static const adamas_unicode_pair {name}[{}] = {{",
        rows.len()
    );
    for chunk in rows.chunks(4) {
        out.push_str("   ");
        for (lo, hi) in chunk {
            let _ = write!(out, " {{0x{lo:X}u, 0x{hi:X}u}},");
        }
        out.push('\n');
    }
    out.push_str("};\n\n");
}

/// Весь текст `c/unicode.c`.
fn generated() -> String {
    let mut out = String::from(HEAD);
    table(&mut out, "ALPHA", &ranges(char::is_alphabetic));
    table(&mut out, "SPACE", &ranges(char::is_whitespace));
    table(&mut out, "UPPER", &ranges(char::is_uppercase));
    table(&mut out, "LOWER", &ranges(char::is_lowercase));
    table(&mut out, "NUMBER", &ranges(char::is_numeric));
    table(&mut out, "TO_UPPER", &mapping(char::to_uppercase));
    table(&mut out, "TO_LOWER", &mapping(char::to_lowercase));
    out.push_str(TAIL);
    out
}

const HEAD: &str = "\
/* Функции символа (§4.4): свойства Юникода и простое отображение регистра.
 *
 * ФАЙЛ ПОРОЖДЁН `crates/adamas-runtime/tests/unicode.rs` из стандартной
 * библиотеки Rust - той же, которой считает машина (`adamas_core::prim::
 * char_class`). Править руками нечего: правится генератор, и тест сверяет
 * файл с ним.
 */

#include \"adamas.h\"

#include <stddef.h>

/* Отрезок кодов `[lo, hi]` либо пара «символ - отображение». */
typedef struct {
    uint32_t lo;
    uint32_t hi;
} adamas_unicode_pair;

";

const TAIL: &str = "\
/* Лежит ли код на одном из отрезков: двоичный поиск по возрастающим. */
static int within(const adamas_unicode_pair *table, size_t count, uint32_t code) {
    size_t low = 0;
    size_t high = count;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (code < table[middle].lo) {
            high = middle;
        } else if (code > table[middle].hi) {
            low = middle + 1;
        } else {
            return 1;
        }
    }
    return 0;
}

/* Отображение кода по таблице пар; нет пары - код сам. */
static uint32_t mapped(const adamas_unicode_pair *table, size_t count, uint32_t code) {
    size_t low = 0;
    size_t high = count;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (code < table[middle].lo) {
            high = middle;
        } else if (code > table[middle].lo) {
            low = middle + 1;
        } else {
            return table[middle].hi;
        }
    }
    return code;
}

#define ADAMAS_COUNT(table) (sizeof(table) / sizeof((table)[0]))

uint64_t adamas_char_op(uint64_t code, uint8_t op) {
    uint32_t symbol = (uint32_t)code;
    switch (op) {
    case ADAMAS_CHAR_UPPER:
        return mapped(TO_UPPER, ADAMAS_COUNT(TO_UPPER), symbol);
    case ADAMAS_CHAR_LOWER:
        return mapped(TO_LOWER, ADAMAS_COUNT(TO_LOWER), symbol);
    default: {
        uint64_t mask = 0;
        if (within(ALPHA, ADAMAS_COUNT(ALPHA), symbol)) {
            mask |= 1u;
        }
        if (within(SPACE, ADAMAS_COUNT(SPACE), symbol)) {
            mask |= 2u;
        }
        if (within(UPPER, ADAMAS_COUNT(UPPER), symbol)) {
            mask |= 4u;
        }
        if (within(LOWER, ADAMAS_COUNT(LOWER), symbol)) {
            mask |= 8u;
        }
        if (within(NUMBER, ADAMAS_COUNT(NUMBER), symbol)) {
            mask |= 16u;
        }
        return mask;
    }
    }
}
";

#[test]
fn the_unicode_tables_are_what_rust_says() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("c/unicode.c");
    let expected = generated();
    if std::env::var_os("ADAMAS_REGENERATE").is_some() {
        std::fs::write(&path, &expected).expect("файл таблиц обязан записываться");
        return;
    }
    let found = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        found == expected,
        "`c/unicode.c` разошёлся со стандартной библиотекой Rust - перепишите: \
         ADAMAS_REGENERATE=1 cargo test -p adamas-runtime --test unicode"
    );
}

/// Маска рантайма и маска машины - одни и те же биты.
#[test]
fn the_mask_bits_are_the_cores() {
    use adamas_core::prim::{CHAR_ALPHA, CHAR_LOWER, CHAR_NUMBER, CHAR_SPACE, CHAR_UPPER};
    assert_eq!(
        (CHAR_ALPHA, CHAR_SPACE, CHAR_UPPER, CHAR_LOWER, CHAR_NUMBER),
        (1, 2, 4, 8, 16)
    );
}
