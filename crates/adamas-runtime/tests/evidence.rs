//! Вектор evidence: доступ по позиции, поиск изнутри наружу, снятие маской.

#![allow(unsafe_code)]

use std::ptr;

use adamas_runtime::ffi::{
    Frame, Kont, LOOKUP_HANDLER, LOOKUP_MISSING, LOOKUP_SUPPRESSED, MARK_HANDLER,
    adamas_evidence_at, adamas_evidence_copy, adamas_evidence_count, adamas_evidence_drop,
    adamas_evidence_dup, adamas_evidence_empty, adamas_evidence_extend, adamas_evidence_label_at,
    adamas_evidence_lookup, adamas_evidence_mask, adamas_evidence_suppress, adamas_kont_init,
    adamas_kont_push, adamas_kont_run, adamas_stat_live, adamas_stat_reset, adamas_unit,
};

/// Поиск метки: вердикт и найденный кадр.
unsafe fn lookup(evidence: *const adamas_runtime::ffi::Evidence, label: u32) -> (i32, *mut Frame) {
    let mut handler: *mut Frame = ptr::null_mut();
    let verdict = unsafe { adamas_evidence_lookup(evidence, label, &raw mut handler) };
    (verdict, handler)
}

#[test]
fn search_goes_from_the_innermost_outwards() {
    unsafe {
        adamas_stat_reset();
        let mut kont = Kont {
            top: ptr::null_mut(),
        };
        adamas_kont_init(&raw mut kont);

        // Два хендлера одной метки и один чужой между ними.
        let empty = adamas_evidence_empty();
        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, empty);
        let first = adamas_evidence_extend(empty, 7, outer);
        let middle = adamas_kont_push(&raw mut kont, MARK_HANDLER, 9, None, None, 0, first);
        let second = adamas_evidence_extend(first, 9, middle);
        let inner = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, second);
        let third = adamas_evidence_extend(second, 7, inner);

        assert_eq!(adamas_evidence_count(third), 3);
        assert_eq!(lookup(third, 7), (LOOKUP_HANDLER, inner));
        assert_eq!(lookup(third, 9), (LOOKUP_HANDLER, middle));
        assert_eq!(lookup(third, 5).0, LOOKUP_MISSING);

        // Доступ без смещения: понижение знает позицию статически.
        assert_eq!(adamas_evidence_label_at(third, 0), 7);
        assert_eq!(adamas_evidence_at(third, 0), outer);
        assert_eq!(adamas_evidence_label_at(third, 2), 7);
        assert_eq!(adamas_evidence_at(third, 2), inner);

        adamas_evidence_drop(third);
        adamas_evidence_drop(second);
        adamas_evidence_drop(first);
        adamas_evidence_drop(empty);
        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn a_suppressed_entry_is_neither_missing_nor_live() {
    unsafe {
        adamas_stat_reset();
        let mut kont = Kont {
            top: ptr::null_mut(),
        };
        adamas_kont_init(&raw mut kont);

        // Две записи одной метки: внешняя жива, внутренняя ответ уже дала.
        let empty = adamas_evidence_empty();
        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, empty);
        let first = adamas_evidence_extend(empty, 7, outer);
        let inner = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, first);
        let second = adamas_evidence_extend(first, 7, inner);

        let closing = adamas_evidence_copy(second);
        adamas_evidence_suppress(closing, inner);

        // Подавление снимает **ответ**, а не запись: поиск останавливается на
        // ней и наружу не идёт. Снятая запись увела бы операцию к `outer` -
        // тот же дефект, что ревью 2026-09-05 нашло у машины.
        assert_eq!(lookup(closing, 7), (LOOKUP_SUPPRESSED, inner));
        // Маску подавленная гасит наравне с живой: снимается она сама, и
        // остаётся внешний.
        let past = adamas_evidence_mask(closing, 7);
        assert_eq!(lookup(past, 7), (LOOKUP_HANDLER, outer));
        adamas_evidence_drop(past);
        // Чужая запись не тронута, исходный вектор - тоже.
        assert_eq!(lookup(second, 7), (LOOKUP_HANDLER, inner));

        adamas_evidence_drop(closing);
        adamas_evidence_drop(second);
        adamas_evidence_drop(first);
        adamas_evidence_drop(empty);
        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Маска снимает **ближайшую** запись своей метки и только её.
///
/// Позиции проверяются поимённо, а не длиной: вектор с одной снятой записью и
/// вектор без последней записи одной длины, и различает их порядок. Родитель
/// обязан остаться нетронутым - под маской идёт вычисление, а вокруг неё живёт
/// тот же вектор, что и был.
#[test]
fn a_mask_takes_the_nearest_entry_of_its_label() {
    unsafe {
        adamas_stat_reset();
        let mut kont = Kont {
            top: ptr::null_mut(),
        };
        adamas_kont_init(&raw mut kont);

        // Три записи метки 7 и чужая между второй и третьей.
        let empty = adamas_evidence_empty();
        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, empty);
        let first = adamas_evidence_extend(empty, 7, outer);
        let middle = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, first);
        let second = adamas_evidence_extend(first, 7, middle);
        let alien = adamas_kont_push(&raw mut kont, MARK_HANDLER, 9, None, None, 0, second);
        let third = adamas_evidence_extend(second, 9, alien);
        let inner = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, third);
        let fourth = adamas_evidence_extend(third, 7, inner);

        let once = adamas_evidence_mask(fourth, 7);
        assert_eq!(adamas_evidence_count(once), 3);
        assert_eq!(lookup(once, 7), (LOOKUP_HANDLER, middle));
        // Чужая метка на месте: снимается запись **своей**, а не последняя.
        assert_eq!(lookup(once, 9), (LOOKUP_HANDLER, alien));
        assert_eq!(adamas_evidence_at(once, 2), alien);

        // Вложенные считаются по одной (§3.4).
        let twice = adamas_evidence_mask(once, 7);
        assert_eq!(lookup(twice, 7), (LOOKUP_HANDLER, outer));
        let thrice = adamas_evidence_mask(twice, 7);
        assert_eq!(lookup(thrice, 7).0, LOOKUP_MISSING);
        // Снимать нечего - копия родителя, и операция кончает тем же `MISSING`.
        let past = adamas_evidence_mask(thrice, 7);
        assert_eq!(adamas_evidence_count(past), adamas_evidence_count(thrice));
        assert_eq!(lookup(past, 9), (LOOKUP_HANDLER, alien));

        // Родитель не тронут.
        assert_eq!(adamas_evidence_count(fourth), 4);
        assert_eq!(lookup(fourth, 7), (LOOKUP_HANDLER, inner));

        for vector in [
            past, thrice, twice, once, fourth, third, second, first, empty,
        ] {
            adamas_evidence_drop(vector);
        }
        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn extension_copies_and_leaves_the_parent_alone() {
    unsafe {
        adamas_stat_reset();
        let empty = adamas_evidence_empty();
        let parent = adamas_evidence_extend(empty, 3, ptr::null_mut());
        let child = adamas_evidence_extend(parent, 4, ptr::null_mut());

        assert_eq!(adamas_evidence_count(empty), 0);
        assert_eq!(adamas_evidence_count(parent), 1);
        assert_eq!(adamas_evidence_count(child), 2);
        assert_eq!(adamas_evidence_label_at(child, 0), 3);
        assert_eq!(adamas_evidence_label_at(child, 1), 4);

        adamas_evidence_drop(child);
        adamas_evidence_drop(parent);
        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn vector_lives_by_the_same_counting_rule() {
    unsafe {
        adamas_stat_reset();
        let evidence = adamas_evidence_empty();
        adamas_evidence_dup(evidence);
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 1);
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}
