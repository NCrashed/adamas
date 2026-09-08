//! Вектор evidence: доступ по позиции, поиск изнутри наружу, счёт масок.

#![allow(unsafe_code)]

use std::ptr;

use adamas_runtime::ffi::{
    Kont, MARK_HANDLER, adamas_evidence_at, adamas_evidence_count, adamas_evidence_drop,
    adamas_evidence_dup, adamas_evidence_empty, adamas_evidence_extend, adamas_evidence_find,
    adamas_evidence_label_at, adamas_kont_init, adamas_kont_push, adamas_kont_run,
    adamas_stat_live, adamas_stat_reset, adamas_unit,
};

#[test]
fn search_goes_from_the_innermost_outwards() {
    unsafe {
        adamas_stat_reset();
        let mut kont = Kont {
            top: ptr::null_mut(),
            depth: 0,
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
        assert_eq!(adamas_evidence_find(third, 7, 0), inner);
        assert_eq!(adamas_evidence_find(third, 9, 0), middle);
        // Маска пропускает один подходящий хендлер (§3.4, §10 вопрос 72).
        assert_eq!(adamas_evidence_find(third, 7, 1), outer);
        assert!(adamas_evidence_find(third, 7, 2).is_null());
        assert!(adamas_evidence_find(third, 5, 0).is_null());

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
