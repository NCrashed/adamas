//! Заголовок объекта: счётчик, уникальность, непосредственные, переиспользование.

// Рантайм и есть тот случай, ради которого `unsafe_code` объявлен `deny`.
#![allow(unsafe_code)]

use std::cell::Cell;

use adamas_runtime::ffi::{
    Value, adamas_alloc, adamas_con0, adamas_drop, adamas_drop_reuse, adamas_dup, adamas_field,
    adamas_imm, adamas_imm_get, adamas_is_imm, adamas_is_unique, adamas_rc, adamas_reuse,
    adamas_set_field, adamas_stat_allocated, adamas_stat_live, adamas_stat_reset, adamas_tag,
    adamas_unit,
};

thread_local! {
    /// Сколько раз позвали дроп детей.
    static RELEASED: Cell<usize> = const { Cell::new(0) };
}

/// Объект с одним полем-числом.
unsafe fn boxed(number: isize) -> Value {
    unsafe {
        let value = adamas_alloc(0, 1);
        adamas_set_field(value, 0, adamas_imm(number));
        value
    }
}

/// Дроп детей: одно поле-объект.
unsafe extern "C" fn release_first(value: Value) {
    unsafe {
        RELEASED.with(|count| count.set(count.get() + 1));
        adamas_drop(adamas_field(value, 0), None);
    }
}

#[test]
fn counter_holds_the_extra_references() {
    unsafe {
        adamas_stat_reset();
        let value = boxed(1);
        // Свежий объект уникален: счётчик считает **лишние** ссылки.
        assert_eq!(adamas_rc(value), 0);
        adamas_dup(value);
        adamas_dup(value);
        adamas_dup(value);
        assert_eq!(adamas_rc(value), 3);
        adamas_drop(value, None);
        adamas_drop(value, None);
        adamas_drop(value, None);
        assert_eq!(adamas_rc(value), 0);
        assert_eq!(adamas_stat_live(), 1);
        adamas_drop(value, None);
        assert_eq!(adamas_stat_live(), 0);
        assert_eq!(adamas_stat_allocated(), 1);
    }
}

#[test]
fn a_block_is_aligned_enough_to_leave_the_tag_bit_free() {
    unsafe {
        adamas_stat_reset();
        // Выравнивание блока - то, что даёт `malloc`: на целях §8 16 байт.
        // Фаза 7 ставит по этому числу `align`, поэтому оно проверяется, а не
        // предполагается.
        for fields in 0..5 {
            let value = adamas_alloc(0, fields);
            let address = value as usize;
            assert_eq!(address % 16, 0, "блок не выровнен под `max_align_t`");
            // Восемь из шестнадцати - несущий инвариант: свободный младший бит
            // и есть то, чем непосредственное значение отличается от объекта.
            assert_eq!(adamas_is_imm(value), 0);
            adamas_drop(value, None);
        }
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn uniqueness_separates_the_shared_object() {
    unsafe {
        adamas_stat_reset();
        let value = boxed(1);
        assert!(adamas_is_unique(value) != 0);
        adamas_dup(value);
        assert_eq!(adamas_is_unique(value), 0);
        adamas_drop(value, None);
        assert!(adamas_is_unique(value) != 0);
        adamas_drop(value, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn immediate_value_needs_no_allocation() {
    unsafe {
        adamas_stat_reset();
        let number = adamas_imm(-42);
        assert!(adamas_is_imm(number) != 0);
        assert_eq!(adamas_imm_get(number), -42);

        let nullary = adamas_con0(7);
        assert!(adamas_is_imm(nullary) != 0);
        // Тег читается той же функцией, что у объекта, - ради этого нульарный
        // конструктор и сделан непосредственным.
        assert_eq!(adamas_tag(nullary), 7);
        assert_eq!(adamas_tag(adamas_unit()), 0);
        // Блока нет, переиспользовать нечего.
        assert_eq!(adamas_is_unique(nullary), 0);

        adamas_dup(nullary);
        adamas_drop(nullary, None);
        assert_eq!(adamas_stat_allocated(), 0);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn reuse_takes_the_block_of_a_unique_object() {
    unsafe {
        adamas_stat_reset();
        let value = boxed(1);
        let block = adamas_drop_reuse(value, None);
        // Блок отдан, а не освобождён: его перепишет конструктор.
        assert_eq!(block, value);
        assert_eq!(adamas_stat_live(), 1);

        let fresh = adamas_reuse(block, 5, 1);
        assert_eq!(fresh, value);
        assert_eq!(adamas_tag(fresh), 5);
        assert_eq!(adamas_rc(fresh), 0);
        adamas_set_field(fresh, 0, adamas_imm(2));
        assert_eq!(adamas_imm_get(adamas_field(fresh, 0)), 2);
        assert_eq!(adamas_stat_allocated(), 1);

        adamas_drop(fresh, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn reuse_of_a_shared_object_allocates_instead() {
    unsafe {
        adamas_stat_reset();
        let value = boxed(1);
        adamas_dup(value);
        let block = adamas_drop_reuse(value, None);
        assert!(block.is_null());
        assert_eq!(adamas_rc(value), 0);

        let fresh = adamas_reuse(block, 5, 1);
        assert_ne!(fresh, value);
        assert_eq!(adamas_stat_allocated(), 2);

        adamas_drop(fresh, None);
        adamas_drop(value, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn last_reference_drops_the_children() {
    unsafe {
        adamas_stat_reset();
        RELEASED.with(|count| count.set(0));

        let outer = adamas_alloc(1, 1);
        adamas_set_field(outer, 0, boxed(9));
        adamas_dup(outer);

        // Ссылка лишняя - детей не трогают.
        adamas_drop(outer, Some(release_first));
        assert_eq!(RELEASED.with(Cell::get), 0);
        assert_eq!(adamas_stat_live(), 2);

        adamas_drop(outer, Some(release_first));
        assert_eq!(RELEASED.with(Cell::get), 1);
        assert_eq!(adamas_stat_live(), 0);
    }
}
