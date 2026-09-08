//! Замыкание: среда, частичное применение, голый указатель на код (§5.3).

#![allow(unsafe_code)]

use std::ptr;

use adamas_runtime::ffi::{
    Evidence, Kont, TAG_CLOSURE, Value, adamas_alloc, adamas_apply, adamas_closure,
    adamas_closure_code, adamas_closure_get, adamas_closure_missing, adamas_closure_release,
    adamas_closure_set, adamas_closure_taken, adamas_drop, adamas_field, adamas_imm,
    adamas_imm_get, adamas_rc, adamas_set_field, adamas_stat_live, adamas_stat_reset, adamas_tag,
};

/// Трёхместная функция с одним захватом. Разряды разные, поэтому перепутанный
/// порядок аргументов виден в ответе.
unsafe extern "C" fn digits(
    closure: Value,
    _evidence: *const Evidence,
    _kont: *mut Kont,
    last: Value,
) -> Value {
    unsafe {
        let captured = adamas_imm_get(adamas_field(adamas_closure_get(closure, 0), 0));
        let first = adamas_imm_get(adamas_closure_get(closure, 1));
        let second = adamas_imm_get(adamas_closure_get(closure, 2));
        adamas_imm(captured + first * 10 + second * 100 + adamas_imm_get(last) * 1000)
    }
}

/// Дроп среды: захват лежит в слоте 0, накопленные аргументы непосредственны.
unsafe extern "C" fn release_capture(closure: Value) {
    unsafe {
        adamas_drop(adamas_closure_get(closure, 0), None);
    }
}

/// Замыкание `digits` с захваченным числом в объекте.
unsafe fn digits_closure(captured: isize) -> Value {
    unsafe {
        let held = adamas_alloc(0, 1);
        adamas_set_field(held, 0, adamas_imm(captured));
        let closure = adamas_closure(Some(digits), Some(release_capture), 3, 1);
        adamas_closure_set(closure, 0, held);
        closure
    }
}

#[test]
fn closure_is_an_object_with_a_header() {
    unsafe {
        adamas_stat_reset();
        let closure = digits_closure(7);
        assert_eq!(adamas_tag(closure), TAG_CLOSURE);
        assert_eq!(adamas_rc(closure), 0);
        assert_eq!(adamas_closure_missing(closure), 3);
        adamas_drop(closure, Some(adamas_closure_release));
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn partial_application_collects_the_arguments_in_order() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let held = adamas_closure_get(first, 0);

        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        // Накопление копирует замыкание: исходное могло быть разделено.
        assert_ne!(second, first);
        assert_eq!(adamas_closure_missing(second), 2);
        // Захват стал общим у двух замыканий - отсюда лишняя ссылка.
        assert_eq!(adamas_rc(held), 1);
        // Среда впереди, накопленные аргументы за ней.
        assert_eq!(adamas_closure_get(second, 0), held);
        assert_eq!(adamas_imm_get(adamas_closure_get(second, 1)), 1);

        let third = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        // Аргументов всё ещё не хватает - ответ снова замыкание, а не значение.
        assert_eq!(adamas_tag(third), TAG_CLOSURE);
        assert_eq!(adamas_closure_missing(third), 1);
        assert_eq!(adamas_rc(held), 2);

        let answer = adamas_apply(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        assert_eq!(adamas_imm_get(answer), 7 + 10 + 200 + 3000);

        adamas_drop(third, Some(adamas_closure_release));
        adamas_drop(second, Some(adamas_closure_release));
        adamas_drop(first, Some(adamas_closure_release));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Занятых слотов ровно столько, сколько дропать порождённому release'у.
///
/// Число это ему негде взять, кроме как здесь: `applied` растёт с каждым
/// частичным применением, а указатель на release остаётся тот же (`adamas.h`,
/// «Замыкание»). Свидетель - **рост**: у трёхместного замыкания с одним
/// захватом занято 1, 2, 3 слота подряд.
#[test]
fn taken_slots_grow_with_partial_application() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        assert_eq!(adamas_closure_taken(first), 1, "среда без аргументов");

        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        assert_eq!(adamas_closure_taken(second), 2);
        let third = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        assert_eq!(adamas_closure_taken(third), 3);

        adamas_drop(third, Some(adamas_closure_release));
        adamas_drop(second, Some(adamas_closure_release));
        adamas_drop(first, Some(adamas_closure_release));
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn a_partially_applied_closure_stays_reusable() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));

        let left = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        let right = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(4));
        let one = adamas_apply(left, ptr::null(), ptr::null_mut(), adamas_imm(3));
        let other = adamas_apply(right, ptr::null(), ptr::null_mut(), adamas_imm(3));

        assert_eq!(adamas_imm_get(one), 7 + 10 + 200 + 3000);
        assert_eq!(adamas_imm_get(other), 7 + 10 + 400 + 3000);

        adamas_drop(right, Some(adamas_closure_release));
        adamas_drop(left, Some(adamas_closure_release));
        adamas_drop(second, Some(adamas_closure_release));
        adamas_drop(first, Some(adamas_closure_release));
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn code_pointer_takes_the_closure_as_userdata() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        let third = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));

        // §5.3: замыкание со средой отдаётся трамплином плюс `userdata`, и
        // `userdata` тут - оно само. Вызов через голый указатель обязан дать то
        // же, что применение.
        let code = adamas_closure_code(third).expect("замыкание без кода не бывает");
        let direct = code(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        let applied = adamas_apply(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        assert_eq!(adamas_imm_get(direct), adamas_imm_get(applied));

        adamas_drop(third, Some(adamas_closure_release));
        adamas_drop(second, Some(adamas_closure_release));
        adamas_drop(first, Some(adamas_closure_release));
        assert_eq!(adamas_stat_live(), 0);
    }
}
