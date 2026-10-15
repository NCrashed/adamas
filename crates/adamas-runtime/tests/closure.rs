//! Замыкание: среда, частичное применение, голый указатель на код (§5.3).
//!
//! Применение замыкание **потребляет** (`adamas.h`, волна 8 Фазы 9): код
//! получает его владением и отпускает, прочитав среду; частичное применение
//! уникального дописывает аргумент на месте, разделённого - копирует.

#![allow(unsafe_code)]

use std::ptr;

use adamas_runtime::ffi::{
    Evidence, Kont, TAG_CLOSURE, Value, adamas_alloc, adamas_apply, adamas_closure,
    adamas_closure_code, adamas_closure_get, adamas_closure_missing, adamas_closure_release,
    adamas_closure_set, adamas_closure_slot_counted, adamas_closure_taken, adamas_drop, adamas_dup,
    adamas_field, adamas_imm, adamas_imm_get, adamas_rc, adamas_set_field, adamas_stat_live,
    adamas_stat_reset, adamas_tag,
};

/// Трёхместная функция с одним захватом. Разряды разные, поэтому перепутанный
/// порядок аргументов виден в ответе. Замыкание приходит владением и
/// отпускается здесь же, как его отпускает порождённый трамплин.
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
        adamas_drop(closure, Some(adamas_closure_release));
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
        let closure = adamas_closure(Some(digits), Some(release_capture), 3, 1, 1);
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

/// Уникальное замыкание дописывается на месте: копия была бы выдачей ради
/// выброса. Насыщенное уходит коду и отпускается им - дропать после нечего.
#[test]
fn a_unique_closure_collects_the_arguments_in_place() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let held = adamas_closure_get(first, 0);

        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        assert_eq!(second, first, "уникальное замыкание скопировано");
        assert_eq!(adamas_closure_missing(second), 2);
        assert_eq!(adamas_rc(held), 0, "захват не разделён - копии не было");
        // Среда впереди, накопленные аргументы за ней.
        assert_eq!(adamas_closure_get(second, 0), held);
        assert_eq!(adamas_imm_get(adamas_closure_get(second, 1)), 1);

        let third = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        assert_eq!(adamas_tag(third), TAG_CLOSURE);
        assert_eq!(adamas_closure_missing(third), 1);

        let answer = adamas_apply(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        assert_eq!(adamas_imm_get(answer), 7 + 10 + 200 + 3000);
        assert_eq!(adamas_stat_live(), 0, "насыщенное замыкание не отпущено");
    }
}

/// Разделённое замыкание копируется: дописать на месте значило бы изменить
/// его у соседа. Своя ссылка при этом отдаётся.
#[test]
fn a_shared_closure_is_copied() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let held = adamas_closure_get(first, 0);
        adamas_dup(first);

        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        assert_ne!(second, first, "разделённое замыкание дописано на месте");
        assert_eq!(adamas_rc(first), 0, "своя ссылка на исходное не отдана");
        assert_eq!(adamas_rc(held), 1, "захват копии не дупнут");
        assert_eq!(adamas_closure_missing(first), 3, "исходное тронуто");

        let third = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        let answer = adamas_apply(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        assert_eq!(adamas_imm_get(answer), 7 + 10 + 200 + 3000);

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
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Частично применённое замыкание применяется дальше дважды: разделённое,
/// оно копируется на каждом применении и остаётся целым.
#[test]
fn a_partially_applied_closure_stays_reusable() {
    unsafe {
        adamas_stat_reset();
        let first = digits_closure(7);
        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));

        adamas_dup(second);
        let left = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(2));
        let right = adamas_apply(second, ptr::null(), ptr::null_mut(), adamas_imm(4));
        let one = adamas_apply(left, ptr::null(), ptr::null_mut(), adamas_imm(3));
        let other = adamas_apply(right, ptr::null(), ptr::null_mut(), adamas_imm(3));

        assert_eq!(adamas_imm_get(one), 7 + 10 + 200 + 3000);
        assert_eq!(adamas_imm_get(other), 7 + 10 + 400 + 3000);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Плоский слот среды: биты лежат в нём сами, и `dup` по ним не идёт.
///
/// Среда здесь разнородна - счётный слот и плоский, - и порядок «счётные
/// первыми» есть соглашение с порождённым кодом (`adamas.h`). Проверяется то,
/// на чём стоит вся раскладка: копия при частичном применении дупает **только**
/// счётный слот, а биты переносит как есть. Копия бывает только у разделённого
/// замыкания, поэтому исходное дупнуто.
///
/// Биты взяты **чётные** нарочно: у нечётного младший бит совпадает с признаком
/// непосредственного, и `adamas_dup` по нему не делает ничего - мутант «дупать
/// всё занятое» выжил бы. На чётном он правит заголовок по адресу числа.
#[test]
fn a_flat_slot_is_not_counted() {
    unsafe {
        adamas_stat_reset();
        let held = adamas_alloc(0, 1);
        adamas_set_field(held, 0, adamas_imm(7));
        // Два слота среды: счётный и плоский. Арность три, поэтому применение
        // копит аргументы, а не бежит.
        let first = adamas_closure(Some(digits), Some(release_capture), 3, 2, 1);
        adamas_closure_set(first, 0, held);
        adamas_closure_set(first, 1, 10_usize as Value);

        assert_ne!(adamas_closure_slot_counted(first, 0), 0, "среда: счётный");
        assert_eq!(adamas_closure_slot_counted(first, 1), 0, "среда: плоский");
        // Накопленные аргументы счётны все: позиция аргумента боксирует.
        assert_ne!(
            adamas_closure_slot_counted(first, 2),
            0,
            "накопленный аргумент обязан считаться"
        );

        adamas_dup(first);
        let second = adamas_apply(first, ptr::null(), ptr::null_mut(), adamas_imm(1));
        assert_eq!(adamas_rc(held), 1, "счётный слот копия обязана дупнуть");
        assert_eq!(
            adamas_closure_get(second, 1),
            10_usize as Value,
            "плоский слот копия обязана перенести как есть"
        );
        assert_eq!(adamas_closure_taken(second), 3);

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
        // же, что применение. Оба потребляют замыкание - отсюда `dup`.
        adamas_dup(third);
        let code = adamas_closure_code(third).expect("замыкание без кода не бывает");
        let direct = code(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        let applied = adamas_apply(third, ptr::null(), ptr::null_mut(), adamas_imm(3));
        assert_eq!(adamas_imm_get(direct), adamas_imm_get(applied));
        assert_eq!(adamas_stat_live(), 0);
    }
}
