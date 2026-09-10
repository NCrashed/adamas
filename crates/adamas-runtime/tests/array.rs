//! Массив: укладка ячеек, владение и дроп (§4.11).
//!
//! Здесь проверяется то, чего не видит ответ программы. Понижение сверяется с
//! `adamas eval` значением, а значение одинаково у правильной укладки и у
//! укладки с чужим шагом: пишут и читают её одним и тем же выражением, и
//! ошибка сокращается. Измерено мутантом - `adamas_array_at`, считающий шаг
//! словом вместо ширины ячейки, проходил корпус понижения целиком, попутно
//! записывая мимо блока. Отсюда правило укладки стоит здесь, где адрес виден
//! числом.

// Рантайм и есть тот случай, ради которого `unsafe_code` объявлен `deny`.
#![allow(unsafe_code)]

use std::cell::Cell;
use std::ffi::c_void;

use adamas_runtime::ffi::{
    Value, adamas_array_alloc, adamas_array_at, adamas_array_count, adamas_array_fill,
    adamas_array_fill_flat, adamas_array_get, adamas_array_init, adamas_array_put,
    adamas_array_read, adamas_array_release, adamas_array_stride, adamas_array_take,
    adamas_array_writable, adamas_drop, adamas_dup, adamas_imm, adamas_is_unique,
    adamas_stat_allocated, adamas_stat_live, adamas_stat_reset,
};

thread_local! {
    /// Сколько раз позвали дроп ячейки.
    static RELEASED: Cell<usize> = const { Cell::new(0) };
}

/// Дроп ячейки: считает вызовы и ничего не делает.
unsafe extern "C" fn counting(_value: Value) {
    RELEASED.with(|count| count.set(count.get() + 1));
}

/// Дроп детей, каким его порождает понижение: массив дропает свои ячейки.
///
/// Все значения этих тестов - массивы (ячейка есть массив нулевой длины),
/// поэтому одной ветви довольно.
unsafe extern "C" fn releasing(value: Value) {
    RELEASED.with(|count| count.set(count.get() + 1));
    unsafe { adamas_array_release(value, Some(releasing)) }
}

/// Смещение нагрузки от начала блока - `adamas.h` называет его числом.
const PAYLOAD: usize = 24;

/// Ячейка `i` лежит по смещению `i * stride` от нагрузки, а нагрузка - от блока.
///
/// Это и есть «`n × size(a)` байт подряд» из §4.11, записанное адресом. Шаг
/// берётся **узкий**: у восьмибайтовой ячейки он совпадает с шириной слова, и
/// подмена одного другим была бы ненаблюдаема.
#[test]
fn a_flat_cell_lies_at_its_own_stride() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(4, 2);
        assert_eq!(adamas_array_count(array), 4);
        assert_eq!(adamas_array_stride(array), 2);
        let base = array.cast::<u8>();
        for index in 0..4usize {
            let cell = adamas_array_at(array, index).cast::<u8>();
            assert_eq!(
                cell as usize - base as usize,
                PAYLOAD + index * 2,
                "ячейка {index} лежит не по своему шагу"
            );
        }
        // Весь массив - один блок, сколько бы ячеек в нём ни было.
        assert_eq!(adamas_stat_allocated(), 1);
        adamas_drop(array, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Колонка `Array 3 Vec3` из §4.11: тридцать шесть байт данных, граница четыре.
///
/// Числа взяты у раздела дословно - «`Vec3` из трёх `Float32` - 12 байт при
/// выравнивании 4» - и здесь они **адреса**, а не ответ программы. Шаг стоит
/// отдельно от ширины слова нарочно: двенадцать не кратно восьми, и подмена
/// шага словом сдвинула бы вторую ячейку на четыре байта.
///
/// Поле внутри ячейки проверяется тем же способом: `z` второй ячейки обязано
/// лежать по смещению `12 + 8`, а не там, куда попало бы поле, занимающее
/// слово.
#[test]
fn a_column_of_vectors_takes_thirty_six_bytes() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(3, 12);
        assert_eq!(adamas_array_stride(array), 12);
        let base = array.cast::<u8>();
        let cell = |index: usize| adamas_array_at(array, index).cast::<u8>() as usize;
        assert_eq!(cell(0) - base as usize, PAYLOAD);
        assert_eq!(
            cell(1) - cell(0),
            12,
            "вторая ячейка стоит не через 12 байт"
        );
        assert_eq!(
            cell(2) - cell(0),
            24,
            "третья ячейка стоит не через 24 байта"
        );
        // Данных ровно `3 × 12`: конец последней ячейки - тридцать шестой байт.
        assert_eq!(cell(2) + 12 - cell(0), 36, "колонка занимает не 36 байт");
        // Граница четыре: начало нагрузки делится на неё, значит и всякая
        // ячейка - шаг кратен четырём.
        assert_eq!((cell(0)) % 4, 0, "нагрузка не выровнена по четырём байтам");
        // Поле `z` второй ячейки - двенадцать плюс восемь от начала данных.
        let written: f32 = 30.0;
        std::ptr::copy_nonoverlapping(
            std::ptr::from_ref(&written).cast::<u8>(),
            (cell(1) + 8) as *mut u8,
            4,
        );
        let read = std::ptr::read_unaligned((cell(0) + 12 + 8) as *const f32);
        assert!(
            (read - 30.0).abs() < f32::EPSILON,
            "поле `z` второй ячейки лежит не по смещению 20"
        );
        assert_eq!(adamas_stat_allocated(), 1, "колонка стоила не одного блока");
        adamas_drop(array, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Заполнение кладёт байты в каждую ячейку и не залезает в соседнюю.
#[test]
fn filling_writes_every_cell_and_only_it() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(3, 2);
        let bits: u16 = 0xBEEF;
        adamas_array_fill_flat(array, std::ptr::from_ref(&bits).cast::<c_void>());
        for index in 0..3usize {
            let cell = adamas_array_at(array, index).cast::<u16>();
            assert_eq!(*cell, 0xBEEF, "ячейка {index} не заполнена");
        }
        // Записанное в одну ячейку соседнюю не трогает: шаг ровно два байта.
        let written: u16 = 7;
        std::ptr::copy_nonoverlapping(
            std::ptr::from_ref(&written).cast::<u8>(),
            adamas_array_at(array, 1).cast::<u8>(),
            2,
        );
        assert_eq!(*adamas_array_at(array, 0).cast::<u16>(), 0xBEEF);
        assert_eq!(*adamas_array_at(array, 1).cast::<u16>(), 7);
        assert_eq!(*adamas_array_at(array, 2).cast::<u16>(), 0xBEEF);
        adamas_drop(array, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Чтение отдаёт байты и **потребляет** массив.
#[test]
fn reading_takes_the_array_with_it() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(2, 2);
        let bits: u16 = 5;
        adamas_array_fill_flat(array, std::ptr::from_ref(&bits).cast::<c_void>());
        let mut out: u16 = 0;
        adamas_array_read(
            array,
            1,
            std::ptr::from_mut(&mut out).cast::<c_void>(),
            None,
        );
        assert_eq!(out, 5);
        assert_eq!(adamas_stat_live(), 0, "чтение массив не отдало");
    }
}

/// Указательный массив: ссылка на ячейку, дроп вытесненного, дроп всех.
#[test]
fn a_pointer_array_counts_its_cells() {
    unsafe {
        adamas_stat_reset();
        RELEASED.with(|count| count.set(0));
        let array = adamas_array_alloc(3, 0);
        assert_eq!(adamas_array_stride(array), 0);
        let element = adamas_imm(1);
        adamas_array_fill(array, element, Some(counting));
        // Непосредственное значение счётчика не имеет, поэтому дроп его не
        // считается; проверяется, что ячейки заполнены все.
        for index in 0..3usize {
            assert_eq!(adamas_array_get(array, index), element);
        }
        // Перезапись дропает вытесненное.
        adamas_array_put(array, 1, adamas_imm(2), Some(counting));
        assert_eq!(adamas_array_get(array, 1), adamas_imm(2));
        adamas_drop(array, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Дроп массива дропает ячейки - и только у указательного.
#[test]
fn releasing_drops_the_cells_of_a_pointer_array() {
    unsafe {
        adamas_stat_reset();
        RELEASED.with(|count| count.set(0));
        let array = adamas_array_alloc(3, 0);
        for index in 0..3usize {
            adamas_array_init(array, index, adamas_array_alloc(0, 0));
        }
        assert_eq!(adamas_stat_live(), 4);
        adamas_array_release(array, Some(releasing));
        // Ячейки отданы все три, и блоков от них не осталось.
        assert_eq!(
            RELEASED.with(Cell::get),
            3,
            "дроп позван не по разу на ячейку"
        );
        assert_eq!(adamas_stat_live(), 1, "живым остался не только сам массив");

        // У плоского дропать нечего вовсе: заголовков у ячеек нет (§4.11).
        RELEASED.with(|count| count.set(0));
        let flat = adamas_array_alloc(3, 2);
        adamas_array_release(flat, Some(releasing));
        assert_eq!(RELEASED.with(Cell::get), 0);
        adamas_drop(flat, None);
        adamas_drop(array, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Уникальный массив переписывается по месту, разделённый копируется.
///
/// Свидетель дифференциальный: «тот же указатель» без соседнего случая
/// показывал бы лишь то, что копии не бывает никогда.
#[test]
fn a_unique_array_is_written_in_place() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(2, 2);
        assert_eq!(adamas_is_unique(array), 1);
        let same = adamas_array_writable(array, None);
        assert_eq!(same, array, "уникальный массив скопирован");
        assert_eq!(adamas_stat_allocated(), 1);

        adamas_dup(same);
        let copy = adamas_array_writable(same, None);
        assert_ne!(copy, same, "разделённый массив переписан по месту");
        assert_eq!(adamas_stat_allocated(), 2);
        adamas_drop(copy, None);
        adamas_drop(same, None);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Ячейка указательного массива приходит владением, а массив уходит.
#[test]
fn taking_a_cell_keeps_it_alive() {
    unsafe {
        adamas_stat_reset();
        let array = adamas_array_alloc(1, 0);
        let cell = adamas_array_alloc(0, 0);
        adamas_array_init(array, 0, cell);
        let taken = adamas_array_take(array, 0, Some(releasing));
        assert_eq!(taken, cell);
        // Массива больше нет, ячейка жива: дроп массива её ячейки отдал, а
        // взятая пережила его лишней ссылкой, которую взяло само чтение.
        assert_eq!(adamas_stat_live(), 1);
        adamas_drop(taken, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}
