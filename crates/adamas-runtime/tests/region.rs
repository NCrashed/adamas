//! Регион: раскладка области, владение и дроп (§3.6).
//!
//! Здесь проверяется то, чего не видит ответ программы. Понижение сверяется с
//! `adamas eval` значением, а значение сходится и у смещения, посчитанного по
//! укладке, и у смещения, посчитанного как «номер аллокации умножить на
//! слово»: пишут и читают его одним выражением, и ошибка сокращается. Различает
//! их только **адрес**, и здесь он виден числом - тот же довод, каким
//! `tests/array.rs` завёлся у массива.

// Рантайм и есть тот случай, ради которого `unsafe_code` объявлен `deny`.
#![allow(unsafe_code)]

use std::ffi::c_void;

use adamas_runtime::ffi::{
    Value, adamas_drop, adamas_dup, adamas_is_unique, adamas_region_alloc, adamas_region_last,
    adamas_region_new, adamas_region_pop, adamas_region_read, adamas_region_recycle,
    adamas_region_release, adamas_region_used, adamas_region_write, adamas_stat_live,
    adamas_stat_reset,
};

/// Дроп нагрузки области - тот, что порождает понижение: делать нечего.
unsafe extern "C" fn releasing(_value: Value) {}

/// Кладёт значение и отдаёт область вместе с его хендлом.
unsafe fn placed<T: Copy>(region: Value, value: T) -> (Value, usize) {
    let made = unsafe {
        adamas_region_alloc(
            region,
            std::ptr::from_ref(&value).cast::<c_void>(),
            size_of::<T>(),
            align_of::<T>(),
        )
    };
    // Хендл спрашивается у **той же** области: `adamas_region_last` берёт её
    // владением, поэтому лишняя ссылка берётся здесь и отдаётся ей.
    let at = unsafe { adamas_region_last(adamas_dup(made), Some(releasing)) };
    (made, at)
}

/// Читает значение по хендлу, не потребляя область.
unsafe fn fetched<T: Copy + Default>(region: Value, at: usize) -> T {
    let mut out = T::default();
    unsafe {
        adamas_region_read(
            adamas_dup(region),
            at,
            std::ptr::from_mut(&mut out).cast::<c_void>(),
            size_of::<T>(),
            Some(releasing),
        );
    }
    out
}

/// Нагрузка разной ширины ложится подряд, каждая по своей границе.
///
/// Числа - те же, что считает типовая сторона (`adamas-elab/src/flat.rs`) и
/// машина (`adamas-core/src/eval.rs`). Три счёта одного смещения обязаны
/// сойтись; разойдись они, хендл повёл бы не туда, а **ответ программы этого не
/// показал бы**: пишут и читают смещение одним выражением, и ошибка
/// сокращается.
///
/// Порядок нагрузок выбран так, чтобы граница была наблюдаема. `Float32`
/// **первым**: после него занято четыре байта, а `Int64` требует восьми, и
/// между ними встаёт заполнитель. Возьми порядок обратный - подъём до границы
/// не сработал бы ни разу, и правило осталось бы без свидетеля.
#[test]
fn payloads_lie_end_to_end_by_their_own_bounds() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, first) = placed(region, 0.25f32);
        assert_eq!(first, 0, "первая аллокация начинается с нуля");
        assert_eq!(adamas_region_used(region), 4);

        let (region, second) = placed(region, 20i64);
        assert_eq!(
            second, 8,
            "восьмибайтовое встаёт по восьми, а не по четырём"
        );
        assert_eq!(adamas_region_used(region), 16);

        let (region, third) = placed(region, [1.0f32, 2.0, 3.0]);
        assert_eq!(third, 16, "агрегат встаёт по своей границе - четыре");
        assert_eq!(
            adamas_region_used(region),
            28,
            "три значения плюс заполнитель занимают 28 байт области"
        );

        assert_eq!(fetched::<f32>(region, first).to_bits(), 0.25f32.to_bits());
        assert_eq!(fetched::<i64>(region, second), 20);
        let read = fetched::<[f32; 3]>(region, third);
        assert_eq!(read.map(f32::to_bits), [1.0f32, 2.0, 3.0].map(f32::to_bits));

        // Область - **один** блок на все три значения, и дроп её один.
        assert_eq!(adamas_stat_live(), 1);
        adamas_drop(region, Some(releasing));
        assert_eq!(adamas_stat_live(), 0, "дроп области освободил её целиком");
    }
}

/// Запись курсора не двигает: `write` §3.6 - операция над размещённым местом.
///
/// Без этого правила вторая запись отвела бы себе новые байты, и хендл,
/// взятый после неё, указывал бы уже не туда.
#[test]
fn a_write_does_not_move_the_cursor() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, at) = placed(region, 20i64);
        let (region, tail) = placed(region, 7i64);
        assert_eq!(adamas_region_used(region), 16);

        let value = 99i64;
        let region = adamas_region_write(
            region,
            at,
            std::ptr::from_ref(&value).cast::<c_void>(),
            size_of::<i64>(),
        );
        assert_eq!(
            adamas_region_used(region),
            16,
            "запись подняла курсор, а размещать ей нечего"
        );
        assert_eq!(fetched::<i64>(region, at), 99);
        assert_eq!(fetched::<i64>(region, tail), 7, "соседнее место не тронуто");

        adamas_drop(region, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Разделённая область копируется целиком - вместе с курсором.
///
/// Договор тот же, что у `adamas_array_writable` (§5.1): уникальность
/// спрашивается у рантайма (`rc == 0`). Копия обязана унести и `used`, иначе
/// хендлы прежних аллокаций указывали бы в ней не туда, - и это проверяется
/// чтением по старому хендлу из копии.
#[test]
fn a_shared_region_is_copied_whole() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, at) = placed(region, 20i64);
        assert_ne!(adamas_is_unique(region), 0);

        // Вторая ссылка делает область разделённой: запись обязана копировать.
        let shared = adamas_dup(region);
        assert_eq!(adamas_is_unique(region), 0);
        let value = 99i64;
        let copy = adamas_region_write(
            region,
            at,
            std::ptr::from_ref(&value).cast::<c_void>(),
            size_of::<i64>(),
        );
        assert_ne!(copy, shared, "разделённая область переписана по месту");
        assert_eq!(adamas_region_used(copy), 8, "копия унесла курсор");
        assert_eq!(fetched::<i64>(copy, at), 99);
        assert_eq!(fetched::<i64>(shared, at), 20, "прежняя область не тронута");

        adamas_drop(copy, Some(releasing));
        adamas_drop(shared, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
        adamas_region_release(adamas_region_new());
    }
}

/// Отданная ячейка достаётся равной по ширине, и курсор при этом стоит.
///
/// Курсор здесь и есть свидетель: **из языка он не виден**, программа видит
/// только хендл. Совпади хендл случайно - например, вернись `recycle` не той
/// ячейкой, а `alloc` тем же нулём просто потому, что область пуста, - число
/// `used` разошлось бы, а ответ нет.
#[test]
fn a_recycled_cell_is_taken_by_the_same_width() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, first) = placed(region, 20i64);
        assert_eq!(adamas_region_used(region), 8);

        let region = adamas_region_recycle(region, first);
        assert_eq!(
            adamas_region_used(region),
            8,
            "возврат ячейки курсора не двигает: занятое остаётся занятым"
        );

        let (region, again) = placed(region, 99i64);
        assert_eq!(again, first, "равная по ширине обязана лечь в отданную");
        assert_eq!(
            adamas_region_used(region),
            8,
            "переиспользование не поднимает курсор: новых байт области не нужно"
        );
        assert_eq!(fetched::<i64>(region, again), 99, "байты легли по хендлу");

        adamas_drop(region, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Узкая нагрузка отданной широкой ячейки не берёт (§3.6: «одинакового
/// размера»).
///
/// Проверяется не только адресом узкой, но и **байтами широкой**: ляг она в
/// чужую ячейку, прежние восемь байт были бы затёрты наполовину, и чтение по
/// старому хендлу это показало бы.
#[test]
fn a_narrow_payload_does_not_take_a_wide_cell() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, wide) = placed(region, 20i64);
        let region = adamas_region_recycle(region, wide);

        let (region, narrow) = placed(region, 0.25f32);
        assert_eq!(narrow, 8, "четыре байта встают за широкой, а не в неё");
        assert_eq!(adamas_region_used(region), 12);
        assert_eq!(
            fetched::<i64>(region, wide),
            20,
            "байты широкой ячейки не тронуты"
        );

        // Равная по ширине ту же ячейку берёт - иначе «одинакового размера»
        // читалось бы как «никогда».
        let (region, same) = placed(region, 7i64);
        assert_eq!(same, wide);
        assert_eq!(adamas_region_used(region), 12);

        adamas_drop(region, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Курсор опускается только с вершины: LIFO (§3.6).
///
/// Два возврата подряд, и они отличаются лишь тем, вершину ли называет хендл.
/// Число `used` показывает разницу прямо, не дожидаясь следующей аллокации.
#[test]
fn a_pop_lowers_the_cursor_only_from_the_top() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, bottom) = placed(region, 20i64);
        let (region, top) = placed(region, 7i64);
        assert_eq!((bottom, top), (0, 8));
        assert_eq!(adamas_region_used(region), 16);

        let region = adamas_region_pop(region, bottom);
        assert_eq!(
            adamas_region_used(region),
            16,
            "возврат не с вершины обязан быть пуст: под ним лежит живая ячейка"
        );

        let region = adamas_region_pop(region, top);
        assert_eq!(adamas_region_used(region), 8, "вершина отдана, курсор упал");
        assert_eq!(
            adamas_region_last(adamas_dup(region), Some(releasing)),
            bottom,
            "последней аллокацией стала предыдущая"
        );

        let (region, again) = placed(region, 99i64);
        assert_eq!(again, top, "следующая легла на место отданной вершины");

        adamas_drop(region, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Разделённая область уносит в копию и журнал, а не только нагрузку.
///
/// Из языка это не видно вовсе: обе ветви ответили бы одним хендлом и без
/// журнала - у пустой области первая аллокация тоже нулевая. Различает их
/// `used`: у копии с журналом свободная ячейка занимается **без** подъёма
/// курсора, у копии без журнала - с подъёмом.
#[test]
fn a_shared_region_copies_its_journal() {
    unsafe {
        adamas_stat_reset();
        let region = adamas_region_new();
        let (region, at) = placed(region, 20i64);
        let region = adamas_region_recycle(region, at);

        let shared = adamas_dup(region);
        assert_eq!(adamas_is_unique(region), 0);

        let value = 99i64;
        let copy = adamas_region_alloc(
            region,
            std::ptr::from_ref(&value).cast::<c_void>(),
            size_of::<i64>(),
            align_of::<i64>(),
        );
        assert_ne!(copy, shared, "разделённая область переписана по месту");
        assert_eq!(adamas_region_used(copy), 8, "копия унесла свободную ячейку");
        assert_eq!(fetched::<i64>(copy, at), 99);
        assert_eq!(fetched::<i64>(shared, at), 20, "прежняя область не тронута");

        // Журнал прежней тоже цел: её свободная ячейка на месте.
        let (shared, mine) = placed(shared, 7i64);
        assert_eq!(mine, at);
        assert_eq!(adamas_region_used(shared), 8);

        adamas_drop(copy, Some(releasing));
        adamas_drop(shared, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}
