//! Разделяемая область: тождество, воркерская рука, счёт живых блоков (§3.6).
//!
//! Здесь проверяется то, чего не видит ни ответ программы, ни санитайзер.
//!
//! *Ответ не видит тождества.* Однопоточная программа над разделяемой областью
//! отвечает **то же**, что над обычной, - и это не совпадение, а требование:
//! иначе корпусная фикстура разошлась бы с машиной на ровном месте. Различает
//! их только область с лишней ссылкой: обычная копируется, разделяемая нет.
//!
//! *Санитайзер не видит потерянного.* Он называет пару доступов, а не
//! последствие. Потерянная прибавка к курсору видна числом - двумя воркерами,
//! получившими один байт, - и это второй механизм обнаружения, тот же, что у
//! `tests/atomic.rs`.
//!
//! Счёт живых блоков стоит в каждом тесте: за фазу он различил пять дефектов,
//! которых не показал ответ, и один - которого не показал санитайзер.

// Рантайм и есть тот случай, ради которого `unsafe_code` объявлен `deny`.
#![allow(unsafe_code)]

use std::ffi::c_void;

use adamas_runtime::ffi::{
    Value, adamas_drop, adamas_dup, adamas_is_shared, adamas_is_unique, adamas_region_alloc,
    adamas_region_last, adamas_region_new, adamas_region_pop, adamas_region_read,
    adamas_region_recycle, adamas_region_used, adamas_shared_new, adamas_shared_release,
    adamas_shared_used, adamas_stat_live, adamas_stat_reset,
};

/// Сколько воркеров и сколько укладок каждый.
///
/// Воркеров вдвое больше типичного числа ядер по той же причине, что в
/// `tests/atomic.rs`: гонку рождает вытеснение, а не параллелизм сам по себе.
const HANDS: usize = 8;
const ROUNDS: usize = 60;

/// Нагрузка воркерского витка: **в кусок помещается ровно одна**.
///
/// Ширина выбрана замером, а не круглым числом, и мерена различающей силой
/// мутанта. Восемь байт дают укладку в свой кусок и встречу у курсора раз в
/// шестьдесят четыре витка - потерянная прибавка при этом видна **раз из
/// десяти прогонов**, то есть свидетель почти не различает. Нагрузка в
/// `ADAMAS_SHARED_CHUNK` минус выравнивание ставит встречу на **каждый**
/// виток, и мутант падает уверенно; числа - в шапке самого теста.
type Wide = [i64; 63];

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
    let at = unsafe { adamas_region_last(adamas_dup(made), Some(releasing)) };
    (made, at)
}

/// Читает значение по хендлу, не потребляя область.
unsafe fn fetched<T: Copy>(region: Value, at: usize) -> T {
    // Через `zeroed`, а не `Default`: нагрузка бывает широкой, а `Default` у
    // массивов длиннее тридцати двух std не даёт.
    let mut out = std::mem::MaybeUninit::<T>::zeroed();
    unsafe {
        adamas_region_read(
            adamas_dup(region),
            at,
            out.as_mut_ptr().cast::<c_void>(),
            size_of::<T>(),
            Some(releasing),
        );
        out.assume_init()
    }
}

/// Указатель на область, переезжающий в другой поток.
///
/// `Send` здесь законен ровно потому, что область рождается разделяемой:
/// счётчик её атомарен с первой ссылки, а укладка синхронизирована. Без этого
/// такой обёртки быть не должно - тот же довод, что у `Shared` в `atomic.rs`.
#[derive(Clone, Copy)]
struct Area(Value);

// SAFETY: воркеры зовут `adamas_region_alloc`/`adamas_region_last` над
// помеченной областью; счётчик её атомарен, курсор правится атомарной
// прибавкой, а рука воркера лежит в его собственном `_Thread_local`.
unsafe impl Send for Area {}

impl Area {
    /// Сама область. Методом, а не разбором поля: разбор захватил бы поле, а
    /// поле - голый указатель и не `Send`.
    const fn value(self) -> Value {
        self.0
    }
}

/// Прогон одной и той же программы над обычной областью и над разделяемой.
///
/// Программа взята у `eval/region-strategies` дословно в той части, где она
/// линейна: положить, спросить хендл, вернуть ячейку, положить снова. Это и
/// есть условие, при котором тождество и значение совпадают.
unsafe fn strategies(region: Value) -> (usize, usize, usize, usize) {
    unsafe {
        let (region, first) = placed(region, 1i64);
        let (region, second) = placed(region, 2i64);
        // Возврат **не с вершины**: его отрабатывает Pool и не отрабатывает
        // StackAlloc.
        let region = adamas_region_recycle(region, first);
        let (region, third) = placed(region, 4i64);
        // Возврат **с вершины**: его отрабатывают оба.
        let region = adamas_region_pop(region, second);
        let (region, fourth) = placed(region, 8i64);
        let answer = (first, second, third, fourth);
        adamas_drop(region, Some(releasing));
        answer
    }
}

/// Однопоточная программа отвечает над разделяемой областью то же, что над
/// обычной.
///
/// Это несущее требование, а не удобство: корпус сверяет ответ с машиной, а
/// машина разделяемых областей не знает вовсе - `sharedNew` у неё та же чистая
/// область. Разойдись правила размещения хоть в одном - фикстура с
/// `SharedArena` перестала бы браться договором трёх вычислителей, и
/// расхождение было бы не в том, что она проверяет.
#[test]
fn a_shared_area_places_like_an_ordinary_one() {
    unsafe {
        adamas_stat_reset();
        let ordinary = strategies(adamas_region_new());
        let shared = strategies(adamas_shared_new());
        assert_eq!(
            ordinary, shared,
            "правило размещения разошлось: обычная область отвечает {ordinary:?}, \
             разделяемая {shared:?}"
        );
    }
}

/// Разделяемая область не копируется при лишней ссылке - и этим отличается.
///
/// Обычная область здесь копируется (`tests/region.rs`,
/// `a_shared_region_is_copied_whole`), и ровно копия делает её
/// потокобезопасной даром: двух воркеров в одной не бывает. Снять копию -
/// единственное, что отличает разделяемую по договору; всё прочее следствие.
#[test]
fn a_shared_area_is_not_copied_when_it_has_a_second_reference() {
    unsafe {
        adamas_stat_reset();
        let area = adamas_shared_new();
        assert_ne!(
            adamas_is_shared(area),
            0,
            "область рождается разделяемой: счётчик её атомарен с первой ссылки"
        );
        let (area, first) = placed(area, 20i64);

        // Вторая ссылка: у обычной области с этого места начинается копия.
        let held = adamas_dup(area);
        assert_eq!(adamas_is_unique(area), 0);
        let (again, second) = placed(area, 99i64);
        assert_eq!(again, held, "разделяемая область осталась той же");
        assert_eq!(second, 8, "укладка пошла в ту же область, а не в копию");
        assert_eq!(fetched::<i64>(again, first), 20, "прежняя ячейка на месте");

        adamas_drop(again, Some(releasing));
        // Дроп нагрузки: детей у области нет, и освобождает её `adamas_drop`.
        adamas_shared_release(held);
        adamas_drop(held, Some(releasing));
        assert_eq!(adamas_stat_live(), 0, "область - один блок, и дроп её один");
    }
}

/// Курсор области поднимается кусками, а не укладками.
///
/// Наблюдаемое, которого нет у обычной области: `adamas_region_used` над
/// разделяемой отвечает **розданным**, а не занятым. Без этого различия
/// «per-thread cache» §3.6 не проверялся бы ничем - укладка в свой кусок
/// выглядела бы так же, как укладка у общего курсора.
#[test]
fn the_area_cursor_moves_by_chunks_and_not_by_placements() {
    unsafe {
        adamas_stat_reset();
        let area = adamas_shared_new();
        let first = adamas_shared_used(area);
        assert_eq!(first, 0, "пустая область никому ничего не раздала");

        let (area, _) = placed(area, 1i64);
        let after = adamas_shared_used(area);
        assert!(
            after >= 512,
            "первая укладка обязана взять кусок целиком, а взяла {after} байт"
        );

        let mut area = area;
        for turn in 0..16i64 {
            let (next, _) = placed(area, turn);
            area = next;
        }
        assert_eq!(
            adamas_shared_used(area),
            after,
            "семнадцать восьмибайтовых укладок умещаются в один кусок, и \
             курсор области за это время не двигался ни разу"
        );

        adamas_drop(area, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Воркеры укладывают в одну область, и ни один байт не достаётся двоим.
///
/// Потерянная прибавка к курсору видна **числом**: два воркера, получившие
/// один кусок, кладут по одному адресу, и значение одного затирается значением
/// другого. Проверяется поэтому не «программа не упала», а то, что каждая
/// ячейка держит своё - тот же механизм обнаружения, что у `atomic.rs`
/// (потерянное обновление), и он различает независимо от санитайзера.
///
/// # Различающая сила измерена, а не заявлена
///
/// Мутант - атомарная прибавка к курсору, заменённая обычной
/// (`shared.c`, `refill`), то есть ровно та реализация, которой бы область
/// вышла без синхронизации. Ширина нагрузки при этом **решает**:
///
/// | нагрузка | встреча у курсора | мутант падает |
/// |---|---|---|
/// | 8 байт | раз в 64 витка | **1 прогон из 10** |
/// | `Wide` (504 байта) | каждый виток | **10 из 10** |
///
/// То есть тот же свидетель на очевидной нагрузке почти не различал бы, и
/// вина не в мутанте: узкая укладка идёт в свой кусок и общего курсора не
/// касается вовсе. Это и есть цена per-thread cache - он **прячет** гонку от
/// свидетеля так же хорошо, как от контеншена.
#[test]
fn no_placement_is_lost_when_workers_share_one_area() {
    unsafe {
        adamas_stat_reset();
        let area = Area(adamas_shared_new());
        // Ссылка хозяина плюс по одной на воркера: дропает каждый свою.
        for _ in 0..HANDS {
            adamas_dup(area.value());
        }

        let places: Vec<Vec<(usize, i64)>> = std::thread::scope(|scope| {
            let mut hands = Vec::new();
            for hand in 0..HANDS {
                hands.push(scope.spawn(move || {
                    let mut mine = Vec::with_capacity(ROUNDS);
                    let mut held = area.value();
                    for round in 0..ROUNDS {
                        let value = i64::try_from(hand * ROUNDS + round).unwrap_or(0) + 1;
                        let mut wide: Wide = [0; 63];
                        wide[0] = value;
                        let (next, at) = placed(held, wide);
                        held = next;
                        mine.push((at, value));
                    }
                    adamas_drop(held, Some(releasing));
                    mine
                }));
            }
            hands.into_iter().map(|hand| hand.join().unwrap()).collect()
        });

        let area = area.value();
        let mut seen = std::collections::HashMap::new();
        for mine in &places {
            for &(at, value) in mine {
                assert!(
                    seen.insert(at, value).is_none(),
                    "хендл {at} достался двум воркерам: прибавка к курсору потеряна"
                );
                assert_eq!(
                    fetched::<Wide>(area, at)[0],
                    value,
                    "ячейка {at} держит не то, что в неё уложили"
                );
            }
        }
        assert_eq!(
            seen.len(),
            HANDS * ROUNDS,
            "уложено меньше, чем просили: часть укладок потерялась"
        );

        adamas_drop(area, Some(releasing));
        assert_eq!(
            adamas_stat_live(),
            0,
            "область освободилась ровно один раз, сколько бы воркеров её ни держало"
        );
    }
}

/// Хендл последней укладки - у **спрашивающего**, а не у области.
///
/// «Последняя» у общей области не определена вовсе: между `store` одного
/// воркера и его `here` встаёт `store` другого. Проверяется это тем, что
/// воркер видит своё после того, как чужой уложил своё, - без воркерской руки
/// хендл уехал бы к соседу, и **ответ программы остался бы правдоподобным**:
/// адрес есть адрес, а чужая ячейка читается не хуже своей.
#[test]
fn the_last_handle_belongs_to_the_worker_that_asked() {
    unsafe {
        adamas_stat_reset();
        let area = Area(adamas_shared_new());
        adamas_dup(area.value());

        let (mine, theirs) = std::thread::scope(|scope| {
            let (ready, wait) = std::sync::mpsc::channel::<()>();
            let (done, back) = std::sync::mpsc::channel::<usize>();
            let other = scope.spawn(move || {
                wait.recv().unwrap();
                let (held, at) = placed(area.value(), 777i64);
                done.send(at).unwrap();
                adamas_drop(held, Some(releasing));
            });
            // Своя укладка - до чужой; хендл спрашивается **после** неё.
            let (held, at) = placed(area.value(), 11i64);
            ready.send(()).unwrap();
            let theirs = back.recv().unwrap();
            let mine = adamas_region_last(adamas_dup(held), Some(releasing));
            other.join().unwrap();
            (mine, (at, theirs))
        });

        let (at, foreign) = theirs;
        assert_eq!(mine, at, "хендл ушёл к чужой укладке: рука воркера не своя");
        assert_ne!(
            mine, foreign,
            "два воркера получили один хендл: куски пересеклись"
        );
        assert_eq!(fetched::<i64>(area.value(), mine), 11);
        assert_eq!(fetched::<i64>(area.value(), foreign), 777);

        adamas_drop(area.value(), Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Возврат ячейки и LIFO - тоже воркерские, и обычная область им равна.
///
/// Здесь различаются `SharedPool` и `SharedStack`: первый отдаёт ячейку из
/// середины, второй только с вершины. Числа те же, что у `eval/region-strategies`,
/// и это ровно то, ради чего правило размещения не расходится.
#[test]
fn a_recycled_cell_and_a_pop_work_per_worker() {
    unsafe {
        adamas_stat_reset();
        let area = adamas_shared_new();
        let (area, first) = placed(area, 20i64);
        let (area, second) = placed(area, 7i64);
        assert_eq!((first, second), (0, 8));

        // Pool: ячейка из середины достаётся равной по ширине.
        let area = adamas_region_recycle(area, first);
        let (area, again) = placed(area, 99i64);
        assert_eq!(again, first, "равная по ширине легла в отданную");

        // StackAlloc: курсор падает только с вершины.
        let area = adamas_region_pop(area, first);
        let (area, aside) = placed(area, 5i64);
        assert_eq!(aside, 16, "возврат не с вершины курсора не двигает");
        let area = adamas_region_pop(area, aside);
        let (area, top) = placed(area, 6i64);
        assert_eq!(top, aside, "вершина отдана, следующая легла на её место");

        // Узкая нагрузка широкой ячейки не берёт: «одинакового размера».
        let area = adamas_region_recycle(area, top);
        let (area, narrow) = placed(area, 0.25f32);
        assert_ne!(narrow, top, "четыре байта в восьмибайтовую не встают");

        // Курсор области при этом остаётся розданным целиком: возврат ячейки
        // кусок области не возвращает, и обратного §3.6 не обещает.
        assert_eq!(adamas_region_used(area), 512);
        adamas_drop(area, Some(releasing));
        assert_eq!(adamas_stat_live(), 0);
    }
}
