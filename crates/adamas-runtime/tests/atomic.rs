//! Атомарный счётчик разделяемого значения (§5.1) и **чем** он проверен.
//!
//! # Почему обычной проверки тут мало
//!
//! Гонка счётчика не воспроизводится по требованию и не видна ответом:
//! программа даёт правильное число тысячу прогонов подряд, а на тысяча первом
//! теряет объект или освобождает живой. Зелёный тест на такой правке не значит
//! ничего - он значит «в этот раз повезло».
//!
//! Поэтому механизмов здесь **два**, и каждый назван тем, что он ловит.
//!
//! *Потерянное обновление* (этот файл). Потоки берут и отдают ссылки на один
//! объект; пропущенная инкрементация видна числом - счётчик после всех взятий
//! обязан быть ровно `потоков × ходов`. Ловит это только тогда, когда гонка
//! случилась, то есть **вероятностно**; зато без инструментов и на каждом
//! прогоне CI.
//!
//! *`ThreadSanitizer`* (`tests/race.rs`). Ловит саму **возможность** гонки, а не
//! её случившийся исход: несинхронизированный доступ к счётчику он назовёт даже
//! там, где число сошлось. Это и есть механизм, которого требует §5.1.
//!
//! # Что здесь проверено и что нет
//!
//! Проверен **счётчик**: `dup`, `drop`, `is_unique` на объекте, помеченном
//! `adamas_share`; **транзитивность** пометки (§5.2) - ребёнок разделяемого
//! родителя считается атомарно так же, как сам родитель; и промоушен внутрь
//! **захваченной резумпции** - значения в средах её кадров.
//!
//! Значение пересекает поток здесь, в стенде, и стенд делает ровно то, что
//! делает `spawn`, - ни на шаг больше. Настоящие потоки у питомника с трека E
//! волны 3 Фазы 7 есть (`ADAMAS_THREADS`, `c/fiber.c`), но проверяются они не
//! отсюда: свидетели круга живут в `adamas-codegen/tests/threads.rs`, потому
//! что кругу нужна программа, а не вызовы рантайма. Здесь - механика счётчика.
//!
//! Граница, которую этот файл **не** покрывает, названа там же и стоила треку
//! дефекта: стенд проходит те пути, которые в нём написаны, и счётчик вектора
//! evidence в их число не входил.

// Рантайм и есть тот случай, ради которого `unsafe_code` объявлен `deny`.
#![allow(unsafe_code)]

use std::sync::atomic::{AtomicU32, Ordering};

use adamas_runtime::ffi::{
    Frame, Kont, MARK_HANDLER, MARK_PLAIN, TAG_SEGMENT, Value, adamas_alloc, adamas_drop,
    adamas_dup, adamas_evidence_drop, adamas_evidence_empty, adamas_field, adamas_frame_env,
    adamas_imm, adamas_is_shared, adamas_is_unique, adamas_kont_cut, adamas_kont_init,
    adamas_kont_push, adamas_rc, adamas_segment_abandon, adamas_segment_promote,
    adamas_segment_value, adamas_set_field, adamas_share, adamas_tag,
};

/// Сколько потоков и сколько ходов каждый.
///
/// Числа не круглые: ходов столько, чтобы прогон оставался быстрым, а потоков
/// вдвое больше типичного числа ядер - гонку рождает вытеснение, а не
/// параллелизм сам по себе.
const THREADS: u32 = 8;
const ROUNDS: u32 = 20_000;

/// Указатель на объект, переезжающий в другой поток.
///
/// `Send` здесь и есть предмет проверки, а не обход правила: значение помечено
/// `adamas_share`, то есть его счётчик атомарен, и переезд законен ровно
/// потому. Без пометки такой обёртки быть не должно.
#[derive(Clone, Copy)]
struct Shared(Value);

// SAFETY: единственное, что потоки делают с указателем, - зовут `adamas_dup` и
// `adamas_drop`, а те на помеченном объекте атомарны (`object.c`). Поля объекта
// никто не пишет.
unsafe impl Send for Shared {}

impl Shared {
    /// Само значение. Методом, а не разбором поля в теле замыкания: разбор
    /// захватил бы **поле**, а поле - голый указатель и не `Send`; захват
    /// структуры целиком и есть то, чем эта обёртка работает.
    const fn value(self) -> Value {
        self.0
    }
}

/// Обход детей, какой порождало бы понижение (`release.c`, но для промоушена).
///
/// Тип стенда - звено списка: единственное поле либо следующее звено, либо
/// число. Непосредственное `adamas_share` отбрасывает сама, поэтому развилки
/// здесь нет, как её нет и у порождённого дропа.
unsafe extern "C" fn spine(value: Value) {
    unsafe { adamas_share(adamas_field(value, 0), Some(spine)) }
}

/// Дроп детей того же типа: тот `release`, которому промоушен симметричен.
unsafe extern "C" fn spine_release(value: Value) {
    unsafe { adamas_drop(adamas_field(value, 0), Some(spine_release)) }
}

/// Объект с одним полем-числом, сразу помеченный разделяемым.
unsafe fn shared_object(number: isize) -> Shared {
    unsafe {
        let value = adamas_alloc(0, 1);
        adamas_set_field(value, 0, adamas_imm(number));
        adamas_share(value, None);
        Shared(value)
    }
}

/// Звено, за которым лежит ещё одно: голова разделяется, ребёнок достижим.
///
/// Это и есть форма захвата, о которой говорит §5.2: `spawn` получает **одно**
/// значение, а поток трогает всё, до чего из него доходит.
unsafe fn shared_pair() -> (Shared, Shared) {
    unsafe {
        let tail = adamas_alloc(0, 1);
        adamas_set_field(tail, 0, adamas_imm(2));
        let head = adamas_alloc(0, 1);
        adamas_set_field(head, 0, tail);
        adamas_share(head, Some(spine));
        (Shared(head), Shared(tail))
    }
}

/// Пометка видна и счётчик остаётся тем же: `rc == 0` значит уникален (§5.1).
///
/// Утверждение не косметическое. Вывод уникальности трека B (`crate::unique`)
/// читает **ровно** `rc == 0`, и перевод счётчика в атомарный режим обязан
/// оставить это соотношение нетронутым: иначе статическая ветвь `Certain`
/// разошлась бы с рантаймом молча.
#[test]
fn sharing_does_not_move_the_zero() {
    unsafe {
        let Shared(value) = shared_object(7);
        assert_eq!(adamas_is_shared(value), 1, "пометка не встала");
        assert_eq!(
            adamas_rc(value),
            0,
            "свежий разделяемый обязан быть уникален"
        );
        assert_eq!(
            adamas_is_unique(value),
            1,
            "`rc == 0` перестал значить уникальность"
        );
        adamas_dup(value);
        assert_eq!(adamas_rc(value), 1);
        assert_eq!(adamas_is_unique(value), 0);
        adamas_drop(value, None);
        assert_eq!(adamas_is_unique(value), 1, "уникальность не вернулась");
        adamas_drop(value, None);
    }
}

/// Пометка доходит до достижимого, а не встаёт на одном объекте (§5.2).
///
/// Наблюдаемое здесь - сам флаг, и стоит оно первым, потому что дёшево и
/// детерминированно. Чего оно **не** показывает - цены: что ребёнок без флага
/// считается неатомарно и второй поток правит его счётчик голым `+=`,
/// показывают соседний стенд под нагрузкой и санитайзер (`tests/race.rs`).
#[test]
fn promotion_reaches_the_children() {
    unsafe {
        let (Shared(head), Shared(tail)) = shared_pair();
        assert_eq!(adamas_is_shared(head), 1, "пометка не встала на голове");
        assert_eq!(
            adamas_is_shared(tail),
            1,
            "пометка не дошла до ребёнка: обещание §5.2 шире сделанного"
        );
        adamas_drop(head, Some(spine_release));
    }
}

/// Локальный объект пометки не несёт и считается по-старому.
///
/// Стоит рядом, потому что режим **гибридный**: сломай ветвление по флагу в
/// сторону «всё атомарно», и этот тест останется зелёным, а §5.1 - нет.
/// Наблюдаемое здесь - сам флаг, и ловит оно ровно обратную правку: «всё
/// локально».
#[test]
fn a_local_object_is_not_shared() {
    unsafe {
        let value = adamas_alloc(0, 1);
        adamas_set_field(value, 0, adamas_imm(1));
        assert_eq!(
            adamas_is_shared(value),
            0,
            "локальный объект помечен разделяемым"
        );
        adamas_dup(value);
        assert_eq!(adamas_rc(value), 1);
        adamas_drop(value, None);
        adamas_drop(value, None);
    }
}

/// Промоушен доходит до значений внутри **захваченной резумпции** (§5.2).
///
/// Резумпция есть обычное значение: `\s -> resume v s` держит её в слоте
/// замыкания, а замыкание бывает телом `spawn`. Значения в средах её кадров
/// уезжают в чужой поток вместе с ней, и без обхода считались бы неатомарно.
///
/// Наблюдаемое - сам флаг, и мутант у него в `frame.c`: сними цикл по
/// `counted`, и пометка встанет на ручке сегмента, а до звена не дойдёт.
/// Проверено снятием: `shared=0` у обоих звеньев.
///
/// **Чего этот свидетель не показывает:** гонки. Гонка на значении внутри
/// резумпции требует программы, порождающей задачу из тела
/// параметризованного хендлера, - её в корпусе нет, и трек её не написал.
/// Сказано это здесь, а не подразумевается.
#[test]
fn promotion_reaches_inside_a_captured_resumption() {
    /// Обход детей, разводящий сегмент и звено: то, что порождает понижение
    /// (`promote.c`). Здесь он написан руками, потому что стенд - рантаймовый.
    unsafe extern "C" fn walk(value: Value) {
        unsafe {
            if adamas_tag(value) == TAG_SEGMENT {
                adamas_segment_promote(value, Some(walk));
                return;
            }
            adamas_share(adamas_field(value, 0), Some(walk));
        }
    }

    /// Дроп среды кадра: без него значение в счётном слоте утекло бы -
    /// `frame_free` зовёт release и только его.
    unsafe extern "C" fn drops_env(frame: *mut Frame, _kont: *mut Kont) {
        unsafe { adamas_drop(*adamas_frame_env(frame), Some(spine_release)) }
    }

    unsafe {
        let mut kont = Kont {
            top: std::ptr::null_mut(),
        };
        adamas_kont_init(&raw mut kont);
        let evidence = adamas_evidence_empty();

        // Голова списка в счётном слоте кадра - то, что несёт с собой
        // приостановленное вычисление.
        let tail = adamas_alloc(0, 1);
        adamas_set_field(tail, 0, adamas_imm(2));
        let head = adamas_alloc(0, 1);
        adamas_set_field(head, 0, tail);

        let base = adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, 0, evidence);
        let frame = adamas_kont_push(
            &raw mut kont,
            MARK_PLAIN,
            0,
            None,
            Some(drops_env),
            1,
            1,
            evidence,
        );
        *adamas_frame_env(frame) = head;
        let segment = adamas_segment_value(adamas_kont_cut(&raw mut kont, base));

        adamas_share(segment, Some(walk));
        assert_eq!(adamas_is_shared(segment), 1, "ручка сегмента не помечена");
        assert_eq!(
            adamas_is_shared(head),
            1,
            "пометка не дошла до среды кадра: резумпция уехала бы с локальным счётчиком"
        );
        assert_eq!(
            adamas_is_shared(tail),
            1,
            "пометка не дошла до ребёнка внутри среды кадра"
        );

        adamas_segment_abandon(segment);
        adamas_drop(segment, None);
        adamas_evidence_drop(evidence);
    }
}

/// Потерянное обновление: счётчик после всех взятий равен числу взятий.
///
/// Каждый поток берёт ссылку `ROUNDS` раз, и **только потом** отдаёт: иначе
/// взятия и отдачи перемешались бы, и промежуточное значение счётчика не было
/// бы предсказуемо ничем. Здесь оно предсказуемо: после барьера ровно
/// `THREADS * ROUNDS` лишних ссылок, и ни одной меньше.
///
/// *Что этот механизм поймает и чего не поймает.* Поймает пропавшую
/// инкрементацию - ту самую, которую даёт `rc += 1` без `lock`. Не поймает
/// гонку, которая в этот раз не случилась: планировщик вправе развести потоки
/// так, что перекрытия не будет вовсе. Поэтому рядом стоит санитайзер.
#[test]
fn no_increment_is_lost_under_contention() {
    unsafe {
        let object = shared_object(1);
        let taken = AtomicU32::new(0);
        std::thread::scope(|scope| {
            for _ in 0..THREADS {
                let taken = &taken;
                scope.spawn(move || {
                    // SAFETY: счётчик помеченного объекта атомарен.
                    let value = object.value();
                    for _ in 0..ROUNDS {
                        adamas_dup(value);
                    }
                    taken.fetch_add(ROUNDS, Ordering::Relaxed);
                });
            }
        });
        let Shared(value) = object;
        assert_eq!(
            adamas_rc(value),
            taken.load(Ordering::Relaxed),
            "счётчик потерял взятия: инкрементация не атомарна"
        );
        for _ in 0..THREADS * ROUNDS {
            adamas_drop(value, None);
        }
        assert_eq!(adamas_rc(value), 0, "счётчик не вернулся к уникальности");
        adamas_drop(value, None);
    }
}

/// То же потерянное обновление, но на **ребёнке** разделяемого значения.
///
/// Свидетель расхождения §5.2 с рантаймом, и он единственный из двух, который
/// виден числом. Потоки получают одну голову - ровно то, что получил бы
/// `spawn` от захвата замыкания, - и трогают счётчик **достижимого** из неё:
/// так делает всякий разбор списка, дупающий хвост.
///
/// Разница измерена. С промоушеном одного объекта (`None` вместо обхода)
/// счётчик хвоста после 160 000 взятий показывал 32 764, 52 284, 54 805,
/// 66 136, 81 617 - пять прогонов, и ни в одном не уцелело даже половины.
/// Стенд с перемешанными взятиями и отдачами того же хвоста не доживал до
/// ответа вовсе: двадцать прогонов дали **шестнадцать** обрывов в `malloc`
/// («double free», «unaligned tcache chunk») и четыре утёкших блока.
#[test]
fn no_increment_is_lost_on_a_child_of_a_shared_value() {
    unsafe {
        let (head, tail) = shared_pair();
        let taken = AtomicU32::new(0);
        std::thread::scope(|scope| {
            for _ in 0..THREADS {
                let taken = &taken;
                scope.spawn(move || {
                    // SAFETY: голова разделена обходом, значит и хвост тоже, -
                    // счётчик достижимого атомарен ровно поэтому.
                    let value = adamas_field(head.value(), 0);
                    for _ in 0..ROUNDS {
                        adamas_dup(value);
                    }
                    taken.fetch_add(ROUNDS, Ordering::Relaxed);
                });
            }
        });
        let Shared(value) = tail;
        assert_eq!(
            adamas_rc(value),
            taken.load(Ordering::Relaxed),
            "счётчик ребёнка потерял взятия: промоушен до него не дошёл"
        );
        for _ in 0..THREADS * ROUNDS {
            adamas_drop(value, None);
        }
        adamas_drop(head.value(), Some(spine_release));
    }
}

/// Блок, выданный одним потоком и освобождённый другим, не обрывает прогон.
///
/// До этого трека обрывал: счёт живых блоков был беззнаковым и потоко-локальным,
/// а на пути освобождения стояла проверка `blocks_live == 0` - «освобождён
/// блок, которого рантайм не выдавал». Поток, ничего не выдававший, попадал в
/// неё на первом же чужом блоке. Ровно это и делает всякая передача значения
/// между потоками, то есть `spawn` (§5.2), - проверка обрывала бы верную
/// программу.
///
/// Свидетель здесь **отрицательный**: наблюдаемое - что прогон дошёл до конца.
/// Различающая сила у него есть - без правки он падает обрывом, - и это
/// измерено, а не предположено.
#[test]
fn a_block_may_be_freed_by_a_thread_that_did_not_issue_it() {
    unsafe {
        let object = shared_object(3);
        let value = object.value();
        adamas_dup(value);
        // Главный отдаёт свою ссылку заранее: последней окажется чужая, и
        // освобождать блок будет поток, который его не выдавал.
        adamas_drop(value, None);
        std::thread::scope(|scope| {
            scope.spawn(move || {
                // SAFETY: счётчик помеченного объекта атомарен.
                adamas_drop(object.value(), None);
            });
        });
    }
}

/// Последней ссылкой оказывается **ровно один** поток.
///
/// Это вторая половина договора, и она сильнее первой: потерянная
/// инкрементация даёт неверное число, а неверное решение «я последний» даёт
/// либо течь, либо двойное освобождение - то, что числом не видно вовсе.
///
/// Наблюдается оно **числом вызовов деструктора**: `release` зовётся ровно на
/// последней ссылке, значит ровно один раз на объект.
///
/// Счётчик живых блоков сюда не годится, и это измерено: сумма по всем потокам
/// общая на весь процесс, а тесты крейта идут потоками того же процесса и
/// аллоцируют параллельно - разность «до и после» оказалась 1 при верном коде.
/// Деструктор считает **свои** объекты и чужих не видит.
///
/// Каждый поток получает свою ссылку заранее (главный дупает `THREADS` раз) и
/// отдаёт её; кто отдаст последнюю - решает планировщик.
#[test]
fn exactly_one_thread_sees_the_last_reference() {
    /// Сколько раз позвали дроп детей. Общий, а не потоко-локальный: зовёт его
    /// тот поток, которому досталась последняя ссылка, и кто это - неизвестно.
    static DEATHS: AtomicU32 = AtomicU32::new(0);

    unsafe extern "C" fn counted(_value: Value) {
        DEATHS.fetch_add(1, Ordering::Relaxed);
    }

    const OBJECTS: u32 = 256;

    unsafe {
        for _ in 0..OBJECTS {
            let object = shared_object(2);
            let value = object.value();
            for _ in 0..THREADS {
                adamas_dup(value);
            }
            // Ссылок теперь `THREADS + 1`: своя у главного и по одной у потока.
            std::thread::scope(|scope| {
                for _ in 0..THREADS {
                    scope.spawn(move || {
                        // SAFETY: счётчик помеченного объекта атомарен.
                        adamas_drop(object.value(), Some(counted));
                    });
                }
            });
            // Своя ссылка главного - последняя, и объект умирает здесь.
            adamas_drop(value, Some(counted));
        }
        assert_eq!(
            DEATHS.load(Ordering::Relaxed),
            OBJECTS,
            "деструктор позван не по разу на объект: либо течь, либо двойное освобождение"
        );
    }
}
