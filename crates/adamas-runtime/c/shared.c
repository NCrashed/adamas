/* Разделяемая область: одна область на несколько воркеров (§3.6, §5.2).
 *
 * Договор описан в `adamas.h`; здесь только то, что видно из реализации.
 *
 * # Чем она отличается от обычной, и это отличие одно
 *
 * Обычная область (`region.c`) есть **значение**: уникальность спрашивается у
 * счётчика, разделённая копируется целиком (`copied`). Ровно это и делает её
 * потокобезопасной даром - двух воркеров в одной области не бывает, потому что
 * второй получает копию. И ровно это делает разделяемый mempool невыразимым.
 *
 * Разделяемая область поэтому есть **тождество**: копии у неё нет ни при каком
 * счётчике, `store` правит ту же область и возвращает тот же указатель. Всё
 * прочее - следствие. Синхронизация нужна потому, что копии больше нет; журнал
 * уехал к воркеру потому, что общий пришлось бы держать под замком; хендл
 * последней укладки стал воркерским потому, что «последняя» у общей области не
 * определена вовсе.
 *
 * `AllocStrategy` (§3.6) от этого не меняется ни одним членом - меняется
 * `new`, и это дословно то, что §3.6 и пишет: «программист выбирает уровень при
 * создании региона». `SharedArena`, `SharedPool` и `SharedStack` расходятся
 * между собой той же одной строкой, что Arena, Pool и StackAlloc, - тем, что
 * делает `free`.
 *
 * # Где воркеры встречаются, и это одно место
 *
 * Общего изменяемого состояния у области ровно одно поле - `cursor`, сколько
 * байт роздано под куски. Правится оно атомарной прибавкой, читается атомарной
 * загрузкой, и больше воркеры не встречаются нигде: свой кусок, свой курсор в
 * нём, свой журнал и свой хендл последней укладки лежат в `_Thread_local`.
 *
 * Отсюда и форма быстрого пути: укладка внутри своего куска не делает ни одной
 * атомарной операции вовсе, а встреча случается раз в кусок. Это и есть
 * «per-thread caches и global-fallback» §3.6, и это же ответ на §10 вопрос
 * 26(а): куски взяты **обеим** стандартным стратегиям, а не одному пулу, -
 * цена развилки измерена (`docs/measurements/shared-region/`).
 *
 * Холодная половина вынесена за `noinline, cold` тем же ходом и по той же
 * причине, что `copied` в `region.c` и `nursery_lock` в `fiber.c`: у LLVM
 * `PartialInlinerPass` в `-O2` выключен, и **делит атрибут, а не две функции**.
 * Цена измерена, см. README замера.
 *
 * # Чего здесь нет, и это названо
 *
 * *Потокобезопасности ячейки.* §3.6 обещает thread-safety **аллокатора**, а не
 * нагрузки, и §10 вопрос 40 ровно об этом: два воркера, пишущие в один хендл,
 * дают гонку данных, и рантайм её не закрывает. Закрыть её нечем без решения,
 * какого из трёх вариантов вопроса 40 держаться, - а это дизайн, не рантайм.
 *
 * *Двух областей у одного воркера разом.* Рука одна, и при смене области она
 * бросает остаток куска и свой журнал: остаток теряется внутри области (её
 * освободит дроп целиком), забытая ячейка перестаёт переиспользоваться. Ни то,
 * ни другое не портит ответа - возврат ячейки, которой область не помнит, и у
 * обычной области оставляет её как есть.
 *
 * *Роста области.* Тот же запрет, что у обычной: `AllocStrategy` метода роста
 * не называет, и молчаливый рост означал бы вторую аллокацию там, где обещана
 * одна.
 */

#include "adamas.h"

#include <string.h>

/* Половина, до которой воркер доходит раз в кусок.
 *
 * Тот же приём и тот же довод, что у `ADAMAS_SHARED_HALF` (`object.c`) и
 * `ADAMAS_CROWDED` (`fiber.c`): `cold` метит место вызова маловероятным, а
 * `noinline` запрещает слияние - без запрета компилятор втягивает холодную
 * половину обратно, и «две функции» перестают быть разделением. */
#define ADAMAS_CONTESTED __attribute__((noinline, cold))

/* Начало полезной нагрузки. Та же раскладка, что у обычной области: байты, а
 * не слоты, - нагрузка плоская по построению (`{Flat a}`, §3.6). */
static char *payload(adamas_value area) {
    return (char *)area + sizeof(adamas_shared);
}

static adamas_shared *area_of(adamas_value area) {
    if (adamas_tag(area) != ADAMAS_TAG_SHARED) {
        adamas_fail("операция разделяемой области над не-областью");
    }
    return (adamas_shared *)area;
}

/* Ближайшее сверху кратное `align` - то же правило, что у `region.c`. */
static size_t aligned(size_t offset, size_t align) {
    size_t bound = align == 0 ? 1 : align;
    size_t slack = offset % bound;
    return slack == 0 ? offset : offset + (bound - slack);
}

/* Рука воркера: его кусок, его журнал, его хендл.
 *
 * Лежит в `_Thread_local`, а не в области, и это не мелочь: так у воркеров нет
 * общей строки кэша вовсе, поэтому ложного разделения не бывает по построению,
 * а санитайзеру нечего смотреть - частная память потока ему не пара доступов.
 * Ценой идёт то, что рука одна на поток: воркер, чередующий две области,
 * бросает кусок на каждом переключении (см. шапку). */
typedef struct adamas_hand {
    /** Чья это рука. `NULL` - ничьей области ещё не касались. */
    const void *area;
    /** Её номер: адреса мало, освобождённый блок `malloc` выдаёт снова. */
    size_t birth;
    /** Хендл последней укладки **этого** воркера. */
    size_t last;
    /** Его курсор внутри своего куска. */
    size_t at;
    /** Конец куска. */
    size_t edge;
    /** Сколько ячеек помнит журнал, и куда писать следующую. */
    uint32_t cells;
    uint32_t next;
    /**
     * Сколько среди них отдано обратно.
     *
     * Держится числом, а не считается обходом, ради **`SharedArena`**: её
     * `free` не делает ничего, свободных ячеек у неё не бывает вовсе, и без
     * этого счётчика всякая её укладка перебирала бы весь журнал впустую -
     * сто двадцать восемь записей на виток. Цена обхода измерена
     * (`docs/measurements/shared-region/`).
     */
    uint32_t frees;
    /** Журнал: последние `ADAMAS_SHARED_CELLS` укладок этого воркера. */
    adamas_cell journal[ADAMAS_SHARED_CELLS];
} adamas_hand;

static _Thread_local adamas_hand hand;

/* Рука, настроенная на эту область. Смена области бросает прежний кусок.
 *
 * Сверяются **адрес и номер**, и второго не выкинуть: область есть блок
 * `malloc`, а освобождённый блок той же ширины `malloc` выдаёт снова. Рука по
 * одному адресу продолжила бы укладывать в кусок, которого новая область
 * никому не раздавала, - и два воркера получили бы одни байты при верном на
 * вид курсоре. Свидетель - `tests/shared.rs`,
 * `a_new_area_at_a_reused_address_is_not_the_old_one`. */
static adamas_hand *handed(adamas_value area) {
    size_t birth = ((const adamas_shared *)area)->birth;
    if (hand.area != (const void *)area || hand.birth != birth) {
        hand.area = (const void *)area;
        hand.birth = birth;
        hand.last = 0;
        hand.at = 0;
        hand.edge = 0;
        hand.cells = 0;
        hand.next = 0;
        hand.frees = 0;
    }
    return &hand;
}

/* Свободная ячейка равной ширины, самая поздняя по размещению.
 *
 * Правило взято у обычной области дословно (`region.c`, цикл в
 * `adamas_region_alloc`): равный размер плюс годная граница. Совпадать они
 * обязаны - иначе однопоточная программа над разделяемой областью отвечала бы
 * не то, что над обычной, и договор трёх вычислителей разошёлся бы на ровном
 * месте.
 *
 * Обход не помечен `cold`, и это не упущение: у `SharedPool` он и есть
 * горячий путь. Холодным его делает не атрибут, а **счётчик отданных** -
 * `SharedArena` до сюда не доходит вовсе. */
static adamas_cell *vacant(adamas_hand *own, size_t size, size_t bound) {
    adamas_cell *best = NULL;
    uint32_t index;
    if (own->frees == 0) {
        return NULL;
    }
    for (index = 0; index < own->cells; index += 1) {
        adamas_cell *cell = &own->journal[index];
        if (cell->free && cell->size == size && cell->at % bound == 0) {
            if (best == NULL || cell->at > best->at) {
                best = cell;
            }
        }
    }
    return best;
}

/* Предыдущая позиция кольца. */
static uint32_t earlier(uint32_t index) {
    return index == 0 ? (uint32_t)ADAMAS_SHARED_CELLS - 1u : index - 1u;
}

/* Ячейка журнала по хендлу; `NULL` - воркер её уже забыл. */
static adamas_cell *recorded(adamas_hand *own, size_t at) {
    uint32_t index;
    for (index = 0; index < own->cells; index += 1) {
        if (!own->journal[index].free && own->journal[index].at == at) {
            return &own->journal[index];
        }
    }
    return NULL;
}

/* Записывает укладку. Журнал кольцевой: переполнение забывает самую давнюю,
 * и забытая ячейка просто перестаёт переиспользоваться - возврат по ней
 * оставляет область как есть, ровно как хендл, не называющий занятой ячейки. */
static void record(adamas_hand *own, size_t at, size_t size) {
    adamas_cell *cell = &own->journal[own->next];
    if (own->cells == ADAMAS_SHARED_CELLS && cell->free) {
        /* Затирается отданная ячейка: она перестаёт ждать, и счёт отданных
         * обязан за этим следить - иначе `vacant` искала бы то, чего нет. */
        own->frees -= 1;
    }
    cell->at = (uint32_t)at;
    cell->size = (uint32_t)size;
    cell->free = 0;
    own->next = (own->next + 1) % ADAMAS_SHARED_CELLS;
    if (own->cells < ADAMAS_SHARED_CELLS) {
        own->cells += 1;
    }
}

/* Новый кусок у курсора области: **единственное** место встречи воркеров.
 *
 * Прибавка атомарна, поэтому двум воркерам один байт не достаётся никогда, и
 * повторять её не приходится - в отличие от CAS-петли, у `fetch_add` отказа
 * нет по построению. Кусок кратен `ADAMAS_SHARED_CHUNK`, оттого его начало
 * выровнено по нему же, и внутри куска обычное правило границы считает
 * абсолютное смещение верно. */
ADAMAS_CONTESTED static void refill(adamas_shared *area, adamas_hand *own, size_t need) {
    size_t want = need <= ADAMAS_SHARED_CHUNK
                      ? (size_t)ADAMAS_SHARED_CHUNK
                      : aligned(need, ADAMAS_SHARED_CHUNK);
    size_t taken = __atomic_fetch_add(&area->cursor, want, __ATOMIC_ACQ_REL);
    if (want > ADAMAS_SHARED_BYTES || taken > ADAMAS_SHARED_BYTES - want) {
        adamas_fail("разделяемая область переполнена: ёмкость области фиксирована");
    }
    own->at = taken;
    own->edge = taken + want;
}

/* Сколько областей заведено с начала процесса: он же номер следующей.
 *
 * Атомарен, потому что заводить область вправе любой воркер; на витке укладки
 * не стоит - трогается он раз на область. */
static size_t born = 0;

adamas_value adamas_shared_new(void) {
    adamas_value area =
        (adamas_value)adamas_block_alloc(sizeof(adamas_shared) + ADAMAS_SHARED_BYTES);
    adamas_shared *head = (adamas_shared *)area;
    head->birth = __atomic_add_fetch(&born, 1, __ATOMIC_ACQ_REL);
    head->header.rc = 0;
    head->header.tag = ADAMAS_TAG_SHARED;
    /* Область рождается разделяемой: счётчик её обязан быть атомарным с первой
     * ссылки, а не с промоушена. Промоушен на границе `spawn` (§5.2) её всё
     * равно увидит - и остановится, потому что уже помечена. */
    head->header.flags = ADAMAS_FLAG_SHARED;
    head->cursor = 0;
    return area;
}

size_t adamas_shared_used(adamas_value area) {
    return __atomic_load_n(&area_of(area)->cursor, __ATOMIC_ACQUIRE);
}

adamas_value adamas_shared_alloc(adamas_value area, const void *bits, size_t size, size_t align) {
    adamas_shared *head = area_of(area);
    adamas_hand *own = handed(area);
    size_t bound = align == 0 ? 1 : align;
    adamas_cell *cell = vacant(own, size, bound);
    size_t at;
    if (cell != NULL) {
        cell->free = 0;
        own->frees -= 1;
        at = cell->at;
    } else {
        at = aligned(own->at, bound);
        if (size > own->edge || at > own->edge - size) {
            refill(head, own, size + bound);
            at = aligned(own->at, bound);
        }
        own->at = at + size;
        record(own, at, size);
    }
    memcpy(payload(area) + at, bits, size);
    own->last = at;
    /* Тождество: область не копируется ни при каком счётчике. Это и есть всё
     * различие с `adamas_region_alloc`. */
    return area;
}

adamas_value adamas_shared_recycle(adamas_value area, size_t at) {
    adamas_hand *own;
    adamas_cell *cell;
    (void)area_of(area);
    own = handed(area);
    cell = recorded(own, at);
    if (cell != NULL) {
        cell->free = 1;
        own->frees += 1;
    }
    return area;
}

adamas_value adamas_shared_pop(adamas_value area, size_t at) {
    adamas_hand *own;
    adamas_cell *cell;
    uint32_t top;
    (void)area_of(area);
    own = handed(area);
    if (own->cells == 0) {
        return area;
    }
    top = earlier(own->next);
    cell = &own->journal[top];
    /* Вершина - **своего** куска: у общей области вершины нет вовсе, и LIFO
     * поэтому воркерский. Не вершина оставляет область как есть - то же
     * наблюдаемое различие Pool и StackAlloc, что у обычной области. */
    if (cell->free || (size_t)cell->at != at || own->at != at + (size_t)cell->size) {
        return area;
    }
    own->at = at;
    own->next = top;
    own->cells -= 1;
    own->last = own->cells == 0 ? 0 : own->journal[earlier(own->next)].at;
    return area;
}

size_t adamas_shared_last(adamas_value area, adamas_release release) {
    size_t at;
    (void)area_of(area);
    at = handed(area)->last;
    adamas_drop(area, release);
    return at;
}

void adamas_shared_read(adamas_value area, size_t at, void *out, size_t size,
                        adamas_release release) {
    size_t given = adamas_shared_used(area);
    if (size > given || at > given - size) {
        adamas_fail("чтение разделяемой области за пределами розданного");
    }
    memcpy(out, payload(area) + at, size);
    adamas_drop(area, release);
}

adamas_value adamas_shared_write(adamas_value area, size_t at, const void *bits, size_t size) {
    size_t given = adamas_shared_used(area);
    if (size > given || at > given - size) {
        adamas_fail("запись в разделяемую область за пределами розданного");
    }
    /* Гонки **ячейки** здесь нет только потому, что её нет в программе: §3.6
     * обещает потокобезопасность аллокатора, а не нагрузки, и два воркера,
     * пишущие в один хендл, дают гонку данных. Это §10 вопрос 40, и закрывать
     * его рантайму нечем. */
    memcpy(payload(area) + at, bits, size);
    return area;
}

void adamas_shared_release(adamas_value area) {
    /* Детей у области нет: нагрузка плоская. Освобождает её `adamas_drop`
     * следом - одним `free` на всю область, как и обещано. */
    (void)area;
}
