/* Массив: один объект кучи на всю длину (§4.11).
 *
 * Договор описан в `adamas.h`; здесь только то, что видно из реализации.
 */

#include "adamas.h"

#include <string.h>

/* Начало полезной нагрузки. Через `char *`, а не через член структуры: у
 * плоского массива там байты, у указательного - слоты, и одного типа на оба
 * нет. */
static char *payload(adamas_value array) {
    return (char *)array + sizeof(adamas_array);
}

static adamas_array *header_of(adamas_value array) {
    return (adamas_array *)array;
}

adamas_value adamas_array_alloc(size_t count, size_t stride) {
    size_t cells = stride == 0 ? sizeof(adamas_value) : stride;
    /* Переполнение произведения обрывает процесс: молчаливая обёртка дала бы
     * блок короче запрошенного, то есть запись мимо него. */
    if (count != 0 && cells > (SIZE_MAX - sizeof(adamas_array)) / count) {
        adamas_fail("массив длиннее адресного пространства");
    }
    adamas_value array =
        (adamas_value)adamas_block_alloc(sizeof(adamas_array) + count * cells);
    adamas_array *head = header_of(array);
    head->header.rc = 0;
    head->header.tag = ADAMAS_TAG_ARRAY;
    head->header.flags = 0;
    head->count = count;
    head->stride = stride;
    return array;
}

size_t adamas_array_count(adamas_value array) {
    return header_of(array)->count;
}

size_t adamas_array_stride(adamas_value array) {
    return header_of(array)->stride;
}

void *adamas_array_at(adamas_value array, size_t index) {
    adamas_array *head = header_of(array);
    if (index >= head->count) {
        adamas_fail("номер ячейки вне длины массива");
    }
    if (head->stride == 0) {
        adamas_fail("плоская ячейка спрошена у указательного массива");
    }
    return payload(array) + index * head->stride;
}

/* Слот указательного массива. Проверки те же и по той же причине. */
static adamas_value *slot(adamas_value array, size_t index) {
    adamas_array *head = header_of(array);
    if (index >= head->count) {
        adamas_fail("номер ячейки вне длины массива");
    }
    if (head->stride != 0) {
        adamas_fail("слот спрошен у плоского массива");
    }
    adamas_value *slots = (adamas_value *)(void *)payload(array);
    return slots + index;
}

adamas_value adamas_array_get(adamas_value array, size_t index) {
    return *slot(array, index);
}

void adamas_array_init(adamas_value array, size_t index, adamas_value value) {
    *slot(array, index) = value;
}

/* Разделённый массив, которому переписывают ячейку: холодная половина.
 *
 * Вынесена по тому же правилу, что и `copied`, и по тому же замеру: на горячем
 * витке пометки нет ни разу, а тело её обработки делает функцию крупнее. */
__attribute__((noinline, cold)) static void localised(adamas_value array) {
    if (!adamas_is_unique(array)) {
        /* Владелец не один: снять пометку нельзя - другой поток держит тот же
         * массив, - а положить в него локального постояльца тем более. В
         * порождённом коде сюда не попасть (`adamas_array_writable` разделённый
         * копирует), поэтому это отказ, а не ветка. */
        adamas_fail("запись в разделённый массив мимо `adamas_array_writable` (§5.2)");
    }
    adamas_header_of(array)->flags = 0;
}

void adamas_array_put(adamas_value array, size_t index, adamas_value value,
                      adamas_release release) {
    adamas_value *cell = slot(array, index);
    adamas_value displaced = *cell;
    /* **Здесь закрывается граница, названная §5.2**: «запись в уже разделённый
     * объект обходом второй раз не покрывается».
     *
     * Ячейка указательного массива - единственное место, где она достижима.
     * Поля конструктора пишутся при постройке, когда объект ещё локален, а
     * `adamas_reuse` пометку снимает; ячейку же переписывают когда угодно.
     * Разделённый массив с локальным постояльцем в слоте и есть та дыра:
     * второй `adamas_share` увидел бы пометку на самом массиве, остановился и
     * до нового ребёнка не дошёл.
     *
     * Снимается пометка тем же доводом, каким её снимает `adamas_reuse`:
     * `rc == 0` значит, что владелец один, - достаться массив никому не может.
     * Локальным он и становится, пока его снова не разделят; разделят - обход
     * пройдёт по новым детям.
     *
     * *Место выбрано замером, а не вкусом.* Первая редакция снимала пометку в
     * `adamas_array_writable`, то есть на **общем** пути записи, - и колонная
     * строка 4а таблицы разрыва замедлилась в **1.497 раза** (два независимых
     * парных замера дали 1.4974 и 1.4984; пол девяти чередующихся прогонов в
     * одном окне, потому что тихой машины не было). Тот же жанр, что нашёл
     * трек B волны 3 Фазы 7: лишний код в точке входа переворачивает решение
     * инлайнера. Здесь его нет вовсе - плоский массив идёт через
     * `adamas_array_at` и до `adamas_array_put` не доходит, - и тот же парный
     * замер дал **1.021** и **0.998**, то есть ноль в пределах разброса окна.
     *
     * Плоскому массиву граница и не нужна: заголовков у ячеек нет (§4.11),
     * значит нет и детей, которых обход мог бы не пометить. */
    if (adamas_header_of(array)->flags != 0) {
        localised(array);
    }
    *cell = value;
    adamas_drop(displaced, release);
}

void adamas_array_fill(adamas_value array, adamas_value value, adamas_release release) {
    adamas_array *head = header_of(array);
    size_t index;
    if (head->stride != 0) {
        adamas_fail("указательное заполнение плоского массива");
    }
    for (index = 0; index < head->count; index += 1) {
        adamas_array_init(array, index, adamas_dup(value));
    }
    /* Значение пришло владением, а ссылок роздано `count`: своя отдаётся. При
     * нулевой длине это единственное, что происходит, - и происходит верно. */
    adamas_drop(value, release);
}

void adamas_array_fill_flat(adamas_value array, const void *bits) {
    adamas_array *head = header_of(array);
    size_t index;
    if (head->stride == 0) {
        adamas_fail("плоское заполнение указательного массива");
    }
    for (index = 0; index < head->count; index += 1) {
        memcpy(payload(array) + index * head->stride, bits, head->stride);
    }
}

adamas_value adamas_array_take(adamas_value array, size_t index, adamas_release release) {
    adamas_value taken = adamas_dup(adamas_array_get(array, index));
    adamas_drop(array, release);
    return taken;
}

void adamas_array_read(adamas_value array, size_t index, void *out, adamas_release release) {
    memcpy(out, adamas_array_at(array, index), header_of(array)->stride);
    adamas_drop(array, release);
}

/* Копия разделённого массива: холодная половина `adamas_array_writable`.
 *
 * Вынесена по тому же правилу и тем же замером, каким вынесена разделяемая
 * половина счётчика (`object.c`, `ADAMAS_SHARED_HALF`, §10 вопрос 175): на
 * горячем витке §4.11 `arraySet` уникален всегда, копия не случается ни разу,
 * а её тело - аллокация, цикл и `memcpy` - делает функцию слишком крупной для
 * инлайнинга целиком.
 *
 * До выноса деление делал **сам компилятор, и только один из двух**: gcc
 * разбивал функцию частичным инлайнингом (`adamas_array_writable.part.0`),
 * конвейер LLVM - нет, потому что `PartialInlinerPass` в его `-O2` по
 * умолчанию выключен. Стоило это строке 4а таблицы разрыва 1.757 против
 * C-бэкенда; замер - в отчёте трека B волны 3 Фазы 7. То есть строка мерила не
 * качество бэкендов, а наличие одного паса у одного из них.
 *
 * `cold` здесь не украшение к `noinline`: он метит место вызова
 * маловероятным, и горячая половина остаётся в прямом пути. */
__attribute__((noinline, cold)) static adamas_value copied(adamas_value array,
                                                           adamas_release release) {
    adamas_array *head = header_of(array);
    adamas_value copy = adamas_array_alloc(head->count, head->stride);
    if (head->stride == 0) {
        size_t index;
        for (index = 0; index < head->count; index += 1) {
            adamas_array_init(copy, index, adamas_dup(adamas_array_get(array, index)));
        }
    } else {
        memcpy(payload(copy), payload(array), head->count * head->stride);
    }
    adamas_drop(array, release);
    return copy;
}

adamas_value adamas_array_writable(adamas_value array, adamas_release release) {
    /* Пометка разделяемости снимается **не здесь**, а в `adamas_array_put`, и
     * это измерено: лишняя ветвь на общем пути записи стоила колонной строке
     * 4а 1.497 раза. Довод и замер - там же. */
    if (adamas_is_unique(array)) {
        return array;
    }
    return copied(array, release);
}

void adamas_array_promote(adamas_value array, adamas_promote children) {
    adamas_array *head = header_of(array);
    size_t index;
    if (head->stride != 0) {
        /* Плоские ячейки заголовков не имеют вовсе (§4.11): метить нечего. */
        return;
    }
    for (index = 0; index < head->count; index += 1) {
        adamas_share(adamas_array_get(array, index), children);
    }
}

void adamas_array_release(adamas_value array, adamas_release release) {
    adamas_array *head = header_of(array);
    size_t index;
    if (head->stride != 0) {
        /* Плоские ячейки заголовков не имеют вовсе (§4.11): дропать нечего. */
        return;
    }
    for (index = 0; index < head->count; index += 1) {
        adamas_drop(adamas_array_get(array, index), release);
    }
}
