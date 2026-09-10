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

void adamas_array_put(adamas_value array, size_t index, adamas_value value,
                      adamas_release release) {
    adamas_value *cell = slot(array, index);
    adamas_value displaced = *cell;
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

adamas_value adamas_array_writable(adamas_value array, adamas_release release) {
    if (adamas_is_unique(array)) {
        return array;
    }
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
