/* Регион: одна область на любое число значений (§3.6).
 *
 * Договор описан в `adamas.h`; здесь только то, что видно из реализации.
 */

#include "adamas.h"

#include <string.h>

/* Начало полезной нагрузки - байты, а не слоты: нагрузка региона плоская по
 * построению (`{Flat a}`, §3.6), и заголовков внутри неё нет. */
static char *payload(adamas_value region) {
    return (char *)region + sizeof(adamas_region);
}

static adamas_region *header_of(adamas_value region) {
    if (adamas_tag(region) != ADAMAS_TAG_REGION) {
        adamas_fail("операция региона над не-регионом");
    }
    return (adamas_region *)region;
}

/* Ячейка журнала по номеру. Журнал растёт от конца области вниз: нулевая
 * запись лежит последними байтами, первая - перед ней. */
static adamas_cell *cell_at(adamas_value region, size_t index) {
    char *end = payload(region) + ADAMAS_REGION_BYTES;
    return (adamas_cell *)(void *)(end - (index + 1) * sizeof(adamas_cell));
}

/* Ближайшее сверху кратное `align`. То же правило, что у типовой стороны
 * (`adamas-elab/src/flat.rs`) и у машины (`adamas-core/src/eval.rs`): три
 * счёта одного смещения обязаны сойтись, иначе хендл поведёт не туда. */
static size_t aligned(size_t offset, size_t align) {
    size_t bound = align == 0 ? 1 : align;
    size_t slack = offset % bound;
    return slack == 0 ? offset : offset + (bound - slack);
}

adamas_value adamas_region_new(void) {
    adamas_value region =
        (adamas_value)adamas_block_alloc(sizeof(adamas_region) + ADAMAS_REGION_BYTES);
    adamas_region *head = (adamas_region *)region;
    head->header.rc = 0;
    head->header.tag = ADAMAS_TAG_REGION;
    head->header.flags = 0;
    head->used = 0;
    head->last = 0;
    head->cells = 0;
    return region;
}

size_t adamas_region_used(adamas_value region) {
    return header_of(region)->used;
}

/* Область, готовая к записи. Тот же договор, что у `adamas_array_writable`:
 * уникальность спрашивается у рантайма (`rc == 0`), разделённая копируется
 * целиком - вместе с курсором и журналом, иначе хендлы прежних аллокаций
 * указывали бы в копии не туда. */
static adamas_value writable(adamas_value region) {
    adamas_region *head = header_of(region);
    adamas_value copy;
    adamas_region *made;
    if (adamas_is_unique(region)) {
        return region;
    }
    copy = adamas_region_new();
    made = (adamas_region *)copy;
    made->used = head->used;
    made->last = head->last;
    made->cells = head->cells;
    /* Оба конца области: нагрузка снизу, журнал сверху. */
    memcpy(payload(copy), payload(region), head->used);
    if (head->cells > 0) {
        memcpy(cell_at(copy, head->cells - 1), cell_at(region, head->cells - 1),
               head->cells * sizeof(adamas_cell));
    }
    adamas_drop(region, adamas_region_release);
    return copy;
}

adamas_value adamas_region_alloc(adamas_value region, const void *bits, size_t size,
                                 size_t align) {
    adamas_value made = writable(region);
    adamas_region *head = (adamas_region *)made;
    size_t bound = align == 0 ? 1 : align;
    size_t index = head->cells;
    size_t at;
    adamas_cell *cell = NULL;
    /* Свободная ячейка равного размера - самая поздняя по размещению. */
    while (index-- > 0) {
        adamas_cell *found = cell_at(made, index);
        if (found->free && found->size == size && found->at % bound == 0) {
            cell = found;
            break;
        }
    }
    if (cell != NULL) {
        cell->free = 0;
        at = cell->at;
    } else {
        at = aligned(head->used, align);
        if (size > ADAMAS_REGION_BYTES || at > ADAMAS_REGION_BYTES - size
            || at + size + (head->cells + 1) * sizeof(adamas_cell) > ADAMAS_REGION_BYTES) {
            /* Роста области здесь нет: `AllocStrategy` §3.6 такого метода не
             * называет, и молчаливый рост означал бы вторую аллокацию там, где
             * обещана одна. */
            adamas_fail("регион переполнен: ёмкость области фиксирована");
        }
        cell = cell_at(made, head->cells);
        cell->at = (uint32_t)at;
        cell->size = (uint32_t)size;
        cell->free = 0;
        head->cells += 1;
        head->used = at + size;
    }
    memcpy(payload(made) + at, bits, size);
    head->last = at;
    return made;
}

adamas_value adamas_region_recycle(adamas_value region, size_t at) {
    adamas_value made = writable(region);
    adamas_region *head = (adamas_region *)made;
    size_t index = head->cells;
    while (index-- > 0) {
        adamas_cell *cell = cell_at(made, index);
        if (!cell->free && cell->at == at) {
            cell->free = 1;
            break;
        }
    }
    return made;
}

adamas_value adamas_region_pop(adamas_value region, size_t at) {
    adamas_value made = writable(region);
    adamas_region *head = (adamas_region *)made;
    adamas_cell *top;
    if (head->cells == 0) {
        return made;
    }
    top = cell_at(made, head->cells - 1);
    if (top->free || top->at != at) {
        /* Не вершина - LIFO не срабатывает, и область остаётся как есть.
         * Ровно этим StackAlloc отличается от Pool наблюдаемо. */
        return made;
    }
    head->cells -= 1;
    head->used = at;
    head->last = head->cells == 0 ? 0 : cell_at(made, head->cells - 1)->at;
    return made;
}

size_t adamas_region_last(adamas_value region, adamas_release release) {
    size_t at = header_of(region)->last;
    adamas_drop(region, release);
    return at;
}

void adamas_region_read(adamas_value region, size_t at, void *out, size_t size,
                        adamas_release release) {
    adamas_region *head = header_of(region);
    if (size > head->used || at > head->used - size) {
        adamas_fail("чтение региона за пределами занятого");
    }
    memcpy(out, payload(region) + at, size);
    adamas_drop(region, release);
}

adamas_value adamas_region_write(adamas_value region, size_t at, const void *bits,
                                 size_t size) {
    adamas_value made = writable(region);
    adamas_region *head = (adamas_region *)made;
    if (size > head->used || at > head->used - size) {
        adamas_fail("запись в регион за пределами занятого");
    }
    memcpy(payload(made) + at, bits, size);
    /* Курсор не двигается: `write` §3.6 - операция над уже размещённым местом.
     */
    return made;
}

void adamas_region_release(adamas_value region) {
    /* Детей у области нет вовсе: нагрузка плоская (§3.6), заголовков внутри
     * нет, и освобождение всей области - это `free` её единственного блока,
     * который делает `adamas_drop` следом. */
    (void)region;
}
