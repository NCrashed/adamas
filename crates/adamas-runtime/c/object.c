/* Заголовок, аллокация, счётчик ссылок, переиспользование блока.
 *
 * Договор описан в `adamas.h`; здесь только то, что видно из реализации.
 */

#include "adamas.h"

#include <stdio.h>
#include <stdlib.h>

/* Счётчики блоков потоко-локальные - как и сам счётчик ссылок (§5.1:
 * неатомарные, куча локальна потоку). Общие врали бы там, где гонки нет.
 * Цена - две инкрементации рядом с `malloc`, которая дороже их на порядки. */
static _Thread_local size_t blocks_allocated = 0;
static _Thread_local size_t blocks_live = 0;

_Noreturn void adamas_fail(const char *message) {
    fprintf(stderr, "adamas: %s\n", message);
    abort();
}

void *adamas_block_alloc(size_t size) {
    void *block = malloc(size);
    if (block == NULL) {
        adamas_fail("куча исчерпана");
    }
    blocks_allocated += 1;
    blocks_live += 1;
    return block;
}

void adamas_block_free(void *block) {
    if (block == NULL) {
        return;
    }
    if (blocks_live == 0) {
        adamas_fail("освобождён блок, которого рантайм не выдавал");
    }
    blocks_live -= 1;
    free(block);
}

adamas_header *adamas_header_of(void *block) {
    /* Заголовок - первый член у объекта, замыкания, кадра, сегмента и вектора.
     * Обращение идёт через `void *`, а не приведением одной структуры к другой:
     * так тип, через который читают байты, совпадает с типом самого члена. */
    return (adamas_header *)block;
}

size_t adamas_stat_allocated(void) {
    return blocks_allocated;
}

size_t adamas_stat_live(void) {
    return blocks_live;
}

void adamas_stat_reset(void) {
    blocks_allocated = 0;
    blocks_live = 0;
}

/* ------------------------------------------------------------------ */
/* Непосредственные значения                                           */
/* ------------------------------------------------------------------ */

int adamas_is_imm(adamas_value value) {
    return ((uintptr_t)value & 1u) != 0u;
}

adamas_value adamas_imm(intptr_t number) {
    return (adamas_value)((((uintptr_t)number) << 1) | 1u);
}

intptr_t adamas_imm_get(adamas_value value) {
    /* Сдвиг знакового вправо арифметический у gcc, clang и msvc; на цели, где
     * это не так, здесь понадобится деление. */
    return ((intptr_t)value) >> 1;
}

adamas_value adamas_con0(uint16_t tag) {
    return adamas_imm((intptr_t)tag);
}

adamas_value adamas_unit(void) {
    return adamas_con0(0);
}

/* ------------------------------------------------------------------ */
/* Объекты                                                             */
/* ------------------------------------------------------------------ */

adamas_value adamas_alloc(uint16_t tag, size_t fields) {
    adamas_value object =
        (adamas_value)adamas_block_alloc(sizeof(adamas_header) + fields * sizeof(adamas_value));
    adamas_header *header = adamas_header_of(object);
    header->rc = 0;
    header->tag = tag;
    header->flags = 0;
    return object;
}

void adamas_free(adamas_value value) {
    if (adamas_is_imm(value)) {
        return;
    }
    adamas_block_free(value);
}

uint16_t adamas_tag(adamas_value value) {
    /* Одна функция на оба представления - ради этого нульарный конструктор и
     * сделан непосредственным: разбор не спрашивает, объект перед ним или нет. */
    if (adamas_is_imm(value)) {
        return (uint16_t)adamas_imm_get(value);
    }
    return adamas_header_of(value)->tag;
}

uint32_t adamas_rc(adamas_value value) {
    if (adamas_is_imm(value)) {
        return 0;
    }
    return adamas_header_of(value)->rc;
}

adamas_value adamas_dup(adamas_value value) {
    if (adamas_is_imm(value)) {
        return value;
    }
    /* Переполнение 32-битного счётчика не обрабатывается: 2^32 лишних ссылок на
     * один объект - не тот режим, который эта стадия обслуживает. */
    adamas_header_of(value)->rc += 1;
    return value;
}

int adamas_is_unique(adamas_value value) {
    if (adamas_is_imm(value)) {
        return 0;
    }
    return adamas_header_of(value)->rc == 0;
}

void adamas_drop(adamas_value value, adamas_release release) {
    if (adamas_is_imm(value)) {
        return;
    }
    adamas_header *header = adamas_header_of(value);
    if (header->rc == 0) {
        if (release != NULL) {
            release(value);
        }
        adamas_block_free(value);
        return;
    }
    header->rc -= 1;
}

adamas_value adamas_drop_reuse(adamas_value value, adamas_release release) {
    if (adamas_is_imm(value)) {
        return NULL;
    }
    adamas_header *header = adamas_header_of(value);
    if (header->rc == 0) {
        if (release != NULL) {
            release(value);
        }
        return value;
    }
    header->rc -= 1;
    return NULL;
}

adamas_value adamas_reuse(adamas_value block, uint16_t tag, size_t fields) {
    if (block == NULL) {
        return adamas_alloc(tag, fields);
    }
    /* Размер не проверяется: reuse срабатывает только при совпадении формы
     * конструкторов (§5.1), и это условие держит вставка Perceus. */
    (void)fields;
    adamas_header *header = adamas_header_of(block);
    header->rc = 0;
    header->tag = tag;
    header->flags = 0;
    return block;
}

adamas_value adamas_field(adamas_value value, size_t index) {
    return value->fields[index];
}

void adamas_set_field(adamas_value value, size_t index, adamas_value field) {
    value->fields[index] = field;
}
