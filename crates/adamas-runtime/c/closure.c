/* Замыкание: заголовок, статический указатель на код, захваченные поля.
 *
 * §5.3 требует, чтобы top-level без захватов отдавался голым C-указателем, а
 * замыкание со средой - трамплином плюс `userdata`. Здесь это выполнено по
 * построению: `adamas_closure_code` отдаёт первый, `adamas_apply` есть второй,
 * и `userdata` для него - само замыкание.
 *
 * Частичное применение копирует замыкание, а не дописывает аргумент на месте:
 * исходное могло быть разделено. Уникальное можно было бы переписать, и это
 * ровно тот же reuse, что у данных, - вставляет его Perceus, поэтому здесь
 * такого пути нет.
 *
 * Слот среды **разнороден** (§4.11, §10 вопрос 158, пересмотр 2026-09-22):
 * плоское значение лежит в нём битами. Границу проводит префикс `counted` -
 * тот же механизм, что у кадра продолжения, - и полос от этого две: среда с
 * префиксом и накопленные аргументы, считающиеся всегда. Подробности и довод
 * против таблицы сортов - в шапке `adamas.h`.
 */

#include "adamas.h"

struct closure_block {
    adamas_header header;
    adamas_code code;
    adamas_release release;
    uint32_t arity;
    uint32_t applied;
    uint32_t captured;
    /* Сколько первых слотов среды считаются RC. Место прежнего выравнивающего
     * поля: раскладка от него не двигается, и `_Static_assert` ниже это ловит. */
    uint32_t counted;
    adamas_value slots[];
};

_Static_assert(offsetof(struct closure_block, slots) == 40, "слоты замыкания идут с 40-го байта");

static struct closure_block *closure_of(adamas_value value) {
    if (adamas_is_imm(value) || adamas_tag(value) != ADAMAS_TAG_CLOSURE) {
        adamas_fail("применение не к замыканию");
    }
    return (struct closure_block *)(void *)value;
}

/* Слотов у замыкания: среда плюс место под накопленные аргументы. Последний
 * аргумент передаётся напрямую в код и слота не занимает. */
static size_t slot_count(const struct closure_block *block) {
    return (size_t)block->captured + (size_t)block->arity - 1;
}

adamas_value adamas_closure(adamas_code code, adamas_release release, uint32_t arity,
                            uint32_t captured, uint32_t counted) {
    if (code == NULL) {
        adamas_fail("замыкание без кода");
    }
    if (arity == 0) {
        adamas_fail("замыкание нульместным не бывает");
    }
    if (counted > captured) {
        adamas_fail("счётных слотов среды больше, чем самих слотов");
    }
    size_t slots = (size_t)captured + (size_t)arity - 1;
    adamas_value value = (adamas_value)adamas_block_alloc(sizeof(struct closure_block) +
                                                          slots * sizeof(adamas_value));
    adamas_header *header = adamas_header_of(value);
    header->rc = 0;
    header->tag = ADAMAS_TAG_CLOSURE;
    header->flags = 0;
    struct closure_block *block = (struct closure_block *)(void *)value;
    block->code = code;
    block->release = release;
    block->arity = arity;
    block->applied = 0;
    block->captured = captured;
    block->counted = counted;
    return value;
}

void adamas_closure_set(adamas_value closure, size_t index, adamas_value field) {
    struct closure_block *block = closure_of(closure);
    if (index >= slot_count(block)) {
        adamas_fail("слот замыкания за его пределами");
    }
    block->slots[index] = field;
}

adamas_value adamas_closure_get(adamas_value closure, size_t index) {
    struct closure_block *block = closure_of(closure);
    if (index >= slot_count(block)) {
        adamas_fail("слот замыкания за его пределами");
    }
    return block->slots[index];
}

adamas_code adamas_closure_code(adamas_value closure) {
    return closure_of(closure)->code;
}

uint32_t adamas_closure_missing(adamas_value closure) {
    struct closure_block *block = closure_of(closure);
    return block->arity - block->applied;
}

size_t adamas_closure_taken(adamas_value closure) {
    struct closure_block *block = closure_of(closure);
    return (size_t)block->captured + (size_t)block->applied;
}

/* Он же по блоку: частичное применение спрашивает это в цикле и повторного
 * разбора значения не хочет. */
static int slot_counted(const struct closure_block *block, size_t index) {
    if (index >= (size_t)block->captured) {
        return 1;
    }
    return index < (size_t)block->counted;
}

int adamas_closure_slot_counted(adamas_value closure, size_t index) {
    return slot_counted(closure_of(closure), index);
}

void adamas_closure_release(adamas_value closure) {
    struct closure_block *block = closure_of(closure);
    if (block->release != NULL) {
        block->release(closure);
    }
}

adamas_value adamas_apply(adamas_value closure, const adamas_evidence *evidence, adamas_kont *kont,
                          adamas_value argument) {
    struct closure_block *block = closure_of(closure);
    if (block->applied + 1 == block->arity) {
        return block->code(closure, evidence, kont, argument);
    }
    adamas_value copy = adamas_closure(block->code, block->release, block->arity, block->captured,
                                       block->counted);
    struct closure_block *fresh = (struct closure_block *)(void *)copy;
    fresh->applied = block->applied + 1;
    /* Занятые слоты у обоих общие - отсюда `dup`. Свежий аргумент приходит
     * владением и дублирования не требует.
     *
     * Плоский слот среды дублировать нечем: в нём лежат биты числа, счётчика у
     * них нет, и `adamas_dup` по чётному значению правил бы заголовок по адресу
     * этого числа. Копия его переносит как есть. */
    size_t taken = (size_t)block->captured + (size_t)block->applied;
    for (size_t index = 0; index < taken; index += 1) {
        fresh->slots[index] = slot_counted(block, index) ? adamas_dup(block->slots[index])
                                                         : block->slots[index];
    }
    fresh->slots[taken] = argument;
    return copy;
}
