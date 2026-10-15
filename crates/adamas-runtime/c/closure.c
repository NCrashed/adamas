/* Замыкание: заголовок, статический указатель на код, захваченные поля.
 *
 * §5.3 требует, чтобы top-level без захватов отдавался голым C-указателем, а
 * замыкание со средой - трамплином плюс `userdata`. Здесь это выполнено по
 * построению: `adamas_closure_code` отдаёт первый, `adamas_apply` есть второй,
 * и `userdata` для него - само замыкание.
 *
 * Применение замыкание **потребляет** (волна 8 Фазы 9): насыщенное отдаётся
 * коду, и тот отпускает его, прочитав среду, - после вызова работы не остаётся,
 * и хвостовая позиция у применения есть. Частичное применение уникального
 * дописывает аргумент на месте, разделённого - копирует.
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
    /* Типизированный вход (§10 вопрос 192, срез 4 волны 8): `NULL` - его нет.
     * Прототип знают построивший и место вызова, рантайм его не читает. */
    void *typed;
    uint32_t arity;
    uint32_t applied;
    uint32_t captured;
    /* Сколько первых слотов среды считаются RC. Место прежнего выравнивающего
     * поля: раскладка от него не двигается, и `_Static_assert` ниже это ловит. */
    uint32_t counted;
    adamas_value slots[];
};

_Static_assert(offsetof(struct closure_block, slots) == 48, "closure slots start at byte 48");

static struct closure_block *closure_of(adamas_value value) {
    if (adamas_is_imm(value) || adamas_tag(value) != ADAMAS_TAG_CLOSURE) {
        adamas_fail("application to a non-closure");
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
        adamas_fail("closure without code");
    }
    if (arity == 0) {
        adamas_fail("a closure is never nullary");
    }
    if (counted > captured) {
        adamas_fail("more counted environment slots than slots");
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
    block->typed = NULL;
    block->arity = arity;
    block->applied = 0;
    block->captured = captured;
    block->counted = counted;
    return value;
}

void adamas_closure_set(adamas_value closure, size_t index, adamas_value field) {
    struct closure_block *block = closure_of(closure);
    if (index >= slot_count(block)) {
        adamas_fail("closure slot out of bounds");
    }
    block->slots[index] = field;
}

adamas_value adamas_closure_get(adamas_value closure, size_t index) {
    struct closure_block *block = closure_of(closure);
    if (index >= slot_count(block)) {
        adamas_fail("closure slot out of bounds");
    }
    return block->slots[index];
}

void adamas_closure_set_typed(adamas_value closure, void *entry) {
    closure_of(closure)->typed = entry;
}

/* Вход отдаётся только целому замыканию и только на полный набор: частичное
 * применение копирует блок без входа, а иная арность значит иной прототип.
 * Тип места вызова от этого не страдает - он тот же, что у построившего.
 *
 * Значение стрелочного типа бывает и не замыканием: резумпция применяется
 * значением (`adamas_apply`, ветка `SEGMENT`). Входа у неё нет, и путь ей -
 * обобщённый. */
void *adamas_closure_entry(adamas_value closure, uint32_t count) {
    if (adamas_is_imm(closure) || adamas_tag(closure) != ADAMAS_TAG_CLOSURE) {
        return NULL;
    }
    struct closure_block *block = closure_of(closure);
    if (block->typed == NULL || block->applied != 0 || block->arity != count) {
        return NULL;
    }
    return block->typed;
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
    /* Резумпция значением (§3.4, §10 вопрос 249): применённая там, где тип её
     * не называет (`advance (Suspended k) = k ()`), она приходит сюда, а не в
     * `Resume`. Делается то же, что там: сегмент встаёт на вершину, а значение
     * операции уходит трамплину - его получит верхний кадр сегмента. Ответ
     * возобновлённого вычисления спустится до кадра под сегментом, то есть до
     * продолжения вызывающего: `Apply` - точка приостановки всегда. */
    if (!adamas_is_imm(closure) && adamas_tag(closure) == ADAMAS_TAG_SEGMENT) {
        adamas_kont_resume(kont, closure);
        /* Ручка уходит владением, как всякое вызываемое: возобновлённая - уже
         * потрачена, и дроп отдаёт один блок. */
        adamas_resumption_drop(kont, closure);
        return argument;
    }
    struct closure_block *block = closure_of(closure);
    if (block->applied + 1 == block->arity) {
        /* Замыкание уходит коду владением (волна 8 Фазы 9): тот читает среду и
         * отдаёт его до своей работы, и после вызова здесь делать нечего - это
         * и освобождает хвостовую позицию у применения. */
        return block->code(closure, evidence, kont, argument);
    }
    /* Частичное применение. Уникальное замыкание дописывается на месте - его
     * никто больше не видит, и копия была бы выдачей ради выброса. */
    if (adamas_is_unique(closure)) {
        block->slots[(size_t)block->captured + (size_t)block->applied] = argument;
        block->applied += 1;
        return closure;
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
    /* Разделённое: своя ссылка отдаётся. Последней она может оказаться и здесь
     * - сосед с другого потока успел отдать свою, - поэтому `release` свой. */
    adamas_drop(closure, block->release);
    return copy;
}
