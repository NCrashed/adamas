/* Уклады чужого указателя: три развилки трека A, четыре уклада.
 *
 * Четыре, а не три, потому что развилка (а) распадается надвое - коробка на
 * каждое пересечение против коробки, живущей полем `resource`, - и цена у
 * половин разная в разы.
 *
 * Пишутся они **диалектом C-эмиттера** (`crates/adamas-codegen/src/emit_c.rs`):
 * те же имена рантайма, тот же порядок - выдать блок, записать слот, прочесть
 * слот, отдать блок. Узла IR под внешний вызов сегодня нет вовсе (его заводит
 * трек B), поэтому граница написана здесь руками; в обход поверхностного языка,
 * как и просит постановка трека.
 *
 * Уклад выбирается `-DSHAPE=`:
 *
 *   1 BOXED - (а) однополевой объект под RC **на каждое пересечение**;
 *   2 HELD  - (а) же, но коробка одна на весь прогон: идиома `resource`;
 *   3 IMM   - (б) сдвинутое непосредственное `(p << 1) | 1`;
 *   4 FLAT  - (в) плоское слово, `adamas_value` не становящееся никогда.
 *
 * Ответ у всех четырёх обязан совпасть до бита, и в него свёрнуто число
 * вызовов самой чужой функции (`adamas_probe_calls`): уклад, сходивший за
 * границу не столько раз, сколько прочие, отвечает иначе, а не «тоже верно».
 *
 * Пятый номер - **не уклад, а точка разложения**:
 *
 *   5 NONE  - тот же цикл, не ходящий за границу вовсе.
 *
 * Отвечает она на то, какая доля наносекунды принадлежит непрозрачному вызову,
 * а какая - самому представлению. Ответ у неё поэтому **другой**, и в сверку
 * четырёх она не входит; берёт её только таблица стенда. Прецедент -
 * `-DKERNEL_SCALAR=1` у соседа капстоуна (`benches/neighbour/packets.c`).
 */

#include "adamas.h"

#include <stdint.h>

#define SHAPE_BOXED 1
#define SHAPE_HELD 2
#define SHAPE_IMM 3
#define SHAPE_FLAT 4
#define SHAPE_NONE 5

#ifndef SHAPE
#error "уклад выбирается -DSHAPE=1..5; без него стенд мерил бы неизвестно что"
#endif

/* Тег коробки уклада (а).
 *
 * `0xFFF7` - первое свободное значение под занятыми рантаймом
 * (`ADAMAS_TAG_SHARED` 0xFFF8 - младшее из них, `ADAMAS_TAG_CLOSURE` 0xFFFF -
 * старшее, плюс 0xFFFC под стёртое у C-эмиттера). В `adamas.h` оно **не
 * вносится**: тег, отведённый ради замера, обязательства рантайма не создаёт, а
 * запись в заголовок пережила бы решение, которое замер как раз и готовит.
 */
#define STAND_TAG_FOREIGN 0xFFF7u

/* Зерно чужого объекта. Значение роли не играет - лишь бы одно на все уклады. */
#define STAND_SEED UINT64_C(2654435761)

void *adamas_probe_open(uint64_t seed);
uint64_t adamas_probe_step(void *handle, uint64_t salt);
uint64_t adamas_probe_calls(void *handle);
void adamas_probe_close(void *handle);

uint64_t adamas_entry(uint64_t calls);

uint64_t adamas_entry(uint64_t calls) {
    void *handle = adamas_probe_open(STAND_SEED);
    uint64_t acc = 0;
    uint64_t i;

#if SHAPE == SHAPE_BOXED
    /* (а) Коробка на каждое пересечение: выдать блок, записать чужой адрес
     * слотом, прочесть его обратно, отдать блок. Деструктор пуст - `NULL`
     * вместо `release`: чужую память освобождает `resource`, а не RC, и обход
     * детей по этому слоту читал бы заголовок по чужому адресу. */
    for (i = 0; i < calls; i += 1) {
        adamas_value box = adamas_alloc(STAND_TAG_FOREIGN, 1);
        void *back;
        adamas_set_field(box, 0, (adamas_value)handle);
        back = (void *)adamas_field(box, 0);
        acc ^= adamas_probe_step(back, i);
        adamas_drop(box, NULL);
    }
#elif SHAPE == SHAPE_HELD
    /* (а) же, но коробка одна: так выглядит `resource CBuffer`, у которого
     * чужой указатель лежит полем, а границу пересекает чтение слота. */
    {
        adamas_value box = adamas_alloc(STAND_TAG_FOREIGN, 1);
        adamas_set_field(box, 0, (adamas_value)handle);
        for (i = 0; i < calls; i += 1) {
            void *back = (void *)adamas_field(box, 0);
            acc ^= adamas_probe_step(back, i);
        }
        adamas_drop(box, NULL);
    }
#elif SHAPE == SHAPE_IMM
    /* (б) Сдвинутое непосредственное. `adamas_imm` есть ровно `(p << 1) | 1`,
     * `adamas_imm_get` - арифметический сдвиг вправо. Ячеек не выдаётся ни
     * одной; `adamas_drop` по непосредственному - проверка младшего бита. */
    for (i = 0; i < calls; i += 1) {
        adamas_value value = adamas_imm((intptr_t)(uintptr_t)handle);
        void *back = (void *)(uintptr_t)adamas_imm_get(value);
        acc ^= adamas_probe_step(back, i);
        adamas_drop(value, NULL);
    }
#elif SHAPE == SHAPE_FLAT
    /* (в) Плоское слово: `adamas_value` чужой указатель не становится вовсе,
     * живёт регистром и слотом по значению - тем же разрядом, каким живёт
     * `UInt64` (`Repr::Flat`, `crates/adamas-codegen/src/ir.rs`). Ни тега, ни
     * заголовка, ни счётчика; отдавать нечего. */
    for (i = 0; i < calls; i += 1) {
        uint64_t bits = (uint64_t)(uintptr_t)handle;
        void *back = (void *)(uintptr_t)bits;
        acc ^= adamas_probe_step(back, i);
    }
#elif SHAPE == SHAPE_NONE
    /* Точка разложения: за границу не ходим ни разу, работа та же по форме.
     * Разность с самым дешёвым укладом и есть цена непрозрачного вызова. */
    for (i = 0; i < calls; i += 1) {
        acc ^= i;
    }
#else
#error "SHAPE вне 1..5"
#endif

    acc ^= adamas_probe_calls(handle);
    adamas_probe_close(handle);
    return acc;
}
