/* Чужая библиотека свидетеля границы Adamas-C (§5.3, уровень 1).
 *
 * Про Adamas она не знает **ничего**: ни заголовка рантайма, ни его типов, ни
 * счётчика ячеек. Память берёт своим `malloc` - мимо кучи Perceus, - и ровно
 * поэтому число живых блоков у прогона остаётся нулём: чужая аллокация нашим
 * счётчиком не считается, а наша сторона на границе не аллоцирует вовсе.
 *
 * Четыре символа - четыре формы границы, какие берёт уровень 1: два слова
 * аргументами, ни одного аргумента, чужой указатель в обе стороны и `void`
 * ответом.
 */

#include <stdint.h>
#include <stdlib.h>

/* Сколько раз через границу ходили. Свёрнут счётчик в ответ программы, поэтому
 * вызов, потерянный понижением, меняет **ответ**, а не молчит. */
static uint64_t crossings = 0;

uint64_t adamas_probe_mix(uint64_t x, uint64_t y) {
    crossings += 1;
    return x * 3 + y;
}

uint64_t adamas_probe_crossings(void) {
    crossings += 1;
    return crossings;
}

uint64_t adamas_probe_alloc(uint64_t payload) {
    crossings += 1;
    uint64_t *cell = malloc(sizeof *cell);
    if (cell == NULL) {
        abort();
    }
    *cell = payload;
    return (uint64_t)(uintptr_t)cell;
}

uint64_t adamas_probe_read(uint64_t address) {
    crossings += 1;
    return *(uint64_t *)(uintptr_t)address;
}

void adamas_probe_free(uint64_t address) {
    crossings += 1;
    free((void *)(uintptr_t)address);
}
