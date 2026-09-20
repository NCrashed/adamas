/* Точка входа стенда границы - одна на **оба** понижения.
 *
 * C-уклады (`entry.c`) и текстовые `.ll`-уклады (`boxed.ll`, `imm.ll`,
 * `flat.ll`) определяют одну и ту же функцию `adamas_entry`, а печатает за них
 * этот файл. Общая точка входа здесь не удобство, а условие годности замера:
 * разойдись печать у двух сторон - и разошёлся бы ответ, которым стороны
 * сверяются.
 *
 * Счётчики печатаются **той же строкой**, что и у порождённых программ
 * (`crates/adamas-codegen/src/main.c`), потому что читает их та же заготовка
 * (`harness::blocks`), и третье число в stderr её роняет.
 *
 * Число вызовов приходит аргументом, а не `-D`: константа дала бы компилятору
 * право развернуть цикл и посчитать его целиком, и стенд померил бы
 * свёртывание.
 */

#include "adamas.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t adamas_entry(uint64_t calls);

int main(int argc, char **argv) {
    unsigned long long calls;
    if (argc != 2) {
        fprintf(stderr, "стенд границы: нужен один аргумент - число вызовов\n");
        return 2;
    }
    calls = strtoull(argv[1], NULL, 10);
    printf("%llu\n", (unsigned long long)adamas_entry((uint64_t)calls));
    fprintf(stderr, "блоков выдано %zu, живо %zu\n", adamas_stat_allocated_everywhere(),
            adamas_stat_live_everywhere());
    return 0;
}
