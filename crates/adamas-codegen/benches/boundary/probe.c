/* Чужая библиотека стенда: сишный объект, которого Adamas не создавал.
 *
 * Тривиальная функция, зовущаяся в цикле через границу (трек A волны 1
 * Фазы 8). Единица трансляции собирается **без** `-flto`, потому что настоящая
 * чужая библиотека лежит отдельным объектом и непрозрачна по построению.
 *
 * Довод «иначе померили бы инлайнинг» **проверен и не подтвердился**: та же
 * единица, собранная `-flto` вместе с программой, даёт 6.74 / 1.03 / 1.01 /
 * 0.27 нс против 7.00 / 0.93 / 0.91 / 0.23 без него, то есть внутри разброса
 * между прогонами. `gcc` тело не разворачивает и так. Флаг снят ради того,
 * чтобы стенд моделировал настоящую библиотеку, а не ради числа.
 *
 * Куча здесь **своя**, `malloc` из libc: счётчик блоков рантайма
 * (`adamas_stat_allocated_everywhere`) обязан считать ровно те ячейки, что
 * выдал сам укладу под чужой указатель, и ни одной сверх. Открытие и закрытие
 * стоят по одной ячейке libc на весь прогон и в счётчик не попадают вовсе -
 * это и делает столбец «аллокаций на вызов» читаемым.
 *
 * Работа внутри не нулевая намеренно: шаг переписывает поле и отвечает
 * зависящим от него словом, поэтому вызов не мёртв и удалить его нечем.
 */

#include <stdint.h>
#include <stdlib.h>

struct adamas_probe {
    uint64_t seed;
    uint64_t calls;
};

/* Множитель PCG/`splitmix`-семейства: одно умножение и одно сложение - чтобы
 * работа была, но не заслоняла собой цену границы. */
#define PROBE_SPICE UINT64_C(6364136223846793005)

void *adamas_probe_open(uint64_t seed);
uint64_t adamas_probe_step(void *handle, uint64_t salt);
uint64_t adamas_probe_calls(void *handle);
void adamas_probe_close(void *handle);

void *adamas_probe_open(uint64_t seed) {
    struct adamas_probe *it = (struct adamas_probe *)malloc(sizeof(struct adamas_probe));
    if (it == NULL) {
        abort();
    }
    it->seed = seed;
    it->calls = 0;
    return it;
}

uint64_t adamas_probe_step(void *handle, uint64_t salt) {
    struct adamas_probe *it = (struct adamas_probe *)handle;
    it->calls += 1;
    it->seed = it->seed * PROBE_SPICE + (salt | UINT64_C(1));
    return it->seed >> 33;
}

uint64_t adamas_probe_calls(void *handle) { return ((struct adamas_probe *)handle)->calls; }

void adamas_probe_close(void *handle) { free(handle); }
