#!/usr/bin/env bash
# Из чего состоит разрыв колонной строки: потолок на C и цена того, что
# понижение кладёт вокруг обращения к ячейке.
#
# Строка «скалярный эквивалент SIMD-ядра» отстаёт от соседа на Rust, и число
# это само по себе не читается: оно не говорит, где отставание сидит. Здесь
# мерятся шесть точек, различающиеся ровно одной вещью каждая, и все шесть
# считают то же самое, что корпусная программа
# `tests/golden/eval/workload-column.adamas`.
#
#   0. потолок      - `float *xs; xs[i] = xs[i]*g + b`, ничего сверх;
#   1. + граница    - проверка `i < count` на чтении и на записи, как её делает
#                     `adamas_array_at` (`crates/adamas-runtime/c/array.c`);
#   2. + шаг рантаймом - чтение через `memcpy(&v, base + i*stride, stride)` с
#                     **переменной** длиной, как его делает `adamas_array_read`;
#   3. + уникальность - `rc == 0` перед записью, без пары `dup`/`drop` вокруг
#                     чтения: так виток выглядел после вопроса 171 (2026-09-15)
#                     и до трека I волны 2 Фазы 7;
#   4. + разделяемость - та же проверка, но через ветвь по флагу
#                     `ADAMAS_FLAG_SHARED`, как её делает `adamas_is_unique`
#                     после трека I: **так виток выглядит сегодня**;
#   5. + счётчик при чтении - точка 3 плюс пара `dup`/`drop` вокруг чтения, как
#                     было до вопроса 171; на ней снята первая редакция таблицы.
#
# Разность соседних точек и есть цена каждой вещи по отдельности. Точки 3 и 4
# стоят рядом потому, что между ними прошла целая фаза: вопрос 171 снял
# счётчик с чтения, трек I вернул на запись ветвь по флагу, и цена у второй
# оказалась того же порядка, что выигрыш первого.
#
# Оценка - пол выборки, как и у стенда: помеха ко времени процесса только
# прибавляет. Привязка к ядру - параметром.
set -eu

CELLS="${CELLS:-8388608}"
PASSES="${PASSES:-8}"
CORE="${CORE:-8}"
RUNS="${RUNS:-5}"

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

cat > "$DIR/column.c" <<'EOF'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define GAIN 1.03125f
#define BIAS 1.0f

/* Заголовок той же формы, что у `adamas_array`, и **в том же блоке**, что
 * ячейки: длина, шаг, счётчик, флаги, дальше payload.
 *
 * Блоком, а не глобальными переменными, и это измерено, а не выбрано.
 * Глобальные gcc поднимает из витка - им неоткуда пересечься с `malloc`-овым
 * буфером, - и точка 3 давала 56.8 мс против 118 у настоящего понижения. В
 * одном блоке чтение счётчика и запись ячейки пересекаются по правилам
 * языка, подъём запрещён, и модель воспроизводит виток, а не описывает его. */
typedef struct {
    size_t count;
    size_t stride;
    uint32_t rc;
    uint32_t flags;
} head_t;

static char *block;

#define head ((head_t *)block)
#define payload (block + sizeof(head_t))
#define count (head->count)
#define stride (head->stride)
#define rc (head->rc)

static void fail(const char *why) {
    fprintf(stderr, "%s\n", why);
    exit(1);
}

static void *cell(size_t index) {
#if MODE >= 1
    if (index >= count) {
        fail("номер ячейки вне длины массива");
    }
#endif
#if MODE >= 2
    return payload + index * stride;
#else
    return payload + index * 4;
#endif
}

/* Пара `dup`/`drop` вокруг чтения стоит только в точке 5: вопрос 171 снял её,
 * чтение с невладеющего локала заимствует. Проверка уникальности перед записью
 * осталась, и потому она в точках 3, 4 и 5. */
static float readable(size_t index) {
#if MODE == 5
    float out;
    rc += 1;                       /* adamas_dup */
    memcpy(&out, cell(index), stride);
    if (rc == 0) {
        fail("блок отдан посреди чтения");
    }
    rc -= 1;                       /* adamas_drop */
    return out;
#elif MODE >= 2
    float out;
    memcpy(&out, cell(index), stride);
    return out;
#else
    return *(float *)cell(index);
#endif
}

/* `adamas_is_unique`: до трека I - одно чтение счётчика, после - ещё и
 * ветвление по флагу разделяемости (§5.1, гибридный режим). */
static int unique(void) {
#if MODE == 4
    if ((head->flags & 1u) != 0) {
        return __atomic_load_n(&rc, __ATOMIC_ACQUIRE) == 0;
    }
#endif
    return rc == 0;
}

static void writable(void) {
#if MODE >= 3
    if (!unique()) {               /* adamas_array_writable */
        fail("блок не уникален: понижение скопировало бы колонку");
    }
#endif
}

int main(int argc, char **argv) {
    size_t cells, passes, index, pass;
    float value, acc;
    if (argc != 4) {
        fail("ожидаются длина колонки, число проходов и шаг");
    }
    cells = strtoull(argv[1], 0, 10);
    passes = strtoull(argv[2], 0, 10);
    block = (char *)malloc(sizeof(head_t) + cells * 4 + 1);
    if (block == 0) {
        fail("колонка не выделилась");
    }
    count = cells;
    /* Шаг приходит **аргументом**, а не написан числом: у настоящего массива
     * он лежит в заголовке блока, и распространить его константой компилятор
     * не может. Написанный здесь литералом, он бы распространился, и точка 2
     * мерила бы не то, что названа. */
    stride = strtoull(argv[3], 0, 10);
    if (stride != 4) {
        fail("шаг колонки `Float32` - четыре байта");
    }
    rc = 0;
    head->flags = 0;

    /* `arrayNew cells zero`: блок заполняется, а не приходит обнулённым. */
    for (index = 0; index < cells; index += 1) {
        *(float *)(payload + index * 4) = 0.0f;
    }
    /* `fill`: номер убывает, значение растёт. */
    value = 1.0f;
    for (index = cells; index != 0; index -= 1) {
        *(float *)(payload + (index - 1) * 4) = value;
        value += 1.0f;
    }
    /* Ядро. */
    for (pass = 0; pass < passes; pass += 1) {
        for (index = cells; index != 0; index -= 1) {
            float got = readable(index - 1);
            float put = got * GAIN + BIAS;
            writable();
            *(float *)cell(index - 1) = put;
        }
    }
    /* `total`: свёртка вычитанием. */
    acc = 0.0f;
    for (index = cells; index != 0; index -= 1) {
        acc = readable(index - 1) - acc;
    }
    printf("%.9g\n", (double)acc);
    free(block);
    return 0;
}
EOF

# Строка сборки та же, что у стенда: `RELEASE` в `benches/harness/mod.rs`.
for mode in 0 1 2 3 4 5; do
  gcc -std=c11 -O2 -flto -fwrapv -DMODE=$mode "$DIR/column.c" -o "$DIR/mode$mode"
done

floor() {
  local name="$1"; shift
  local best="" answer=""
  for _ in $(seq 1 "$RUNS"); do
    local start end elapsed
    start=$(date +%s%N)
    answer=$(taskset -c "$CORE" "$@")
    end=$(date +%s%N)
    elapsed=$(( (end - start) / 1000 ))
    if [ -z "$best" ] || [ "$elapsed" -lt "$best" ]; then best=$elapsed; fi
  done
  printf '%s.%03d мс — %s (ответ %s)\n' "$((best / 1000))" "$((best % 1000))" \
         "$name" "$answer"
}

echo "ячеек $CELLS, проходов $PASSES, ядро $CORE, пол по $RUNS запускам"
floor "потолок: руками на C" "$DIR/mode0" "$CELLS" "$PASSES" 4
floor "+ проверка границы" "$DIR/mode1" "$CELLS" "$PASSES" 4
floor "+ шаг рантаймом (memcpy)" "$DIR/mode2" "$CELLS" "$PASSES" 4
floor "+ уникальность перед записью (после вопроса 171, до трека I)" \
      "$DIR/mode3" "$CELLS" "$PASSES" 4
floor "+ ветвь по флагу разделяемости (понижение сегодня)" \
      "$DIR/mode4" "$CELLS" "$PASSES" 4
floor "+ счётчик при чтении (понижение до вопроса 171)" \
      "$DIR/mode5" "$CELLS" "$PASSES" 4
