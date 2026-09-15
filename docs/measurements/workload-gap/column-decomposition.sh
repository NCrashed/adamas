#!/usr/bin/env bash
# Из чего состоит разрыв колонной строки: потолок на C и цена того, что
# понижение кладёт вокруг обращения к ячейке.
#
# Строка «скалярный эквивалент SIMD-ядра» отстаёт от соседа на Rust в семь раз,
# и число это само по себе не читается: оно не говорит, где отставание сидит.
# Здесь мерятся четыре точки, различающиеся ровно одной вещью каждая, и все
# четыре считают то же самое, что корпусная программа
# `tests/golden/eval/workload-column.adamas`.
#
#   1. потолок      - `float *xs; xs[i] = xs[i]*g + b`, ничего сверх;
#   2. + граница    - проверка `i < count` на чтении и на записи, как её делает
#                     `adamas_array_at` (`crates/adamas-runtime/c/array.c`);
#   3. + шаг рантаймом - чтение через `memcpy(&v, base + i*stride, stride)` с
#                     **переменной** длиной, как его делает `adamas_array_read`;
#   4. + счётчик    - пара `dup`/`drop` вокруг чтения и проверка уникальности
#                     перед записью, как их ставит понижение.
#
# Точка 4 - это и есть то, во что понижение переводит виток ядра. Разность
# соседних точек и есть цена каждой из трёх вещей по отдельности.
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

/* Заголовок той же формы, что у `adamas_array`: длина, шаг, счётчик. */
static size_t count;
static size_t stride;
static uint32_t rc;
static char *payload;

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

static float readable(size_t index) {
#if MODE >= 3
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

static void writable(void) {
#if MODE >= 3
    if (rc != 0) {                 /* adamas_array_writable */
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
    count = cells;
    /* Шаг приходит **аргументом**, а не написан числом: у настоящего массива
     * он лежит в заголовке блока, и распространить его константой компилятор
     * не может. Написанный здесь литералом, он бы распространился, и точка 3
     * мерила бы не то, что названа. */
    stride = strtoull(argv[3], 0, 10);
    if (stride != 4) {
        fail("шаг колонки `Float32` - четыре байта");
    }
    rc = 0;
    payload = (char *)malloc(cells * 4 + 1);
    if (payload == 0) {
        fail("колонка не выделилась");
    }

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
    free(payload);
    return 0;
}
EOF

# Строка сборки та же, что у стенда: `RELEASE` в `benches/harness/mod.rs`.
for mode in 0 1 2 3; do
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
floor "+ счётчик ссылок" "$DIR/mode3" "$CELLS" "$PASSES" 4
