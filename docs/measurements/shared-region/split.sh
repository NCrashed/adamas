#!/usr/bin/env bash
# Разделяемая область: холодная половина, кусок, сосед §6 и разложение (§3.6).
#
# Четыре точки замера, и вопросы у них разные. Числа - в README рядом.
#
# **1. Делит ли атрибут.** Правило трека B волны 3 Фазы 7: точку входа с редкой
# тяжёлой ветвью обязан делить исходник, а не компилятор - у gcc частичный
# инлайнинг делит сам, у LLVM `PartialInlinerPass` в `-O2` выключен. На обычной
# области это стоило 1.46 раза (`docs/measurements/region-alloc/`). Здесь
# проверяется та же развилка у `refill` в `shared.c`: быстрый путь - подъём
# курсора в **своём** куске, редкий - новый кусок у курсора области.
#
#   plain - `#define ADAMAS_CONTESTED` пуст: делит компилятор;
#   split - `__attribute__((noinline, cold))`: делит исходник.
#
# Виток тот же, что у обычной области, - `alloc` плюс `pop` над своей
# областью, - и выбран он тем же доводом: холодная половина не случается ни
# разу после первого витка, и мерится ровно то, мешает ли она горячей.
#
# **2. Чего стоит кусок.** §10 вопрос 26(а) спрашивает прямо: `SharedArena` -
# атомарный CAS на bump pointer'е (просто, но контеншен) или per-thread caches
# (сложнее, но масштабируется). Реализация взяла куски **обеим** стандартным
# стратегиям, и здесь это мерено, а не заявлено: тот же код собирается с
# `ADAMAS_SHARED_CHUNK` 512 и 8, то есть со встречей воркеров раз в 64 витка и
# раз в два, и гоняется на одном, двух и четырёх потоках.
#
# Ёмкость области фиксирована (§3.6), поэтому виток второй точки устроен
# раундами: область заводится, потоки разбирают её кусками, область дропается.
#
# Оценка - пол выборки, чередование сторон внутри блока, привязка к ядру.
set -eu

CPU="${CPU:-8}"
BLOCKS="${BLOCKS:-5}"
RUNS="${RUNS:-5}"
TURNS="${TURNS:-10000000}"
ROUNDS="${ROUNDS:-2000}"

root=$(cd "$(dirname "$0")/../../.." && pwd)
work="${TMPDIR:-/tmp}/adamas-shared-region"
rm -rf "$work"
mkdir -p "$work"

# --- точка 1: атрибут -------------------------------------------------------

mkdir -p "$work/plain" "$work/split" "$work/include"
cp "$root"/crates/adamas-runtime/c/*.c "$work/split/"
cp "$root"/crates/adamas-runtime/c/*.c "$work/plain/"
cp "$root"/crates/adamas-runtime/include/*.h "$work/include/"
sed -i 's|^#define ADAMAS_CONTESTED __attribute__((noinline, cold))$|#define ADAMAS_CONTESTED /* делит компилятор */|' \
    "$work/plain/shared.c"
if cmp -s "$work/plain/shared.c" "$work/split/shared.c"; then
    echo "точки не разошлись: атрибута у refill в shared.c нет вовсе" >&2
    exit 1
fi

cat > "$work/drive.c" <<'PROBE'
/* Виток укладки в разделяемую область: положить и опустить курсор (§3.6).
 *
 * Своя область, один поток: холодная половина (`refill`) случается ровно один
 * раз, а `pop` возвращает курсор воркера на место. Мерится не контеншен, а
 * то, мешает ли вынесенная холодная половина горячей. */
#include "adamas.h"

#include <stdio.h>
#include <stdlib.h>

static void release(adamas_value value) { (void)value; }

int main(int argc, char **argv) {
    size_t turns = argc > 1 ? (size_t)atol(argv[1]) : 0;
    uint64_t seed = 1;
    adamas_value area = adamas_shared_new();
    size_t turn;
    for (turn = 0; turn < turns; turn += 1) {
        area = adamas_region_alloc(area, &seed, sizeof(seed), sizeof(seed));
        seed += 1;
        area = adamas_region_pop(area, 0);
    }
    area = adamas_region_alloc(area, &seed, sizeof(seed), sizeof(seed));
    printf("%llu %llu\n", (unsigned long long)adamas_region_used(area),
           (unsigned long long)seed);
    adamas_drop(area, release);
    return 0;
}
PROBE

# --- точка 2: ширина куска и число воркеров ---------------------------------

mkdir -p "$work/chunk" "$work/every" "$work/include-every"
cp "$root"/crates/adamas-runtime/c/*.c "$work/chunk/"
cp "$root"/crates/adamas-runtime/c/*.c "$work/every/"
cp "$root"/crates/adamas-runtime/include/*.h "$work/include-every/"
sed -i 's|^#define ADAMAS_SHARED_CHUNK 512u$|#define ADAMAS_SHARED_CHUNK 8u|' \
    "$work/include-every/adamas.h"
if cmp -s "$work/include/adamas.h" "$work/include-every/adamas.h"; then
    echo "точки не разошлись: ADAMAS_SHARED_CHUNK в adamas.h не нашлась" >&2
    exit 1
fi

cat > "$work/crowd.c" <<'CROWD'
/* Несколько воркеров укладывают в одну область (§3.6, §5.2).
 *
 * Раундами, потому что ёмкость области фиксирована: область заводится, потоки
 * разбирают её кусками, область дропается. Число укладок на раунд одно при
 * любом числе потоков - сравниваются равные работы. */
#include "adamas.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define PLACES 32000

static adamas_value area;
static size_t share;

static void release(adamas_value value) { (void)value; }

static void *hand(void *arg) {
    uint64_t seed = (uint64_t)(uintptr_t)arg;
    size_t turn;
    for (turn = 0; turn < share; turn += 1) {
        adamas_region_alloc(area, &seed, sizeof(seed), sizeof(seed));
        seed += 1;
    }
    return NULL;
}

int main(int argc, char **argv) {
    size_t hands = argc > 1 ? (size_t)atol(argv[1]) : 1;
    size_t rounds = argc > 2 ? (size_t)atol(argv[2]) : 1;
    pthread_t *crew = calloc(hands, sizeof(pthread_t));
    size_t round;
    size_t at;
    unsigned long long given = 0;
    share = PLACES / hands;
    for (round = 0; round < rounds; round += 1) {
        area = adamas_shared_new();
        for (at = 1; at < hands; at += 1) {
            pthread_create(&crew[at], NULL, hand, (void *)(uintptr_t)at);
        }
        hand((void *)(uintptr_t)0);
        for (at = 1; at < hands; at += 1) {
            pthread_join(crew[at], NULL);
        }
        given = (unsigned long long)adamas_region_used(area);
        adamas_drop(area, release);
    }
    free(crew);
    printf("%llu %llu\n", given, (unsigned long long)adamas_stat_live_everywhere());
    return 0;
}
CROWD

# --- точка 3: сосед §6 ------------------------------------------------------
#
# §6 держит строку «Multi-core shared-mempool workloads (§3.6) - паритет с
# DPDK/tcmalloc», и **референсом** в ней стоит не библиотека, а «C с lock-free
# mempool», то есть сосед, написанный руками, - ровно как у строки SIMD стоит
# «C с intrinsics». Здесь он и написан: тот же ход, что у нашего аллокатора, и
# ничего сверх - per-thread кусок, атомарная прибавка к общему курсору, копия
# нагрузки.
#
# Мерится этим **половина** строки §6, и вторая половина отсюда не берётся.
# Аллокатор - да: цена наша против цены ручной. Нагрузка - нет: строка §6 про
# multi-core mempool-**нагрузку**, а её нет вовсе, пока не написан капстоун
# (трек C). Сказано это здесь, чтобы число не читалось шире сделанного.

cat > "$work/rival.c" <<'RIVAL'
/* Ручной lock-free mempool на C: референс строки §6.
 *
 * Тот же ход, что у `shared.c`, и ничего сверх: кусок у потока, атомарная
 * прибавка к общему курсору, копия нагрузки на место. Чего у него нет -
 * журнала (то есть возврата ячейки), тега, номера области и проверки границ. */
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PLACES 32000
#define BYTES 262144u
#define CHUNK 512u

typedef struct pool {
    size_t cursor;
    char bytes[BYTES];
} pool;

static pool *area;
static size_t share;
static _Thread_local size_t at;
static _Thread_local size_t edge;

static void *place(size_t size) {
    void *out;
    if (at + size > edge) {
        size_t taken = __atomic_fetch_add(&area->cursor, CHUNK, __ATOMIC_ACQ_REL);
        if (taken + CHUNK > BYTES) {
            fprintf(stderr, "сосед: пул переполнен\n");
            abort();
        }
        at = taken;
        edge = taken + CHUNK;
    }
    out = area->bytes + at;
    at += size;
    return out;
}

static void *hand(void *arg) {
    uint64_t seed = (uint64_t)(uintptr_t)arg;
    size_t turn;
    at = 0;
    edge = 0;
    for (turn = 0; turn < share; turn += 1) {
        memcpy(place(sizeof(seed)), &seed, sizeof(seed));
        seed += 1;
    }
    return NULL;
}

int main(int argc, char **argv) {
    size_t hands = argc > 1 ? (size_t)atol(argv[1]) : 1;
    size_t rounds = argc > 2 ? (size_t)atol(argv[2]) : 1;
    pthread_t *crew = calloc(hands, sizeof(pthread_t));
    size_t round;
    size_t index;
    unsigned long long given = 0;
    share = PLACES / hands;
    for (round = 0; round < rounds; round += 1) {
        area = calloc(1, sizeof(pool));
        for (index = 1; index < hands; index += 1) {
            pthread_create(&crew[index], NULL, hand, (void *)(uintptr_t)index);
        }
        hand((void *)(uintptr_t)0);
        for (index = 1; index < hands; index += 1) {
            pthread_join(crew[index], NULL);
        }
        given = (unsigned long long)area->cursor;
        free(area);
    }
    free(crew);
    printf("%llu 0\n", given);
    return 0;
}
RIVAL

# --- сборка -----------------------------------------------------------------

# Точка 1 собирается обеими цепочками: правило «делит атрибут» проверялось на
# LLVM, где `PartialInlinerPass` выключен, и там же оно стоило больше всего.
for point in plain split; do
    "${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing \
        -ffp-contract=off -pthread -I "$work/include" "$work/$point"/*.c "$work/drive.c" \
        -o "$work/$point.gcc.bin"

    units=()
    for source in "$work/$point"/*.c "$work/drive.c"; do
        unit="$work/$point.$(basename "$source" .c).bc"
        "${ADAMAS_CLANG:-clang}" -std=c11 -O1 -Xclang -disable-llvm-passes \
            -emit-llvm -c -I "$work/include" "$source" -o "$unit"
        units+=("$unit")
    done
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}llvm-link" "${units[@]}" -o "$work/$point.bc"
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}opt" -O2 "$work/$point.bc" -o "$work/$point.opt.bc"
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}llc" -O2 -filetype=obj -relocation-model=pic \
        "$work/$point.opt.bc" -o "$work/$point.llvm.o"
    "${ADAMAS_CC:-cc}" -pthread "$work/$point.llvm.o" -o "$work/$point.llvm.bin"
done

# Точка 2 - одной цепочкой: вопрос у неё про контеншен, а не про инлайнер.
"${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing -ffp-contract=off \
    -pthread -I "$work/include" "$work/chunk"/*.c "$work/crowd.c" -o "$work/chunk.bin"
"${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing -ffp-contract=off \
    -pthread -I "$work/include-every" "$work/every"/*.c "$work/crowd.c" -o "$work/every.bin"

# Сосед - той же строкой, чтобы различие не оказалось в ключах.
"${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing -ffp-contract=off \
    -pthread "$work/rival.c" -o "$work/rival.bin"

# Точка 4: та же наша область **без журнала**. Разложение разрыва с соседом по
# статьям: журнал есть единственное, чего у соседа нет вовсе, и без него
# `SharedPool` перестаёт быть выразимым - «переиспользование ячеек равного
# размера» §3.6 не выражается ничем иным. Цена его поэтому не дефект, а цена
# члена `free` у общего `AllocStrategy`; здесь она названа числом.
mkdir -p "$work/bare"
cp "$root"/crates/adamas-runtime/c/*.c "$work/bare/"
sed -i 's|^        record(own, at, size);$|        (void)0; /* журнала нет */|' "$work/bare/shared.c"
if cmp -s "$work/bare/shared.c" "$work/chunk/shared.c"; then
    echo "точки не разошлись: вызова record в shared.c не нашлось" >&2
    exit 1
fi
"${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing -ffp-contract=off \
    -pthread -I "$work/include" "$work/bare"/*.c "$work/crowd.c" -o "$work/bare.bin"

echo "== точка 1: ответ и что осталось от половин в символах"
for point in plain split; do
    for chain in gcc llvm; do
        answer=$("$work/$point.$chain.bin" 1000)
        symbols=$(nm "$work/$point.$chain.bin" 2>/dev/null \
                      | grep -iE ' (t|T) (refill|adamas_shared_alloc)' \
                      | awk '{ print $3 }' | sort | tr '\n' ' ')
        printf '%-6s %-4s ответ «%s», символы: %s\n' \
            "$point" "$chain" "$answer" "${symbols:-нет}"
    done
done

echo
echo "== точки 2 и 3: ответ (розданное и живые блоки)"
for point in chunk every rival bare; do
    for hands in 1 2 4; do
        printf '%-6s %d воркер(ов): %s\n' "$point" "$hands" "$("$work/$point.bin" "$hands" 2)"
    done
done

# --- отношение чередованием -------------------------------------------------

floor() {
    local best=999999999 t0 t1 d
    for _ in $(seq 1 "$RUNS"); do
        t0=$(date +%s%N); "$@" >/dev/null 2>&1; t1=$(date +%s%N)
        d=$(((t1 - t0) / 1000))
        [ "$d" -lt "$best" ] && best=$d
    done
    echo "$best"
}

race() {
    echo
    echo "== точка 1, $1: plain против split, чередованием"
    for block in $(seq 1 "$BLOCKS"); do
        a=$(floor "$work/plain.$1.bin" "$TURNS")
        b=$(floor "$work/split.$1.bin" "$TURNS")
        awk -v a="$a" -v b="$b" -v n="$block" \
            'BEGIN { printf "блок %d: %.3f против %.3f мс, отношение %.4f\n", n, a/1000, b/1000, a/b }'
    done
}

crowd() {
    echo
    echo "== точка 2: кусок 8 против куска 512, чередованием"
    for hands in 1 2 4; do
        for block in $(seq 1 "$BLOCKS"); do
            a=$(floor "$work/every.bin" "$hands" "$ROUNDS")
            b=$(floor "$work/chunk.bin" "$hands" "$ROUNDS")
            awk -v a="$a" -v b="$b" -v n="$block" -v h="$hands" \
                'BEGIN { printf "воркеров %d, блок %d: %.3f против %.3f мс, отношение %.4f\n", h, n, a/1000, b/1000, a/b }'
        done
    done
}

rival() {
    echo
    echo "== точка 3: наша область против ручного mempool на C, чередованием"
    for hands in 1 2 4; do
        for block in $(seq 1 "$BLOCKS"); do
            a=$(floor "$work/chunk.bin" "$hands" "$ROUNDS")
            b=$(floor "$work/rival.bin" "$hands" "$ROUNDS")
            awk -v a="$a" -v b="$b" -v n="$block" -v h="$hands" \
                'BEGIN { printf "воркеров %d, блок %d: наши %.3f против соседа %.3f мс, отношение %.4f\n", h, n, a/1000, b/1000, a/b }'
        done
    done
}

journal() {
    echo
    echo "== точка 4: наша область с журналом и без него, чередованием"
    for block in $(seq 1 "$BLOCKS"); do
        a=$(floor "$work/chunk.bin" 1 "$ROUNDS")
        b=$(floor "$work/bare.bin" 1 "$ROUNDS")
        c=$(floor "$work/rival.bin" 1 "$ROUNDS")
        awk -v a="$a" -v b="$b" -v c="$c" -v n="$block" \
            'BEGIN { printf "блок %d: с журналом %.3f, без %.3f, сосед %.3f мс; журнал %.4f, остаток к соседу %.4f\n", n, a/1000, b/1000, c/1000, a/b, b/c }'
    done
}

# Привязка к одному логическому процессору годится только точке 1: точка 2
# мерит контеншен, и на одном ядре его не бывает.
if [ "$CPU" = "-" ]; then
    race gcc
    race llvm
else
    taskset -c "$CPU" bash -c \
        "$(declare -f floor race); work=$work; TURNS=$TURNS; RUNS=$RUNS; BLOCKS=$BLOCKS; race gcc; race llvm"
fi
crowd
rival
journal
