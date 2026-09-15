#!/usr/bin/env bash
# Сколько стоит **невыровненная** векторная загрузка: цена `AlignedBuffer`.
#
# §4.9 заводит выровненный буфер ресурсным типом:
#
#     resource AlignedBuffer (n : Nat) (a : Type) where
#       drop b = freeAligned b
#     -- Alignment гарантирован конструктором (aligned malloc)
#
# и тут же, абзацем ниже, отказывается от пере-выравнивания записей:
#
#     Атрибут пере-выравнивания сознательно не заводится: на современных x86 и
#     ARM невыровненная загрузка стоит около нуля.
#
# Два эти утверждения про разные вещи - про кучу и про поле записи, - но довод у
# второго годится и для первого, а если он верен, то `AlignedBuffer` есть
# машинерия под цену, которой нет. Довод этот **не измерен ни разу**: §4.9 писан
# до реализации. Здесь он меряется.
#
# Мерятся пять точек на одном и том же проходе по колонке `Float32` векторами
# ширины восемь (`Simd 8 Float32` §4.9). Вектор занимает 32 байта, линия кэша -
# 64, и точки различаются **только** смещением буфера:
#
#   1. aligned   - смещение 0: граница 64, то есть и 32 тоже;
#   2. align32   - смещение 32: граница ровно 32 - вектору довольно, линии нет.
#                  Свидетель того, что мерится граница **вектора**, а не линии;
#   3. offset4   - смещение 4, то есть одна дорожка: граница 4, и каждая вторая
#                  загрузка пересекает линию кэша;
#   4. crossing  - смещение 48: линию пересекает **каждая** загрузка;
#   5. scalar    - тот же проход дорожка за дорожкой, без вектора: точка отсчёта
#                  для «сколько вообще даёт вектор».
#
# Точки 1-4 различаются только выравниванием: то же число загрузок, тот же объём
# трафика, та же форма цикла, и ответ у всех четырёх обязан совпасть. Их разность
# и есть цена, ради которой §4.9 заводит ресурсный тип `AlignedBuffer`.
#
# **Размер колонки решает, что мерится.** На колонке больше L3 проход упирается
# в пропускную способность памяти, и выравнивание за ней прячется; на колонке,
# помещающейся в кэш, прятаться нечему. Мерить надо оба - см. README.
#
# Ключ `-fno-tree-vectorize` стоит у скалярной точки нарочно: без него gcc
# соберёт вектор сам, и точка 4 перестанет быть точкой отсчёта.
#
# Оценка - пол выборки: помеха ко времени только прибавляет. Привязка к ядру -
# параметром, как у соседних замеров.
set -eu

CELLS="${CELLS:-8388608}"
PASSES="${PASSES:-8}"
CORE="${CORE:-8}"
RUNS="${RUNS:-9}"

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

cat > "$DIR/align.c" <<'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define GAIN 1.03125f
#define BIAS 1.0f

typedef float v8 __attribute__((vector_size(32)));

/* Проход векторами: ровно то, во что понижение переводит `Simd 8 Float32`
 * (`simdMul` плюс `simdAdd`). Загрузка и запись идут `memcpy`-свободно, через
 * разыменование указателя на векторный тип: выравнивание при этом обещает
 * **буфер**, а не атрибут, и в том весь смысл замера. */
static void vector_pass(float *xs, size_t cells, size_t passes) {
    v8 gain, bias;
    size_t pass, at, lane;
    for (lane = 0; lane < 8; lane += 1) {
        gain[lane] = GAIN;
        bias[lane] = BIAS;
    }
    for (pass = 0; pass < passes; pass += 1) {
        for (at = 0; at + 8 <= cells; at += 8) {
            v8 chunk;
            __builtin_memcpy(&chunk, xs + at, sizeof chunk);
            chunk = chunk * gain + bias;
            __builtin_memcpy(xs + at, &chunk, sizeof chunk);
        }
    }
}

__attribute__((optimize("no-tree-vectorize")))
static void scalar_pass(float *xs, size_t cells, size_t passes) {
    size_t pass, at;
    for (pass = 0; pass < passes; pass += 1) {
        for (at = 0; at < cells; at += 1) {
            xs[at] = xs[at] * GAIN + BIAS;
        }
    }
}

int main(int argc, char **argv) {
    size_t cells = (size_t)strtoull(argv[1], NULL, 10);
    size_t passes = (size_t)strtoull(argv[2], NULL, 10);
    /* Смещение в **байтах** от границы 64: 0 и 32 оставляют вектор выровненным
     * (ему довольно 32), 4 и 48 - нет. */
    size_t skew = (size_t)strtoull(argv[3], NULL, 10);
    int vectorised = argv[4][0] == 'v';
    char *raw = aligned_alloc(64, (cells + 32) * sizeof(float) + 64);
    float *xs = (float *)(raw + skew);
    size_t at;
    double total = 0.0;
    (void)argc;
    for (at = 0; at < cells; at += 1) {
        xs[at] = (float)(at & 1023);
    }
    if (vectorised) {
        vector_pass(xs, cells, passes);
    } else {
        scalar_pass(xs, cells, passes);
    }
    for (at = 0; at < cells; at += 1) {
        total = total - (double)xs[at];
    }
    printf("%.6f\n", total);
    free(raw);
    return 0;
}
EOF

CC="${CC:-gcc}"
"$CC" -std=c11 -O2 -fwrapv -w -o "$DIR/align" "$DIR/align.c"

# Пол по `RUNS` запускам: медиана врёт на редкой помехе, пол - нет.
floor() {
    local best="" elapsed
    for _ in $(seq "$RUNS"); do
        local start end
        start=$(date +%s%N)
        taskset -c "$CORE" "$DIR/align" "$CELLS" "$PASSES" "$1" "$2" > "$DIR/answer"
        end=$(date +%s%N)
        elapsed=$(( (end - start) / 1000000 ))
        if [ -z "$best" ] || [ "$elapsed" -lt "$best" ]; then best=$elapsed; fi
    done
    printf '%s' "$best"
}

echo "колонка $CELLS ячеек, $PASSES проходов, ядро $CORE, пол по $RUNS запускам"
for point in "0 v aligned" "32 v align32" "4 v offset4" "48 v crossing" "0 s scalar"; do
    set -- $point
    ms=$(floor "$1" "$2")
    answer=$(cat "$DIR/answer")
    printf '%-10s %6s мс   ответ %s\n' "$3" "$ms" "$answer"
done
