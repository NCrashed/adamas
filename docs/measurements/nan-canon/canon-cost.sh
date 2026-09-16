#!/usr/bin/env bash
# Цена трёх вариантов вопроса 172, измеренная на модели витка.
#
# Вопрос: знак и нагрузка NaN, порождённого недопустимой операцией, IEEE-754 не
# заданы, а `totalOrder` §4.3 их наблюдает. Варианты закрытия платят в разных
# местах, и «в разных местах» - это и есть то, что здесь мерится:
#
#   (а) канонизация на выходе каждой операции - платит **арифметика**;
#   (в) канонизация NaN в ключе порядка - платит **сравнение**;
#   (б) сужение обещания - не платит ничего, и строки у него здесь нет.
#
# Четыре ядра, и каждое нагружает ровно одно из двух мест.
#
#   «арифметика» - колонное ядро `x[i] := x[i]·gain + bias` (§4.9, нагрузка 4а
#     трека Z), точка 4 разложения `column-decomposition.sh`: так виток
#     выглядит сегодня. Сравнений в нём ноль.
#   «вектор» - то же ядро без обвязки обращения к ячейке, то есть
#     векторизуемое: у варианта (а) `fadd <8 x float>` перестаёт быть одной
#     инструкцией. Сравнений в нём тоже ноль.
#   «сравнение з.» - минимум колонки ключом `totalOrder`: на ячейку два ключа,
#     и ключ накопителя лежит на кольцевой зависимости витка. Худший случай
#     варианта (в); арифметики ноль.
#   «сравнение н.» - счёт ячеек ниже порога: ключ порога поднимается из витка,
#     на ячейку остаётся один ключ, витки друг друга не ждут. Обычный случай.
#
# Модель, а не порождённый код, по тому же доводу, что у
# `column-decomposition.sh`: заголовок лежит в одном блоке с ячейками, и подъём
# счётчика из витка запрещён правилами языка. Три из четырёх ядер перемеряны
# сверх этого на **порождённом** коде (`README.md`, «Порождённый код»), и
# расходятся модель со стендом на доли процента. Векторной строки у стенда нет:
# LLVM-эмиттер массивов не берёт, а C-понижение кладёт вокруг обращения к
# ячейке столько, что векторизация не идёт.
#
# Оценка - пол выборки; стороны **чередуются** внутри блока, потому что
# абсолютные числа в занятом окне не читаются, а отношение переживает (тем же
# правилом, что `harness::ratio`).
set -eu

CELLS="${CELLS:-8388608}"
PASSES="${PASSES:-8}"
CORE="${CORE:-8}"
BLOCKS="${BLOCKS:-5}"

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

cat > "$DIR/canon.c" <<'EOF'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define GAIN 1.03125f
#define BIAS 1.0f

/* Заголовок той же формы, что у `adamas_array`, и в том же блоке, что ячейки:
 * иначе gcc поднимает счётчик из витка, и модель мерит не виток. */
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

/* Канонический тихий NaN: знак снят, нагрузка нулевая. Тот же, что у
 * `f64::NAN` в Rust и у свёртки констант LLVM. */
#define CANON32 0x7FC00000u

static void fail(const char *why) {
    fprintf(stderr, "%s\n", why);
    exit(1);
}

static float adamas_bits_Float32(uint32_t bits) {
    float v;
    memcpy(&v, &bits, sizeof v);
    return v;
}

/* Вариант (а): канонизация на выходе операции. */
static float quiet(float value) {
#if CANON_OP
    return value == value ? value : adamas_bits_Float32(CANON32);
#else
    return value;
#endif
}

static float adamas_add_Float32(float a, float b) { return quiet(a + b); }
static float adamas_mul_Float32(float a, float b) { return quiet(a * b); }

/* Ключ `totalOrder` (§4.3). Вариант (в) добавляет сюда канонизацию NaN.
 *
 * Канонизация идёт **в целом домене**, а не подменой самого значения: подмена
 * заставляла бы гонять число через регистр с плавающей точкой обратно, и модель
 * мерила бы её, а не вариант. Три целых операции: `and` по модулю, сравнение с
 * экспонентой всех единиц, условная пересылка. Первые две уходят параллельно
 * самому ключу, на критическом пути остаётся третья. */
#define KEY_CANON32 (CANON32 | 0x80000000u)

static uint32_t adamas_order_Float32(float value) {
    uint32_t bits;
    uint32_t key;
    uint32_t top = (uint32_t)1 << 31;
    memcpy(&bits, &value, sizeof bits);
    key = (bits & top) != 0 ? ~bits : (bits | top);
#if CANON_KEY
    if ((bits & 0x7FFFFFFFu) > 0x7F800000u) {
        key = KEY_CANON32;
    }
#endif
    return key;
}

static int adamas_lt_Float32(float a, float b) {
    return adamas_order_Float32(a) < adamas_order_Float32(b);
}

/* Обращение к ячейке ровно как его делает понижение сегодня: проверка границы,
 * шаг из заголовка, ветвь по флагу разделяемости перед записью (точка 4
 * `column-decomposition.sh`). */
static void *cell(size_t index) {
    if (index >= count) {
        fail("номер ячейки вне длины массива");
    }
    return payload + index * stride;
}

static float readable(size_t index) {
    float out;
    memcpy(&out, cell(index), stride);
    return out;
}

static int unique(void) {
    if ((head->flags & 1u) != 0) {
        return __atomic_load_n(&rc, __ATOMIC_ACQUIRE) == 0;
    }
    return rc == 0;
}

static void writable(void) {
    if (!unique()) {
        fail("блок не уникален: понижение скопировало бы колонку");
    }
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
    stride = strtoull(argv[3], 0, 10);
    if (stride != 4) {
        fail("шаг колонки `Float32` - четыре байта");
    }
    rc = 0;
    head->flags = 0;

    for (index = 0; index < cells; index += 1) {
        *(float *)(payload + index * 4) = 0.0f;
    }
    value = 1.0f;
    for (index = cells; index != 0; index -= 1) {
        *(float *)(payload + (index - 1) * 4) = value;
        value += 1.0f;
    }

#if KERNEL == 1
    /* Ядро сравнения, **зависимое**: минимум колонки ключом `totalOrder`. На
     * ячейку один `lt`, то есть два ключа, и ключ накопителя лежит на
     * кольцевой зависимости витка - худший случай для варианта (в). */
    acc = readable(0);
    for (pass = 0; pass < passes; pass += 1) {
        for (index = cells; index != 0; index -= 1) {
            float got = readable(index - 1);
            if (adamas_lt_Float32(got, acc)) {
                acc = got;
            }
        }
    }
    printf("%.9g\n", (double)acc);
#elif KERNEL == 3
    /* Ядро §4.9: тот же проход, но **векторизуемый** - без проверки границы, без
     * шага из заголовка и без счётчика. Мерится, во что канонизация обходится
     * там, где компилятор кладёт восемь дорожек в одну инструкцию: у варианта
     * (а) `fadd <8 x float>` перестаёт быть одной инструкцией и становится
     * тремя. Сравнений здесь ноль, поэтому вариант (в) обязан ничего не стоить. */
    {
        float *xs = (float *)payload;
        for (pass = 0; pass < passes; pass += 1) {
            for (index = 0; index < cells; index += 1) {
                xs[index] = adamas_add_Float32(adamas_mul_Float32(xs[index], GAIN), BIAS);
            }
        }
        acc = 0.0f;
        for (index = cells; index != 0; index -= 1) {
            acc = xs[index - 1] - acc;
        }
        printf("%.9g\n", (double)acc);
    }
#elif KERNEL == 2
    /* Ядро сравнения, **независимое**: сколько ячеек ниже порога. Ключ порога
     * постоянен и поднимается из витка, на ячейку остаётся один ключ, и витки
     * друг друга не ждут - обычный случай для варианта (в). */
    {
        uint64_t below = 0;
        float threshold = adamas_bits_Float32(0x4F000000u); /* 2³¹ */
        for (pass = 0; pass < passes; pass += 1) {
            for (index = cells; index != 0; index -= 1) {
                below += (uint64_t)adamas_lt_Float32(readable(index - 1), threshold);
            }
        }
        printf("%llu\n", (unsigned long long)below);
    }
#else
    /* Ядро арифметики: `x[i] := x[i]·gain + bias`. Сравнений ноль. */
    for (pass = 0; pass < passes; pass += 1) {
        for (index = cells; index != 0; index -= 1) {
            float got = readable(index - 1);
            float put = adamas_add_Float32(adamas_mul_Float32(got, GAIN), BIAS);
            writable();
            *(float *)cell(index - 1) = put;
        }
    }
    acc = 0.0f;
    for (index = cells; index != 0; index -= 1) {
        acc = readable(index - 1) - acc;
    }
    printf("%.9g\n", (double)acc);
#endif
    free(block);
    return 0;
}
EOF

# Строка сборки та же, что у стенда: `RELEASE` в `benches/harness/mod.rs`.
build() { # имя ядро канон_оп канон_ключ
  gcc -std=c11 -O2 -flto -fwrapv -ffp-contract=off \
      -DKERNEL="$2" -DCANON_OP="$3" -DCANON_KEY="$4" \
      "$DIR/canon.c" -o "$DIR/$1"
}

build arith.plain    0 0 0
build arith.canonop  0 1 0
build arith.canonkey 0 0 1
build dep.plain      1 0 0
build dep.canonop    1 1 0
build dep.canonkey   1 0 1
build free.plain     2 0 0
build free.canonop   2 1 0
build free.canonkey  2 0 1
build vec.plain      3 0 0
build vec.canonop    3 1 0
build vec.canonkey   3 0 1

# Пол по чередующимся блокам: в блоке по одному запуску каждой стороны подряд,
# у каждой стороны берётся минимум по блокам.
pair() { # заголовок левый правый
  local title="$1" left="$2" right="$3"
  local bl="" br="" answer_l="" answer_r="" i
  for i in $(seq 1 "$BLOCKS"); do
    local s e t
    s=$(date +%s%N); answer_l=$(taskset -c "$CORE" "$DIR/$left" "$CELLS" "$PASSES" 4); e=$(date +%s%N)
    t=$(( (e - s) / 1000 )); if [ -z "$bl" ] || [ "$t" -lt "$bl" ]; then bl=$t; fi
    s=$(date +%s%N); answer_r=$(taskset -c "$CORE" "$DIR/$right" "$CELLS" "$PASSES" 4); e=$(date +%s%N)
    t=$(( (e - s) / 1000 )); if [ -z "$br" ] || [ "$t" -lt "$br" ]; then br=$t; fi
  done
  # Ответ обязан совпасть: канонизация меняет цену, а не число. Разойдись он -
  # мерилось бы не то, что названо.
  if [ "$answer_l" != "$answer_r" ]; then
    echo "$title: стороны посчитали разное - $answer_l против $answer_r" >&2
    exit 1
  fi
  printf '%s: %s.%03d мс против %s.%03d мс, отношение %s (ответ %s)\n' \
    "$title" "$((br / 1000))" "$((br % 1000))" "$((bl / 1000))" "$((bl % 1000))" \
    "$(awk -v a="$br" -v b="$bl" 'BEGIN { printf "%.4f", a / b }')" "$answer_l"
}

echo "ячеек $CELLS, проходов $PASSES, ядро $CORE, пол по $BLOCKS чередующимся блокам"
pair "арифметика,   (а) на выходе операции" arith.plain arith.canonop
pair "арифметика,   (в) в ключе порядка   " arith.plain arith.canonkey
pair "сравнение з., (а) на выходе операции" dep.plain dep.canonop
pair "сравнение з., (в) в ключе порядка   " dep.plain dep.canonkey
pair "сравнение н., (а) на выходе операции" free.plain free.canonop
pair "сравнение н., (в) в ключе порядка   " free.plain free.canonkey
pair "вектор,       (а) на выходе операции" vec.plain vec.canonop
pair "вектор,       (в) в ключе порядка   " vec.plain vec.canonkey
