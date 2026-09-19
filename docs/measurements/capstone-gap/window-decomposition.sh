#!/usr/bin/env bash
# Из чего состоит разрыв капстоуна: потолок вектора руками и цена того, что
# понижение кладёт вокруг **окна**.
#
# Строка милестоуна говорит «капстоун против C+intrinsics», и число само по
# себе не читается: оно не называет, где отставание сидит. Здесь мерятся пять
# точек, различающиеся ровно одной вещью каждая, и все пять считают одно и то
# же - то же ядро `churn`, что у `tests/golden/eval/packets.adamas`:
#
#   0. потолок       - `_mm_loadu`/`_mm_storeu` по прямому указателю, ничего
#                      сверх: ровно то, что делает сосед
#                      (`crates/adamas-codegen/benches/neighbour/packets.c`);
#   1. + граница окна - `lanes > count || index > count - lanes` на чтении и на
#                      записи, как её делает `adamas_array_window`
#                      (`crates/adamas-runtime/c/array.c`);
#   2. + шаг рантаймом - адрес считается как `payload + index * stride` с
#                      проверкой `stride != 0`, где `stride` лежит в заголовке
#                      блока; там же, оба обращения;
#   3. + уникальность  - `adamas_is_unique` перед записью: непосредственность,
#                      ветвь по флагу разделяемости и `rc == 0`, как их делает
#                      `adamas_array_writable`. **Так виток выглядит сегодня.**
#   4. по дорожке      - то же ядро скаляром, без единого вектора: потолок той
#                      формы, в которую §4.9 и не давала бы писать.
#
# Разность соседних точек и есть цена каждой вещи по отдельности. Точка 4 стоит
# особняком и отвечает на другой вопрос: чего сам вектор стоит на этой машине и
# на этой базовой линии архитектуры (`gcc` без `-march`, то есть SSE2).
#
# Заголовок лежит **в том же блоке**, что ячейки, и это не оформление: в
# разложении колонной строки (`workload-gap/column-decomposition.sh`)
# глобальные переменные gcc поднимал из витка, и модель переставала
# воспроизводить понижение.
#
# Оценка - пол выборки, как и у стенда: помеха ко времени процесса только
# прибавляет. Привязка к ядру - параметром.
set -eu

PACKETS="${PACKETS:-4096}"
# Пять буферов стенда (главный и четыре воркера) на 1024 прохода каждый.
PASSES="${PASSES:-5120}"
CORE="${CORE:-8}"
# Девять, а не пять: точки здесь идут **подряд**, а не чередованием, и помеха,
# накрывшая окно одной точки, из отношения не уходит. Свидетель того, что она
# всё же накрыла: точка 1 обязана быть не ниже точки 0, а точка 3 - не ниже
# точки 2, потому что работы у них строго больше. Прогон, где порядок нарушен,
# читать нельзя (случалось на пяти запусках: точка 0 выходила на 27% выше
# точки 1).
RUNS="${RUNS:-9}"

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

cat > "$DIR/window.c" <<'EOF'
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <emmintrin.h>

#define STRIDE 8u
#define LANES 4u
#define SPICE UINT64_C(6364136223846793005)
#define PEPPER UINT64_C(1442695040888963407)

/* Заголовок той же формы и в том же блоке, что у `adamas_array`: счётчик,
 * флаги, длина, шаг, дальше payload по смещению 24. */
typedef struct {
    uint32_t rc;
    uint16_t spare;
    uint8_t flags;
    uint8_t tag;
    size_t count;
    size_t stride;
} head_t;

static char *block;

#define head ((head_t *)block)
#define payload (block + sizeof(head_t))
#define count (head->count)
#define stride (head->stride)

static void fail(const char *why) {
    fprintf(stderr, "%s\n", why);
    exit(1);
}

/* `adamas_array_window`: хвост окна проверяется вычитанием, чтобы не
 * завернуть, - дословно как в рантайме. */
static void *window(size_t index) {
#if MODE >= 1
    if (LANES > count || index > count - LANES) {
        fail("окно вектора вне длины массива");
    }
#endif
#if MODE >= 2
    if (stride == 0) {
        fail("окно вектора спрошено у указательного массива");
    }
    return payload + index * stride;
#else
    return payload + index * STRIDE;
#endif
}

/* `adamas_is_unique`: непосредственное значение, флаг разделяемости, счётчик.
 * Атомарная половина вынесена за `noinline` - так она устроена после вопроса
 * 175 (`object.c`, `ADAMAS_SHARED_HALF`). */
__attribute__((noinline, cold)) static int unique_shared(void) {
    return __atomic_load_n(&head->rc, __ATOMIC_ACQUIRE) == 0;
}

static void writable(void) {
#if MODE >= 3
    if (((uintptr_t)block & 1u) != 0) {
        fail("непосредственное значение вместо блока");
    }
    if ((head->flags & 1u) != 0) {
        if (!unique_shared()) {
            fail("блок не уникален: понижение скопировало бы колонку");
        }
        return;
    }
    if (head->rc != 0) {
        fail("блок не уникален: понижение скопировало бы колонку");
    }
#endif
}

#if MODE <= 3
static inline __m128i mul_epi64(__m128i a, __m128i b) {
    __m128i lo = _mm_mul_epu32(a, b);
    __m128i a_hi = _mm_srli_epi64(a, 32);
    __m128i b_hi = _mm_srli_epi64(b, 32);
    __m128i cross = _mm_add_epi64(_mm_mul_epu32(a_hi, b), _mm_mul_epu32(a, b_hi));
    return _mm_add_epi64(lo, _mm_slli_epi64(cross, 32));
}

static void churn(size_t packets) {
    const __m128i spice = _mm_set1_epi64x((long long)SPICE);
    const __m128i pepper = _mm_set1_epi64x((long long)PEPPER);
    size_t k;
    for (k = packets; k != 0; k -= 1) {
        size_t at = (k - 1) * STRIDE + LANES;
        char *got = (char *)window(at);
        __m128i lo = _mm_loadu_si128((const __m128i *)got);
        __m128i hi = _mm_loadu_si128((const __m128i *)(got + 16));
        lo = _mm_add_epi64(mul_epi64(lo, spice), pepper);
        hi = _mm_add_epi64(mul_epi64(hi, spice), pepper);
        writable();
        got = (char *)window(at);
        _mm_storeu_si128((__m128i *)got, lo);
        _mm_storeu_si128((__m128i *)(got + 16), hi);
    }
}
#else
static void churn(size_t packets) {
    size_t k;
    for (k = packets; k != 0; k -= 1) {
        size_t at = (k - 1) * STRIDE + LANES;
        uint64_t *got = (uint64_t *)(payload + at * STRIDE);
        unsigned lane;
        for (lane = 0; lane < LANES; lane += 1) {
            got[lane] = got[lane] * SPICE + PEPPER;
        }
    }
}
#endif

int main(int argc, char **argv) {
    size_t packets, passes, cells, index, pass;
    uint64_t acc;
    if (argc != 4) {
        fail("ожидаются число пакетов, число проходов и шаг");
    }
    packets = strtoull(argv[1], 0, 10);
    passes = strtoull(argv[2], 0, 10);
    cells = packets * STRIDE;
    block = (char *)malloc(sizeof(head_t) + cells * 8 + 1);
    if (block == 0) {
        fail("колонка не выделилась");
    }
    count = cells;
    /* Шаг приходит **аргументом**: у настоящего массива он лежит в заголовке
     * блока, и распространить его константой компилятор не может. Написанный
     * литералом, он бы распространился, и точка 2 мерила бы не то, что
     * названа. */
    stride = strtoull(argv[3], 0, 10);
    if (stride != 8) {
        fail("шаг колонки `UInt64` - восемь байт");
    }
    head->rc = 0;
    head->flags = 0;
    for (index = 0; index < cells; index += 1) {
        ((uint64_t *)payload)[index] = index + 1;
    }
    for (pass = 0; pass < passes; pass += 1) {
        churn(packets);
    }
    acc = 0;
    for (index = 0; index < cells; index += 1) {
        acc = ((uint64_t *)payload)[index] - acc;
    }
    printf("%" PRIu64 "\n", acc);
    free(block);
    return 0;
}
EOF

# Строка сборки та же, что у стенда: `RELEASE` в `benches/harness/mod.rs`.
# `-march` не ставится: базовая линия у всех сторон замера generic.
for mode in 0 1 2 3 4; do
  gcc -std=c11 -O2 -flto -fwrapv -ffp-contract=off -DMODE=$mode \
      -include inttypes.h "$DIR/window.c" -o "$DIR/mode$mode"
done

floor() { # пол выборки в микросекундах
  local best="" answer=""
  for _ in $(seq 1 "$RUNS"); do
    local start end elapsed
    start=$(date +%s%N)
    answer=$(taskset -c "$CORE" "$@")
    end=$(date +%s%N)
    elapsed=$(( (end - start) / 1000 ))
    if [ -z "$best" ] || [ "$elapsed" -lt "$best" ]; then best=$elapsed; fi
  done
  echo "$best $answer"
}

# Свой пол вычитается у каждой точки: заполнение, свёртка и запуск процесса
# одинаковы у всех пяти, но в отношение они входить не должны. Пол - та же
# точка на нуле проходов.
CEILING=""
point() {
  local name="$1"; shift
  local full pit answer
  read -r full answer <<< "$(floor "$@" "$PACKETS" "$PASSES" 8)"
  read -r pit _ <<< "$(floor "$@" "$PACKETS" 0 8)"
  local kernel=$(( full - pit ))
  if [ -z "$CEILING" ]; then CEILING="$kernel"; fi
  printf '%s.%03d мс — %s (к потолку %s, пол точки %s.%03d мс, ответ %s)\n' \
         "$((kernel / 1000))" "$((kernel % 1000))" "$name" \
         "$(awk -v a="$kernel" -v b="$CEILING" 'BEGIN{printf "%.3f", a/b}')" \
         "$((pit / 1000))" "$((pit % 1000))" "$answer"
}

echo "пакетов $PACKETS, проходов $PASSES, ядро $CORE, пол по $RUNS запускам"
point "потолок: вектор руками" "$DIR/mode0"
point "+ граница окна" "$DIR/mode1"
point "+ шаг рантаймом" "$DIR/mode2"
point "+ уникальность перед записью (виток сегодня)" "$DIR/mode3"
point "то же ядро по дорожке (потолок скаляра)" "$DIR/mode4"
