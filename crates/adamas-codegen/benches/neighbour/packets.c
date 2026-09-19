/* Сосед капстоуна: тот же обработчик пакетов, написанный руками на C.
 *
 * §6 держит строку «SIMD-heavy код (§4.9) - паритет с C+intrinsics», и
 * референсом там стоит ручной вектор, а не то, что угадает автовекторизатор.
 * Поэтому горячая половина здесь написана intrinsics'ами (`churn`, `digest`),
 * а не циклом по дорожкам.
 *
 * Программа обязана печатать **тот же ответ**, что `tests/golden/eval/
 * packets.adamas`: стенд сверяет строки до всякого замера. Расхождение здесь -
 * не косметика, а признак того, что сравниваются две разные работы.
 *
 * # Что подставляется снаружи
 *
 *   -DPACKETS=<число>   пакетов в буфере (у фикстуры `packets = <число>`);
 *   -DROUNDS=<число>    проходов вектора по колонке (`rounds = <число>`);
 *   -DKERNEL_SCALAR=1   горячая половина **по дорожке**, без intrinsics.
 *
 * Последнее - не сосед, а точка разложения: она отвечает, чего стоит сам
 * вектор на этой машине и на этой базовой линии архитектуры.
 *
 * # Базовая линия - SSE2, и это не выбор, а условие годности числа
 *
 * Таблица разрыва уравнивает базовую линию архитектуры у обеих сторон: `gcc`
 * без `-march`, `llc` без `-mcpu`. Наш `Simd 4 UInt64` понижается в два
 * `<2 x i64>`, потому что шире базовая линия x86-64 не даёт. Сосед с `-mavx2`
 * мерил бы ключ компилятора, а не руку программиста, и повторил бы ровно ту
 * ошибку, которой Фаза 6 стоила отозванного вывода.
 *
 * Умножения 64-битных дорожек в SSE2 нет ни одного: `pmuludq` умножает
 * 32×32→64. Поэтому `mul_epi64` ниже - обычная трёхчастная эмуляция, та же,
 * которую порождают из `mul <2 x i64>` оба наших бэкенда.
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__x86_64__)
#include <immintrin.h>
#else
#error "сосед написан под x86-64: intrinsics другой архитектуры сюда не дописаны, а собрать его скаляром значило бы выдать скаляр за вектор"
#endif

#ifndef PACKETS
#define PACKETS 6
#endif
#ifndef ROUNDS
#define ROUNDS 1
#endif
#ifndef KERNEL_SCALAR
#define KERNEL_SCALAR 0
#endif
#ifndef KERNEL_WIDE
#define KERNEL_WIDE 0
#endif
#if KERNEL_WIDE && !defined(__AVX2__)
#error "широкое ядро просит `-march=x86-64-v3` и выше: без AVX2 `_mm256_mul_epu32` нет"
#endif

#define STRIDE UINT64_C(8)
#define BUCKETS UINT64_C(8)
#define CELLS ((uint64_t)(PACKETS) * STRIDE)

#define SPICE UINT64_C(6364136223846793005)
#define PEPPER UINT64_C(1442695040888963407)
#define THIRTY_ONE UINT64_C(31)

/* --- разряды слова ------------------------------------------------------ */

static inline uint64_t low_mask(unsigned width) {
    return width >= 64 ? ~UINT64_C(0) : ~(~UINT64_C(0) << width);
}

static inline uint64_t fld(uint64_t word, unsigned at, unsigned width) {
    return (at >= 64 ? UINT64_C(0) : (word >> at)) & low_mask(width);
}

static inline uint64_t poke(uint64_t word, unsigned at, unsigned width, uint64_t value) {
    uint64_t hole = word & ~(low_mask(width) << at);
    return hole | ((value & low_mask(width)) << at);
}

/* --- контрольная сумма и порождение ------------------------------------- */

static inline uint64_t half_at(uint64_t word, unsigned i) { return fld(word, i * 16u, 16); }

static inline uint64_t word_sum(uint64_t w) {
    return (half_at(w, 0) + half_at(w, 1)) + (half_at(w, 2) + half_at(w, 3));
}

static inline uint64_t carry_of(uint64_t s) { return (s & 65535) + (s >> 16); }

static uint64_t checksum_over(uint64_t c0, uint64_t c1, uint64_t c2, uint64_t c3) {
    uint64_t bare = poke(c1, 32, 16, 0);
    uint64_t raw = (word_sum(c0) + word_sum(bare)) + (word_sum(c2) + word_sum(c3));
    return (carry_of(carry_of(raw)) ^ 65535) & 65535;
}

static inline uint64_t mix64(uint64_t x) {
    uint64_t a = x ^ (x << 13);
    uint64_t b = a ^ (a >> 7);
    return b ^ (b << 17);
}

static inline uint64_t grain(uint64_t seed, uint64_t k) {
    return mix64(seed * UINT64_C(2654435761) + (k + 1) * UINT64_C(40503));
}

static inline uint64_t proto_of(uint64_t k) {
    if (k == 0) return 1;
    if (k == 1) return 6;
    if (k == 2) return 17;
    return 47;
}

static uint64_t made_head0(uint64_t seed, uint64_t p) {
    uint64_t r = grain(seed, p * STRIDE);
    uint64_t ver = (p % 7 == 3) ? UINT64_C(6) : UINT64_C(4);
    uint64_t dscp = fld(r, 3, 8);
    uint64_t len = fld(r, 11, 10) + 40;
    uint64_t ident = fld(r, 21, 16);
    uint64_t flags = fld(r, 37, 3);
    uint64_t frag = fld(r, 40, 13);
    return ((ver << 60) | ((UINT64_C(5) << 56) | (dscp << 48)))
         | ((len << 32) | ((ident << 16) | ((flags << 13) | frag)));
}

static uint64_t made_head1(uint64_t seed, uint64_t p) {
    uint64_t r = grain(seed, p * STRIDE + 1);
    uint64_t ttl = fld(r, 0, 6) + 2;
    uint64_t proto = proto_of(fld(r, 6, 2));
    uint64_t src = fld(r, 8, 32);
    return ((ttl << 56) | (proto << 48)) | src;
}

static uint64_t made_head2(uint64_t seed, uint64_t p) {
    uint64_t r = grain(seed, p * STRIDE + 2);
    return (fld(r, 0, 32) << 32) | ((fld(r, 32, 16) << 16) | fld(r, 48, 16));
}

static void write_packet(uint64_t *xs, uint64_t seed, uint64_t p) {
    uint64_t base = p * STRIDE;
    uint64_t c0 = made_head0(seed, p);
    uint64_t bare = made_head1(seed, p);
    uint64_t c2 = made_head2(seed, p);
    uint64_t c3 = grain(seed, base + 3);
    uint64_t sum = checksum_over(c0, bare, c2, c3);
    uint64_t c1 = poke(bare, 32, 16, (p % 5 == 2) ? (sum ^ 1) : sum);
    xs[base] = c0;
    xs[base + 1] = c1;
    xs[base + 2] = c2;
    xs[base + 3] = c3;
    xs[base + 4] = grain(seed, base + 4);
    xs[base + 5] = grain(seed, base + 5);
    xs[base + 6] = grain(seed, base + 6);
    xs[base + 7] = grain(seed, base + 7);
}

/* Порождение идёт **сверху вниз**, как рекурсия фикстуры: порядок записи здесь
 * ответа не меняет, но менять его без нужды значило бы писать другую программу. */
static void generate(uint64_t *xs, uint64_t seed, uint64_t packets) {
    for (uint64_t k = packets; k != 0; k--) write_packet(xs, seed, k - 1);
}

/* --- политика и хеш потока ----------------------------------------------- */

static const uint8_t POLICY[8] = {1, 2, 1, 3, 2, 0, 3, 1};

static inline uint64_t weight_of(uint8_t code) {
    if (code == 0) return 0;
    if (code == 1) return 1;
    if (code == 2) return 3;
    return 7;
}

static inline uint64_t flow_hash(uint64_t src, uint64_t dst, uint64_t sp, uint64_t dp,
                                 uint64_t proto) {
    return mix64((src * UINT64_C(2246822519))
                 ^ ((dst * UINT64_C(3266489917))
                    ^ (((sp << 16) | dp) ^ (proto * UINT64_C(668265263)))));
}

/* --- разбор -------------------------------------------------------------- */

typedef struct {
    uint64_t accepted, dropped, bytes, hops, flows, weight, expired;
} tally;

static tally scan(const uint64_t *xs, const uint8_t *pol, uint64_t packets) {
    tally t = {0, 0, 0, 0, 0, 0, 0};
    for (uint64_t k = packets; k != 0; k--) {
        uint64_t p = k - 1;
        uint64_t base = p * STRIDE;
        uint64_t c0 = xs[base], c1 = xs[base + 1], c2 = xs[base + 2], c3 = xs[base + 3];
        uint64_t ver = fld(c0, 60, 4);
        uint64_t len = fld(c0, 32, 16);
        uint64_t ttl = fld(c1, 56, 8);
        uint64_t proto = fld(c1, 48, 8);
        uint64_t stored = fld(c1, 32, 16);
        uint64_t src = fld(c1, 0, 32);
        uint64_t dst = fld(c2, 32, 32);
        uint64_t sp = fld(c2, 16, 16);
        uint64_t dp = fld(c2, 0, 16);
        uint64_t want = checksum_over(c0, c1, c2, c3);
        uint64_t flow = flow_hash(src, dst, sp, dp, proto);
        uint8_t code = pol[flow & 7];
        if (ver == 4 && stored == want && code != 0) {
            t.accepted += 1;
            t.bytes += len;
            t.hops += ttl;
            t.flows ^= flow;
            t.weight += weight_of(code);
            t.expired += (ttl <= 1) ? 1 : 0;
        } else {
            t.dropped += 1;
        }
    }
    return t;
}

/* --- горячая половина: вектор руками ------------------------------------- */

#if KERNEL_WIDE
/* Тот же вектор, но в 256-битном регистре: так пишет тот, кому разрешили
 * `-march=x86-64-v3`.
 *
 * Точка эта стоит здесь затем, что ручные intrinsics прибиты к **ширине,
 * которую написал программист**, а `Simd 4 UInt64` есть тип - и бэкенд кладёт
 * его в тот регистр, какой даёт цель. Сравнивать нашу широкую сборку с узким
 * соседом значило бы записать себе в заслугу то, что сосед не переписан. */
static inline __m256i mul_epi64_wide(__m256i a, __m256i b) {
    __m256i lo = _mm256_mul_epu32(a, b);
    __m256i a_hi = _mm256_srli_epi64(a, 32);
    __m256i b_hi = _mm256_srli_epi64(b, 32);
    __m256i cross = _mm256_add_epi64(_mm256_mul_epu32(a_hi, b), _mm256_mul_epu32(a, b_hi));
    return _mm256_add_epi64(lo, _mm256_slli_epi64(cross, 32));
}

static void churn(uint64_t *xs, uint64_t packets) {
    const __m256i spice = _mm256_set1_epi64x((long long)SPICE);
    const __m256i pepper = _mm256_set1_epi64x((long long)PEPPER);
    for (uint64_t k = packets; k != 0; k--) {
        uint64_t *w = xs + (k - 1) * STRIDE + 4;
        __m256i v = _mm256_loadu_si256((const __m256i *)w);
        v = _mm256_add_epi64(mul_epi64_wide(v, spice), pepper);
        _mm256_storeu_si256((__m256i *)w, v);
    }
}

static void digest(const uint64_t *xs, uint64_t packets, uint64_t out[4]) {
    const __m256i thirty_one = _mm256_set1_epi64x((long long)THIRTY_ONE);
    __m256i acc = _mm256_setzero_si256();
    for (uint64_t k = packets; k != 0; k--) {
        const uint64_t *w = xs + (k - 1) * STRIDE + 4;
        acc = _mm256_add_epi64(mul_epi64_wide(acc, thirty_one),
                               _mm256_loadu_si256((const __m256i *)w));
    }
    _mm256_storeu_si256((__m256i *)out, acc);
}
#elif !KERNEL_SCALAR
/* Умножение 64-битных дорожек: SSE2 его не имеет, и это та же эмуляция,
 * в которую `mul <2 x i64>` разворачивают оба наших бэкенда. */
static inline __m128i mul_epi64(__m128i a, __m128i b) {
    __m128i lo = _mm_mul_epu32(a, b);
    __m128i a_hi = _mm_srli_epi64(a, 32);
    __m128i b_hi = _mm_srli_epi64(b, 32);
    __m128i cross = _mm_add_epi64(_mm_mul_epu32(a_hi, b), _mm_mul_epu32(a, b_hi));
    return _mm_add_epi64(lo, _mm_slli_epi64(cross, 32));
}

static void churn(uint64_t *xs, uint64_t packets) {
    const __m128i spice = _mm_set1_epi64x((long long)SPICE);
    const __m128i pepper = _mm_set1_epi64x((long long)PEPPER);
    for (uint64_t k = packets; k != 0; k--) {
        uint64_t *w = xs + (k - 1) * STRIDE + 4;
        __m128i lo = _mm_loadu_si128((const __m128i *)w);
        __m128i hi = _mm_loadu_si128((const __m128i *)(w + 2));
        lo = _mm_add_epi64(mul_epi64(lo, spice), pepper);
        hi = _mm_add_epi64(mul_epi64(hi, spice), pepper);
        _mm_storeu_si128((__m128i *)w, lo);
        _mm_storeu_si128((__m128i *)(w + 2), hi);
    }
}

static void digest(const uint64_t *xs, uint64_t packets, uint64_t out[4]) {
    const __m128i thirty_one = _mm_set1_epi64x((long long)THIRTY_ONE);
    __m128i lo = _mm_setzero_si128();
    __m128i hi = _mm_setzero_si128();
    for (uint64_t k = packets; k != 0; k--) {
        const uint64_t *w = xs + (k - 1) * STRIDE + 4;
        lo = _mm_add_epi64(mul_epi64(lo, thirty_one), _mm_loadu_si128((const __m128i *)w));
        hi = _mm_add_epi64(mul_epi64(hi, thirty_one), _mm_loadu_si128((const __m128i *)(w + 2)));
    }
    _mm_storeu_si128((__m128i *)out, lo);
    _mm_storeu_si128((__m128i *)(out + 2), hi);
}
#else
/* Точка разложения: та же работа по дорожке. Вектора здесь нет ни одного, и
 * автовекторизатору собрать его не из чего - 64-битного умножения в базовой
 * линии нет. */
static void churn(uint64_t *xs, uint64_t packets) {
    for (uint64_t k = packets; k != 0; k--) {
        uint64_t *w = xs + (k - 1) * STRIDE + 4;
        for (unsigned lane = 0; lane < 4; lane++) w[lane] = w[lane] * SPICE + PEPPER;
    }
}

static void digest(const uint64_t *xs, uint64_t packets, uint64_t out[4]) {
    uint64_t acc[4] = {0, 0, 0, 0};
    for (uint64_t k = packets; k != 0; k--) {
        const uint64_t *w = xs + (k - 1) * STRIDE + 4;
        for (unsigned lane = 0; lane < 4; lane++) acc[lane] = acc[lane] * THIRTY_ONE + w[lane];
    }
    for (unsigned lane = 0; lane < 4; lane++) out[lane] = acc[lane];
}
#endif

static void churning(uint64_t *xs, uint64_t packets, uint64_t rounds) {
    for (uint64_t r = rounds; r != 0; r--) churn(xs, packets);
}

static inline uint64_t fold_lanes(const uint64_t v[4]) {
    return v[3] - (v[2] - (v[1] - v[0]));
}

static uint64_t sealed_of(const uint64_t *xs, uint64_t packets) {
    uint64_t lanes[4];
    digest(xs, packets, lanes);
    return fold_lanes(lanes);
}

/* --- пересылка ----------------------------------------------------------- */

static void forward(uint64_t *xs, uint64_t packets) {
    for (uint64_t k = packets; k != 0; k--) {
        uint64_t base = (k - 1) * STRIDE;
        uint64_t c0 = xs[base];
        uint64_t c1 = xs[base + 1];
        xs[base + 1] = (fld(c0, 60, 4) == 4) ? poke(c1, 56, 8, fld(c1, 56, 8) - 1) : c1;
    }
}

static uint64_t hops_of(const uint64_t *xs, uint64_t packets) {
    uint64_t acc = 0;
    for (uint64_t k = packets; k != 0; k--) acc += fld(xs[(k - 1) * STRIDE + 1], 56, 8);
    return acc;
}

/* --- область под пакет: ручная арена ------------------------------------- */
/*
 * §3.6 называет две стратегии, и расходятся они одним членом: Arena ячейку
 * обратно не берёт, Pool берёт. Руками на C это курсор и один придержанный
 * слот - ровно то, что §6 и называет «C с manual arena management».
 *
 * `here` есть смещение последней укладки (§3.6, `Ptr`), и оттого в ответе
 * стоят 16 у Arena и 0 у Pool: у Arena вторая укладка идёт за первой, у Pool -
 * в возвращённую ячейку.
 */

typedef struct {
    uint64_t flow, bytes;
} cell;

#define ARENA_WORDS 16

typedef struct {
    uint64_t words[ARENA_WORDS];
    uint64_t cursor;
    uint64_t last;
    uint64_t freed;
    int has_freed;
} region;

static inline void region_new(region *r) {
    r->cursor = 0;
    r->last = 0;
    r->has_freed = 0;
    r->freed = 0;
}

static inline uint64_t region_store(region *r, cell d) {
    uint64_t at;
    if (r->has_freed) {
        at = r->freed;
        r->has_freed = 0;
    } else {
        at = r->cursor;
        r->cursor += sizeof(cell);
    }
    memcpy((unsigned char *)r->words + at, &d, sizeof d);
    r->last = at;
    return at;
}

static inline cell region_load(const region *r, uint64_t at) {
    cell d;
    memcpy(&d, (const unsigned char *)r->words + at, sizeof d);
    return d;
}

/* Плоское слово, а не запись: mempool воркеров кладёт `UInt64`. */
static inline uint64_t region_store_word(region *r, uint64_t value) {
    uint64_t at = r->cursor;
    r->cursor += sizeof(uint64_t);
    memcpy((unsigned char *)r->words + at, &value, sizeof value);
    r->last = at;
    return at;
}

static inline uint64_t region_load_word(const region *r, uint64_t at) {
    uint64_t value;
    memcpy(&value, (const unsigned char *)r->words + at, sizeof value);
    return value;
}

static inline void region_recycle(region *r, uint64_t at) {
    r->freed = at;
    r->has_freed = 1;
}

static cell cell_at(const uint64_t *xs, uint64_t p) {
    uint64_t base = p * STRIDE;
    uint64_t c0 = xs[base], c1 = xs[base + 1], c2 = xs[base + 2];
    cell d;
    d.flow = flow_hash(fld(c1, 0, 32), fld(c2, 32, 32), fld(c2, 16, 16), fld(c2, 0, 16),
                       fld(c1, 48, 8));
    d.bytes = fld(c0, 32, 16);
    return d;
}

static uint64_t sweep_arena(const uint64_t *xs, uint64_t packets) {
    uint64_t acc = 0;
    region r;
    for (uint64_t k = packets; k != 0; k--) {
        cell d = cell_at(xs, k - 1);
        region_new(&r);
        uint64_t at = region_store(&r, d);
        cell got = region_load(&r, at);
        acc += got.flow ^ got.bytes;
    }
    return acc;
}

static uint64_t sweep_pool(const uint64_t *xs, uint64_t packets) {
    uint64_t acc = 0;
    region r;
    for (uint64_t k = packets; k != 0; k--) {
        cell d = cell_at(xs, k - 1);
        region_new(&r);
        uint64_t at = region_store(&r, d);
        cell got = region_load(&r, at);
        region_recycle(&r, at);
        region_store(&r, d);
        acc += got.flow ^ got.bytes;
    }
    return acc;
}

/* Тело пробы - одно на три стратегии, как функтор у фикстуры. */
static uint64_t scratch_once(uint64_t flow, uint64_t bytes) {
    cell d = {flow, bytes};
    region r;
    region_new(&r);
    uint64_t at = region_store(&r, d);
    cell got = region_load(&r, at);
    return got.flow ^ got.bytes;
}

static uint64_t scratch_again(uint64_t flow, uint64_t bytes, int recycles) {
    cell d = {flow, bytes};
    region r;
    region_new(&r);
    uint64_t at = region_store(&r, d);
    if (recycles) region_recycle(&r, at);
    return region_store(&r, d);
}

/* --- воркеры ------------------------------------------------------------- */
/*
 * Воркеров четыре, и идут они **по очереди**, а не потоками. Причина - предмет
 * строки: §6 спрашивает о качестве кода, а четыре настоящих потока мерили бы
 * планировщик и раскладку кучи под ним. Что капстоун работает на воркерах, и
 * работает верно, проверено врозь (`adamas-codegen/tests/capstone.rs`, 24
 * прогона обоими бэкендами); стенд обе стороны гоняет однопоточными, и наша
 * сторона под `ADAMAS_THREADS` не запускается.
 */

typedef struct {
    uint64_t accepted, dropped, bytes, sealed, flows;
} digest_value;

static digest_value worker(region *mempool, uint64_t seed, uint64_t packets, uint64_t rounds) {
    uint64_t *raw = (uint64_t *)calloc((size_t)(packets * STRIDE), sizeof(uint64_t));
    if (raw == NULL) {
        fprintf(stderr, "воркеру не хватило памяти\n");
        exit(1);
    }
    generate(raw, seed, packets);
    tally t = scan(raw, POLICY, packets);
    churning(raw, packets, rounds);
    uint64_t sealed = sealed_of(raw, packets);
    uint64_t at = region_store_word(mempool, t.bytes);
    digest_value d;
    d.accepted = t.accepted;
    d.dropped = t.dropped;
    d.bytes = region_load_word(mempool, at);
    d.sealed = sealed;
    d.flows = t.flows;
    free(raw);
    return d;
}

static digest_value merge(digest_value a, digest_value b) {
    digest_value out;
    out.accepted = a.accepted + b.accepted;
    out.dropped = a.dropped + b.dropped;
    out.bytes = a.bytes + b.bytes;
    out.sealed = a.sealed ^ b.sealed;
    out.flows = a.flows ^ b.flows;
    return out;
}

/* --- точка входа ---------------------------------------------------------- */

int main(void) {
    const uint64_t packets = (uint64_t)(PACKETS);
    const uint64_t rounds = (uint64_t)(ROUNDS);

    uint64_t *raw = (uint64_t *)calloc((size_t)CELLS, sizeof(uint64_t));
    if (raw == NULL) {
        fprintf(stderr, "буферу не хватило памяти\n");
        return 1;
    }
    generate(raw, 7, packets);
    tally t = scan(raw, POLICY, packets);
    churning(raw, packets, rounds);
    uint64_t sealed = sealed_of(raw, packets);
    uint64_t scratched = sweep_arena(raw, packets);
    uint64_t mempooled = sweep_pool(raw, packets);
    cell first = cell_at(raw, 0);
    forward(raw, packets);
    uint64_t left = hops_of(raw, packets);
    uint64_t alone = scratch_once(first.flow, first.bytes);
    uint64_t joint = scratch_once(first.flow, first.bytes);

    region mempool;
    region_new(&mempool);
    digest_value w1 = worker(&mempool, 7, packets, rounds);
    digest_value w2 = worker(&mempool, 11, packets, rounds);
    digest_value w3 = worker(&mempool, 13, packets, rounds);
    digest_value w4 = worker(&mempool, 17, packets, rounds);
    digest_value crew = merge(merge(w1, w2), merge(w3, w4));

    uint64_t average = t.accepted == 0 ? 0 : t.bytes / t.accepted;
    uint64_t guarded = t.expired == 0 ? 999 : t.bytes / t.expired;

    printf("MkAnswer ({accepted = %" PRIu64 ", dropped = %" PRIu64 ", bytes = %" PRIu64
           ", hops = %" PRIu64 ", flows = %" PRIu64 ", weight = %" PRIu64 ", churned = %" PRIu64
           ", pooled = %" PRIu64 ", shared = %" PRIu64 ", average = %" PRIu64
           ", guarded = %" PRIu64 "}) (MkDigest %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64
           " %" PRIu64 ") %" PRIu64 " %" PRIu64 "\n",
           t.accepted, t.dropped, t.bytes, left, t.flows, t.weight, sealed,
           mempooled - scratched, joint - alone, average, guarded, crew.accepted, crew.dropped,
           crew.bytes, crew.sealed, crew.flows,
           scratch_again(first.flow, first.bytes, 0), scratch_again(first.flow, first.bytes, 1));

    free(raw);
    return 0;
}
