/* Плоское значение в C: без заголовка и без счётчика (§4.11).
 *
 * Договор записан в `adamas.h`: «`Flat` заголовка не имеет вовсе и здесь не
 * представлен: плоское значение лежит по значению внутри чужого объекта или в
 * регистре». Отсюда всё содержимое этого файла и его же граница - в рантайме
 * ничего из этого нет, потому что представлять там нечего.
 *
 * # Три места, где плоское значение живёт
 *
 * *Регистр.* Локальное связывание примитивного типа - обычная C-переменная
 * своего типа (`int64_t`, `double`), а не `adamas_value`. Ячейки кучи под неё
 * не выдаётся ни одной, и это видно счётчиком блоков.
 *
 * *Слот чужого объекта.* Поле боксированного конструктора занимает своё слово
 * **по значению**: там лежат биты числа, а не указатель на объект. Слово, а не
 * упакованные четыре байта: раскладка объекта Perceus - слово на слот
 * (`adamas.h`, «поле `i` лежит по смещению `8 + 8i`»). Плотная укладка §4.11 -
 * 12 байт на `Vec3` - принадлежит плоским массивам и агрегатам, а их здесь нет.
 *
 * *Ответ функции.* Плоский ответ уходит своим C-типом, а не значением.
 *
 * # Что из этого следует для дропа и печати
 *
 * Слот, в котором лежит число, **не указатель**, и отдать его `adamas_drop`
 * значило бы читать по адресу этого числа. Поэтому обе таблицы - дроп детей и
 * печать - спрашивают у сорта слота (`adamas_slot_kind`), число там или ссылка.
 * Сорт раздаёт понижение по типу поля.
 *
 * # Заворачивание
 *
 * Целочисленные операции считаются в `unsigned long long` и обрезаются по
 * ширине типа: §4.3 требует определённого поведения вместо неопределённого, а
 * продвижение к `int` дало бы переполнение знакового на `UInt32`. Обратное
 * приведение к знаковому типу - реализационно определённое до C23 и модульное у
 * gcc и clang; ровно ту же арифметику считает [`adamas_core::prim`].
 *
 * # Печать плавающего
 *
 * Повторяет `{:?}` Rust'а, потому что с ним сверяется ответ (`tests/agreement`):
 * кратчайшая запись, читающаяся обратно тем же числом; позиционная форма при
 * нуле и при `1e-4 <= |x| < 1e16`, экспоненциальная иначе; целое позиционное
 * дописывает `.0`; показатель без плюса и без ведущих нулей.
 */

#include <stdlib.h>
#include <string.h>

/* Сорт слота. Ноль - указатель; остальные - номер примитива в порядке §4.11.
 * Числа обязаны совпасть с теми, что раздаёт эмиттер, и совпадение проверяется
 * тестом (`emit_c.rs`, `the_kinds_match_the_printer`), а не обещанием. */
#define ADAMAS_FLAT_BOXED 0u
#define ADAMAS_FLAT_INT8 1u
#define ADAMAS_FLAT_INT16 2u
#define ADAMAS_FLAT_INT32 3u
#define ADAMAS_FLAT_INT64 4u
#define ADAMAS_FLAT_UINT8 5u
#define ADAMAS_FLAT_UINT16 6u
#define ADAMAS_FLAT_UINT32 7u
#define ADAMAS_FLAT_UINT64 8u
#define ADAMAS_FLAT_FLOAT32 9u
#define ADAMAS_FLAT_FLOAT64 10u

/* Биты слота как они лежат. `memcpy`, а не приведение указателя: слот объявлен
 * `adamas_value`, и читать его как целое иначе значило бы нарушить строгий
 * алиасинг. */
static uint64_t adamas_slot_bits(adamas_value value, size_t index) {
    uint64_t bits;
    memcpy(&bits, &value->fields[index], sizeof bits);
    return bits;
}

/* Обратно: биты числа занимают слот целиком, владения при этом не возникает. */
static void adamas_slot_write(adamas_value value, size_t index, uint64_t bits) {
    memcpy(&value->fields[index], &bits, sizeof bits);
}

#define ADAMAS_FLAT_INTEGER(name, ctype, utype, wide, spec)                                        \
    static ctype adamas_bits_##name(uint64_t bits) { return (ctype)(utype)bits; }                  \
    static uint64_t adamas_word_##name(ctype value) { return (uint64_t)(utype)value; }             \
    static ctype adamas_add_##name(ctype a, ctype b) {                                             \
        unsigned long long folded = (unsigned long long)(utype)a + (unsigned long long)(utype)b;   \
        return (ctype)(utype)folded;                                                               \
    }                                                                                              \
    static ctype adamas_sub_##name(ctype a, ctype b) {                                             \
        unsigned long long folded = (unsigned long long)(utype)a - (unsigned long long)(utype)b;   \
        return (ctype)(utype)folded;                                                               \
    }                                                                                              \
    static ctype adamas_mul_##name(ctype a, ctype b) {                                             \
        unsigned long long folded = (unsigned long long)(utype)a * (unsigned long long)(utype)b;   \
        return (ctype)(utype)folded;                                                               \
    }                                                                                              \
    static void adamas_show_##name(ctype value) { printf(spec, (wide)value); }

static void adamas_show_real(double value, int width);

#define ADAMAS_FLAT_REAL(name, ctype, utype)                                                       \
    static ctype adamas_bits_##name(uint64_t bits) {                                               \
        utype word = (utype)bits;                                                                  \
        ctype value;                                                                               \
        memcpy(&value, &word, sizeof value);                                                       \
        return value;                                                                              \
    }                                                                                              \
    static uint64_t adamas_word_##name(ctype value) {                                              \
        utype word;                                                                                \
        memcpy(&word, &value, sizeof word);                                                        \
        return (uint64_t)word;                                                                     \
    }                                                                                              \
    static ctype adamas_add_##name(ctype a, ctype b) { return a + b; }                             \
    static ctype adamas_sub_##name(ctype a, ctype b) { return a - b; }                             \
    static ctype adamas_mul_##name(ctype a, ctype b) { return a * b; }                             \
    static void adamas_show_##name(ctype value) { adamas_show_real((double)value, (int)sizeof value); }

ADAMAS_FLAT_INTEGER(Int8, int8_t, uint8_t, long long, "%lld")
ADAMAS_FLAT_INTEGER(Int16, int16_t, uint16_t, long long, "%lld")
ADAMAS_FLAT_INTEGER(Int32, int32_t, uint32_t, long long, "%lld")
ADAMAS_FLAT_INTEGER(Int64, int64_t, uint64_t, long long, "%lld")
ADAMAS_FLAT_INTEGER(UInt8, uint8_t, uint8_t, unsigned long long, "%llu")
ADAMAS_FLAT_INTEGER(UInt16, uint16_t, uint16_t, unsigned long long, "%llu")
ADAMAS_FLAT_INTEGER(UInt32, uint32_t, uint32_t, unsigned long long, "%llu")
ADAMAS_FLAT_INTEGER(UInt64, uint64_t, uint64_t, unsigned long long, "%llu")
ADAMAS_FLAT_REAL(Float32, float, uint32_t)
ADAMAS_FLAT_REAL(Float64, double, uint64_t)

/* Кратчайшая запись плавающего в форме Rust'а. `width` - 4 либо 8: сужение до
 * `float` решает и точность записи, и границы позиционной формы. */
static void adamas_show_real(double value, int width) {
    char written[48];
    char mantissa[32];
    const char *cursor;
    uint64_t bits;
    int precision;
    int exponent;
    int digits = 0;
    int positional;

    if (value != value) {
        printf("NaN");
        return;
    }
    memcpy(&bits, &value, sizeof bits);
    if ((bits >> 63) != 0) {
        printf("-");
        value = -value;
    }
    /* Бесконечность узнаётся без `<float.h>`: половина от неё есть она сама. */
    if (value != 0.0 && value * 0.5 == value) {
        printf("inf");
        return;
    }
    for (precision = 0; precision < 17; precision += 1) {
        double back;
        snprintf(written, sizeof written, "%.*e", precision, value);
        back = strtod(written, NULL);
        if (width == 4 ? ((float)back == (float)value) : (back == value)) {
            break;
        }
    }
    for (cursor = written; *cursor != '\0' && *cursor != 'e'; cursor += 1) {
        if (*cursor != '.' && digits < (int)sizeof mantissa - 1) {
            mantissa[digits] = *cursor;
            digits += 1;
        }
    }
    mantissa[digits] = '\0';
    exponent = (*cursor == 'e') ? (int)strtol(cursor + 1, NULL, 10) : 0;

    positional = width == 4 ? ((float)value == 0.0f
                               || ((float)value >= 1e-4f && (float)value < 1e16f))
                            : (value == 0.0 || (value >= 1e-4 && value < 1e16));
    if (!positional) {
        printf("%c", mantissa[0]);
        if (digits > 1) {
            printf(".%s", mantissa + 1);
        }
        printf("e%d", exponent);
        return;
    }
    if (exponent < 0) {
        int gap;
        printf("0.");
        for (gap = -exponent - 1; gap > 0; gap -= 1) {
            printf("0");
        }
        printf("%s", mantissa);
        return;
    }
    if (exponent + 1 >= digits) {
        int pad;
        printf("%s", mantissa);
        for (pad = exponent + 1 - digits; pad > 0; pad -= 1) {
            printf("0");
        }
        printf(".0");
        return;
    }
    printf("%.*s.%s", exponent + 1, mantissa, mantissa + exponent + 1);
}

/* Отрицательно ли плоское значение: аргументу с минусом нужны скобки, ровно как
 * `Prim::negative` в ядре. */
static int adamas_flat_negative(uint8_t kind, uint64_t bits) {
    switch (kind) {
    case ADAMAS_FLAT_INT8:
        return adamas_bits_Int8(bits) < 0;
    case ADAMAS_FLAT_INT16:
        return adamas_bits_Int16(bits) < 0;
    case ADAMAS_FLAT_INT32:
        return adamas_bits_Int32(bits) < 0;
    case ADAMAS_FLAT_INT64:
        return adamas_bits_Int64(bits) < 0;
    case ADAMAS_FLAT_FLOAT32: {
        float value = adamas_bits_Float32(bits);
        return (bits & 0x80000000ULL) != 0 && value == value;
    }
    case ADAMAS_FLAT_FLOAT64: {
        double value = adamas_bits_Float64(bits);
        return (bits & 0x8000000000000000ULL) != 0 && value == value;
    }
    default:
        return 0;
    }
}

static void adamas_print_flat(uint8_t kind, uint64_t bits, int nested) {
    int paren = nested && adamas_flat_negative(kind, bits);
    if (paren) {
        printf("(");
    }
    switch (kind) {
    case ADAMAS_FLAT_INT8:
        adamas_show_Int8(adamas_bits_Int8(bits));
        break;
    case ADAMAS_FLAT_INT16:
        adamas_show_Int16(adamas_bits_Int16(bits));
        break;
    case ADAMAS_FLAT_INT32:
        adamas_show_Int32(adamas_bits_Int32(bits));
        break;
    case ADAMAS_FLAT_INT64:
        adamas_show_Int64(adamas_bits_Int64(bits));
        break;
    case ADAMAS_FLAT_UINT8:
        adamas_show_UInt8(adamas_bits_UInt8(bits));
        break;
    case ADAMAS_FLAT_UINT16:
        adamas_show_UInt16(adamas_bits_UInt16(bits));
        break;
    case ADAMAS_FLAT_UINT32:
        adamas_show_UInt32(adamas_bits_UInt32(bits));
        break;
    case ADAMAS_FLAT_UINT64:
        adamas_show_UInt64(adamas_bits_UInt64(bits));
        break;
    case ADAMAS_FLAT_FLOAT32:
        adamas_show_Float32(adamas_bits_Float32(bits));
        break;
    case ADAMAS_FLAT_FLOAT64:
        adamas_show_Float64(adamas_bits_Float64(bits));
        break;
    default:
        adamas_fail("печать: у слота нет сорта");
    }
    if (paren) {
        printf(")");
    }
}
