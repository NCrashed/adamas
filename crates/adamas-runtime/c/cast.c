/* Преобразование между числовыми типами (§4.3, §10 вопрос 205).
 *
 * Реализация **одна на оба понижения**, и это не экономия строк. У преобразования
 * плавающего в целое выход за диапазон есть неопределённое поведение и у C, и у
 * LLVM: две инлайновые реализации разошлись бы там молча, а договор трёх
 * вычислителей требует одного ответа. Поэтому функция живёт в рантайме, который
 * линкуют оба, а машина повторяет её правила в `PrimCast::apply` - и сверяет их
 * корпус.
 *
 * Цена названа: вызов вместо инструкции. Инлайнить это оптимизатору не мешает
 * ничто - функция маленькая и без побочных действий, - но обещать инлайн здесь
 * нечем, и в отладочной сборке его не будет.
 *
 * Биты приходят и уходят словом: типизирует их вызывающий, у которого есть
 * написанный тип. Тег типа - индекс в `PrimTy::ALL`, и порядок этот сверяется
 * тестом на стороне Rust.
 */

#include "adamas.h"

#include <math.h>
#include <string.h>

/* Ширина типа в битах по его тегу. */
static unsigned width_of(uint8_t ty) {
    switch (ty) {
    case ADAMAS_TY_INT8:
    case ADAMAS_TY_UINT8:
        return 8;
    case ADAMAS_TY_INT16:
    case ADAMAS_TY_UINT16:
        return 16;
    case ADAMAS_TY_INT32:
    case ADAMAS_TY_UINT32:
    case ADAMAS_TY_FLOAT32:
        return 32;
    default:
        return 64;
    }
}

static int signed_of(uint8_t ty) {
    return ty == ADAMAS_TY_INT8 || ty == ADAMAS_TY_INT16 || ty == ADAMAS_TY_INT32 ||
           ty == ADAMAS_TY_INT64;
}

static int floating_of(uint8_t ty) {
    return ty == ADAMAS_TY_FLOAT32 || ty == ADAMAS_TY_FLOAT64;
}

/* Младшие биты по ширине: хранимое представление всегда нормальное. */
static uint64_t masked(uint64_t bits, unsigned width) {
    return width == 64 ? bits : bits & ((UINT64_C(1) << width) - 1);
}

/* Целое со знаком из битов, расширенное до 64. */
static int64_t widened(uint64_t bits, uint8_t ty) {
    unsigned width = width_of(ty);
    if (!signed_of(ty) || width == 64) {
        return (int64_t)bits;
    }
    unsigned shift = 64 - width;
    return ((int64_t)(bits << shift)) >> shift;
}

/* Значение как `double`: по роду и знаку исходного типа. */
static double as_double(uint64_t bits, uint8_t ty) {
    if (ty == ADAMAS_TY_FLOAT32) {
        float single;
        uint32_t narrow = (uint32_t)bits;
        memcpy(&single, &narrow, sizeof(single));
        return (double)single;
    }
    if (ty == ADAMAS_TY_FLOAT64) {
        double wide;
        memcpy(&wide, &bits, sizeof(wide));
        return wide;
    }
    if (signed_of(ty)) {
        return (double)widened(bits, ty);
    }
    return (double)bits;
}

/* Биты плавающего из числа. */
static uint64_t from_double(double value, uint8_t ty) {
    if (ty == ADAMAS_TY_FLOAT32) {
        float single = (float)value;
        uint32_t narrow;
        memcpy(&narrow, &single, sizeof(narrow));
        return (uint64_t)narrow;
    }
    uint64_t wide;
    memcpy(&wide, &value, sizeof(wide));
    return wide;
}

/* Целое из плавающего: усечение к нулю с насыщением по краям, NaN - ноль. */
static uint64_t saturated(double value, uint8_t ty) {
    unsigned width = width_of(ty);
    if (isnan(value)) {
        return 0;
    }
    if (signed_of(ty)) {
        int64_t top = width == 64 ? INT64_MAX : (INT64_C(1) << (width - 1)) - 1;
        int64_t bottom = width == 64 ? INT64_MIN : -(INT64_C(1) << (width - 1));
        if (value >= (double)top) {
            return masked((uint64_t)top, width);
        }
        if (value <= (double)bottom) {
            return masked((uint64_t)bottom, width);
        }
        return masked((uint64_t)(int64_t)value, width);
    }
    uint64_t top = width == 64 ? UINT64_MAX : (UINT64_C(1) << width) - 1;
    if (value >= (double)top) {
        return masked(top, width);
    }
    if (value <= 0.0) {
        return 0;
    }
    return masked((uint64_t)value, width);
}

uint64_t adamas_cast(uint64_t bits, uint8_t from, uint8_t to) {
    if (!floating_of(from) && !floating_of(to)) {
        return masked((uint64_t)widened(bits, from), width_of(to));
    }
    if (!floating_of(to)) {
        return saturated(as_double(bits, from), to);
    }
    return from_double(as_double(bits, from), to);
}
