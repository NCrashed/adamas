/* Режим плавающей арифметики (§4.3, §10 вопрос 68).
 *
 * Основные операции воспроизводимы только в режиме по умолчанию: округление к
 * ближайшему, денормалы как есть (без FTZ/DAZ), исключения замаскированы. Режим
 * - состояние процессора, а не значение, и чужая функция вправе его сменить и
 * не вернуть: `fesetround` из libm сдвигает ответ `0.1 + 0.2` на ULP во всей
 * программе.
 *
 * Поэтому режим выставляется при старте, а после каждого чужого вызова
 * сверяется и, если сменился, возвращается. Сверка - чтение регистра и
 * сравнение, запись - только при смене: около наносекунды на вызов (замер
 * 2026-10-10, x86-64). Липкие флаги исключений не сверяются и не трогаются:
 * их выставляет всякая арифметика, и режимом они не являются.
 *
 * Прочие архитектуры режима не сверяют: обещание §4.3 держится там на слове
 * обёртки.
 */

#include "adamas.h"

#if defined(__x86_64__)

#include <xmmintrin.h>

/* MXCSR без шести младших битов - флагов исключений: DAZ, маски, округление,
 * FTZ. */
#define ADAMAS_FPU_CONTROL 0xffc0u
#define ADAMAS_FPU_DEFAULT 0x1f80u

void adamas_fpu_default(void) {
    _mm_setcsr(ADAMAS_FPU_DEFAULT | (_mm_getcsr() & ~ADAMAS_FPU_CONTROL));
}

void adamas_fpu_check(void) {
    unsigned int csr = _mm_getcsr();
    if ((csr & ADAMAS_FPU_CONTROL) != ADAMAS_FPU_DEFAULT) {
        _mm_setcsr(ADAMAS_FPU_DEFAULT | (csr & ~ADAMAS_FPU_CONTROL));
    }
}

#elif defined(__aarch64__)

/* FPCR целиком управляющий: флаги исключений живут в FPSR. Умолчание - ноль. */
static uint64_t adamas_fpcr(void) {
    uint64_t value;
    __asm__ volatile("mrs %0, fpcr" : "=r"(value));
    return value;
}

void adamas_fpu_default(void) {
    __asm__ volatile("msr fpcr, %0" : : "r"((uint64_t)0));
}

void adamas_fpu_check(void) {
    if (adamas_fpcr() != 0) {
        adamas_fpu_default();
    }
}

#else

void adamas_fpu_default(void) {}

void adamas_fpu_check(void) {}

#endif
