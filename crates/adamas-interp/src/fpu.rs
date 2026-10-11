//! Режим плавающей арифметики на границе с чужим кодом (§4.3, §10 вопрос 68).
//!
//! Машина зовёт чужой символ в своём же процессе, и режим, оставленный им
//! (`fesetround`, FTZ/DAZ), меняет её собственную арифметику - и арифметику
//! компилятора после неё. Правило то же, что у понижений (`c/fpu.c`
//! рантайма): после вызова режим сверяется и, если сменился, возвращается к
//! умолчанию. Колбэк зеркален: на входе ставится наш режим, на выходе
//! вызвавшей стороне возвращается её. Флаги исключений не трогаются.

/// Управляющая часть регистра режима: без флагов исключений.
#[cfg(target_arch = "x86_64")]
const CONTROL: u64 = 0xffc0;

/// Режим по умолчанию: округление к ближайшему, исключения замаскированы,
/// денормалы как есть.
#[cfg(target_arch = "x86_64")]
const DEFAULT: u64 = 0x1f80;

/// Регистр режима целиком.
#[cfg(target_arch = "x86_64")]
fn read() -> u64 {
    let mut csr: u32 = 0;
    // SAFETY: `stmxcsr` пишет четыре байта в `csr` - живую локальную.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("stmxcsr [{}]", in(reg) &raw mut csr, options(nostack, preserves_flags));
    }
    u64::from(csr)
}

/// Записывает регистр режима целиком.
#[cfg(target_arch = "x86_64")]
fn write(value: u64) {
    let csr = u32::try_from(value).unwrap_or(0x1f80);
    // SAFETY: `ldmxcsr` читает четыре байта из `csr` - живой локальной.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("ldmxcsr [{}]", in(reg) &raw const csr, options(nostack, preserves_flags));
    }
}

/// FPCR целиком управляющий: флаги исключений живут в FPSR.
#[cfg(target_arch = "aarch64")]
const CONTROL: u64 = u64::MAX;

/// Умолчание FPCR - ноль.
#[cfg(target_arch = "aarch64")]
const DEFAULT: u64 = 0;

/// Регистр режима целиком.
#[cfg(target_arch = "aarch64")]
fn read() -> u64 {
    let fpcr: u64;
    // SAFETY: чтение FPCR памяти не касается.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("mrs {}, fpcr", out(reg) fpcr, options(nomem, nostack, preserves_flags));
    }
    fpcr
}

/// Записывает регистр режима целиком.
#[cfg(target_arch = "aarch64")]
fn write(value: u64) {
    // SAFETY: запись FPCR памяти не касается.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("msr fpcr, {}", in(reg) value, options(nomem, nostack, preserves_flags));
    }
}

/// Прочие архитектуры режима не сверяют - как и рантайм.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const CONTROL: u64 = 0;

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const DEFAULT: u64 = 0;

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn read() -> u64 {
    0
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn write(_value: u64) {}

/// Ставит управляющую часть `wanted`, если сейчас стоит другая. Отдаёт
/// управляющую часть, стоявшую до того.
fn set(wanted: u64) -> u64 {
    let current = read();
    if current & CONTROL != wanted {
        write(wanted | (current & !CONTROL));
    }
    current & CONTROL
}

/// Возвращает режим по умолчанию после чужого вызова, если он сменился.
pub(crate) fn restore() {
    set(DEFAULT);
}

/// Вход в колбэк: ставит наш режим и отдаёт режим вызвавшей стороны.
pub(crate) fn enter() -> u64 {
    set(DEFAULT)
}

/// Выход из колбэка: возвращает вызвавшей стороне её режим.
pub(crate) fn leave(saved: u64) {
    set(saved);
}
