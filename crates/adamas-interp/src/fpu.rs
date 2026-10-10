//! Режим плавающей арифметики после чужого вызова (§4.3, §10 вопрос 68).
//!
//! Машина зовёт чужой символ в своём же процессе, и режим, оставленный им
//! (`fesetround`, FTZ/DAZ), меняет её собственную арифметику - и арифметику
//! компилятора после неё. Правило то же, что у понижений (`c/fpu.c`
//! рантайма): после вызова режим сверяется и, если сменился, возвращается к
//! умолчанию. Флаги исключений не трогаются.

/// Возвращает режим по умолчанию, если он сменился.
#[cfg(target_arch = "x86_64")]
pub(crate) fn restore() {
    /// MXCSR без флагов исключений: DAZ, маски, округление, FTZ.
    const CONTROL: u32 = 0xffc0;
    /// Округление к ближайшему, исключения замаскированы, денормалы как есть.
    const DEFAULT: u32 = 0x1f80;

    let mut csr: u32 = 0;
    // SAFETY: `stmxcsr` пишет четыре байта в `csr`, `ldmxcsr` читает четыре
    // байта из `fixed`; оба адреса - живые локальные переменные.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("stmxcsr [{}]", in(reg) &raw mut csr, options(nostack, preserves_flags));
    }
    if csr & CONTROL != DEFAULT {
        let fixed = DEFAULT | (csr & !CONTROL);
        #[allow(
            unsafe_code,
            reason = "регистр режима читается и пишется только инструкцией (§4.3)"
        )]
        unsafe {
            std::arch::asm!("ldmxcsr [{}]", in(reg) &raw const fixed, options(nostack, preserves_flags));
        }
    }
}

/// Возвращает режим по умолчанию, если он сменился.
#[cfg(target_arch = "aarch64")]
pub(crate) fn restore() {
    let fpcr: u64;
    // SAFETY: чтение и запись FPCR памяти не касаются.
    #[allow(
        unsafe_code,
        reason = "регистр режима читается и пишется только инструкцией (§4.3)"
    )]
    unsafe {
        std::arch::asm!("mrs {}, fpcr", out(reg) fpcr, options(nomem, nostack, preserves_flags));
        if fpcr != 0 {
            std::arch::asm!("msr fpcr, {}", in(reg) 0_u64, options(nomem, nostack, preserves_flags));
        }
    }
}

/// Прочие архитектуры режима не сверяют - как и рантайм.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub(crate) fn restore() {}
