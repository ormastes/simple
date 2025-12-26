//! SysTick Timer
//!
//! System timer for ARM Cortex-M processors.

/// SysTick Control and Status Register.
const SYST_CSR: *mut u32 = 0xE000_E010 as *mut u32;

/// SysTick Reload Value Register.
const SYST_RVR: *mut u32 = 0xE000_E014 as *mut u32;

/// SysTick Current Value Register.
const SYST_CVR: *mut u32 = 0xE000_E018 as *mut u32;

/// SysTick Calibration Value Register.
const SYST_CALIB: *const u32 = 0xE000_E01C as *const u32;

/// CSR bit: Enable counter.
const CSR_ENABLE: u32 = 1 << 0;

/// CSR bit: Enable interrupt.
const CSR_TICKINT: u32 = 1 << 1;

/// CSR bit: Use processor clock (vs external reference).
const CSR_CLKSOURCE: u32 = 1 << 2;

/// CSR bit: Counter reached zero since last read.
const CSR_COUNTFLAG: u32 = 1 << 16;

/// SysTick timer configuration.
#[derive(Debug, Clone, Copy)]
pub struct SysTickConfig {
    /// Reload value (24-bit max).
    pub reload: u32,
    /// Use processor clock (true) or external reference (false).
    pub use_processor_clock: bool,
    /// Enable interrupt on zero.
    pub enable_interrupt: bool,
}

impl Default for SysTickConfig {
    fn default() -> Self {
        Self {
            reload: 0x00FF_FFFF, // Max value
            use_processor_clock: true,
            enable_interrupt: false,
        }
    }
}

/// Configure and start SysTick.
pub fn configure(config: SysTickConfig) {
    // Disable first
    disable();

    // Clear current value
    unsafe {
        SYST_CVR.write_volatile(0);
    }

    // Set reload value (24-bit)
    let reload = config.reload & 0x00FF_FFFF;
    unsafe {
        SYST_RVR.write_volatile(reload);
    }

    // Configure and enable
    let mut csr = CSR_ENABLE;
    if config.use_processor_clock {
        csr |= CSR_CLKSOURCE;
    }
    if config.enable_interrupt {
        csr |= CSR_TICKINT;
    }

    unsafe {
        SYST_CSR.write_volatile(csr);
    }
}

/// Enable SysTick counter.
pub fn enable() {
    unsafe {
        let csr = SYST_CSR.read_volatile();
        SYST_CSR.write_volatile(csr | CSR_ENABLE);
    }
}

/// Disable SysTick counter.
pub fn disable() {
    unsafe {
        let csr = SYST_CSR.read_volatile();
        SYST_CSR.write_volatile(csr & !CSR_ENABLE);
    }
}

/// Enable SysTick interrupt.
pub fn enable_interrupt() {
    unsafe {
        let csr = SYST_CSR.read_volatile();
        SYST_CSR.write_volatile(csr | CSR_TICKINT);
    }
}

/// Disable SysTick interrupt.
pub fn disable_interrupt() {
    unsafe {
        let csr = SYST_CSR.read_volatile();
        SYST_CSR.write_volatile(csr & !CSR_TICKINT);
    }
}

/// Get current counter value.
#[inline]
pub fn current() -> u32 {
    unsafe { SYST_CVR.read_volatile() & 0x00FF_FFFF }
}

/// Get reload value.
#[inline]
pub fn reload_value() -> u32 {
    unsafe { SYST_RVR.read_volatile() & 0x00FF_FFFF }
}

/// Check if counter has reached zero since last read.
#[inline]
pub fn has_wrapped() -> bool {
    unsafe { (SYST_CSR.read_volatile() & CSR_COUNTFLAG) != 0 }
}

/// Check if SysTick is enabled.
#[inline]
pub fn is_enabled() -> bool {
    unsafe { (SYST_CSR.read_volatile() & CSR_ENABLE) != 0 }
}

/// Get calibration value.
///
/// Returns the reload value for a 10ms tick at the processor clock frequency.
/// Returns None if calibration is not available.
pub fn calibration() -> Option<u32> {
    let calib = unsafe { SYST_CALIB.read_volatile() };

    // Bit 31: NOREF - no external reference clock
    // Bit 30: SKEW - calibration value is not exactly 10ms
    // Bits 23:0: TENMS - reload value for 10ms

    let tenms = calib & 0x00FF_FFFF;
    if tenms == 0 {
        None
    } else {
        Some(tenms)
    }
}

/// Configure SysTick for a specific frequency.
///
/// Returns the actual frequency achieved, or None if not possible.
pub fn configure_frequency(cpu_freq_hz: u32, tick_freq_hz: u32) -> Option<u32> {
    if tick_freq_hz == 0 || cpu_freq_hz == 0 {
        return None;
    }

    let reload = cpu_freq_hz / tick_freq_hz;
    if reload == 0 || reload > 0x00FF_FFFF {
        return None;
    }

    configure(SysTickConfig {
        reload: reload - 1, // Counter counts from RELOAD to 0
        use_processor_clock: true,
        enable_interrupt: true,
    });

    // Return actual frequency
    Some(cpu_freq_hz / reload)
}

/// Simple delay using SysTick polling.
///
/// Note: This is a blocking delay and should only be used when interrupts are disabled
/// or SysTick interrupt is not being used for other purposes.
pub fn delay_cycles(cycles: u32) {
    // Save current config
    let was_enabled = is_enabled();
    let old_reload = reload_value();
    let old_csr = unsafe { SYST_CSR.read_volatile() };

    // Configure for delay
    disable();
    unsafe {
        SYST_CVR.write_volatile(0);
    }

    let mut remaining = cycles;
    while remaining > 0 {
        let count = remaining.min(0x00FF_FFFF);
        unsafe {
            SYST_RVR.write_volatile(count);
            SYST_CVR.write_volatile(0);
            SYST_CSR.write_volatile(CSR_ENABLE | CSR_CLKSOURCE);
        }

        // Wait for wrap
        while !has_wrapped() {}

        remaining = remaining.saturating_sub(count + 1);
    }

    // Restore config
    disable();
    unsafe {
        SYST_RVR.write_volatile(old_reload);
        SYST_CVR.write_volatile(0);
        SYST_CSR.write_volatile(old_csr);
    }

    if was_enabled {
        enable();
    }
}
