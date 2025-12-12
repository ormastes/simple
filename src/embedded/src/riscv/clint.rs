//! Core Local Interruptor (CLINT)
//!
//! RISC-V standard timer and software interrupt controller.

/// Default CLINT base address (platform specific).
pub const CLINT_BASE: usize = 0x0200_0000;

/// CLINT configuration.
#[derive(Clone, Copy)]
pub struct ClintConfig {
    /// Base address of the CLINT.
    pub base: usize,
    /// Number of harts.
    pub num_harts: usize,
    /// Timer frequency in Hz.
    pub timer_freq: u64,
}

impl Default for ClintConfig {
    fn default() -> Self {
        Self {
            base: CLINT_BASE,
            num_harts: 1,
            timer_freq: 10_000_000, // 10 MHz default
        }
    }
}

/// CLINT driver.
pub struct Clint {
    config: ClintConfig,
}

impl Clint {
    /// Create a new CLINT instance.
    pub const fn new(config: ClintConfig) -> Self {
        Self { config }
    }

    /// Get MSIP (machine software interrupt pending) register address.
    #[inline]
    fn msip_addr(&self, hart: usize) -> *mut u32 {
        (self.config.base + hart * 4) as *mut u32
    }

    /// Get MTIMECMP register address.
    #[inline]
    fn mtimecmp_addr(&self, hart: usize) -> *mut u64 {
        (self.config.base + 0x4000 + hart * 8) as *mut u64
    }

    /// Get MTIME register address.
    #[inline]
    fn mtime_addr(&self) -> *mut u64 {
        (self.config.base + 0xBFF8) as *mut u64
    }

    /// Trigger a software interrupt on a hart.
    pub fn trigger_soft_interrupt(&self, hart: usize) {
        if hart < self.config.num_harts {
            unsafe {
                self.msip_addr(hart).write_volatile(1);
            }
        }
    }

    /// Clear a software interrupt on a hart.
    pub fn clear_soft_interrupt(&self, hart: usize) {
        if hart < self.config.num_harts {
            unsafe {
                self.msip_addr(hart).write_volatile(0);
            }
        }
    }

    /// Check if software interrupt is pending for a hart.
    pub fn soft_interrupt_pending(&self, hart: usize) -> bool {
        if hart < self.config.num_harts {
            unsafe { self.msip_addr(hart).read_volatile() != 0 }
        } else {
            false
        }
    }

    /// Read the current time value.
    #[inline]
    pub fn read_mtime(&self) -> u64 {
        // For 32-bit systems, need to read carefully to avoid tearing
        #[cfg(feature = "riscv32")]
        {
            loop {
                let hi1 = unsafe { ((self.mtime_addr() as usize + 4) as *const u32).read_volatile() };
                let lo = unsafe { (self.mtime_addr() as *const u32).read_volatile() };
                let hi2 = unsafe { ((self.mtime_addr() as usize + 4) as *const u32).read_volatile() };
                if hi1 == hi2 {
                    return ((hi1 as u64) << 32) | (lo as u64);
                }
            }
        }

        #[cfg(not(feature = "riscv32"))]
        unsafe {
            self.mtime_addr().read_volatile()
        }
    }

    /// Write the time value.
    ///
    /// # Safety
    /// Modifying MTIME affects all harts.
    pub unsafe fn write_mtime(&self, value: u64) {
        self.mtime_addr().write_volatile(value);
    }

    /// Read the timer compare value for a hart.
    pub fn read_mtimecmp(&self, hart: usize) -> u64 {
        if hart < self.config.num_harts {
            // For 32-bit, read carefully
            #[cfg(feature = "riscv32")]
            unsafe {
                let addr = self.mtimecmp_addr(hart);
                let lo = (addr as *const u32).read_volatile();
                let hi = ((addr as usize + 4) as *const u32).read_volatile();
                ((hi as u64) << 32) | (lo as u64)
            }

            #[cfg(not(feature = "riscv32"))]
            unsafe {
                self.mtimecmp_addr(hart).read_volatile()
            }
        } else {
            0
        }
    }

    /// Set the timer compare value for a hart.
    ///
    /// When MTIME >= MTIMECMP, a timer interrupt is generated.
    pub fn write_mtimecmp(&self, hart: usize, value: u64) {
        if hart < self.config.num_harts {
            // For 32-bit systems, write hi first with max value to prevent spurious interrupts
            #[cfg(feature = "riscv32")]
            unsafe {
                let addr = self.mtimecmp_addr(hart);
                // Write max value to high word first
                ((addr as usize + 4) as *mut u32).write_volatile(0xFFFF_FFFF);
                // Write low word
                (addr as *mut u32).write_volatile(value as u32);
                // Write actual high word
                ((addr as usize + 4) as *mut u32).write_volatile((value >> 32) as u32);
            }

            #[cfg(not(feature = "riscv32"))]
            unsafe {
                self.mtimecmp_addr(hart).write_volatile(value);
            }
        }
    }

    /// Set a timer interrupt to fire after a delay.
    ///
    /// `delay_ticks` is in timer ticks (not seconds).
    pub fn set_timer(&self, hart: usize, delay_ticks: u64) {
        let now = self.read_mtime();
        self.write_mtimecmp(hart, now.wrapping_add(delay_ticks));
    }

    /// Set a timer interrupt to fire after a delay in microseconds.
    pub fn set_timer_us(&self, hart: usize, delay_us: u64) {
        let ticks = delay_us * self.config.timer_freq / 1_000_000;
        self.set_timer(hart, ticks);
    }

    /// Set a timer interrupt to fire after a delay in milliseconds.
    pub fn set_timer_ms(&self, hart: usize, delay_ms: u64) {
        let ticks = delay_ms * self.config.timer_freq / 1_000;
        self.set_timer(hart, ticks);
    }

    /// Clear timer interrupt by setting MTIMECMP to max.
    pub fn clear_timer(&self, hart: usize) {
        self.write_mtimecmp(hart, u64::MAX);
    }

    /// Get the timer frequency.
    pub fn timer_freq(&self) -> u64 {
        self.config.timer_freq
    }

    /// Convert timer ticks to microseconds.
    pub fn ticks_to_us(&self, ticks: u64) -> u64 {
        ticks * 1_000_000 / self.config.timer_freq
    }

    /// Convert microseconds to timer ticks.
    pub fn us_to_ticks(&self, us: u64) -> u64 {
        us * self.config.timer_freq / 1_000_000
    }
}

/// Global CLINT instance (must be initialized before use).
static mut CLINT: Option<Clint> = None;

/// Initialize the global CLINT.
///
/// # Safety
/// Must be called once before using other CLINT functions.
pub unsafe fn init(config: ClintConfig) {
    CLINT = Some(Clint::new(config));
}

/// Get the global CLINT instance.
pub fn clint() -> Option<&'static Clint> {
    unsafe { CLINT.as_ref() }
}

/// Simple delay using MTIME polling.
pub fn delay_us(us: u64) {
    if let Some(c) = clint() {
        let start = c.read_mtime();
        let ticks = c.us_to_ticks(us);
        while c.read_mtime().wrapping_sub(start) < ticks {
            core::hint::spin_loop();
        }
    }
}

/// Simple delay in milliseconds.
pub fn delay_ms(ms: u64) {
    delay_us(ms * 1000);
}
