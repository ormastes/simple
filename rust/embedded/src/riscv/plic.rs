//! Platform-Level Interrupt Controller (PLIC)
//!
//! RISC-V standard external interrupt controller.

/// Default PLIC base address (platform specific).
pub const PLIC_BASE: usize = 0x0C00_0000;

/// Maximum number of interrupt sources.
pub const MAX_SOURCES: usize = 1024;

/// Maximum number of contexts (hart * 2 for M and S modes).
pub const MAX_CONTEXTS: usize = 15872;

/// PLIC configuration.
#[derive(Clone, Copy)]
pub struct PlicConfig {
    /// Base address of the PLIC.
    pub base: usize,
    /// Number of interrupt sources.
    pub num_sources: usize,
    /// Number of contexts.
    pub num_contexts: usize,
}

impl Default for PlicConfig {
    fn default() -> Self {
        Self {
            base: PLIC_BASE,
            num_sources: 128,
            num_contexts: 2,
        }
    }
}

/// PLIC driver.
pub struct Plic {
    config: PlicConfig,
}

impl Plic {
    /// Create a new PLIC instance.
    pub const fn new(config: PlicConfig) -> Self {
        Self { config }
    }

    /// Get priority register address for a source.
    #[inline]
    fn priority_addr(&self, source: usize) -> *mut u32 {
        (self.config.base + source * 4) as *mut u32
    }

    /// Get pending register address for a source.
    #[inline]
    fn pending_addr(&self, source: usize) -> *const u32 {
        (self.config.base + 0x1000 + (source / 32) * 4) as *const u32
    }

    /// Get enable register address for a context and source.
    #[inline]
    fn enable_addr(&self, context: usize, source: usize) -> *mut u32 {
        (self.config.base + 0x2000 + context * 0x80 + (source / 32) * 4) as *mut u32
    }

    /// Get threshold register address for a context.
    #[inline]
    fn threshold_addr(&self, context: usize) -> *mut u32 {
        (self.config.base + 0x20_0000 + context * 0x1000) as *mut u32
    }

    /// Get claim/complete register address for a context.
    #[inline]
    fn claim_addr(&self, context: usize) -> *mut u32 {
        (self.config.base + 0x20_0000 + context * 0x1000 + 4) as *mut u32
    }

    /// Set interrupt priority (0 = disabled, 1-7 = priority).
    pub fn set_priority(&self, source: usize, priority: u32) {
        if source > 0 && source < self.config.num_sources {
            unsafe {
                self.priority_addr(source).write_volatile(priority & 0x7);
            }
        }
    }

    /// Get interrupt priority.
    pub fn get_priority(&self, source: usize) -> u32 {
        if source > 0 && source < self.config.num_sources {
            unsafe { self.priority_addr(source).read_volatile() & 0x7 }
        } else {
            0
        }
    }

    /// Check if an interrupt is pending.
    pub fn is_pending(&self, source: usize) -> bool {
        if source > 0 && source < self.config.num_sources {
            let word = source / 32;
            let bit = source % 32;
            unsafe { (self.pending_addr(word).read_volatile() >> bit) & 1 != 0 }
        } else {
            false
        }
    }

    /// Enable an interrupt for a context.
    pub fn enable(&self, context: usize, source: usize) {
        if source > 0 && source < self.config.num_sources && context < self.config.num_contexts {
            let bit = source % 32;
            unsafe {
                let addr = self.enable_addr(context, source);
                addr.write_volatile(addr.read_volatile() | (1 << bit));
            }
        }
    }

    /// Disable an interrupt for a context.
    pub fn disable(&self, context: usize, source: usize) {
        if source > 0 && source < self.config.num_sources && context < self.config.num_contexts {
            let bit = source % 32;
            unsafe {
                let addr = self.enable_addr(context, source);
                addr.write_volatile(addr.read_volatile() & !(1 << bit));
            }
        }
    }

    /// Check if an interrupt is enabled for a context.
    pub fn is_enabled(&self, context: usize, source: usize) -> bool {
        if source > 0 && source < self.config.num_sources && context < self.config.num_contexts {
            let bit = source % 32;
            unsafe { (self.enable_addr(context, source).read_volatile() >> bit) & 1 != 0 }
        } else {
            false
        }
    }

    /// Set threshold for a context.
    pub fn set_threshold(&self, context: usize, threshold: u32) {
        if context < self.config.num_contexts {
            unsafe {
                self.threshold_addr(context).write_volatile(threshold & 0x7);
            }
        }
    }

    /// Get threshold for a context.
    pub fn get_threshold(&self, context: usize) -> u32 {
        if context < self.config.num_contexts {
            unsafe { self.threshold_addr(context).read_volatile() & 0x7 }
        } else {
            0
        }
    }

    /// Claim the highest priority pending interrupt.
    ///
    /// Returns the interrupt source number, or 0 if no interrupt is pending.
    pub fn claim(&self, context: usize) -> u32 {
        if context < self.config.num_contexts {
            unsafe { self.claim_addr(context).read_volatile() }
        } else {
            0
        }
    }

    /// Complete interrupt handling.
    ///
    /// Must be called after handling an interrupt.
    pub fn complete(&self, context: usize, source: u32) {
        if context < self.config.num_contexts {
            unsafe {
                self.claim_addr(context).write_volatile(source);
            }
        }
    }
}

/// Global PLIC instance (must be initialized before use).
static mut PLIC: Option<Plic> = None;

/// Initialize the global PLIC.
///
/// # Safety
/// Must be called once before using other PLIC functions.
pub unsafe fn init(config: PlicConfig) {
    PLIC = Some(Plic::new(config));
}

/// Get the global PLIC instance.
pub fn plic() -> Option<&'static Plic> {
    unsafe { PLIC.as_ref() }
}
