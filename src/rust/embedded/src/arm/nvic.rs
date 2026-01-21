//! Nested Vectored Interrupt Controller (NVIC)
//!
//! Provides interrupt management for ARM Cortex-M processors.

/// NVIC base address.
const NVIC_BASE: usize = 0xE000_E100;

/// NVIC Interrupt Set-Enable Registers (ISER).
const NVIC_ISER: *mut u32 = NVIC_BASE as *mut u32;

/// NVIC Interrupt Clear-Enable Registers (ICER).
const NVIC_ICER: *mut u32 = (NVIC_BASE + 0x80) as *mut u32;

/// NVIC Interrupt Set-Pending Registers (ISPR).
const NVIC_ISPR: *mut u32 = (NVIC_BASE + 0x100) as *mut u32;

/// NVIC Interrupt Clear-Pending Registers (ICPR).
const NVIC_ICPR: *mut u32 = (NVIC_BASE + 0x180) as *mut u32;

/// NVIC Interrupt Active Bit Registers (IABR).
const NVIC_IABR: *const u32 = (NVIC_BASE + 0x200) as *const u32;

/// NVIC Interrupt Priority Registers (IPR).
const NVIC_IPR: *mut u8 = (NVIC_BASE + 0x300) as *mut u8;

/// Maximum number of external interrupts.
pub const MAX_IRQS: usize = 240;

/// Interrupt number type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Irq(pub u8);

impl Irq {
    /// Create a new IRQ from number.
    pub const fn new(n: u8) -> Self {
        Self(n)
    }

    /// Get the IRQ number.
    pub const fn number(&self) -> u8 {
        self.0
    }
}

/// Enable an interrupt.
#[inline]
pub fn enable(irq: Irq) {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe {
        NVIC_ISER.add(reg_index).write_volatile(1 << bit_index);
    }
}

/// Disable an interrupt.
#[inline]
pub fn disable(irq: Irq) {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe {
        NVIC_ICER.add(reg_index).write_volatile(1 << bit_index);
    }
}

/// Check if an interrupt is enabled.
#[inline]
pub fn is_enabled(irq: Irq) -> bool {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe { (NVIC_ISER.add(reg_index).read_volatile() >> bit_index) & 1 != 0 }
}

/// Set an interrupt pending.
#[inline]
pub fn set_pending(irq: Irq) {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe {
        NVIC_ISPR.add(reg_index).write_volatile(1 << bit_index);
    }
}

/// Clear an interrupt pending flag.
#[inline]
pub fn clear_pending(irq: Irq) {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe {
        NVIC_ICPR.add(reg_index).write_volatile(1 << bit_index);
    }
}

/// Check if an interrupt is pending.
#[inline]
pub fn is_pending(irq: Irq) -> bool {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe { (NVIC_ISPR.add(reg_index).read_volatile() >> bit_index) & 1 != 0 }
}

/// Check if an interrupt is active.
#[inline]
pub fn is_active(irq: Irq) -> bool {
    let n = irq.0 as usize;
    let reg_index = n / 32;
    let bit_index = n % 32;

    unsafe { (NVIC_IABR.add(reg_index).read_volatile() >> bit_index) & 1 != 0 }
}

/// Set interrupt priority.
///
/// Priority is typically 0-255, with 0 being highest priority.
/// Note: Many Cortex-M devices only implement the upper bits (e.g., 4 bits = 16 levels).
#[inline]
pub fn set_priority(irq: Irq, priority: u8) {
    unsafe {
        NVIC_IPR.add(irq.0 as usize).write_volatile(priority);
    }
}

/// Get interrupt priority.
#[inline]
pub fn get_priority(irq: Irq) -> u8 {
    unsafe { NVIC_IPR.add(irq.0 as usize).read_volatile() }
}

/// System Control Block registers for system exceptions.
mod scb {
    /// SCB SHPR (System Handler Priority Register) base.
    const SCB_SHPR: *mut u8 = 0xE000_ED18 as *mut u8;

    /// System exception indices in SHPR.
    #[repr(u8)]
    pub enum SystemException {
        MemManage = 4,
        BusFault = 5,
        UsageFault = 6,
        SVCall = 11,
        DebugMonitor = 12,
        PendSV = 14,
        SysTick = 15,
    }

    /// Set system exception priority.
    pub fn set_system_priority(exc: SystemException, priority: u8) {
        let idx = match exc {
            SystemException::MemManage => 0,
            SystemException::BusFault => 1,
            SystemException::UsageFault => 2,
            SystemException::SVCall => 7,
            SystemException::DebugMonitor => 8,
            SystemException::PendSV => 10,
            SystemException::SysTick => 11,
        };

        unsafe {
            SCB_SHPR.add(idx).write_volatile(priority);
        }
    }
}

pub use scb::{set_system_priority, SystemException};

/// Disable all interrupts and return the previous state.
#[inline]
pub fn disable_all() -> bool {
    let primask: u32;
    unsafe {
        core::arch::asm!(
            "mrs {}, primask",
            "cpsid i",
            out(reg) primask,
            options(nomem, nostack)
        );
    }
    primask & 1 == 0 // Return true if interrupts were enabled
}

/// Restore interrupt state.
#[inline]
pub fn restore(enabled: bool) {
    if enabled {
        unsafe {
            core::arch::asm!("cpsie i", options(nomem, nostack));
        }
    }
}
