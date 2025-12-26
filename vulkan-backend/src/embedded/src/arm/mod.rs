//! ARM Cortex-M Support
//!
//! This module provides startup code and runtime support for ARM Cortex-M processors.

pub mod nvic;
pub mod startup;
pub mod systick;
pub mod vector;

pub use startup::*;
pub use vector::*;

use crate::arch::{ArchInit, MemoryBarrier};

/// ARM Cortex-M architecture implementation.
pub struct CortexM;

impl ArchInit for CortexM {
    unsafe fn early_init() {
        // Disable interrupts during startup
        core::arch::asm!("cpsid i", options(nomem, nostack));

        // Enable FPU if available (Cortex-M4/M7)
        #[cfg(any(feature = "arm-cortex-m4", feature = "arm-cortex-m7"))]
        {
            // CPACR at 0xE000ED88
            // Enable CP10 and CP11 (FPU)
            let cpacr = 0xE000_ED88 as *mut u32;
            cpacr.write_volatile(cpacr.read_volatile() | (0xF << 20));

            // Ensure FPU is enabled before continuing
            core::arch::asm!("dsb", "isb", options(nomem, nostack));
        }
    }

    unsafe fn late_init() {
        // Set priority grouping (4 bits preemption, 0 bits subpriority)
        let aircr = 0xE000_ED0C as *mut u32;
        let key = 0x05FA_0000;
        let prigroup = 0x300; // 4 bits preemption priority
        aircr.write_volatile(key | prigroup | (aircr.read_volatile() & 0x700));
    }

    unsafe fn enable_interrupts() {
        core::arch::asm!("cpsie i", options(nomem, nostack));
    }

    unsafe fn disable_interrupts() {
        core::arch::asm!("cpsid i", options(nomem, nostack));
    }

    fn wait_for_interrupt() {
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }
    }

    fn reset() -> ! {
        unsafe {
            // Request system reset via AIRCR
            let aircr = 0xE000_ED0C as *mut u32;
            let key = 0x05FA_0000;
            let sysresetreq = 0x4;
            core::arch::asm!("dsb", options(nomem, nostack));
            aircr.write_volatile(key | sysresetreq);
            core::arch::asm!("dsb", options(nomem, nostack));
        }
        loop {
            unsafe {
                core::arch::asm!("wfi", options(nomem, nostack));
            }
        }
    }

    fn stack_pointer() -> usize {
        let sp: usize;
        unsafe {
            core::arch::asm!("mov {}, sp", out(reg) sp, options(nomem, nostack));
        }
        sp
    }

    unsafe fn set_stack_pointer(sp: usize) {
        core::arch::asm!("msr msp, {}", in(reg) sp, options(nomem, nostack));
    }
}

impl MemoryBarrier for CortexM {
    fn dmb() {
        unsafe {
            core::arch::asm!("dmb", options(nomem, nostack));
        }
    }

    fn dsb() {
        unsafe {
            core::arch::asm!("dsb", options(nomem, nostack));
        }
    }

    fn isb() {
        unsafe {
            core::arch::asm!("isb", options(nomem, nostack));
        }
    }
}

/// Read the current exception number.
#[inline]
pub fn current_exception() -> u8 {
    let ipsr: u32;
    unsafe {
        core::arch::asm!("mrs {}, ipsr", out(reg) ipsr, options(nomem, nostack));
    }
    (ipsr & 0xFF) as u8
}

/// Check if we're in handler mode.
#[inline]
pub fn in_handler_mode() -> bool {
    current_exception() != 0
}

/// Read the priority mask register.
#[inline]
pub fn primask() -> bool {
    let primask: u32;
    unsafe {
        core::arch::asm!("mrs {}, primask", out(reg) primask, options(nomem, nostack));
    }
    primask & 1 != 0
}

/// Critical section guard.
pub struct CriticalSection {
    primask: bool,
}

impl CriticalSection {
    /// Enter a critical section (disable interrupts).
    #[inline]
    pub fn enter() -> Self {
        let primask = primask();
        unsafe {
            core::arch::asm!("cpsid i", options(nomem, nostack));
        }
        CriticalSection { primask }
    }
}

impl Drop for CriticalSection {
    #[inline]
    fn drop(&mut self) {
        if !self.primask {
            unsafe {
                core::arch::asm!("cpsie i", options(nomem, nostack));
            }
        }
    }
}

/// Execute code in a critical section.
#[inline]
pub fn critical_section<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    let _cs = CriticalSection::enter();
    f()
}
