//! RISC-V Support
//!
//! This module provides startup code and runtime support for RISC-V processors.

pub mod clint;
pub mod csr;
pub mod plic;
pub mod startup;

pub use startup::*;

use crate::arch::{ArchInit, MemoryBarrier};

/// RISC-V architecture implementation.
pub struct Riscv;

impl ArchInit for Riscv {
    unsafe fn early_init() {
        // Disable all interrupts
        #[cfg(feature = "riscv32")]
        core::arch::asm!("csrci mstatus, 0x8", options(nomem, nostack)); // Clear MIE

        #[cfg(feature = "riscv64")]
        core::arch::asm!("csrci mstatus, 0x8", options(nomem, nostack)); // Clear MIE

        // Set up trap vector
        extern "C" {
            fn _trap_handler();
        }
        let trap_addr = _trap_handler as usize;

        #[cfg(feature = "riscv32")]
        core::arch::asm!(
            "csrw mtvec, {0}",
            in(reg) trap_addr,
            options(nomem, nostack)
        );

        #[cfg(feature = "riscv64")]
        core::arch::asm!(
            "csrw mtvec, {0}",
            in(reg) trap_addr,
            options(nomem, nostack)
        );
    }

    unsafe fn late_init() {
        // Enable machine external interrupts if needed
        // This depends on the specific platform
    }

    unsafe fn enable_interrupts() {
        #[cfg(feature = "riscv32")]
        core::arch::asm!("csrsi mstatus, 0x8", options(nomem, nostack)); // Set MIE

        #[cfg(feature = "riscv64")]
        core::arch::asm!("csrsi mstatus, 0x8", options(nomem, nostack));
    }

    unsafe fn disable_interrupts() {
        #[cfg(feature = "riscv32")]
        core::arch::asm!("csrci mstatus, 0x8", options(nomem, nostack)); // Clear MIE

        #[cfg(feature = "riscv64")]
        core::arch::asm!("csrci mstatus, 0x8", options(nomem, nostack));
    }

    fn wait_for_interrupt() {
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }
    }

    fn reset() -> ! {
        // Attempt to reset via the debug module or platform-specific method
        // Fallback to infinite loop
        loop {
            unsafe {
                core::arch::asm!("wfi", options(nomem, nostack));
            }
        }
    }

    fn stack_pointer() -> usize {
        let sp: usize;
        unsafe {
            core::arch::asm!("mv {}, sp", out(reg) sp, options(nomem, nostack));
        }
        sp
    }

    unsafe fn set_stack_pointer(sp: usize) {
        core::arch::asm!("mv sp, {}", in(reg) sp, options(nomem, nostack));
    }
}

impl MemoryBarrier for Riscv {
    fn dmb() {
        unsafe {
            core::arch::asm!("fence rw, rw", options(nomem, nostack));
        }
    }

    fn dsb() {
        unsafe {
            core::arch::asm!("fence rw, rw", options(nomem, nostack));
        }
    }

    fn isb() {
        unsafe {
            core::arch::asm!("fence.i", options(nomem, nostack));
        }
    }
}

/// Read a CSR.
#[macro_export]
macro_rules! read_csr {
    ($csr:expr) => {{
        let value: usize;
        unsafe {
            core::arch::asm!(
                concat!("csrr {0}, ", $csr),
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }};
}

/// Write a CSR.
#[macro_export]
macro_rules! write_csr {
    ($csr:expr, $value:expr) => {{
        unsafe {
            core::arch::asm!(
                concat!("csrw ", $csr, ", {0}"),
                in(reg) $value,
                options(nomem, nostack)
            );
        }
    }};
}

/// Set bits in a CSR.
#[macro_export]
macro_rules! set_csr {
    ($csr:expr, $bits:expr) => {{
        unsafe {
            core::arch::asm!(
                concat!("csrs ", $csr, ", {0}"),
                in(reg) $bits,
                options(nomem, nostack)
            );
        }
    }};
}

/// Clear bits in a CSR.
#[macro_export]
macro_rules! clear_csr {
    ($csr:expr, $bits:expr) => {{
        unsafe {
            core::arch::asm!(
                concat!("csrc ", $csr, ", {0}"),
                in(reg) $bits,
                options(nomem, nostack)
            );
        }
    }};
}

/// Check if we're in machine mode.
#[inline]
pub fn in_machine_mode() -> bool {
    // Read mstatus to check privilege level
    // This is a simplified check - actual implementation depends on extensions
    true // Assume machine mode for bare metal
}

/// Critical section guard for RISC-V.
pub struct CriticalSection {
    mstatus: usize,
}

impl CriticalSection {
    /// Enter a critical section (disable interrupts).
    #[inline]
    pub fn enter() -> Self {
        let mstatus: usize;
        unsafe {
            core::arch::asm!(
                "csrrci {0}, mstatus, 0x8",  // Read and clear MIE
                out(reg) mstatus,
                options(nomem, nostack)
            );
        }
        CriticalSection { mstatus }
    }
}

impl Drop for CriticalSection {
    #[inline]
    fn drop(&mut self) {
        // Restore MIE bit if it was set
        if self.mstatus & 0x8 != 0 {
            unsafe {
                core::arch::asm!("csrsi mstatus, 0x8", options(nomem, nostack));
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
