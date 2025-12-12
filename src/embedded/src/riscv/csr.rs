//! RISC-V Control and Status Registers (CSR)
//!
//! Common CSR definitions and accessors.

/// Machine Status Register bits.
pub mod mstatus {
    /// Machine Interrupt Enable.
    pub const MIE: usize = 1 << 3;
    /// Machine Previous Interrupt Enable.
    pub const MPIE: usize = 1 << 7;
    /// Machine Previous Privilege.
    pub const MPP_MASK: usize = 0x3 << 11;
    /// Floating-point Status (dirty).
    pub const FS_MASK: usize = 0x3 << 13;
}

/// Machine Interrupt Enable Register bits.
pub mod mie {
    /// Machine Software Interrupt Enable.
    pub const MSIE: usize = 1 << 3;
    /// Machine Timer Interrupt Enable.
    pub const MTIE: usize = 1 << 7;
    /// Machine External Interrupt Enable.
    pub const MEIE: usize = 1 << 11;
}

/// Machine Interrupt Pending Register bits.
pub mod mip {
    /// Machine Software Interrupt Pending.
    pub const MSIP: usize = 1 << 3;
    /// Machine Timer Interrupt Pending.
    pub const MTIP: usize = 1 << 7;
    /// Machine External Interrupt Pending.
    pub const MEIP: usize = 1 << 11;
}

/// Machine Cause Register values.
pub mod mcause {
    // Interrupts (bit 31/63 set)
    /// Machine Software Interrupt.
    pub const MSI: usize = 3;
    /// Machine Timer Interrupt.
    pub const MTI: usize = 7;
    /// Machine External Interrupt.
    pub const MEI: usize = 11;

    // Exceptions (bit 31/63 clear)
    /// Instruction address misaligned.
    pub const INSTR_MISALIGNED: usize = 0;
    /// Instruction access fault.
    pub const INSTR_ACCESS_FAULT: usize = 1;
    /// Illegal instruction.
    pub const ILLEGAL_INSTR: usize = 2;
    /// Breakpoint.
    pub const BREAKPOINT: usize = 3;
    /// Load address misaligned.
    pub const LOAD_MISALIGNED: usize = 4;
    /// Load access fault.
    pub const LOAD_ACCESS_FAULT: usize = 5;
    /// Store/AMO address misaligned.
    pub const STORE_MISALIGNED: usize = 6;
    /// Store/AMO access fault.
    pub const STORE_ACCESS_FAULT: usize = 7;
    /// Environment call from U-mode.
    pub const ECALL_U: usize = 8;
    /// Environment call from S-mode.
    pub const ECALL_S: usize = 9;
    /// Environment call from M-mode.
    pub const ECALL_M: usize = 11;
    /// Instruction page fault.
    pub const INSTR_PAGE_FAULT: usize = 12;
    /// Load page fault.
    pub const LOAD_PAGE_FAULT: usize = 13;
    /// Store/AMO page fault.
    pub const STORE_PAGE_FAULT: usize = 15;
}

/// Read mstatus CSR.
#[inline]
pub fn read_mstatus() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mstatus", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Write mstatus CSR.
#[inline]
pub unsafe fn write_mstatus(value: usize) {
    core::arch::asm!("csrw mstatus, {}", in(reg) value, options(nomem, nostack));
}

/// Read mie CSR.
#[inline]
pub fn read_mie() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mie", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Write mie CSR.
#[inline]
pub unsafe fn write_mie(value: usize) {
    core::arch::asm!("csrw mie, {}", in(reg) value, options(nomem, nostack));
}

/// Read mip CSR.
#[inline]
pub fn read_mip() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mip", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Read mcause CSR.
#[inline]
pub fn read_mcause() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mcause", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Read mepc CSR.
#[inline]
pub fn read_mepc() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mepc", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Write mepc CSR.
#[inline]
pub unsafe fn write_mepc(value: usize) {
    core::arch::asm!("csrw mepc, {}", in(reg) value, options(nomem, nostack));
}

/// Read mtvec CSR.
#[inline]
pub fn read_mtvec() -> usize {
    let value: usize;
    unsafe {
        core::arch::asm!("csrr {}, mtvec", out(reg) value, options(nomem, nostack));
    }
    value
}

/// Write mtvec CSR.
#[inline]
pub unsafe fn write_mtvec(value: usize) {
    core::arch::asm!("csrw mtvec, {}", in(reg) value, options(nomem, nostack));
}

/// Read cycle counter.
#[inline]
pub fn read_cycle() -> u64 {
    #[cfg(feature = "riscv32")]
    {
        loop {
            let hi1: u32;
            let lo: u32;
            let hi2: u32;
            unsafe {
                core::arch::asm!(
                    "csrr {0}, cycleh",
                    "csrr {1}, cycle",
                    "csrr {2}, cycleh",
                    out(reg) hi1,
                    out(reg) lo,
                    out(reg) hi2,
                    options(nomem, nostack)
                );
            }
            if hi1 == hi2 {
                return ((hi1 as u64) << 32) | (lo as u64);
            }
        }
    }

    #[cfg(feature = "riscv64")]
    {
        let value: u64;
        unsafe {
            core::arch::asm!("csrr {}, cycle", out(reg) value, options(nomem, nostack));
        }
        value
    }

    #[cfg(not(any(feature = "riscv32", feature = "riscv64")))]
    0
}

/// Read time counter.
#[inline]
pub fn read_time() -> u64 {
    #[cfg(feature = "riscv32")]
    {
        loop {
            let hi1: u32;
            let lo: u32;
            let hi2: u32;
            unsafe {
                core::arch::asm!(
                    "csrr {0}, timeh",
                    "csrr {1}, time",
                    "csrr {2}, timeh",
                    out(reg) hi1,
                    out(reg) lo,
                    out(reg) hi2,
                    options(nomem, nostack)
                );
            }
            if hi1 == hi2 {
                return ((hi1 as u64) << 32) | (lo as u64);
            }
        }
    }

    #[cfg(feature = "riscv64")]
    {
        let value: u64;
        unsafe {
            core::arch::asm!("csrr {}, time", out(reg) value, options(nomem, nostack));
        }
        value
    }

    #[cfg(not(any(feature = "riscv32", feature = "riscv64")))]
    0
}

/// Read instructions retired counter.
#[inline]
pub fn read_instret() -> u64 {
    #[cfg(feature = "riscv32")]
    {
        loop {
            let hi1: u32;
            let lo: u32;
            let hi2: u32;
            unsafe {
                core::arch::asm!(
                    "csrr {0}, instreth",
                    "csrr {1}, instret",
                    "csrr {2}, instreth",
                    out(reg) hi1,
                    out(reg) lo,
                    out(reg) hi2,
                    options(nomem, nostack)
                );
            }
            if hi1 == hi2 {
                return ((hi1 as u64) << 32) | (lo as u64);
            }
        }
    }

    #[cfg(feature = "riscv64")]
    {
        let value: u64;
        unsafe {
            core::arch::asm!("csrr {}, instret", out(reg) value, options(nomem, nostack));
        }
        value
    }

    #[cfg(not(any(feature = "riscv32", feature = "riscv64")))]
    0
}
