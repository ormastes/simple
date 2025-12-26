//! Architecture Definitions and Detection
//!
//! Common architecture traits and detection for embedded targets.

/// Supported embedded architectures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmbeddedArch {
    /// ARM Cortex-M0/M0+
    CortexM0,
    /// ARM Cortex-M3
    CortexM3,
    /// ARM Cortex-M4
    CortexM4,
    /// ARM Cortex-M7
    CortexM7,
    /// RISC-V 32-bit
    Riscv32,
    /// RISC-V 64-bit
    Riscv64,
}

impl EmbeddedArch {
    /// Get the current target architecture.
    #[cfg(feature = "arm-cortex-m0")]
    pub const fn current() -> Self {
        Self::CortexM0
    }

    #[cfg(feature = "arm-cortex-m3")]
    pub const fn current() -> Self {
        Self::CortexM3
    }

    #[cfg(feature = "arm-cortex-m4")]
    pub const fn current() -> Self {
        Self::CortexM4
    }

    #[cfg(feature = "arm-cortex-m7")]
    pub const fn current() -> Self {
        Self::CortexM7
    }

    #[cfg(feature = "riscv32")]
    pub const fn current() -> Self {
        Self::Riscv32
    }

    #[cfg(feature = "riscv64")]
    pub const fn current() -> Self {
        Self::Riscv64
    }

    #[cfg(not(any(
        feature = "arm-cortex-m0",
        feature = "arm-cortex-m3",
        feature = "arm-cortex-m4",
        feature = "arm-cortex-m7",
        feature = "riscv32",
        feature = "riscv64"
    )))]
    pub const fn current() -> Self {
        Self::CortexM4 // Default fallback
    }

    /// Get pointer size in bytes.
    pub const fn pointer_size(&self) -> usize {
        match self {
            Self::CortexM0 | Self::CortexM3 | Self::CortexM4 | Self::CortexM7 | Self::Riscv32 => 4,
            Self::Riscv64 => 8,
        }
    }

    /// Check if architecture has FPU.
    pub const fn has_fpu(&self) -> bool {
        match self {
            Self::CortexM4 | Self::CortexM7 => true,
            _ => false,
        }
    }

    /// Check if architecture has DSP extensions.
    pub const fn has_dsp(&self) -> bool {
        match self {
            Self::CortexM4 | Self::CortexM7 => true,
            _ => false,
        }
    }

    /// Get default stack alignment.
    pub const fn stack_alignment(&self) -> usize {
        match self {
            Self::CortexM0 | Self::CortexM3 | Self::CortexM4 | Self::CortexM7 => 8,
            Self::Riscv32 => 16,
            Self::Riscv64 => 16,
        }
    }

    /// Get the interrupt vector table size (number of entries).
    pub const fn vector_table_size(&self) -> usize {
        match self {
            Self::CortexM0 => 48,  // 16 + 32 external
            Self::CortexM3 => 256, // 16 + 240 external
            Self::CortexM4 => 256,
            Self::CortexM7 => 256,
            Self::Riscv32 | Self::Riscv64 => 32, // PLIC interrupts
        }
    }
}

/// Architecture-specific initialization trait.
pub trait ArchInit {
    /// Perform early initialization before BSS/data setup.
    ///
    /// # Safety
    /// Called before C runtime is set up.
    unsafe fn early_init();

    /// Perform late initialization after BSS/data setup.
    ///
    /// # Safety
    /// Called after C runtime is set up but before main.
    unsafe fn late_init();

    /// Enable interrupts.
    unsafe fn enable_interrupts();

    /// Disable interrupts.
    unsafe fn disable_interrupts();

    /// Wait for interrupt (low power sleep).
    fn wait_for_interrupt();

    /// Trigger a software reset.
    fn reset() -> !;

    /// Get the current stack pointer.
    fn stack_pointer() -> usize;

    /// Set the stack pointer.
    ///
    /// # Safety
    /// Caller must ensure the new stack pointer is valid.
    unsafe fn set_stack_pointer(sp: usize);
}

/// Memory barrier operations.
pub trait MemoryBarrier {
    /// Data memory barrier.
    fn dmb();

    /// Data synchronization barrier.
    fn dsb();

    /// Instruction synchronization barrier.
    fn isb();
}
