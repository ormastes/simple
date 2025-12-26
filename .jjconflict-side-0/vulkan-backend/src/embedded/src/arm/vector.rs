//! ARM Cortex-M Vector Table
//!
//! This module defines the interrupt vector table for ARM Cortex-M processors.

use super::startup::*;

/// Exception handler function type.
pub type ExceptionHandler = unsafe extern "C" fn();

/// Exception handler that never returns.
pub type ExceptionHandlerNoReturn = unsafe extern "C" fn() -> !;

/// Vector table entry union.
#[repr(C)]
#[derive(Copy, Clone)]
pub union VectorTableEntry {
    /// Handler function pointer.
    pub handler: ExceptionHandler,
    /// Initial stack pointer (entry 0).
    pub stack_pointer: u32,
    /// Reserved entry.
    pub reserved: u32,
}

/// ARM Cortex-M vector table structure.
///
/// The vector table is placed at the start of flash (or RAM for bootloaders)
/// and contains the initial stack pointer and exception handlers.
#[repr(C)]
pub struct VectorTable {
    /// Initial stack pointer value.
    pub initial_sp: u32,
    /// Reset handler.
    pub reset: ExceptionHandler,
    /// Non-maskable interrupt.
    pub nmi: ExceptionHandler,
    /// Hard fault.
    pub hard_fault: ExceptionHandler,
    /// Memory management fault (Cortex-M3+).
    pub mem_manage: ExceptionHandler,
    /// Bus fault (Cortex-M3+).
    pub bus_fault: ExceptionHandler,
    /// Usage fault (Cortex-M3+).
    pub usage_fault: ExceptionHandler,
    /// Reserved entries.
    pub reserved1: [u32; 4],
    /// SVCall (supervisor call).
    pub svcall: ExceptionHandler,
    /// Debug monitor (Cortex-M3+).
    pub debug_monitor: ExceptionHandler,
    /// Reserved.
    pub reserved2: u32,
    /// PendSV (pendable service call).
    pub pendsv: ExceptionHandler,
    /// SysTick timer.
    pub systick: ExceptionHandler,
    /// External interrupts (device specific).
    pub interrupts: [ExceptionHandler; 240],
}

/// Default vector table with standard handlers.
///
/// This table is placed at address 0x00000000 (or 0x08000000 for STM32).
#[no_mangle]
#[link_section = ".vector_table"]
#[used]
pub static VECTOR_TABLE: VectorTable = VectorTable {
    initial_sp: 0, // Will be filled by linker script (__stack_top)
    reset: Reset_Handler,
    nmi: NMI_Handler,
    hard_fault: hard_fault_trampoline,
    mem_manage: mem_manage_trampoline,
    bus_fault: bus_fault_trampoline,
    usage_fault: usage_fault_trampoline,
    reserved1: [0; 4],
    svcall: SVC_Handler,
    debug_monitor: DebugMon_Handler,
    reserved2: 0,
    pendsv: PendSV_Handler,
    systick: SysTick_Handler,
    interrupts: [Default_Handler; 240],
};

// Trampoline functions to convert non-returning handlers to regular handlers
// This is needed because the vector table expects `fn()`, not `fn() -> !`

#[no_mangle]
unsafe extern "C" fn hard_fault_trampoline() {
    HardFault_Handler()
}

#[no_mangle]
unsafe extern "C" fn mem_manage_trampoline() {
    MemManage_Handler()
}

#[no_mangle]
unsafe extern "C" fn bus_fault_trampoline() {
    BusFault_Handler()
}

#[no_mangle]
unsafe extern "C" fn usage_fault_trampoline() {
    UsageFault_Handler()
}

/// Standard Cortex-M exception numbers.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Exception {
    /// Thread mode (not in exception).
    ThreadMode = 0,
    /// Reset.
    Reset = 1,
    /// NMI.
    NMI = 2,
    /// Hard fault.
    HardFault = 3,
    /// Memory management fault.
    MemManage = 4,
    /// Bus fault.
    BusFault = 5,
    /// Usage fault.
    UsageFault = 6,
    /// SVCall.
    SVCall = 11,
    /// Debug monitor.
    DebugMonitor = 12,
    /// PendSV.
    PendSV = 14,
    /// SysTick.
    SysTick = 15,
}

impl Exception {
    /// Convert from exception number.
    pub fn from_number(n: u8) -> Option<Self> {
        match n {
            0 => Some(Self::ThreadMode),
            1 => Some(Self::Reset),
            2 => Some(Self::NMI),
            3 => Some(Self::HardFault),
            4 => Some(Self::MemManage),
            5 => Some(Self::BusFault),
            6 => Some(Self::UsageFault),
            11 => Some(Self::SVCall),
            12 => Some(Self::DebugMonitor),
            14 => Some(Self::PendSV),
            15 => Some(Self::SysTick),
            _ => None, // External interrupt or invalid
        }
    }

    /// Check if this is an external interrupt (IRQ).
    pub fn is_external(n: u8) -> bool {
        n >= 16
    }

    /// Get the IRQ number from exception number.
    pub fn to_irq(n: u8) -> Option<u8> {
        if n >= 16 {
            Some(n - 16)
        } else {
            None
        }
    }
}

/// Macro to define a custom vector table with specific interrupt handlers.
#[macro_export]
macro_rules! define_vector_table {
    (
        stack = $stack:expr,
        $(irq[$n:expr] = $handler:expr),* $(,)?
    ) => {
        #[no_mangle]
        #[link_section = ".vector_table"]
        #[used]
        pub static VECTOR_TABLE: $crate::arm::vector::VectorTable = {
            let mut table = $crate::arm::vector::VectorTable {
                initial_sp: $stack as u32,
                reset: $crate::arm::startup::Reset_Handler,
                nmi: $crate::arm::startup::NMI_Handler,
                hard_fault: hard_fault_trampoline,
                mem_manage: mem_manage_trampoline,
                bus_fault: bus_fault_trampoline,
                usage_fault: usage_fault_trampoline,
                reserved1: [0; 4],
                svcall: $crate::arm::startup::SVC_Handler,
                debug_monitor: $crate::arm::startup::DebugMon_Handler,
                reserved2: 0,
                pendsv: $crate::arm::startup::PendSV_Handler,
                systick: $crate::arm::startup::SysTick_Handler,
                interrupts: [$crate::arm::startup::Default_Handler; 240],
            };
            $(
                table.interrupts[$n] = $handler;
            )*
            table
        };
    };
}
