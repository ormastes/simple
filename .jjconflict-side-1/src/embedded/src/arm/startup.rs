//! ARM Cortex-M Startup Code
//!
//! This module provides the reset handler and startup sequence for ARM Cortex-M.

use core::ptr;

use super::CortexM;
use crate::arch::ArchInit;

/// Reset handler - entry point after reset.
///
/// This is the first code that runs after the processor comes out of reset.
/// It initializes the runtime and calls main.
#[no_mangle]
#[link_section = ".reset_handler"]
pub unsafe extern "C" fn Reset_Handler() -> ! {
    // Early architecture-specific initialization
    CortexM::early_init();

    // Get linker-provided symbols
    extern "C" {
        static mut __bss_start: u32;
        static mut __bss_end: u32;
        static mut __data_start: u32;
        static mut __data_end: u32;
        static __data_load: u32;
        static __stack_top: u32;
    }

    // Zero BSS section
    let bss_start = &mut __bss_start as *mut u32;
    let bss_end = &mut __bss_end as *mut u32;
    let bss_len = (bss_end as usize - bss_start as usize) / 4;

    ptr::write_bytes(bss_start, 0, bss_len);

    // Copy data section from flash to RAM
    let data_start = &mut __data_start as *mut u32;
    let data_end = &mut __data_end as *mut u32;
    let data_load = &__data_load as *const u32;
    let data_len = (data_end as usize - data_start as usize) / 4;

    ptr::copy_nonoverlapping(data_load, data_start, data_len);

    // Late architecture-specific initialization
    CortexM::late_init();

    // Initialize heap if alloc feature is enabled
    #[cfg(feature = "alloc")]
    {
        extern "C" {
            static mut __heap_start: u8;
            static __heap_size: u32;
        }
        crate::runtime::init_heap(&mut __heap_start as *mut u8, __heap_size as usize);
    }

    // Call main
    extern "C" {
        fn main() -> !;
    }

    main()
}

/// Hard fault handler.
#[no_mangle]
#[link_section = ".hard_fault_handler"]
pub unsafe extern "C" fn HardFault_Handler() -> ! {
    // Read fault status registers for debugging
    let cfsr = (0xE000_ED28 as *const u32).read_volatile();
    let hfsr = (0xE000_ED2C as *const u32).read_volatile();
    let _mmfar = (0xE000_ED34 as *const u32).read_volatile();
    let _bfar = (0xE000_ED38 as *const u32).read_volatile();

    // Check what kind of fault
    let _is_bus_fault = (cfsr >> 8) & 0xFF != 0;
    let _is_mem_fault = cfsr & 0xFF != 0;
    let _is_usage_fault = (cfsr >> 16) & 0xFFFF != 0;
    let _is_forced = hfsr & (1 << 30) != 0;

    // In release mode, reset. In debug mode, halt.
    #[cfg(debug_assertions)]
    loop {
        core::arch::asm!("bkpt #0", options(nomem, nostack));
    }

    #[cfg(not(debug_assertions))]
    CortexM::reset()
}

/// Memory management fault handler.
#[no_mangle]
#[link_section = ".mem_fault_handler"]
pub unsafe extern "C" fn MemManage_Handler() -> ! {
    #[cfg(debug_assertions)]
    loop {
        core::arch::asm!("bkpt #1", options(nomem, nostack));
    }

    #[cfg(not(debug_assertions))]
    CortexM::reset()
}

/// Bus fault handler.
#[no_mangle]
#[link_section = ".bus_fault_handler"]
pub unsafe extern "C" fn BusFault_Handler() -> ! {
    #[cfg(debug_assertions)]
    loop {
        core::arch::asm!("bkpt #2", options(nomem, nostack));
    }

    #[cfg(not(debug_assertions))]
    CortexM::reset()
}

/// Usage fault handler.
#[no_mangle]
#[link_section = ".usage_fault_handler"]
pub unsafe extern "C" fn UsageFault_Handler() -> ! {
    #[cfg(debug_assertions)]
    loop {
        core::arch::asm!("bkpt #3", options(nomem, nostack));
    }

    #[cfg(not(debug_assertions))]
    CortexM::reset()
}

/// Non-maskable interrupt handler.
#[no_mangle]
pub unsafe extern "C" fn NMI_Handler() {
    // NMI can be caused by various sources - just return for now
}

/// SVCall handler (used for system calls).
#[no_mangle]
pub unsafe extern "C" fn SVC_Handler() {
    // Not implemented - can be used for OS syscalls
}

/// Debug monitor handler.
#[no_mangle]
pub unsafe extern "C" fn DebugMon_Handler() {
    // Debug monitor - used by debuggers
}

/// PendSV handler (used for context switching).
#[no_mangle]
pub unsafe extern "C" fn PendSV_Handler() {
    // Not implemented - used for OS context switching
}

/// SysTick handler.
#[no_mangle]
pub unsafe extern "C" fn SysTick_Handler() {
    // Call the registered systick callback if any
    if let Some(cb) = SYSTICK_CALLBACK {
        cb();
    }
}

/// Default interrupt handler.
#[no_mangle]
pub unsafe extern "C" fn Default_Handler() {
    // Unhandled interrupt - halt or reset
    #[cfg(debug_assertions)]
    loop {
        core::arch::asm!("bkpt #255", options(nomem, nostack));
    }

    #[cfg(not(debug_assertions))]
    CortexM::reset()
}

/// SysTick callback type.
pub type SysTickCallback = fn();

/// Global SysTick callback.
static mut SYSTICK_CALLBACK: Option<SysTickCallback> = None;

/// Register a SysTick callback.
///
/// # Safety
/// Must be called from a single thread (typically before enabling interrupts).
pub unsafe fn set_systick_callback(cb: SysTickCallback) {
    SYSTICK_CALLBACK = Some(cb);
}

/// Clear the SysTick callback.
///
/// # Safety
/// Must be called from a single thread or with interrupts disabled.
pub unsafe fn clear_systick_callback() {
    SYSTICK_CALLBACK = None;
}
