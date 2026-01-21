//! RISC-V Startup Code
//!
//! This module provides the reset handler and startup sequence for RISC-V processors.

use core::ptr;

use super::Riscv;
use crate::arch::ArchInit;

/// Reset handler - entry point after reset.
///
/// This is placed at the reset vector and is the first code that runs.
#[no_mangle]
#[link_section = ".init.boot"]
#[naked]
pub unsafe extern "C" fn _start() -> ! {
    #[cfg(feature = "riscv32")]
    core::arch::asm!(
        // Set up global pointer
        ".option push",
        ".option norelax",
        "la gp, __global_pointer$",
        ".option pop",
        // Set up stack pointer
        "la sp, __stack_top",
        // Clear bss
        "la a0, __bss_start",
        "la a1, __bss_end",
        "1:",
        "bgeu a0, a1, 2f",
        "sw zero, 0(a0)",
        "addi a0, a0, 4",
        "j 1b",
        "2:",
        // Copy data section
        "la a0, __data_start",
        "la a1, __data_end",
        "la a2, __data_load",
        "3:",
        "bgeu a0, a1, 4f",
        "lw a3, 0(a2)",
        "sw a3, 0(a0)",
        "addi a0, a0, 4",
        "addi a2, a2, 4",
        "j 3b",
        "4:",
        // Call Rust init
        "call __riscv_init",
        // Call main
        "call main",
        // If main returns, halt
        "5:",
        "wfi",
        "j 5b",
        options(noreturn)
    );

    #[cfg(feature = "riscv64")]
    core::arch::asm!(
        // Set up global pointer
        ".option push",
        ".option norelax",
        "la gp, __global_pointer$",
        ".option pop",
        // Set up stack pointer
        "la sp, __stack_top",
        // Clear bss
        "la a0, __bss_start",
        "la a1, __bss_end",
        "1:",
        "bgeu a0, a1, 2f",
        "sd zero, 0(a0)",
        "addi a0, a0, 8",
        "j 1b",
        "2:",
        // Copy data section
        "la a0, __data_start",
        "la a1, __data_end",
        "la a2, __data_load",
        "3:",
        "bgeu a0, a1, 4f",
        "ld a3, 0(a2)",
        "sd a3, 0(a0)",
        "addi a0, a0, 8",
        "addi a2, a2, 8",
        "j 3b",
        "4:",
        // Call Rust init
        "call __riscv_init",
        // Call main
        "call main",
        // If main returns, halt
        "5:",
        "wfi",
        "j 5b",
        options(noreturn)
    );

    #[cfg(not(any(feature = "riscv32", feature = "riscv64")))]
    loop {}
}

/// Rust-level initialization called from _start.
#[no_mangle]
pub unsafe extern "C" fn __riscv_init() {
    // Early architecture initialization
    Riscv::early_init();

    // Initialize heap if alloc feature is enabled
    #[cfg(feature = "alloc")]
    {
        extern "C" {
            static mut __heap_start: u8;
            static __heap_size: usize;
        }
        crate::runtime::init_heap(&mut __heap_start as *mut u8, __heap_size);
    }

    // Late initialization
    Riscv::late_init();
}

/// Trap handler - handles exceptions and interrupts.
#[no_mangle]
#[link_section = ".trap.handler"]
#[naked]
pub unsafe extern "C" fn _trap_handler() -> ! {
    #[cfg(feature = "riscv32")]
    core::arch::asm!(
        // Save context
        "addi sp, sp, -32*4",
        "sw ra, 0*4(sp)",
        "sw t0, 1*4(sp)",
        "sw t1, 2*4(sp)",
        "sw t2, 3*4(sp)",
        "sw a0, 4*4(sp)",
        "sw a1, 5*4(sp)",
        "sw a2, 6*4(sp)",
        "sw a3, 7*4(sp)",
        "sw a4, 8*4(sp)",
        "sw a5, 9*4(sp)",
        "sw a6, 10*4(sp)",
        "sw a7, 11*4(sp)",
        "sw t3, 12*4(sp)",
        "sw t4, 13*4(sp)",
        "sw t5, 14*4(sp)",
        "sw t6, 15*4(sp)",
        // Read cause and handle
        "csrr a0, mcause",
        "csrr a1, mepc",
        "call __trap_handler_rust",
        // Restore context
        "lw ra, 0*4(sp)",
        "lw t0, 1*4(sp)",
        "lw t1, 2*4(sp)",
        "lw t2, 3*4(sp)",
        "lw a0, 4*4(sp)",
        "lw a1, 5*4(sp)",
        "lw a2, 6*4(sp)",
        "lw a3, 7*4(sp)",
        "lw a4, 8*4(sp)",
        "lw a5, 9*4(sp)",
        "lw a6, 10*4(sp)",
        "lw a7, 11*4(sp)",
        "lw t3, 12*4(sp)",
        "lw t4, 13*4(sp)",
        "lw t5, 14*4(sp)",
        "lw t6, 15*4(sp)",
        "addi sp, sp, 32*4",
        "mret",
        options(noreturn)
    );

    #[cfg(feature = "riscv64")]
    core::arch::asm!(
        // Save context
        "addi sp, sp, -32*8",
        "sd ra, 0*8(sp)",
        "sd t0, 1*8(sp)",
        "sd t1, 2*8(sp)",
        "sd t2, 3*8(sp)",
        "sd a0, 4*8(sp)",
        "sd a1, 5*8(sp)",
        "sd a2, 6*8(sp)",
        "sd a3, 7*8(sp)",
        "sd a4, 8*8(sp)",
        "sd a5, 9*8(sp)",
        "sd a6, 10*8(sp)",
        "sd a7, 11*8(sp)",
        "sd t3, 12*8(sp)",
        "sd t4, 13*8(sp)",
        "sd t5, 14*8(sp)",
        "sd t6, 15*8(sp)",
        // Read cause and handle
        "csrr a0, mcause",
        "csrr a1, mepc",
        "call __trap_handler_rust",
        // Restore context
        "ld ra, 0*8(sp)",
        "ld t0, 1*8(sp)",
        "ld t1, 2*8(sp)",
        "ld t2, 3*8(sp)",
        "ld a0, 4*8(sp)",
        "ld a1, 5*8(sp)",
        "ld a2, 6*8(sp)",
        "ld a3, 7*8(sp)",
        "ld a4, 8*8(sp)",
        "ld a5, 9*8(sp)",
        "ld a6, 10*8(sp)",
        "ld a7, 11*8(sp)",
        "ld t3, 12*8(sp)",
        "ld t4, 13*8(sp)",
        "ld t5, 14*8(sp)",
        "ld t6, 15*8(sp)",
        "addi sp, sp, 32*8",
        "mret",
        options(noreturn)
    );

    #[cfg(not(any(feature = "riscv32", feature = "riscv64")))]
    loop {}
}

/// Rust trap handler called from assembly.
#[no_mangle]
pub extern "C" fn __trap_handler_rust(mcause: usize, mepc: usize) {
    let is_interrupt = mcause >> (core::mem::size_of::<usize>() * 8 - 1) != 0;
    let cause = mcause & !(1 << (core::mem::size_of::<usize>() * 8 - 1));

    if is_interrupt {
        // Handle interrupt
        match cause {
            3 => {
                // Machine software interrupt
                if let Some(cb) = unsafe { MSI_CALLBACK } {
                    cb();
                }
            }
            7 => {
                // Machine timer interrupt
                if let Some(cb) = unsafe { MTI_CALLBACK } {
                    cb();
                }
            }
            11 => {
                // Machine external interrupt
                if let Some(cb) = unsafe { MEI_CALLBACK } {
                    cb();
                }
            }
            _ => {
                // Unknown interrupt - ignore
            }
        }
    } else {
        // Handle exception
        handle_exception(cause, mepc);
    }
}

/// Handle exceptions.
fn handle_exception(cause: usize, mepc: usize) -> ! {
    // Common exception causes:
    // 0: Instruction address misaligned
    // 1: Instruction access fault
    // 2: Illegal instruction
    // 3: Breakpoint
    // 4: Load address misaligned
    // 5: Load access fault
    // 6: Store/AMO address misaligned
    // 7: Store/AMO access fault
    // 8-11: Environment calls (ecall)
    // 12: Instruction page fault
    // 13: Load page fault
    // 15: Store/AMO page fault

    #[cfg(debug_assertions)]
    {
        // In debug mode, loop forever for debugging
        loop {
            unsafe {
                core::arch::asm!("wfi", options(nomem, nostack));
            }
        }
    }

    #[cfg(not(debug_assertions))]
    {
        // In release mode, reset
        Riscv::reset()
    }
}

/// Interrupt callback type.
pub type InterruptCallback = fn();

/// Machine software interrupt callback.
static mut MSI_CALLBACK: Option<InterruptCallback> = None;

/// Machine timer interrupt callback.
static mut MTI_CALLBACK: Option<InterruptCallback> = None;

/// Machine external interrupt callback.
static mut MEI_CALLBACK: Option<InterruptCallback> = None;

/// Set machine software interrupt callback.
///
/// # Safety
/// Must be called from a single thread (typically before enabling interrupts).
pub unsafe fn set_msi_callback(cb: InterruptCallback) {
    MSI_CALLBACK = Some(cb);
}

/// Set machine timer interrupt callback.
///
/// # Safety
/// Must be called from a single thread (typically before enabling interrupts).
pub unsafe fn set_mti_callback(cb: InterruptCallback) {
    MTI_CALLBACK = Some(cb);
}

/// Set machine external interrupt callback.
///
/// # Safety
/// Must be called from a single thread (typically before enabling interrupts).
pub unsafe fn set_mei_callback(cb: InterruptCallback) {
    MEI_CALLBACK = Some(cb);
}
