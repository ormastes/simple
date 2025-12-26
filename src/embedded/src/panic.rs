//! Panic Handler for Embedded Systems
//!
//! Provides panic handling strategies for no_std environments.
#![allow(static_mut_refs)]

use core::panic::PanicInfo;

/// Panic strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PanicStrategy {
    /// Halt the processor (infinite loop).
    Halt,
    /// Reset the processor.
    Reset,
    /// Abort (same as halt but may trigger debug breakpoint).
    Abort,
}

/// Current panic strategy (can be overridden).
#[cfg(feature = "panic-reset")]
#[allow(dead_code)]
static PANIC_STRATEGY: PanicStrategy = PanicStrategy::Reset;

#[cfg(not(feature = "panic-reset"))]
#[allow(dead_code)]
static PANIC_STRATEGY: PanicStrategy = PanicStrategy::Halt;

/// Default panic handler.
///
/// This is used when no custom panic handler is defined.
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // In debug builds, we might want to preserve panic info for debugging
    #[cfg(debug_assertions)]
    {
        // Store panic info in a static buffer for debugger inspection
        static mut PANIC_MSG: [u8; 256] = [0; 256];

        unsafe {
            // Try to format a basic message
            if let Some(location) = _info.location() {
                let file = location.file();
                let line = location.line();

                // Simple formatting without format! macro
                let mut idx = 0;
                for b in b"panic at " {
                    if idx < PANIC_MSG.len() {
                        PANIC_MSG[idx] = *b;
                        idx += 1;
                    }
                }
                for b in file.as_bytes() {
                    if idx < PANIC_MSG.len() {
                        PANIC_MSG[idx] = *b;
                        idx += 1;
                    }
                }
                if idx < PANIC_MSG.len() {
                    PANIC_MSG[idx] = b':';
                    idx += 1;
                }
                // Write line number (simple decimal conversion)
                let mut line_buf = [0u8; 10];
                let mut line_idx = 0;
                let mut n = line;
                loop {
                    line_buf[line_idx] = b'0' + (n % 10) as u8;
                    line_idx += 1;
                    n /= 10;
                    if n == 0 {
                        break;
                    }
                }
                while line_idx > 0 {
                    line_idx -= 1;
                    if idx < PANIC_MSG.len() {
                        PANIC_MSG[idx] = line_buf[line_idx];
                        idx += 1;
                    }
                }
            }
        }
    }

    match PANIC_STRATEGY {
        PanicStrategy::Halt => halt(),
        PanicStrategy::Reset => reset(),
        PanicStrategy::Abort => abort(),
    }
}

/// Halt the processor.
#[allow(dead_code)]
fn halt() -> ! {
    loop {
        #[cfg(feature = "arm-cortex-m")]
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }

        #[cfg(any(feature = "riscv32", feature = "riscv64"))]
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }

        #[cfg(not(any(feature = "arm-cortex-m", feature = "riscv32", feature = "riscv64")))]
        core::hint::spin_loop();
    }
}

/// Reset the processor.
#[allow(dead_code)]
fn reset() -> ! {
    #[cfg(feature = "arm-cortex-m")]
    {
        crate::arm::CortexM::reset()
    }

    #[cfg(any(feature = "riscv32", feature = "riscv64"))]
    {
        crate::riscv::Riscv::reset()
    }

    #[cfg(not(any(feature = "arm-cortex-m", feature = "riscv32", feature = "riscv64")))]
    halt()
}

/// Abort execution (halt with debug breakpoint).
#[allow(dead_code)]
fn abort() -> ! {
    #[cfg(debug_assertions)]
    unsafe {
        #[cfg(feature = "arm-cortex-m")]
        core::arch::asm!("bkpt #0", options(nomem, nostack));

        #[cfg(any(feature = "riscv32", feature = "riscv64"))]
        core::arch::asm!("ebreak", options(nomem, nostack));
    }

    halt()
}

/// Custom panic hook type.
pub type PanicHook = fn(&PanicInfo) -> !;

/// Set a custom panic hook.
///
/// Note: This requires modifying the panic handler, which may not be
/// possible in all configurations.
#[cfg(feature = "custom-panic")]
static mut PANIC_HOOK: Option<PanicHook> = None;

#[cfg(feature = "custom-panic")]
pub fn set_panic_hook(hook: PanicHook) {
    unsafe {
        PANIC_HOOK = Some(hook);
    }
}

/// Assert macro for embedded.
#[macro_export]
macro_rules! embedded_assert {
    ($cond:expr) => {
        if !$cond {
            panic!("assertion failed");
        }
    };
    ($cond:expr, $msg:expr) => {
        if !$cond {
            panic!($msg);
        }
    };
}

/// Debug assert (only in debug builds).
#[macro_export]
macro_rules! embedded_debug_assert {
    ($cond:expr) => {
        #[cfg(debug_assertions)]
        if !$cond {
            panic!("assertion failed");
        }
    };
    ($cond:expr, $msg:expr) => {
        #[cfg(debug_assertions)]
        if !$cond {
            panic!($msg);
        }
    };
}
