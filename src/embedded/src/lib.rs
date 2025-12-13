//! Embedded/Bare-Metal Startup and Runtime for Simple Language
//!
//! This crate provides startup code and minimal runtime support for running
//! Simple programs on embedded systems without an operating system.
//!
//! ## Supported Architectures
//!
//! - ARM Cortex-M (M0, M3, M4, M7)
//! - RISC-V (RV32, RV64)
//!
//! ## Features
//!
//! - `arm-cortex-m`: Enable ARM Cortex-M support
//! - `riscv32`: Enable RISC-V 32-bit support
//! - `riscv64`: Enable RISC-V 64-bit support
//! - `alloc`: Enable heap allocation
//! - `panic-halt`: Halt on panic (default)
//! - `panic-reset`: Reset on panic
//!
//! ## Usage
//!
//! ```ignore
//! // In your embedded Simple program
//! #[no_std]
//! #[no_main]
//!
//! use simple_embedded::entry;
//!
//! #[entry]
//! fn main() -> ! {
//!     loop {
//!         // Your application code
//!     }
//! }
//! ```

#![no_std]
#![allow(unused_unsafe)]

pub mod arch;
pub mod memory;
pub mod panic;
pub mod runtime;
pub mod teardown;
pub mod variants;

#[cfg(feature = "arm-cortex-m")]
pub mod arm;

#[cfg(any(feature = "riscv32", feature = "riscv64"))]
pub mod riscv;

// Re-exports
pub use memory::{MemoryLayout, MemoryRegion};
pub use runtime::{EmbeddedRuntime, RuntimeConfig};

/// Entry point attribute macro placeholder.
///
/// Mark your main function with `#[entry]` to designate it as the program entry point.
/// The function must have signature `fn() -> !` (never returns).
#[macro_export]
macro_rules! entry {
    ($path:path) => {
        #[export_name = "main"]
        pub unsafe extern "C" fn __simple_main() -> ! {
            let f: fn() -> ! = $path;
            f()
        }
    };
}

/// Initialize the embedded runtime.
///
/// This should be called at the start of your program before any other operations.
/// It initializes BSS, copies data section, and sets up the heap if enabled.
///
/// # Safety
///
/// This function must only be called once, at program startup.
#[inline(never)]
#[allow(static_mut_refs)]
pub unsafe fn init() {
    // Clear BSS
    extern "C" {
        static mut __bss_start: u8;
        static mut __bss_end: u8;
    }

    let bss_start = &mut __bss_start as *mut u8;
    let bss_end = &mut __bss_end as *mut u8;
    let bss_len = bss_end as usize - bss_start as usize;

    core::ptr::write_bytes(bss_start, 0, bss_len);

    // Copy data section from flash to RAM
    extern "C" {
        static mut __data_start: u8;
        static mut __data_end: u8;
        static __data_load: u8;
    }

    let data_start = &mut __data_start as *mut u8;
    let data_end = &mut __data_end as *mut u8;
    let data_load = &__data_load as *const u8;
    let data_len = data_end as usize - data_start as usize;

    core::ptr::copy_nonoverlapping(data_load, data_start, data_len);

    // Initialize heap if alloc feature is enabled
    #[cfg(feature = "alloc")]
    {
        extern "C" {
            static mut __heap_start: u8;
            static mut __heap_end: u8;
        }

        let heap_start = &mut __heap_start as *mut u8;
        let heap_end = &mut __heap_end as *mut u8;
        let heap_size = heap_end as usize - heap_start as usize;

        runtime::init_heap(heap_start, heap_size);
    }
}

// Note: Linker symbols (__bss_start, __bss_end, __data_start, __data_end, __data_load,
// __heap_start, __heap_end) must be provided by the linker script.
// See linker/cortex-m.ld or linker/riscv.ld for examples.

// Tests are disabled for no_std crate - use integration tests instead
