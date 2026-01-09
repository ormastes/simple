//! Embedded Runtime Support
//!
//! Minimal runtime for embedded systems without standard library.

use core::ptr;

/// Runtime configuration.
#[derive(Debug, Clone, Copy, Default)]
pub struct RuntimeConfig {
    /// Enable heap allocation.
    pub enable_heap: bool,
    /// Heap start address (if enable_heap is true).
    pub heap_start: usize,
    /// Heap size in bytes.
    pub heap_size: usize,
}

/// Embedded runtime state.
pub struct EmbeddedRuntime {
    config: RuntimeConfig,
    initialized: bool,
}

impl Default for EmbeddedRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl EmbeddedRuntime {
    /// Create a new runtime with default configuration.
    pub const fn new() -> Self {
        Self {
            config: RuntimeConfig {
                enable_heap: false,
                heap_start: 0,
                heap_size: 0,
            },
            initialized: false,
        }
    }

    /// Create with configuration.
    pub const fn with_config(config: RuntimeConfig) -> Self {
        Self {
            config,
            initialized: false,
        }
    }

    /// Initialize the runtime.
    ///
    /// # Safety
    /// Must be called exactly once before using runtime features.
    pub unsafe fn init(&mut self) {
        if self.initialized {
            return;
        }

        if self.config.enable_heap && self.config.heap_size > 0 {
            init_heap(self.config.heap_start as *mut u8, self.config.heap_size);
        }

        self.initialized = true;
    }

    /// Check if runtime is initialized.
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }
}

// Simple bump allocator for embedded use

/// Heap state for bump allocator.
struct HeapState {
    start: *mut u8,
    end: *mut u8,
    current: *mut u8,
}

static mut HEAP: HeapState = HeapState {
    start: ptr::null_mut(),
    end: ptr::null_mut(),
    current: ptr::null_mut(),
};

/// Initialize the heap.
///
/// # Safety
/// Must be called exactly once with valid memory region.
pub unsafe fn init_heap(start: *mut u8, size: usize) {
    HEAP.start = start;
    HEAP.end = start.add(size);
    HEAP.current = start;
}

/// Allocate memory from the heap (bump allocator).
///
/// Returns null if allocation fails.
///
/// # Safety
/// Heap must be initialized before calling this function.
#[cfg(feature = "alloc")]
pub unsafe fn heap_alloc(size: usize, align: usize) -> *mut u8 {
    // Align current pointer
    let current = HEAP.current as usize;
    let aligned = (current + align - 1) & !(align - 1);
    let new_current = aligned + size;

    if new_current > HEAP.end as usize {
        // Out of memory
        ptr::null_mut()
    } else {
        HEAP.current = new_current as *mut u8;
        aligned as *mut u8
    }
}

/// Get heap usage statistics.
pub fn heap_stats() -> (usize, usize, usize) {
    unsafe {
        let total = HEAP.end as usize - HEAP.start as usize;
        let used = HEAP.current as usize - HEAP.start as usize;
        let free = total - used;
        (total, used, free)
    }
}

/// Reset the heap (free all allocations).
///
/// # Safety
/// All existing allocations become invalid after this call.
pub unsafe fn heap_reset() {
    HEAP.current = HEAP.start;
}

// Global allocator implementation for #[global_allocator]

#[cfg(feature = "alloc")]
mod allocator {
    use super::*;
    use core::alloc::{GlobalAlloc, Layout};

    /// Bump allocator for embedded use.
    pub struct BumpAllocator;

    unsafe impl GlobalAlloc for BumpAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            heap_alloc(layout.size(), layout.align())
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
            // Bump allocator doesn't support individual deallocation
            // Memory is only freed by resetting the entire heap
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            // Simple realloc: allocate new, copy, don't free old
            let new_ptr = self.alloc(Layout::from_size_align_unchecked(new_size, layout.align()));
            if !new_ptr.is_null() {
                ptr::copy_nonoverlapping(ptr, new_ptr, layout.size().min(new_size));
            }
            new_ptr
        }
    }

    #[global_allocator]
    static ALLOCATOR: BumpAllocator = BumpAllocator;
}

// Abort intrinsic for no_std

/// Abort execution.
#[inline(never)]
#[no_mangle]
pub extern "C" fn abort() -> ! {
    loop {
        // In debug mode, trigger breakpoint
        #[cfg(debug_assertions)]
        unsafe {
            #[cfg(feature = "arm-cortex-m")]
            core::arch::asm!("bkpt #0", options(nomem, nostack));

            #[cfg(any(feature = "riscv32", feature = "riscv64"))]
            core::arch::asm!("ebreak", options(nomem, nostack));
        }

        // Wait for interrupt / halt
        #[cfg(feature = "arm-cortex-m")]
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }

        #[cfg(any(feature = "riscv32", feature = "riscv64"))]
        unsafe {
            core::arch::asm!("wfi", options(nomem, nostack));
        }
    }
}

// Memory intrinsics that may be needed without std

/// Copy `n` bytes from `src` to `dest`.
///
/// # Safety
/// - `dest` and `src` must be valid for reads/writes of `n` bytes.
/// - The memory regions must not overlap (use memmove for overlapping).
#[no_mangle]
pub unsafe extern "C" fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    // Avoid calling into compiler-builtins memcpy to prevent recursion when the
    // intrinsic lowers back to this symbol. Do a simple forward byte copy.
    let mut i = 0;
    while i < n {
        *dest.add(i) = *src.add(i);
        i += 1;
    }
    dest
}

/// Move `n` bytes from `src` to `dest`, handling overlapping regions.
///
/// # Safety
/// - `dest` and `src` must be valid for reads/writes of `n` bytes.
#[no_mangle]
pub unsafe extern "C" fn memmove(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    // Handle overlap manually: choose direction based on pointer order.
    if dest as usize <= src as usize {
        let mut i = 0;
        while i < n {
            *dest.add(i) = *src.add(i);
            i += 1;
        }
    } else {
        let mut i = n;
        while i != 0 {
            i -= 1;
            *dest.add(i) = *src.add(i);
        }
    }
    dest
}

/// Fill `n` bytes at `dest` with value `c`.
///
/// # Safety
/// - `dest` must be valid for writes of `n` bytes.
#[no_mangle]
pub unsafe extern "C" fn memset(dest: *mut u8, c: i32, n: usize) -> *mut u8 {
    let byte = c as u8;
    let mut i = 0;
    while i < n {
        *dest.add(i) = byte;
        i += 1;
    }
    dest
}

/// Compare `n` bytes of `s1` and `s2`.
///
/// # Safety
/// - `s1` and `s2` must be valid for reads of `n` bytes.
#[no_mangle]
pub unsafe extern "C" fn memcmp(s1: *const u8, s2: *const u8, n: usize) -> i32 {
    for i in 0..n {
        let a = *s1.add(i);
        let b = *s2.add(i);
        if a != b {
            return (a as i32) - (b as i32);
        }
    }
    0
}

/// Get the length of a null-terminated string.
///
/// # Safety
/// - `s` must be a valid null-terminated string.
#[no_mangle]
pub unsafe extern "C" fn strlen(s: *const u8) -> usize {
    let mut len = 0;
    while *s.add(len) != 0 {
        len += 1;
    }
    len
}
