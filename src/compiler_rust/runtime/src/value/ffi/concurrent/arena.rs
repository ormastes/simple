//! Arena allocator FFI.
//!
//! Provides a fast bump allocator for temporary allocations that can be freed all at once.
//! Useful for request-scoped allocations, parsing buffers, or batch processing.
//!
//! ## Usage Pattern
//!
//! 1. Create arena with capacity: `rt_arena_new(capacity)`
//! 2. Allocate from arena: `rt_arena_alloc(handle, size, align)`
//! 3. Use allocated memory
//! 4. Reset for reuse: `rt_arena_reset(handle)` OR free: `rt_arena_free(handle)`

use std::collections::HashMap;
use std::sync::Mutex;

struct Arena {
    buffer: Vec<u8>,
    capacity: usize,
    used: usize,
}

impl Arena {
    fn new(capacity: usize) -> Self {
        Self {
            buffer: vec![0; capacity],
            capacity,
            used: 0,
        }
    }

    fn alloc(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        let align_offset = (align - (self.used % align)) % align;
        let aligned_start = self.used + align_offset;

        if aligned_start + size > self.capacity {
            return None;
        }

        let ptr = unsafe { self.buffer.as_mut_ptr().add(aligned_start) };
        self.used = aligned_start + size;
        Some(ptr)
    }

    fn reset(&mut self) {
        self.used = 0;
    }
}

lazy_static::lazy_static! {
    static ref ARENA_MAP: Mutex<HashMap<i64, Box<Arena>>> = Mutex::new(HashMap::new());
}

static mut ARENA_COUNTER: i64 = 1;

/// Create a new arena allocator with given capacity
#[no_mangle]
pub extern "C" fn rt_arena_new(capacity: i64) -> i64 {
    let arena = Box::new(Arena::new(capacity as usize));
    unsafe {
        let handle = ARENA_COUNTER;
        ARENA_COUNTER += 1;
        ARENA_MAP.lock().unwrap().insert(handle, arena);
        handle
    }
}

/// Allocate memory from arena
/// Returns pointer to allocated memory, or 0 if allocation failed
#[no_mangle]
pub extern "C" fn rt_arena_alloc(handle: i64, size: i64, align: i64) -> i64 {
    ARENA_MAP
        .lock()
        .unwrap()
        .get_mut(&handle)
        .and_then(|arena| arena.alloc(size as usize, align as usize))
        .map(|ptr| ptr as i64)
        .unwrap_or(0)
}

/// Get arena capacity
#[no_mangle]
pub extern "C" fn rt_arena_capacity(handle: i64) -> i64 {
    ARENA_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|arena| arena.capacity as i64)
        .unwrap_or(0)
}

/// Get arena used bytes
#[no_mangle]
pub extern "C" fn rt_arena_used(handle: i64) -> i64 {
    ARENA_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|arena| arena.used as i64)
        .unwrap_or(0)
}

/// Reset arena (clear all allocations)
#[no_mangle]
pub extern "C" fn rt_arena_reset(handle: i64) {
    if let Some(arena) = ARENA_MAP.lock().unwrap().get_mut(&handle) {
        arena.reset();
    }
}

/// Free arena
#[no_mangle]
pub extern "C" fn rt_arena_free(handle: i64) {
    ARENA_MAP.lock().unwrap().remove(&handle);
}

/// Clear all arena handles (for test cleanup)
pub fn clear_arena_registry() {
    ARENA_MAP.lock().unwrap().clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_new() {
        let handle = rt_arena_new(1024);
        assert!(handle > 0);

        assert_eq!(rt_arena_capacity(handle), 1024);
        assert_eq!(rt_arena_used(handle), 0);

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_basic_alloc() {
        let handle = rt_arena_new(1024);

        // Allocate 64 bytes with 8-byte alignment
        let ptr = rt_arena_alloc(handle, 64, 8);
        assert_ne!(ptr, 0);
        assert_eq!(rt_arena_used(handle), 64);

        // Allocate another 32 bytes
        let ptr2 = rt_arena_alloc(handle, 32, 8);
        assert_ne!(ptr2, 0);
        assert_eq!(rt_arena_used(handle), 96); // 64 + 32

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_alignment() {
        let handle = rt_arena_new(1024);

        // Allocate with 1-byte alignment
        let ptr1 = rt_arena_alloc(handle, 5, 1);
        assert_ne!(ptr1, 0);
        assert_eq!(rt_arena_used(handle), 5);

        // Allocate with 8-byte alignment (should add padding)
        let ptr2 = rt_arena_alloc(handle, 8, 8);
        assert_ne!(ptr2, 0);
        // Used should be 5 + 3 (padding) + 8 = 16
        assert_eq!(rt_arena_used(handle), 16);

        // Verify alignment
        assert_eq!(ptr2 % 8, 0);

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_out_of_memory() {
        let handle = rt_arena_new(100);

        // Try to allocate more than capacity
        let ptr = rt_arena_alloc(handle, 200, 1);
        assert_eq!(ptr, 0); // Should fail

        // Allocate within capacity
        let ptr2 = rt_arena_alloc(handle, 50, 1);
        assert_ne!(ptr2, 0); // Should succeed

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_reset() {
        let handle = rt_arena_new(1024);

        // Allocate some memory
        let ptr1 = rt_arena_alloc(handle, 100, 1);
        assert_ne!(ptr1, 0);
        assert_eq!(rt_arena_used(handle), 100);

        // Reset arena
        rt_arena_reset(handle);
        assert_eq!(rt_arena_used(handle), 0);

        // Should be able to allocate again from the beginning
        let ptr2 = rt_arena_alloc(handle, 100, 1);
        assert_ne!(ptr2, 0);
        assert_eq!(rt_arena_used(handle), 100);

        // Pointers should be the same (same location in buffer)
        assert_eq!(ptr1, ptr2);

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_multiple_arenas() {
        let handle1 = rt_arena_new(512);
        let handle2 = rt_arena_new(1024);

        assert_ne!(handle1, handle2);
        assert_eq!(rt_arena_capacity(handle1), 512);
        assert_eq!(rt_arena_capacity(handle2), 1024);

        // Allocate from both
        let ptr1 = rt_arena_alloc(handle1, 100, 1);
        let ptr2 = rt_arena_alloc(handle2, 200, 1);

        assert_ne!(ptr1, 0);
        assert_ne!(ptr2, 0);
        assert_eq!(rt_arena_used(handle1), 100);
        assert_eq!(rt_arena_used(handle2), 200);

        rt_arena_free(handle1);
        rt_arena_free(handle2);
    }

    #[test]
    fn test_arena_invalid_handle() {
        // Operations on invalid handle should be safe
        assert_eq!(rt_arena_capacity(999999), 0);
        assert_eq!(rt_arena_used(999999), 0);
        assert_eq!(rt_arena_alloc(999999, 100, 1), 0);
        rt_arena_reset(999999); // Should not crash
        rt_arena_free(999999); // Should not crash
    }

    #[test]
    fn test_arena_double_free() {
        let handle = rt_arena_new(1024);
        rt_arena_free(handle);
        // Double free should be safe
        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_fill_completely() {
        let handle = rt_arena_new(128);

        // Fill arena completely
        let mut total_allocated = 0;
        loop {
            let ptr = rt_arena_alloc(handle, 16, 1);
            if ptr == 0 {
                break;
            }
            total_allocated += 16;
        }

        // Should have allocated close to capacity
        assert!(total_allocated >= 112); // At least 7*16 bytes
        assert_eq!(rt_arena_used(handle), total_allocated);

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_various_alignments() {
        let handle = rt_arena_new(1024);

        // Test various alignments: 1, 2, 4, 8, 16
        for align in [1, 2, 4, 8, 16] {
            rt_arena_reset(handle);

            let ptr = rt_arena_alloc(handle, 32, align);
            assert_ne!(ptr, 0);
            assert_eq!(ptr % (align as i64), 0);
        }

        rt_arena_free(handle);
    }

    #[test]
    fn test_arena_zero_size_alloc() {
        let handle = rt_arena_new(1024);

        // Allocating zero bytes should succeed but not advance used counter
        let ptr = rt_arena_alloc(handle, 0, 1);
        assert_ne!(ptr, 0); // Returns a pointer
        assert_eq!(rt_arena_used(handle), 0); // But doesn't use space

        rt_arena_free(handle);
    }
}
