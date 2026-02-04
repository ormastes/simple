//! Raw memory allocation FFI functions.
//!
//! Provides zero-cost abstraction support for struct allocation in codegen.
//! These functions provide malloc/free-like semantics with 8-byte alignment.

use crate::value::core::RuntimeValue;
use crate::value::heap::HeapHeader;

// ============================================================================
// Raw memory allocation (FFI-safe, zero-cost abstraction support)
// ============================================================================

/// Allocate raw memory with 8-byte alignment (like malloc)
/// Returns a pointer to the allocated memory, or null on failure.
/// Used for zero-cost struct allocation in codegen.
#[no_mangle]
pub extern "C" fn rt_alloc(size: u64) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe { std::alloc::alloc_zeroed(layout) }
}

/// Free memory allocated by rt_alloc
#[no_mangle]
pub extern "C" fn rt_free(ptr: *mut u8, size: u64) {
    if ptr.is_null() || size == 0 {
        return;
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe {
        std::alloc::dealloc(ptr, layout);
    }
}

/// Convert raw pointer to RuntimeValue (for struct pointers)
/// The pointer is stored as a heap-tagged value.
#[no_mangle]
pub extern "C" fn rt_ptr_to_value(ptr: *mut u8) -> RuntimeValue {
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    unsafe { RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader) }
}

/// Extract raw pointer from RuntimeValue
#[no_mangle]
pub extern "C" fn rt_value_to_ptr(v: RuntimeValue) -> *mut u8 {
    if !v.is_heap() {
        return std::ptr::null_mut();
    }
    v.as_heap_ptr() as *mut u8
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_free() {
        // Allocate 64 bytes
        let ptr = rt_alloc(64);
        assert!(!ptr.is_null());

        // Memory should be zero-initialized
        unsafe {
            for i in 0..64 {
                assert_eq!(*ptr.add(i), 0);
            }

            // Write some data
            *ptr = 42;
            *(ptr.add(63)) = 99;
            assert_eq!(*ptr, 42);
            assert_eq!(*(ptr.add(63)), 99);
        }

        // Free the memory
        rt_free(ptr, 64);
    }

    #[test]
    fn test_alloc_zero_size() {
        let ptr = rt_alloc(0);
        assert!(ptr.is_null());
        rt_free(ptr, 0); // Should be safe
    }

    #[test]
    fn test_free_null_ptr() {
        rt_free(std::ptr::null_mut(), 64); // Should be safe
    }

    #[test]
    fn test_ptr_to_value_null() {
        let val = rt_ptr_to_value(std::ptr::null_mut());
        assert!(val.is_nil());
    }

    #[test]
    fn test_value_to_ptr_non_heap() {
        let int_val = RuntimeValue::from_int(42);
        let ptr = rt_value_to_ptr(int_val);
        assert!(ptr.is_null());

        let float_val = RuntimeValue::from_float(3.25);
        let ptr = rt_value_to_ptr(float_val);
        assert!(ptr.is_null());

        let bool_val = RuntimeValue::from_bool(true);
        let ptr = rt_value_to_ptr(bool_val);
        assert!(ptr.is_null());

        let nil_val = RuntimeValue::NIL;
        let ptr = rt_value_to_ptr(nil_val);
        assert!(ptr.is_null());
    }

    #[test]
    fn test_alloc_various_sizes() {
        // Test different allocation sizes
        for size in [1, 8, 16, 32, 64, 128, 256, 512, 1024] {
            let ptr = rt_alloc(size);
            assert!(!ptr.is_null());

            // Verify zero-initialization
            unsafe {
                for i in 0..size {
                    assert_eq!(*ptr.add(i as usize), 0);
                }
            }

            rt_free(ptr, size);
        }
    }

    #[test]
    fn test_alloc_alignment() {
        // Allocated memory should be 8-byte aligned
        for _ in 0..100 {
            let ptr = rt_alloc(64);
            assert!(!ptr.is_null());
            assert_eq!(ptr as usize % 8, 0, "Pointer should be 8-byte aligned");
            rt_free(ptr, 64);
        }
    }
}
