//! Core FFI functions for value creation, extraction, and memory allocation.

use super::collections::RuntimeString;
use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

// ============================================================================
// Value creation FFI functions
// ============================================================================

/// Create an integer RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}

/// Create a float RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}

/// Create a bool RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}

/// Get the NIL value (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}

// ============================================================================
// Value extraction FFI functions
// ============================================================================

/// Extract integer from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}

/// Extract float from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}

/// Extract bool from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}

// ============================================================================
// Value type checking FFI functions
// ============================================================================

/// Check if value is truthy (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}

/// Check if value is nil (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}

/// Check if value is int (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}

/// Check if value is float (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}

/// Check if value is bool (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}

/// Check if value is heap pointer (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}

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

// ============================================================================
// Value equality (FFI-safe)
// ============================================================================

/// Compare two RuntimeValues for equality
#[no_mangle]
pub extern "C" fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    // Quick check: same raw value
    if a.to_raw() == b.to_raw() {
        return 1;
    }

    // Both must be same type for equality
    if a.is_int() && b.is_int() {
        return if a.as_int() == b.as_int() { 1 } else { 0 };
    }
    if a.is_float() && b.is_float() {
        return if a.as_float() == b.as_float() { 1 } else { 0 };
    }
    if a.is_bool() && b.is_bool() {
        return if a.as_bool() == b.as_bool() { 1 } else { 0 };
    }
    if a.is_nil() && b.is_nil() {
        return 1;
    }

    // For heap objects, compare by content for strings
    if a.is_heap() && b.is_heap() {
        let ptr_a = a.as_heap_ptr();
        let ptr_b = b.as_heap_ptr();
        unsafe {
            if (*ptr_a).object_type == HeapObjectType::String
                && (*ptr_b).object_type == HeapObjectType::String
            {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;
                if (*str_a).len != (*str_b).len {
                    return 0;
                }
                let data_a = (str_a.add(1)) as *const u8;
                let data_b = (str_b.add(1)) as *const u8;
                for i in 0..(*str_a).len {
                    if *data_a.add(i as usize) != *data_b.add(i as usize) {
                        return 0;
                    }
                }
                return 1;
            }
        }
    }

    0
}

// ============================================================================
// Interpreter bridge FFI (for hybrid execution)
// ============================================================================

/// Call an interpreted function by name with RuntimeValue arguments.
/// This is a simpler FFI wrapper that avoids BridgeValue complexity.
///
/// # Arguments
/// * `name_ptr` - Pointer to function name string (UTF-8)
/// * `name_len` - Length of function name
/// * `args` - RuntimeValue array containing arguments
///
/// # Returns
/// RuntimeValue result (NIL if function not found or error)
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_interp_call(
    name_ptr: *const u8,
    name_len: u64,
    args: RuntimeValue,
) -> RuntimeValue {
    // This is a stub implementation - the actual interpreter bridge
    // is in the compiler crate (interpreter_ffi.rs).
    // For now, return NIL to indicate interpreter not available.
    // The compiled code should call simple_interp_call directly
    // when proper interpreter integration is needed.
    let _ = (name_ptr, name_len, args);
    RuntimeValue::NIL
}

/// Evaluate an expression by index (stub).
/// The actual expression storage and evaluation is handled
/// by the compiler's interpreter_ffi module.
///
/// # Arguments
/// * `expr_index` - Index of the stored expression
///
/// # Returns
/// RuntimeValue result (NIL if expression not found or error)
#[no_mangle]
pub extern "C" fn rt_interp_eval(expr_index: u64) -> RuntimeValue {
    // Stub - actual implementation in compiler crate
    let _ = expr_index;
    RuntimeValue::NIL
}

// ============================================================================
// Error handling (FFI-safe)
// ============================================================================

/// Called when a function is not found at runtime.
/// Prints an error message and returns NIL (caller should handle the error).
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    if name_ptr.is_null() {
        eprintln!("Runtime error: Function not found (unknown name)");
    } else {
        let name_slice = std::slice::from_raw_parts(name_ptr, name_len as usize);
        if let Ok(name_str) = std::str::from_utf8(name_slice) {
            eprintln!("Runtime error: Function '{}' not found", name_str);
        } else {
            eprintln!("Runtime error: Function not found (invalid UTF-8 name)");
        }
    }
    RuntimeValue::NIL
}

/// Called when a method is not found at runtime.
/// Prints an error message and returns NIL.
///
/// # Safety
/// type_ptr and method_ptr must be valid pointers to UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    let type_name = if type_ptr.is_null() {
        "<unknown type>"
    } else {
        let slice = std::slice::from_raw_parts(type_ptr, type_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let method_name = if method_ptr.is_null() {
        "<unknown method>"
    } else {
        let slice = std::slice::from_raw_parts(method_ptr, method_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    eprintln!(
        "Runtime error: Method '{}' not found on type '{}'",
        method_name, type_name
    );
    RuntimeValue::NIL
}
