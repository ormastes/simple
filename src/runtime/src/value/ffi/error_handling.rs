//! Error handling FFI for runtime errors.
//!
//! Provides FFI functions for reporting runtime errors such as function not found
//! and method not found. These are called from compiled code when runtime lookups fail.
//!
//! ## Usage Pattern
//!
//! 1. Compiled code attempts to call a function or method
//! 2. If lookup fails, calls `rt_function_not_found` or `rt_method_not_found`
//! 3. Error is printed to stderr
//! 4. Returns NIL to allow caller to handle the error
//!
//! ## Error Handling Strategy
//!
//! These functions print errors to stderr but do not panic, allowing the caller
//! to handle the error gracefully (e.g., by checking for NIL return value).

use crate::value::core::RuntimeValue;

/// Called when a function is not found at runtime.
/// Prints an error message and returns NIL (caller should handle the error).
///
/// # Arguments
/// * `name_ptr` - Pointer to function name string (UTF-8)
/// * `name_len` - Length of function name
///
/// # Returns
/// RuntimeValue::NIL
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data, or null.
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
/// # Arguments
/// * `type_ptr` - Pointer to type name string (UTF-8)
/// * `type_len` - Length of type name
/// * `method_ptr` - Pointer to method name string (UTF-8)
/// * `method_len` - Length of method name
///
/// # Returns
/// RuntimeValue::NIL
///
/// # Safety
/// type_ptr and method_ptr must be valid pointers to UTF-8 data, or null.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_not_found_with_name() {
        let name = b"my_function";
        let result = unsafe { rt_function_not_found(name.as_ptr(), name.len() as u64) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_function_not_found_null_name() {
        let result = unsafe { rt_function_not_found(std::ptr::null(), 0) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_function_not_found_invalid_utf8() {
        let invalid_utf8 = [0xFF, 0xFE, 0xFD]; // Invalid UTF-8 sequence
        let result = unsafe { rt_function_not_found(invalid_utf8.as_ptr(), invalid_utf8.len() as u64) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_with_names() {
        let type_name = b"MyStruct";
        let method_name = b"my_method";
        let result = unsafe {
            rt_method_not_found(
                type_name.as_ptr(),
                type_name.len() as u64,
                method_name.as_ptr(),
                method_name.len() as u64,
            )
        };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_null_type() {
        let method_name = b"my_method";
        let result =
            unsafe { rt_method_not_found(std::ptr::null(), 0, method_name.as_ptr(), method_name.len() as u64) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_null_method() {
        let type_name = b"MyStruct";
        let result = unsafe { rt_method_not_found(type_name.as_ptr(), type_name.len() as u64, std::ptr::null(), 0) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_both_null() {
        let result = unsafe { rt_method_not_found(std::ptr::null(), 0, std::ptr::null(), 0) };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_invalid_utf8_type() {
        let invalid_utf8 = [0xFF, 0xFE, 0xFD];
        let method_name = b"my_method";
        let result = unsafe {
            rt_method_not_found(
                invalid_utf8.as_ptr(),
                invalid_utf8.len() as u64,
                method_name.as_ptr(),
                method_name.len() as u64,
            )
        };
        assert!(result.is_nil());
    }

    #[test]
    fn test_method_not_found_invalid_utf8_method() {
        let type_name = b"MyStruct";
        let invalid_utf8 = [0xFF, 0xFE, 0xFD];
        let result = unsafe {
            rt_method_not_found(
                type_name.as_ptr(),
                type_name.len() as u64,
                invalid_utf8.as_ptr(),
                invalid_utf8.len() as u64,
            )
        };
        assert!(result.is_nil());
    }
}
