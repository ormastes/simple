//! Error handling SFFI implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::tags;

unsafe fn string_from_raw_parts(ptr: *const u8, len: u64, fallback: &str) -> String {
    if ptr.is_null() || len == 0 {
        return fallback.to_string();
    }
    let bytes = std::slice::from_raw_parts(ptr, len as usize);
    String::from_utf8_lossy(bytes).into_owned()
}

fn runtime_error_value() -> RuntimeValue {
    RuntimeValue::from_special(tags::SPECIAL_ERROR)
}

#[inline(always)]
pub unsafe fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    if name_ptr.is_null() {
        eprintln!("Runtime error: Function not found (unknown name)");
    } else {
        let name = string_from_raw_parts(name_ptr, name_len, "");
        eprintln!("Runtime error: Function '{name}' not found");
    }
    runtime_error_value()
}
#[inline(always)]
pub unsafe fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    let type_name = string_from_raw_parts(type_ptr, type_len, "<unknown type>");
    let method_name = string_from_raw_parts(method_ptr, method_len, "<unknown method>");
    eprintln!("Runtime error: Method '{method_name}' not found on type '{type_name}'");
    runtime_error_value()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_not_found_with_name() {
        let name = b"my_function";
        let result = unsafe { rt_function_not_found(name.as_ptr(), name.len() as u64) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }

    #[test]
    fn test_function_not_found_null_name() {
        let result = unsafe { rt_function_not_found(std::ptr::null(), 0) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }

    #[test]
    fn test_function_not_found_invalid_utf8() {
        let invalid_utf8 = [0xFF, 0xFE, 0xFD]; // Invalid UTF-8 sequence
        let result = unsafe { rt_function_not_found(invalid_utf8.as_ptr(), invalid_utf8.len() as u64) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
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
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }

    #[test]
    fn test_method_not_found_null_type() {
        let method_name = b"my_method";
        let result =
            unsafe { rt_method_not_found(std::ptr::null(), 0, method_name.as_ptr(), method_name.len() as u64) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }

    #[test]
    fn test_method_not_found_null_method() {
        let type_name = b"MyStruct";
        let result = unsafe { rt_method_not_found(type_name.as_ptr(), type_name.len() as u64, std::ptr::null(), 0) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }

    #[test]
    fn test_method_not_found_both_null() {
        let result = unsafe { rt_method_not_found(std::ptr::null(), 0, std::ptr::null(), 0) };
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
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
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
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
        assert_eq!(result, RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR));
    }
}
