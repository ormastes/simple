//! Error handling SFFI — implementations in src/runtime/runtime_error.c.

use crate::value::core::RuntimeValue;

mod c_sffi {
    use crate::value::core::RuntimeValue;
    extern "C" {
        pub(super) fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue;
        pub(super) fn rt_method_not_found(
            type_ptr: *const u8,
            type_len: u64,
            method_ptr: *const u8,
            method_len: u64,
        ) -> RuntimeValue;
    }
}

#[inline(always)]
pub unsafe fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    c_sffi::rt_function_not_found(name_ptr, name_len)
}
#[inline(always)]
pub unsafe fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    c_sffi::rt_method_not_found(type_ptr, type_len, method_ptr, method_len)
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
