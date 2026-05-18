//! Stub regex SFFI bindings — implementations in src/runtime/runtime_regex_stub.c.

use crate::value::core::RuntimeValue;

mod c_sffi {
    use crate::value::core::RuntimeValue;
    extern "C" {
        pub(super) fn sffi_regex_is_match(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_find(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_find_all(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_captures(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_replace(pattern: RuntimeValue, text: RuntimeValue, replacement: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_replace_all(pattern: RuntimeValue, text: RuntimeValue, replacement: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_split(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue;
        pub(super) fn sffi_regex_split_n(pattern: RuntimeValue, text: RuntimeValue, limit: RuntimeValue) -> RuntimeValue;
    }
}

pub fn clear_regex_cache() {}

#[inline(always)]
pub fn sffi_regex_is_match(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_is_match(pattern, text) }
}

#[inline(always)]
pub fn sffi_regex_find(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_find(pattern, text) }
}

#[inline(always)]
pub fn sffi_regex_find_all(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_find_all(pattern, text) }
}

#[inline(always)]
pub fn sffi_regex_captures(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_captures(pattern, text) }
}

#[inline(always)]
pub fn sffi_regex_replace(pattern: RuntimeValue, text: RuntimeValue, replacement: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_replace(pattern, text, replacement) }
}

#[inline(always)]
pub fn sffi_regex_replace_all(pattern: RuntimeValue, text: RuntimeValue, replacement: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_replace_all(pattern, text, replacement) }
}

#[inline(always)]
pub fn sffi_regex_split(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_split(pattern, text) }
}

#[inline(always)]
pub fn sffi_regex_split_n(pattern: RuntimeValue, text: RuntimeValue, limit: RuntimeValue) -> RuntimeValue {
    unsafe { c_sffi::sffi_regex_split_n(pattern, text, limit) }
}
