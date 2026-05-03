//! Stub regex FFI bindings used when the runtime-regex feature is disabled.

use super::super::RuntimeValue;
use super::super::collections::{rt_array_new, rt_array_push};

pub fn clear_regex_cache() {}

#[no_mangle]
pub extern "C" fn ffi_regex_is_match(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    RuntimeValue::FALSE
}

#[no_mangle]
pub extern "C" fn ffi_regex_find(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[no_mangle]
pub extern "C" fn ffi_regex_find_all(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[no_mangle]
pub extern "C" fn ffi_regex_captures(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[no_mangle]
pub extern "C" fn ffi_regex_replace(
    _pattern: RuntimeValue,
    text: RuntimeValue,
    _replacement: RuntimeValue,
) -> RuntimeValue {
    text
}

#[no_mangle]
pub extern "C" fn ffi_regex_replace_all(
    _pattern: RuntimeValue,
    text: RuntimeValue,
    _replacement: RuntimeValue,
) -> RuntimeValue {
    text
}

#[no_mangle]
pub extern "C" fn ffi_regex_split(_pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let result = rt_array_new(1);
    rt_array_push(result, text);
    result
}

#[no_mangle]
pub extern "C" fn ffi_regex_split_n(_pattern: RuntimeValue, text: RuntimeValue, _limit: RuntimeValue) -> RuntimeValue {
    let result = rt_array_new(1);
    rt_array_push(result, text);
    result
}
