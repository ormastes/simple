//! Stub regex SFFI bindings used when the runtime-regex feature is disabled.

use crate::value::core::RuntimeValue;
use crate::value::collections::{rt_array_new, rt_array_push};

pub fn clear_regex_cache() {}

#[inline(always)]
pub fn sffi_regex_is_match(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    RuntimeValue::FALSE
}

#[inline(always)]
pub fn sffi_regex_find(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[inline(always)]
pub fn sffi_regex_find_all(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[inline(always)]
pub fn sffi_regex_captures(_pattern: RuntimeValue, _text: RuntimeValue) -> RuntimeValue {
    rt_array_new(0)
}

#[inline(always)]
pub fn sffi_regex_replace(_pattern: RuntimeValue, text: RuntimeValue, _replacement: RuntimeValue) -> RuntimeValue {
    text
}

#[inline(always)]
pub fn sffi_regex_replace_all(_pattern: RuntimeValue, text: RuntimeValue, _replacement: RuntimeValue) -> RuntimeValue {
    text
}

#[inline(always)]
pub fn sffi_regex_split(_pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    single_item_array(text)
}

#[inline(always)]
pub fn sffi_regex_split_n(_pattern: RuntimeValue, text: RuntimeValue, _limit: RuntimeValue) -> RuntimeValue {
    single_item_array(text)
}

fn single_item_array(value: RuntimeValue) -> RuntimeValue {
    let result = rt_array_new(1);
    rt_array_push(result, value);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_array_get, rt_array_len};

    #[test]
    fn stub_match_is_false() {
        assert_eq!(
            sffi_regex_is_match(RuntimeValue::NIL, RuntimeValue::NIL),
            RuntimeValue::FALSE
        );
    }

    #[test]
    fn stub_find_returns_empty_arrays() {
        assert_eq!(rt_array_len(sffi_regex_find(RuntimeValue::NIL, RuntimeValue::NIL)), 0);
        assert_eq!(
            rt_array_len(sffi_regex_find_all(RuntimeValue::NIL, RuntimeValue::NIL)),
            0
        );
        assert_eq!(
            rt_array_len(sffi_regex_captures(RuntimeValue::NIL, RuntimeValue::NIL)),
            0
        );
    }

    #[test]
    fn stub_replace_returns_input_text() {
        let text = RuntimeValue::from_int(42);
        assert_eq!(sffi_regex_replace(RuntimeValue::NIL, text, RuntimeValue::NIL), text);
        assert_eq!(sffi_regex_replace_all(RuntimeValue::NIL, text, RuntimeValue::NIL), text);
    }

    #[test]
    fn stub_split_returns_text_singleton() {
        let text = RuntimeValue::from_int(42);
        let split = sffi_regex_split(RuntimeValue::NIL, text);
        let split_n = sffi_regex_split_n(RuntimeValue::NIL, text, RuntimeValue::from_int(1));

        assert_eq!(rt_array_len(split), 1);
        assert_eq!(rt_array_get(split, 0), text);
        assert_eq!(rt_array_len(split_n), 1);
        assert_eq!(rt_array_get(split_n, 0), text);
    }
}
