//! Regular expression FFI bindings for Simple language
//!
//! This module provides FFI functions to expose Rust's regex crate to Simple.
//! It handles:
//! - Regex compilation and caching
//! - Pattern matching and searching
//! - Capture groups
//! - Text replacement
//! - Text splitting
//!
//! ## Design
//! FFI functions return simple types (bool, string, array) that the Simple
//! wrapper (`regex_utils.spl`) wraps in proper Simple types (Option, Struct).

use regex::Regex;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use super::super::RuntimeValue;
use super::super::collections::{rt_array_new, rt_array_push, rt_string_new, RuntimeString};
use super::super::heap::HeapObjectType;

/// Global regex cache to avoid recompiling patterns
lazy_static::lazy_static! {
    static ref REGEX_CACHE: Mutex<HashMap<String, Arc<Regex>>> = Mutex::new(HashMap::new());
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Get a string from a RuntimeValue (returns None if not a string)
fn get_string(val: &RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::String {
            return None;
        }
        let str_ptr = ptr as *const RuntimeString;
        let bytes = (*str_ptr).as_bytes();
        String::from_utf8(bytes.to_vec()).ok()
    }
}

/// Create a RuntimeValue string from Rust &str
fn create_string(s: &str) -> RuntimeValue {
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

/// Compile a regex pattern
///
/// # Arguments
/// * `pattern` - The regex pattern string
///
/// # Returns
/// * `Some(handle)` - Success, returns cache handle
/// * `None` - Compilation failed
fn regex_compile(pattern: &str) -> Option<Arc<Regex>> {
    // Check cache first
    {
        let cache = REGEX_CACHE.lock().ok()?;
        if let Some(regex) = cache.get(pattern) {
            return Some(Arc::clone(regex));
        }
    }

    // Compile new regex
    match Regex::new(pattern) {
        Ok(regex) => {
            let regex_arc = Arc::new(regex);
            // Store in cache
            if let Ok(mut cache) = REGEX_CACHE.lock() {
                cache.insert(pattern.to_string(), Arc::clone(&regex_arc));
            }
            Some(regex_arc)
        }
        Err(_) => None,
    }
}

// ============================================================================
// Core Regex Operations
// ============================================================================

/// Check if pattern matches text
///
/// FFI signature: regex_is_match(pattern: text, text: text) -> bool
#[no_mangle]
pub extern "C" fn ffi_regex_is_match(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return RuntimeValue::FALSE;
    };

    let Some(text_str) = get_string(&text) else {
        return RuntimeValue::FALSE;
    };

    match regex_compile(&pattern_str) {
        Some(regex) => RuntimeValue::from_bool(regex.is_match(&text_str)),
        None => RuntimeValue::FALSE,
    }
}

/// Find first match in text
///
/// Returns array [text, start, end] or empty array if no match
/// FFI signature: regex_find_internal(pattern: text, text: text) -> [text, i64, i64] or []
#[no_mangle]
pub extern "C" fn ffi_regex_find(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return rt_array_new(0);
    };

    let Some(text_str) = get_string(&text) else {
        return rt_array_new(0);
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        return rt_array_new(0);
    };

    match regex.find(&text_str) {
        Some(m) => {
            // Return [text, start, end]
            let array = rt_array_new(3);
            if array.is_nil() {
                return rt_array_new(0);
            }

            rt_array_push(array, create_string(m.as_str()));
            rt_array_push(array, RuntimeValue::from_int(m.start() as i64));
            rt_array_push(array, RuntimeValue::from_int(m.end() as i64));

            array
        }
        None => rt_array_new(0),
    }
}

/// Find all matches in text
///
/// Returns array of [text, start, end] arrays
/// FFI signature: regex_find_all_internal(pattern: text, text: text) -> [[text, i64, i64], ...]
#[no_mangle]
pub extern "C" fn ffi_regex_find_all(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return rt_array_new(0);
    };

    let Some(text_str) = get_string(&text) else {
        return rt_array_new(0);
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        return rt_array_new(0);
    };

    // Count matches first to allocate array
    let match_count = regex.find_iter(&text_str).count();
    let result = rt_array_new(match_count as u64);

    if result.is_nil() {
        return rt_array_new(0);
    }

    // Populate array with match data
    for m in regex.find_iter(&text_str) {
        let match_array = rt_array_new(3);
        if !match_array.is_nil() {
            rt_array_push(match_array, create_string(m.as_str()));
            rt_array_push(match_array, RuntimeValue::from_int(m.start() as i64));
            rt_array_push(match_array, RuntimeValue::from_int(m.end() as i64));
            rt_array_push(result, match_array);
        }
    }

    result
}

/// Capture groups from first match
///
/// Returns [full_match, group1_or_empty, group2_or_empty, ...] or empty array if no match
/// Empty string indicates that group didn't match (e.g., optional groups)
/// FFI signature: regex_captures_internal(pattern: text, text: text) -> [text, ...]
#[no_mangle]
pub extern "C" fn ffi_regex_captures(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return rt_array_new(0);
    };

    let Some(text_str) = get_string(&text) else {
        return rt_array_new(0);
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        return rt_array_new(0);
    };

    match regex.captures(&text_str) {
        Some(caps) => {
            // Allocate array for all captures (full match + groups)
            let result = rt_array_new(caps.len() as u64);
            if result.is_nil() {
                return rt_array_new(0);
            }

            // Add full match (group 0)
            let full_match = caps.get(0).map(|m| m.as_str()).unwrap_or("");
            rt_array_push(result, create_string(full_match));

            // Add capture groups (1, 2, ...) - empty string if group didn't match
            for i in 1..caps.len() {
                let group_str = caps.get(i).map(|m| m.as_str()).unwrap_or("");
                rt_array_push(result, create_string(group_str));
            }

            result
        }
        None => rt_array_new(0),
    }
}

// ============================================================================
// Replacement Operations
// ============================================================================

/// Replace first match
///
/// FFI signature: regex_replace(pattern: text, text: text, replacement: text) -> text
#[no_mangle]
pub extern "C" fn ffi_regex_replace(
    pattern: RuntimeValue,
    text: RuntimeValue,
    replacement: RuntimeValue,
) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return text;
    };

    let Some(text_str) = get_string(&text) else {
        return text;
    };

    let Some(replacement_str) = get_string(&replacement) else {
        return text;
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        return text;
    };

    let result = regex.replace(&text_str, replacement_str.as_str()).to_string();
    create_string(&result)
}

/// Replace all matches
///
/// FFI signature: regex_replace_all(pattern: text, text: text, replacement: text) -> text
#[no_mangle]
pub extern "C" fn ffi_regex_replace_all(
    pattern: RuntimeValue,
    text: RuntimeValue,
    replacement: RuntimeValue,
) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        return text;
    };

    let Some(text_str) = get_string(&text) else {
        return text;
    };

    let Some(replacement_str) = get_string(&replacement) else {
        return text;
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        return text;
    };

    let result = regex.replace_all(&text_str, replacement_str.as_str()).to_string();
    create_string(&result)
}

// ============================================================================
// Split Operations
// ============================================================================

/// Split text by pattern
///
/// FFI signature: regex_split(pattern: text, text: text) -> [text, ...]
#[no_mangle]
pub extern "C" fn ffi_regex_split(pattern: RuntimeValue, text: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        let result = rt_array_new(1);
        rt_array_push(result, text);
        return result;
    };

    let Some(text_str) = get_string(&text) else {
        return rt_array_new(0);
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        let result = rt_array_new(1);
        rt_array_push(result, text);
        return result;
    };

    // Count parts first
    let parts: Vec<&str> = regex.split(&text_str).collect();
    let result = rt_array_new(parts.len() as u64);

    if result.is_nil() {
        return rt_array_new(0);
    }

    for part in parts {
        rt_array_push(result, create_string(part));
    }

    result
}

/// Split text by pattern with limit
///
/// FFI signature: regex_split_n(pattern: text, text: text, limit: i64) -> [text, ...]
#[no_mangle]
pub extern "C" fn ffi_regex_split_n(pattern: RuntimeValue, text: RuntimeValue, limit: RuntimeValue) -> RuntimeValue {
    let Some(pattern_str) = get_string(&pattern) else {
        let result = rt_array_new(1);
        rt_array_push(result, text);
        return result;
    };

    let Some(text_str) = get_string(&text) else {
        return rt_array_new(0);
    };

    let limit_val = if limit.is_int() {
        limit.as_int().max(0) as usize
    } else {
        usize::MAX
    };

    let Some(regex) = regex_compile(&pattern_str) else {
        let result = rt_array_new(1);
        rt_array_push(result, text);
        return result;
    };

    // Count parts first
    let parts: Vec<&str> = regex.splitn(&text_str, limit_val).collect();
    let result = rt_array_new(parts.len() as u64);

    if result.is_nil() {
        return rt_array_new(0);
    }

    for part in parts {
        rt_array_push(result, create_string(part));
    }

    result
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{rt_array_get, rt_array_len};

    #[test]
    fn test_regex_is_match() {
        let pattern = create_string(r"\d+");
        let text = create_string("Hello 123");
        let result = ffi_regex_is_match(pattern, text);
        assert_eq!(result, RuntimeValue::TRUE);

        let text_no_match = create_string("Hello");
        let result_no_match = ffi_regex_is_match(pattern, text_no_match);
        assert_eq!(result_no_match, RuntimeValue::FALSE);
    }

    #[test]
    fn test_regex_find() {
        let pattern = create_string(r"\d+");
        let text = create_string("Price: $42.99");
        let result = ffi_regex_find(pattern, text);

        // Check it's an array with 3 elements
        assert!(!result.is_nil());
        assert_eq!(rt_array_len(result), 3);

        // Check first element is "42"
        let match_text = rt_array_get(result, 0);
        if let Some(s) = get_string(&match_text) {
            assert_eq!(s, "42");
        } else {
            panic!("Expected string match");
        }
    }

    #[test]
    fn test_regex_replace_all() {
        let pattern = create_string(r"\d+");
        let text = create_string("I have 5 apples and 3 oranges");
        let replacement = create_string("X");
        let result = ffi_regex_replace_all(pattern, text, replacement);

        if let Some(s) = get_string(&result) {
            assert_eq!(s, "I have X apples and X oranges");
        } else {
            panic!("Expected string result");
        }
    }

    #[test]
    fn test_regex_split() {
        let pattern = create_string(r"\s+");
        let text = create_string("one  two   three");
        let result = ffi_regex_split(pattern, text);

        assert_eq!(rt_array_len(result), 3);
    }
}
