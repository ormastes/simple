//! data module
//!
//! Data Structures FFI
//! 
//! Regex, string interning, and data structures.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use regex::Regex;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Check if text matches regex pattern
#[no_mangle]
pub unsafe extern "C" fn rt_regex_match(pattern: *const c_char, text: *const c_char) -> bool {
    let pattern_str = CStr::from_ptr(pattern as *const i8).to_string_lossy();
    let text_str = CStr::from_ptr(text as *const i8).to_string_lossy();
    match Regex::new(pattern_str.as_ref()) {
        Ok(re) => re.is_match(text_str.as_ref()),
        Err(_) => false,
    }
}

/// Find all regex matches (newline-separated)
#[no_mangle]
pub unsafe extern "C" fn rt_regex_find_all(pattern: *const c_char, text: *const c_char) -> *mut c_char {
    let pattern_str = CStr::from_ptr(pattern as *const i8).to_string_lossy();
    let text_str = CStr::from_ptr(text as *const i8).to_string_lossy();
    match Regex::new(pattern_str.as_ref()) {
        Ok(re) => {
            let matches: Vec<String> = re.find_iter(text_str.as_ref())
                .map(|m| m.as_str().to_string())
                .collect();
            let joined = matches.join("\n");
            CString::new(joined).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Replace all regex matches
#[no_mangle]
pub unsafe extern "C" fn rt_regex_replace(pattern: *const c_char, text: *const c_char, replacement: *const c_char) -> *mut c_char {
    let pattern_str = CStr::from_ptr(pattern as *const i8).to_string_lossy();
    let text_str = CStr::from_ptr(text as *const i8).to_string_lossy();
    let repl_str = CStr::from_ptr(replacement as *const i8).to_string_lossy();
    match Regex::new(pattern_str.as_ref()) {
        Ok(re) => {
            let result = re.replace_all(text_str.as_ref(), repl_str.as_ref()).to_string();
            CString::new(result).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

