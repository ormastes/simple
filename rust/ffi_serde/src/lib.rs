//! serde module
//!
//! Serialization FFI
//! 
//! JSON, TOML, YAML, and bincode serialization.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use serde_json::Value;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Check if JSON string is valid
#[no_mangle]
pub unsafe extern "C" fn rt_json_parse(json_str: *const c_char) -> bool {
    let json = CStr::from_ptr(json_str as *const i8).to_string_lossy();
    serde_json::from_str::<Value>(json.as_ref()).is_ok()
}

/// Convert data to JSON string (stub)
#[no_mangle]
pub unsafe extern "C" fn rt_json_stringify(_data: *const c_char) -> *mut c_char {
    // TODO: Implement JSON stringification
    std::ptr::null_mut()
}

/// Get value from JSON by path
#[no_mangle]
pub unsafe extern "C" fn rt_json_get(json_str: *const c_char, path: *const c_char) -> *mut c_char {
    let json = CStr::from_ptr(json_str as *const i8).to_string_lossy();
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    match serde_json::from_str::<Value>(json.as_ref()) {
        Ok(val) => {
            let result = val.get(path_str.as_ref())
                .and_then(|v| serde_json::to_string(v).ok());
            match result {
                Some(s) => CString::new(s).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
                None => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Check if TOML string is valid
#[no_mangle]
pub unsafe extern "C" fn rt_toml_parse(toml_str: *const c_char) -> bool {
    let toml = CStr::from_ptr(toml_str as *const i8).to_string_lossy();
    toml::from_str::<toml::Value>(toml.as_ref()).is_ok()
}

