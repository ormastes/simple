//! net module
//!
//! Network Operations FFI
//! 
//! HTTP requests and socket operations.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// HTTP GET request
#[no_mangle]
pub unsafe extern "C" fn rt_http_get(url: *const c_char) -> *mut c_char {
    let url_str = CStr::from_ptr(url as *const i8).to_string_lossy();
    match ureq::get(url_str.as_ref()).call() {
        Ok(response) => {
            match response.into_string() {
                Ok(body) => CString::new(body).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
                Err(_) => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// HTTP POST request
#[no_mangle]
pub unsafe extern "C" fn rt_http_post(url: *const c_char, body: *const c_char) -> *mut c_char {
    let url_str = CStr::from_ptr(url as *const i8).to_string_lossy();
    let body_str = CStr::from_ptr(body as *const i8).to_string_lossy();
    match ureq::post(url_str.as_ref()).send_string(body_str.as_ref()) {
        Ok(response) => {
            match response.into_string() {
                Ok(resp_body) => CString::new(resp_body).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
                Err(_) => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

