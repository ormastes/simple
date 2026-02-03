//! system module
//!
//! System Information FFI
//! 
//! Hostname, CPU count, and system info.

use std::ffi::CString;
use std::os::raw::c_char;
use hostname::get;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Get system hostname
#[no_mangle]
pub extern "C" fn rt_hostname() -> *mut c_char {
    match get() {
        Ok(name) => {
            let name_str = name.to_string_lossy().to_string();
            CString::new(name_str).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Get number of logical CPU cores
#[no_mangle]
pub extern "C" fn rt_system_cpu_count() -> i64 {
    num_cpus::get() as i64
}

