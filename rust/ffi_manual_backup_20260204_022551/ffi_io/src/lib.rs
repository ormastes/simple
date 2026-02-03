//! io module
//!
//! I/O Operations FFI
//! 
//! Complete file, directory, environment, and glob operations.

use std::fs;
use std::env;
use std::path::Path;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use glob::glob;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Check if file exists
#[no_mangle]
pub unsafe extern "C" fn rt_file_exists(path: *const c_char) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    Path::new(path_str.as_ref()).exists()
}

/// Read entire file as text
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text(path: *const c_char) -> *mut c_char {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    match fs::read_to_string(path_str.as_ref()) {
        Ok(s) => CString::new(s).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Write text to file
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_text(path: *const c_char, content: *const c_char) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    let content_str = CStr::from_ptr(content as *const i8).to_string_lossy();
    fs::write(path_str.as_ref(), content_str.as_ref()).is_ok()
}

/// Copy file
#[no_mangle]
pub unsafe extern "C" fn rt_file_copy(src: *const c_char, dst: *const c_char) -> bool {
    let src_str = CStr::from_ptr(src as *const i8).to_string_lossy();
    let dst_str = CStr::from_ptr(dst as *const i8).to_string_lossy();
    fs::copy(src_str.as_ref(), dst_str.as_ref()).is_ok()
}

/// Delete file
#[no_mangle]
pub unsafe extern "C" fn rt_file_delete(path: *const c_char) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    fs::remove_file(path_str.as_ref()).is_ok()
}

/// Atomic write (write to temp, then rename)
#[no_mangle]
pub unsafe extern "C" fn rt_file_atomic_write(path: *const c_char, content: *const c_char) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    let content_str = CStr::from_ptr(content as *const i8).to_string_lossy();
    let temp_path = format!("{}.tmp", path_str);
    if fs::write(&temp_path, content_str.as_ref()).is_err() { return false; }
    fs::rename(&temp_path, path_str.as_ref()).is_ok()
}

/// Create directory
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create(path: *const c_char, recursive: bool) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    if recursive {
        fs::create_dir_all(path_str.as_ref()).is_ok()
    } else {
        fs::create_dir(path_str.as_ref()).is_ok()
    }
}

/// Create directory recursively
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create_all(path: *const c_char) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    fs::create_dir_all(path_str.as_ref()).is_ok()
}

/// List directory entries (newline-separated)
#[no_mangle]
pub unsafe extern "C" fn rt_dir_list(path: *const c_char) -> *mut c_char {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    match fs::read_dir(path_str.as_ref()) {
        Ok(entries) => {
            let names: Vec<String> = entries
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().to_string())
                .collect();
            let joined = names.join("\n");
            CString::new(joined).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Walk directory recursively
#[no_mangle]
pub unsafe extern "C" fn rt_dir_walk(_path: *const c_char) -> *mut c_char {
    // TODO: Implement recursive directory walk
    std::ptr::null_mut()
}

/// Remove directory
#[no_mangle]
pub unsafe extern "C" fn rt_dir_remove(path: *const c_char, recursive: bool) -> bool {
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    if recursive {
        fs::remove_dir_all(path_str.as_ref()).is_ok()
    } else {
        fs::remove_dir(path_str.as_ref()).is_ok()
    }
}

/// Get current working directory
#[no_mangle]
pub extern "C" fn rt_env_cwd() -> *mut c_char {
    env::current_dir()
        .ok()
        .and_then(|p| CString::new(p.to_string_lossy().to_string()).ok())
        .map(|c| c.into_raw())
        .unwrap_or(std::ptr::null_mut())
}

/// Get home directory
#[no_mangle]
pub extern "C" fn rt_env_home() -> *mut c_char {
    env::var("HOME")
        .ok()
        .and_then(|s| CString::new(s).ok())
        .map(|c| c.into_raw())
        .unwrap_or(std::ptr::null_mut())
}

/// Get environment variable
#[no_mangle]
pub unsafe extern "C" fn rt_env_get(key: *const c_char) -> *mut c_char {
    let key_str = CStr::from_ptr(key as *const i8).to_string_lossy();
    env::var(key_str.as_ref())
        .ok()
        .and_then(|s| CString::new(s).ok())
        .map(|c| c.into_raw())
        .unwrap_or(std::ptr::null_mut())
}

/// Set environment variable
#[no_mangle]
pub unsafe extern "C" fn rt_env_set(key: *const c_char, value: *const c_char) -> bool {
    let key_str = CStr::from_ptr(key as *const i8).to_string_lossy();
    let val_str = CStr::from_ptr(value as *const i8).to_string_lossy();
    env::set_var(key_str.as_ref(), val_str.as_ref());
    true
}

/// Find files matching glob pattern
#[no_mangle]
pub unsafe extern "C" fn rt_glob(pattern: *const c_char) -> *mut c_char {
    let pattern_str = CStr::from_ptr(pattern as *const i8).to_string_lossy();
    match glob(pattern_str.as_ref()) {
        Ok(paths) => {
            let files: Vec<String> = paths
                .filter_map(|p| p.ok())
                .map(|p| p.to_string_lossy().to_string())
                .collect();
            let joined = files.join("\n");
            CString::new(joined).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

