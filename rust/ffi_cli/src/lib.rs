//! cli module
//!
//! CLI Tools FFI
//! 
//! Readline, file watching, and signal handling.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use rustyline::DefaultEditor;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Read line from stdin with default prompt
#[no_mangle]
pub extern "C" fn rt_readline() -> *mut c_char {
    match DefaultEditor::new() {
        Ok(mut editor) => {
            match editor.readline("> ") {
                Ok(line) => CString::new(line).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
                Err(_) => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Read line from stdin with custom prompt
#[no_mangle]
pub unsafe extern "C" fn rt_readline_with_prompt(prompt: *const c_char) -> *mut c_char {
    let prompt_str = CStr::from_ptr(prompt as *const i8).to_string_lossy();
    match DefaultEditor::new() {
        Ok(mut editor) => {
            match editor.readline(prompt_str.as_ref()) {
                Ok(line) => CString::new(line).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut()),
                Err(_) => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

