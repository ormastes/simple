//! Print and input FFI functions with capture support.
//!
//! Provides print(), println(), eprint(), eprintln() and input() functionality
//! for Simple programs. Supports capture mode for testing and embedding.
//!
//! ## Features
//!
//! - **Print to stdout**: rt_print_str(), rt_println_str()
//! - **Print to stderr**: rt_eprint_str(), rt_eprintln_str()
//! - **Value printing**: rt_print_value(), rt_println_value(), etc.
//! - **Input from stdin**: rt_read_stdin_line_ffi()
//! - **Capture Support**: Respects I/O capture mode (see io_capture module)
//!
//! ## Usage Pattern
//!
//! ```ignore
//! // Print a string
//! let msg = b"Hello, world!";
//! unsafe { rt_println_str(msg.as_ptr(), msg.len() as u64); }
//!
//! // Print a RuntimeValue
//! let val = RuntimeValue::from_int(42);
//! rt_println_value(val);
//!
//! // Read from stdin
//! let input = rt_read_stdin_line_ffi();
//! ```
//!
//! ## Capture Mode
//!
//! When I/O capture is enabled (via rt_capture_stdout_start()), print functions
//! append to the capture buffer instead of writing to stdout/stderr.

use crate::value::core::RuntimeValue;
use crate::value::heap::{HeapHeader, HeapObjectType};
use crate::value::collections::RuntimeString;
use super::io_capture::{append_stdout, append_stderr, is_stdout_capturing, is_stderr_capturing, read_stdin_line_internal};
use std::io::Write;

// ============================================================================
// Print FFI Functions (with capture support)
// ============================================================================

/// Print a string to stdout (with optional capture).
/// If capture mode is enabled, appends to capture buffer instead of printing.
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_print_str(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }
    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let s = std::str::from_utf8_unchecked(slice);

    if is_stdout_capturing() {
        append_stdout(s);
    } else {
        print!("{}", s);
        let _ = std::io::stdout().flush();
    }
}

/// Print a string to stdout with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_println_str(ptr: *const u8, len: u64) {
    rt_print_str(ptr, len);
    if is_stdout_capturing() {
        append_stdout("\n");
    } else {
        println!();
    }
}

/// Print a string to stderr (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_eprint_str(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }
    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let s = std::str::from_utf8_unchecked(slice);

    if is_stderr_capturing() {
        append_stderr(s);
    } else {
        eprint!("{}", s);
        let _ = std::io::stderr().flush();
    }
}

/// Print a string to stderr with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_eprintln_str(ptr: *const u8, len: u64) {
    rt_eprint_str(ptr, len);
    if is_stderr_capturing() {
        append_stderr("\n");
    } else {
        eprintln!();
    }
}

/// Print a RuntimeValue to stdout (converts to display string first).
#[no_mangle]
pub extern "C" fn rt_print_value(v: RuntimeValue) {
    let s = value_to_display_string(v);
    unsafe {
        rt_print_str(s.as_ptr(), s.len() as u64);
    }
}

/// Print a RuntimeValue to stdout with newline.
#[no_mangle]
pub extern "C" fn rt_println_value(v: RuntimeValue) {
    let s = value_to_display_string(v);
    unsafe {
        rt_println_str(s.as_ptr(), s.len() as u64);
    }
}

/// Print a RuntimeValue to stderr.
#[no_mangle]
pub extern "C" fn rt_eprint_value(v: RuntimeValue) {
    let s = value_to_display_string(v);
    unsafe {
        rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
}

/// Print a RuntimeValue to stderr with newline.
#[no_mangle]
pub extern "C" fn rt_eprintln_value(v: RuntimeValue) {
    let s = value_to_display_string(v);
    unsafe {
        rt_eprintln_str(s.as_ptr(), s.len() as u64);
    }
}

/// Convert RuntimeValue to display string.
fn value_to_display_string(v: RuntimeValue) -> String {
    if v.is_nil() {
        "nil".to_string()
    } else if v.is_int() {
        v.as_int().to_string()
    } else if v.is_float() {
        v.as_float().to_string()
    } else if v.is_bool() {
        if v.as_bool() { "true" } else { "false" }.to_string()
    } else if v.is_heap() {
        let ptr = v.as_heap_ptr();
        unsafe {
            match (*ptr).object_type {
                HeapObjectType::String => {
                    let str_obj = ptr as *const RuntimeString;
                    let data = (str_obj.add(1)) as *const u8;
                    let slice = std::slice::from_raw_parts(data, (*str_obj).len as usize);
                    String::from_utf8_lossy(slice).into_owned()
                }
                HeapObjectType::Array => format!("<array@{:p}>", ptr),
                HeapObjectType::Dict => format!("<dict@{:p}>", ptr),
                HeapObjectType::Object => format!("<object@{:p}>", ptr),
                HeapObjectType::Closure => format!("<closure@{:p}>", ptr),
                _ => format!("<heap@{:p}>", ptr),
            }
        }
    } else {
        format!("<value:{:#x}>", v.to_raw())
    }
}

// ============================================================================
// Stdin Input Functions
// ============================================================================

use std::io::{self, BufRead};

/// Read a line from stdin (checks mock first, then real stdin)
#[export_name = "rt_read_stdin_line"]
pub extern "C" fn rt_read_stdin_line_ffi() -> RuntimeValue {
    // First try mock stdin for testing
    if let Some(line) = read_stdin_line_internal() {
        let bytes = line.as_bytes();
        return unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) };
    }

    // Fall back to real stdin
    let stdin = io::stdin();
    let mut line = String::new();

    match stdin.lock().read_line(&mut line) {
        Ok(_) => {
            // Remove trailing newline
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            let bytes = line.as_bytes();
            unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
        }
        Err(_) => RuntimeValue::NIL,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ffi::io_capture::{
        rt_capture_stdout_start, rt_capture_stdout_stop, rt_capture_stderr_start, rt_capture_stderr_stop, rt_set_stdin,
    };

    #[test]
    fn test_print_str_basic() {
        rt_capture_stdout_start();
        let msg = b"Hello, world!";
        unsafe {
            rt_print_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "Hello, world!");
    }

    #[test]
    fn test_println_str_basic() {
        rt_capture_stdout_start();
        let msg = b"Hello";
        unsafe {
            rt_println_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "Hello\n");
    }

    #[test]
    fn test_eprint_str_basic() {
        rt_capture_stderr_start();
        let msg = b"Error message";
        unsafe {
            rt_eprint_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "Error message");
    }

    #[test]
    fn test_eprintln_str_basic() {
        rt_capture_stderr_start();
        let msg = b"Error";
        unsafe {
            rt_eprintln_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "Error\n");
    }

    #[test]
    fn test_print_str_null() {
        rt_capture_stdout_start();
        unsafe {
            rt_print_str(std::ptr::null(), 0);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, ""); // Should not crash
    }

    #[test]
    fn test_print_value_int() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_int(42));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "42");
    }

    #[test]
    fn test_print_value_float() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_float(3.25));
        let output = rt_capture_stdout_stop();
        // Float to string conversion may have precision issues
        assert!(output.starts_with("3.25") || output == "3.139999999999997");
    }

    #[test]
    fn test_print_value_bool() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_bool(true));
        unsafe {
            rt_print_str(b" ".as_ptr(), 1);
        }
        rt_print_value(RuntimeValue::from_bool(false));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "true false");
    }

    #[test]
    fn test_print_value_nil() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::NIL);
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "nil");
    }

    #[test]
    fn test_println_value() {
        rt_capture_stdout_start();
        rt_println_value(RuntimeValue::from_int(42));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "42\n");
    }

    #[test]
    fn test_eprint_value() {
        rt_capture_stderr_start();
        rt_eprint_value(RuntimeValue::from_int(99));
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "99");
    }

    #[test]
    fn test_eprintln_value() {
        rt_capture_stderr_start();
        rt_eprintln_value(RuntimeValue::from_int(99));
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "99\n");
    }

    #[test]
    fn test_value_to_display_string() {
        assert_eq!(value_to_display_string(RuntimeValue::NIL), "nil");
        assert_eq!(value_to_display_string(RuntimeValue::from_int(42)), "42");
        // Float to string conversion may have precision issues
        let float_str = value_to_display_string(RuntimeValue::from_float(3.25));
        assert!(float_str.starts_with("3.25") || float_str == "3.139999999999997");
        assert_eq!(value_to_display_string(RuntimeValue::from_bool(true)), "true");
        assert_eq!(value_to_display_string(RuntimeValue::from_bool(false)), "false");
    }

    #[test]
    fn test_read_stdin_line_mock() {
        rt_set_stdin("test input\n");
        let result = rt_read_stdin_line_ffi();

        // Result should be a string RuntimeValue
        assert!(result.is_heap());

        // Convert to Rust string to verify
        let ptr = result.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr).len as usize);
            let s = String::from_utf8_lossy(slice);
            assert_eq!(s, "test input");
        }
    }

    #[test]
    fn test_read_stdin_line_multiple() {
        rt_set_stdin("line1\nline2\n");

        let result1 = rt_read_stdin_line_ffi();
        let ptr1 = result1.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr1.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr1).len as usize);
            assert_eq!(String::from_utf8_lossy(slice), "line1");
        }

        let result2 = rt_read_stdin_line_ffi();
        let ptr2 = result2.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr2.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr2).len as usize);
            assert_eq!(String::from_utf8_lossy(slice), "line2");
        }
    }
}
