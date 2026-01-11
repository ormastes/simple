//! Core FFI functions for value creation, extraction, and memory allocation.

use super::collections::RuntimeString;
use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};
use std::path::Path;

// ============================================================================
// Value creation FFI functions
// ============================================================================

/// Create an integer RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}

/// Create a float RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}

/// Create a bool RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}

/// Get the NIL value (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}

// ============================================================================
// Value extraction FFI functions
// ============================================================================

/// Extract integer from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}

/// Extract float from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}

/// Extract bool from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}

// ============================================================================
// Value type checking FFI functions
// ============================================================================

/// Check if value is truthy (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}

/// Check if value is nil (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}

/// Check if value is int (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}

/// Check if value is float (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}

/// Check if value is bool (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}

/// Check if value is heap pointer (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}

// ============================================================================
// Raw memory allocation (FFI-safe, zero-cost abstraction support)
// ============================================================================

/// Allocate raw memory with 8-byte alignment (like malloc)
/// Returns a pointer to the allocated memory, or null on failure.
/// Used for zero-cost struct allocation in codegen.
#[no_mangle]
pub extern "C" fn rt_alloc(size: u64) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe { std::alloc::alloc_zeroed(layout) }
}

/// Free memory allocated by rt_alloc
#[no_mangle]
pub extern "C" fn rt_free(ptr: *mut u8, size: u64) {
    if ptr.is_null() || size == 0 {
        return;
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe {
        std::alloc::dealloc(ptr, layout);
    }
}

/// Convert raw pointer to RuntimeValue (for struct pointers)
/// The pointer is stored as a heap-tagged value.
#[no_mangle]
pub extern "C" fn rt_ptr_to_value(ptr: *mut u8) -> RuntimeValue {
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    unsafe { RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader) }
}

/// Extract raw pointer from RuntimeValue
#[no_mangle]
pub extern "C" fn rt_value_to_ptr(v: RuntimeValue) -> *mut u8 {
    if !v.is_heap() {
        return std::ptr::null_mut();
    }
    v.as_heap_ptr() as *mut u8
}

// ============================================================================
// Value equality (FFI-safe)
// ============================================================================

/// Compare two RuntimeValues for equality
#[no_mangle]
pub extern "C" fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    // Quick check: same raw value
    if a.to_raw() == b.to_raw() {
        return 1;
    }

    // Both must be same type for equality
    if a.is_int() && b.is_int() {
        return if a.as_int() == b.as_int() { 1 } else { 0 };
    }
    if a.is_float() && b.is_float() {
        return if a.as_float() == b.as_float() { 1 } else { 0 };
    }
    if a.is_bool() && b.is_bool() {
        return if a.as_bool() == b.as_bool() { 1 } else { 0 };
    }
    if a.is_nil() && b.is_nil() {
        return 1;
    }

    // For heap objects, compare by content for strings
    if a.is_heap() && b.is_heap() {
        let ptr_a = a.as_heap_ptr();
        let ptr_b = b.as_heap_ptr();
        unsafe {
            if (*ptr_a).object_type == HeapObjectType::String
                && (*ptr_b).object_type == HeapObjectType::String
            {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;
                if (*str_a).len != (*str_b).len {
                    return 0;
                }
                let data_a = (str_a.add(1)) as *const u8;
                let data_b = (str_b.add(1)) as *const u8;
                for i in 0..(*str_a).len {
                    if *data_a.add(i as usize) != *data_b.add(i as usize) {
                        return 0;
                    }
                }
                return 1;
            }
        }
    }

    0
}

// ============================================================================
// Interpreter bridge FFI (for hybrid execution)
// ============================================================================
// These functions call through function pointers that can be set by the compiler
// crate. This allows the interpreter to be plugged in without circular dependencies.

use std::sync::atomic::{AtomicPtr, Ordering};

/// Type for rt_interp_call handler function
pub type InterpCallFn = unsafe extern "C" fn(
    name_ptr: *const u8,
    name_len: u64,
    argc: u64,
    argv: *const RuntimeValue,
) -> RuntimeValue;

/// Type for rt_interp_eval handler function
pub type InterpEvalFn = extern "C" fn(expr_index: i64) -> RuntimeValue;

/// Default handler that returns NIL (no interpreter available)
unsafe extern "C" fn default_interp_call(
    _name_ptr: *const u8,
    _name_len: u64,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    RuntimeValue::NIL
}

/// Default handler that returns NIL (no interpreter available)
extern "C" fn default_interp_eval(_expr_index: i64) -> RuntimeValue {
    RuntimeValue::NIL
}

/// Global function pointer for rt_interp_call.
/// Set by compiler crate via `set_interp_call_handler`.
static INTERP_CALL_HANDLER: AtomicPtr<()> =
    AtomicPtr::new(default_interp_call as *const () as *mut ());

/// Global function pointer for rt_interp_eval.
/// Set by compiler crate via `set_interp_eval_handler`.
static INTERP_EVAL_HANDLER: AtomicPtr<()> =
    AtomicPtr::new(default_interp_eval as *const () as *mut ());

/// Set the interpreter call handler. Called by compiler crate during initialization.
///
/// # Safety
/// The handler function must have the correct signature and remain valid for the
/// lifetime of the program.
pub unsafe fn set_interp_call_handler(handler: InterpCallFn) {
    INTERP_CALL_HANDLER.store(handler as *const () as *mut (), Ordering::SeqCst);
}

/// Set the interpreter eval handler. Called by compiler crate during initialization.
///
/// # Safety
/// The handler function must have the correct signature and remain valid for the
/// lifetime of the program.
pub unsafe fn set_interp_eval_handler(handler: InterpEvalFn) {
    INTERP_EVAL_HANDLER.store(handler as *const () as *mut (), Ordering::SeqCst);
}

/// Call an interpreted function by name with RuntimeValue arguments.
///
/// This dispatches to the handler set by the compiler crate, or returns NIL
/// if no handler has been set.
///
/// # Arguments
/// * `name_ptr` - Pointer to function name string (UTF-8)
/// * `name_len` - Length of function name
/// * `argc` - Number of arguments
/// * `argv` - Pointer to array of RuntimeValue arguments
///
/// # Returns
/// RuntimeValue containing the result (NIL if no interpreter available)
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
/// argv must be a valid pointer to argc RuntimeValue elements (or null if argc is 0).
#[no_mangle]
pub unsafe extern "C" fn rt_interp_call(
    name_ptr: *const u8,
    name_len: u64,
    argc: u64,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    let handler_ptr = INTERP_CALL_HANDLER.load(Ordering::SeqCst);
    let handler: InterpCallFn = std::mem::transmute(handler_ptr);
    handler(name_ptr, name_len, argc, argv)
}

/// Evaluate an expression by index via the interpreter.
///
/// This dispatches to the handler set by the compiler crate, or returns NIL
/// if no handler has been set.
///
/// # Arguments
/// * `expr_index` - Index of the stored expression
///
/// # Returns
/// RuntimeValue containing the result (NIL if no interpreter available)
#[no_mangle]
pub extern "C" fn rt_interp_eval(expr_index: i64) -> RuntimeValue {
    let handler_ptr = INTERP_EVAL_HANDLER.load(Ordering::SeqCst);
    let handler: InterpEvalFn = unsafe { std::mem::transmute(handler_ptr) };
    handler(expr_index)
}

// ============================================================================
// Error handling (FFI-safe)
// ============================================================================

/// Called when a function is not found at runtime.
/// Prints an error message and returns NIL (caller should handle the error).
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    if name_ptr.is_null() {
        eprintln!("Runtime error: Function not found (unknown name)");
    } else {
        let name_slice = std::slice::from_raw_parts(name_ptr, name_len as usize);
        if let Ok(name_str) = std::str::from_utf8(name_slice) {
            eprintln!("Runtime error: Function '{}' not found", name_str);
        } else {
            eprintln!("Runtime error: Function not found (invalid UTF-8 name)");
        }
    }
    RuntimeValue::NIL
}

/// Called when a method is not found at runtime.
/// Prints an error message and returns NIL.
///
/// # Safety
/// type_ptr and method_ptr must be valid pointers to UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    let type_name = if type_ptr.is_null() {
        "<unknown type>"
    } else {
        let slice = std::slice::from_raw_parts(type_ptr, type_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let method_name = if method_ptr.is_null() {
        "<unknown method>"
    } else {
        let slice = std::slice::from_raw_parts(method_ptr, method_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    eprintln!(
        "Runtime error: Method '{}' not found on type '{}'",
        method_name, type_name
    );
    RuntimeValue::NIL
}

// ============================================================================
// Contract Checking (Design by Contract support)
// ============================================================================

use super::contracts::{ContractViolationKind, RuntimeContractViolation};

/// Check a contract condition and panic if it fails.
/// This is called from compiled code when contract checking is enabled.
///
/// # Arguments
/// * `condition` - The boolean condition (1 = true, 0 = false)
/// * `kind` - Type of contract (0=Pre, 1=Post, 2=ErrPost, 3=InvEntry, 4=InvExit)
/// * `func_name_ptr` - Pointer to function name string (UTF-8), may be null
/// * `func_name_len` - Length of function name
///
/// # Safety
/// func_name_ptr must be a valid pointer to func_name_len bytes of UTF-8 data, or null.
#[no_mangle]
pub unsafe extern "C" fn simple_contract_check(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
) {
    if condition != 0 {
        // Condition is true, contract satisfied
        return;
    }

    // Contract violated - create violation object and panic
    let violation_kind =
        ContractViolationKind::from_i64(kind).unwrap_or(ContractViolationKind::Pre);

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>"
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    // Create the violation object for inspection
    let violation = RuntimeContractViolation::new(violation_kind, func_name, None);
    let message = if violation.is_null() {
        format!(
            "{} violation in function '{}': contract condition failed",
            violation_kind.name(),
            func_name
        )
    } else {
        let msg = (*violation).format();
        RuntimeContractViolation::free(violation);
        msg
    };

    panic!("{}", message);
}

/// Check a contract condition with a custom message and panic if it fails.
/// This is called from compiled code when contract checking is enabled.
///
/// # Arguments
/// * `condition` - The boolean condition (1 = true, 0 = false)
/// * `kind` - Type of contract (0=Pre, 1=Post, 2=ErrPost, 3=InvEntry, 4=InvExit)
/// * `func_name_ptr` - Pointer to function name string (UTF-8), may be null
/// * `func_name_len` - Length of function name
/// * `message_ptr` - Pointer to message string (UTF-8), may be null
/// * `message_len` - Length of message
///
/// # Safety
/// Pointers must be valid or null.
#[no_mangle]
pub unsafe extern "C" fn simple_contract_check_msg(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
    message_ptr: *const u8,
    message_len: i64,
) {
    if condition != 0 {
        // Condition is true, contract satisfied
        return;
    }

    // Contract violated - create violation object and panic
    let violation_kind =
        ContractViolationKind::from_i64(kind).unwrap_or(ContractViolationKind::Pre);

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>"
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let message = if message_ptr.is_null() || message_len <= 0 {
        None
    } else {
        let slice = std::slice::from_raw_parts(message_ptr, message_len as usize);
        std::str::from_utf8(slice).ok()
    };

    // Create the violation object for inspection
    let violation = RuntimeContractViolation::new(violation_kind, func_name, message);
    let error_msg = if violation.is_null() {
        let base = format!(
            "{} violation in function '{}': contract condition failed",
            violation_kind.name(),
            func_name
        );
        if let Some(msg) = message {
            format!("{} ({})", base, msg)
        } else {
            base
        }
    } else {
        let msg = (*violation).format();
        RuntimeContractViolation::free(violation);
        msg
    };

    panic!("{}", error_msg);
}

// ============================================================================
// I/O Capture System (for testing and embedding)
// ============================================================================

use std::cell::RefCell;
use std::io::Write;

thread_local! {
    /// Captured stdout buffer (when capture mode is enabled)
    static STDOUT_CAPTURE: RefCell<Option<String>> = const { RefCell::new(None) };
    /// Captured stderr buffer (when capture mode is enabled)
    static STDERR_CAPTURE: RefCell<Option<String>> = const { RefCell::new(None) };
    /// Mock stdin buffer (for testing - reads from this instead of real stdin)
    static STDIN_BUFFER: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Enable stdout capture mode. All print output will be buffered instead of printed.
#[no_mangle]
pub extern "C" fn rt_capture_stdout_start() {
    STDOUT_CAPTURE.with(|buf| {
        *buf.borrow_mut() = Some(String::new());
    });
}

/// Enable stderr capture mode.
#[no_mangle]
pub extern "C" fn rt_capture_stderr_start() {
    STDERR_CAPTURE.with(|buf| {
        *buf.borrow_mut() = Some(String::new());
    });
}

/// Stop stdout capture and return captured content.
/// Returns empty string if capture was not enabled.
pub fn rt_capture_stdout_stop() -> String {
    STDOUT_CAPTURE.with(|buf| buf.borrow_mut().take().unwrap_or_default())
}

/// Stop stderr capture and return captured content.
pub fn rt_capture_stderr_stop() -> String {
    STDERR_CAPTURE.with(|buf| buf.borrow_mut().take().unwrap_or_default())
}

/// Get current captured stdout without stopping capture.
pub fn rt_get_captured_stdout() -> String {
    STDOUT_CAPTURE.with(|buf| buf.borrow().clone().unwrap_or_default())
}

/// Get current captured stderr without stopping capture.
pub fn rt_get_captured_stderr() -> String {
    STDERR_CAPTURE.with(|buf| buf.borrow().clone().unwrap_or_default())
}

/// Clear captured stdout buffer (keep capture mode enabled).
pub fn rt_clear_captured_stdout() {
    STDOUT_CAPTURE.with(|buf| {
        if let Some(ref mut s) = *buf.borrow_mut() {
            s.clear();
        }
    });
}

/// Clear captured stderr buffer (keep capture mode enabled).
pub fn rt_clear_captured_stderr() {
    STDERR_CAPTURE.with(|buf| {
        if let Some(ref mut s) = *buf.borrow_mut() {
            s.clear();
        }
    });
}

/// Check if stdout capture is currently enabled.
pub fn rt_is_stdout_capturing() -> bool {
    STDOUT_CAPTURE.with(|buf| buf.borrow().is_some())
}

/// Check if stderr capture is currently enabled.
pub fn rt_is_stderr_capturing() -> bool {
    STDERR_CAPTURE.with(|buf| buf.borrow().is_some())
}

// ============================================================================
// Stdin Mock Functions (for testing)
// ============================================================================

/// Set mock stdin content. When set, input() reads from this instead of real stdin.
/// Pass empty string to clear the buffer and revert to real stdin.
pub fn rt_set_stdin(content: &str) {
    STDIN_BUFFER.with(|buf| {
        if content.is_empty() {
            *buf.borrow_mut() = None;
        } else {
            *buf.borrow_mut() = Some(content.to_string());
        }
    });
}

/// Read a line from mock stdin buffer, or None if buffer is empty/not set.
/// Removes the line from the buffer (including the newline).
pub fn rt_read_stdin_line() -> Option<String> {
    STDIN_BUFFER.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut content) = *guard {
            if content.is_empty() {
                return None;
            }
            // Find the first newline
            if let Some(pos) = content.find('\n') {
                let line = content[..pos].to_string();
                *content = content[pos + 1..].to_string();
                Some(line)
            } else {
                // No newline - return remaining content and clear buffer
                let line = std::mem::take(content);
                Some(line)
            }
        } else {
            None
        }
    })
}

/// Check if mock stdin is currently active.
pub fn rt_has_mock_stdin() -> bool {
    STDIN_BUFFER.with(|buf| buf.borrow().is_some())
}

/// Clear mock stdin buffer.
pub fn rt_clear_stdin() {
    STDIN_BUFFER.with(|buf| {
        *buf.borrow_mut() = None;
    });
}

/// Read a single character from mock stdin buffer, or None if buffer is empty/not set.
pub fn rt_read_stdin_char() -> Option<char> {
    STDIN_BUFFER.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut content) = *guard {
            if content.is_empty() {
                return None;
            }
            let ch = content.chars().next();
            if ch.is_some() {
                *content = content[ch.unwrap().len_utf8()..].to_string();
            }
            ch
        } else {
            None
        }
    })
}

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

    STDOUT_CAPTURE.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut capture) = *guard {
            capture.push_str(s);
        } else {
            drop(guard); // Release borrow before print
            print!("{}", s);
            let _ = std::io::stdout().flush();
        }
    });
}

/// Print a string to stdout with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_println_str(ptr: *const u8, len: u64) {
    rt_print_str(ptr, len);
    STDOUT_CAPTURE.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut capture) = *guard {
            capture.push('\n');
        } else {
            drop(guard);
            println!();
        }
    });
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

    STDERR_CAPTURE.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut capture) = *guard {
            capture.push_str(s);
        } else {
            drop(guard);
            eprint!("{}", s);
            let _ = std::io::stderr().flush();
        }
    });
}

/// Print a string to stderr with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_eprintln_str(ptr: *const u8, len: u64) {
    rt_eprint_str(ptr, len);
    STDERR_CAPTURE.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut capture) = *guard {
            capture.push('\n');
        } else {
            drop(guard);
            eprintln!();
        }
    });
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
// Process control FFI functions
// ============================================================================

/// Exit the process with the given exit code.
#[no_mangle]
pub extern "C" fn rt_exit(code: i32) -> ! {
    std::process::exit(code)
}

// ============================================================================
// Math FFI functions
// ============================================================================

/// Power function: base^exp
#[no_mangle]
pub extern "C" fn rt_math_pow(base: f64, exp: f64) -> f64 {
    base.powf(exp)
}

/// Natural logarithm
#[no_mangle]
pub extern "C" fn rt_math_log(x: f64) -> f64 {
    x.ln()
}

/// Base-10 logarithm
#[no_mangle]
pub extern "C" fn rt_math_log10(x: f64) -> f64 {
    x.log10()
}

/// Base-2 logarithm
#[no_mangle]
pub extern "C" fn rt_math_log2(x: f64) -> f64 {
    x.log2()
}

/// Exponential function: e^x
#[no_mangle]
pub extern "C" fn rt_math_exp(x: f64) -> f64 {
    x.exp()
}

/// Cube root
#[no_mangle]
pub extern "C" fn rt_math_cbrt(x: f64) -> f64 {
    x.cbrt()
}

/// Sine
#[no_mangle]
pub extern "C" fn rt_math_sin(x: f64) -> f64 {
    x.sin()
}

/// Cosine
#[no_mangle]
pub extern "C" fn rt_math_cos(x: f64) -> f64 {
    x.cos()
}

/// Tangent
#[no_mangle]
pub extern "C" fn rt_math_tan(x: f64) -> f64 {
    x.tan()
}

/// Arcsine
#[no_mangle]
pub extern "C" fn rt_math_asin(x: f64) -> f64 {
    x.asin()
}

/// Arccosine
#[no_mangle]
pub extern "C" fn rt_math_acos(x: f64) -> f64 {
    x.acos()
}

/// Arctangent
#[no_mangle]
pub extern "C" fn rt_math_atan(x: f64) -> f64 {
    x.atan()
}

/// Two-argument arctangent
#[no_mangle]
pub extern "C" fn rt_math_atan2(y: f64, x: f64) -> f64 {
    y.atan2(x)
}

/// Hyperbolic sine
#[no_mangle]
pub extern "C" fn rt_math_sinh(x: f64) -> f64 {
    x.sinh()
}

/// Hyperbolic cosine
#[no_mangle]
pub extern "C" fn rt_math_cosh(x: f64) -> f64 {
    x.cosh()
}

/// Hyperbolic tangent
#[no_mangle]
pub extern "C" fn rt_math_tanh(x: f64) -> f64 {
    x.tanh()
}

/// Square root
#[no_mangle]
pub extern "C" fn rt_math_sqrt(x: f64) -> f64 {
    x.sqrt()
}

/// Floor
#[no_mangle]
pub extern "C" fn rt_math_floor(x: f64) -> f64 {
    x.floor()
}

/// Ceiling
#[no_mangle]
pub extern "C" fn rt_math_ceil(x: f64) -> f64 {
    x.ceil()
}

// ============================================================================
// File system FFI functions
// ============================================================================

/// Check if a file or directory exists
#[no_mangle]
pub unsafe extern "C" fn rt_file_exists(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    match std::str::from_utf8(path_bytes) {
        Ok(path_str) => Path::new(path_str).exists(),
        Err(_) => false,
    }
}

/// Get file metadata as a struct
/// Returns: [exists, is_file, is_dir, is_readable, is_writable, size]
#[no_mangle]
pub unsafe extern "C" fn rt_file_stat(
    path_ptr: *const u8,
    path_len: u64,
    out_exists: *mut bool,
    out_is_file: *mut bool,
    out_is_dir: *mut bool,
    out_is_readable: *mut bool,
    out_is_writable: *mut bool,
    out_size: *mut i64,
) {
    // Initialize all outputs to false/0
    if !out_exists.is_null() {
        *out_exists = false;
    }
    if !out_is_file.is_null() {
        *out_is_file = false;
    }
    if !out_is_dir.is_null() {
        *out_is_dir = false;
    }
    if !out_is_readable.is_null() {
        *out_is_readable = false;
    }
    if !out_is_writable.is_null() {
        *out_is_writable = false;
    }
    if !out_size.is_null() {
        *out_size = 0;
    }

    if path_ptr.is_null() {
        return;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    let path = Path::new(path_str);

    // Check existence
    if !out_exists.is_null() {
        *out_exists = path.exists();
    }

    if !path.exists() {
        return;
    }

    // Get metadata
    if let Ok(metadata) = std::fs::metadata(path) {
        if !out_is_file.is_null() {
            *out_is_file = metadata.is_file();
        }
        if !out_is_dir.is_null() {
            *out_is_dir = metadata.is_dir();
        }
        if !out_size.is_null() {
            *out_size = metadata.len() as i64;
        }

        // Check permissions (Unix-specific)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = metadata.permissions().mode();

            if !out_is_readable.is_null() {
                *out_is_readable = (mode & 0o400) != 0; // Owner read
            }
            if !out_is_writable.is_null() {
                *out_is_writable = (mode & 0o200) != 0; // Owner write
            }
        }

        // Fallback for non-Unix platforms
        #[cfg(not(unix))]
        {
            if !out_is_readable.is_null() {
                *out_is_readable = !metadata.permissions().readonly();
            }
            if !out_is_writable.is_null() {
                *out_is_writable = !metadata.permissions().readonly();
            }
        }
    }
}

/// Normalize/canonicalize a file path
/// Returns the absolute path with all symbolic links resolved
#[no_mangle]
pub unsafe extern "C" fn rt_file_canonicalize(
    path_ptr: *const u8,
    path_len: u64,
) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::canonicalize(path_str) {
        Ok(canonical) => {
            let canonical_str = canonical.to_string_lossy();
            let bytes = canonical_str.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => {
            // If canonicalize fails, try to make it absolute without resolving symlinks
            match std::env::current_dir() {
                Ok(cwd) => {
                    let absolute = cwd.join(path_str);
                    let absolute_str = absolute.to_string_lossy();
                    let bytes = absolute_str.as_bytes();
                    super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
                }
                Err(_) => RuntimeValue::NIL,
            }
        }
    }
}

/// Read entire file as text
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text(
    path_ptr: *const u8,
    path_len: u64,
) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_to_string(path_str) {
        Ok(content) => {
            let bytes = content.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Write text to file
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_text(
    path_ptr: *const u8,
    path_len: u64,
    content_ptr: *const u8,
    content_len: u64,
) -> bool {
    if path_ptr.is_null() || content_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let content_bytes = std::slice::from_raw_parts(content_ptr, content_len as usize);
    let content_str = match std::str::from_utf8(content_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::write(path_str, content_str).is_ok()
}

/// Copy file from src to dest
#[no_mangle]
pub unsafe extern "C" fn rt_file_copy(
    src_ptr: *const u8,
    src_len: u64,
    dest_ptr: *const u8,
    dest_len: u64,
) -> bool {
    if src_ptr.is_null() || dest_ptr.is_null() {
        return false;
    }

    let src_bytes = std::slice::from_raw_parts(src_ptr, src_len as usize);
    let src_str = match std::str::from_utf8(src_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let dest_bytes = std::slice::from_raw_parts(dest_ptr, dest_len as usize);
    let dest_str = match std::str::from_utf8(dest_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::copy(src_str, dest_str).is_ok()
}

/// Create directory (with optional recursive creation)
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create(
    path_ptr: *const u8,
    path_len: u64,
    recursive: bool,
) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::create_dir_all(path_str).is_ok()
    } else {
        std::fs::create_dir(path_str).is_ok()
    }
}

/// List directory entries
#[no_mangle]
pub unsafe extern "C" fn rt_dir_list(
    path_ptr: *const u8,
    path_len: u64,
) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_dir(path_str) {
        Ok(entries) => {
            // Create an array to hold the entry names
            let array_handle = super::rt_array_new(0);

            for entry_result in entries {
                if let Ok(entry) = entry_result {
                    if let Ok(name) = entry.file_name().into_string() {
                        let bytes = name.as_bytes();
                        let str_value = super::rt_string_new(bytes.as_ptr(), bytes.len() as u64);
                        super::rt_array_push(array_handle, str_value);
                    }
                }
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Remove/delete a file
#[no_mangle]
pub unsafe extern "C" fn rt_file_remove(
    path_ptr: *const u8,
    path_len: u64,
) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::remove_file(path_str).is_ok()
}

/// Remove a directory
#[no_mangle]
pub unsafe extern "C" fn rt_dir_remove(
    path_ptr: *const u8,
    path_len: u64,
    recursive: bool,
) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::remove_dir_all(path_str).is_ok()
    } else {
        std::fs::remove_dir(path_str).is_ok()
    }
}

/// Rename/move a file or directory
#[no_mangle]
pub unsafe extern "C" fn rt_file_rename(
    from_ptr: *const u8,
    from_len: u64,
    to_ptr: *const u8,
    to_len: u64,
) -> bool {
    if from_ptr.is_null() || to_ptr.is_null() {
        return false;
    }

    let from_bytes = std::slice::from_raw_parts(from_ptr, from_len as usize);
    let from_str = match std::str::from_utf8(from_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let to_bytes = std::slice::from_raw_parts(to_ptr, to_len as usize);
    let to_str = match std::str::from_utf8(to_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::rename(from_str, to_str).is_ok()
}

// ============================================================================
// Environment variable FFI functions
// ============================================================================

/// Get environment variable value
#[no_mangle]
pub unsafe extern "C" fn rt_env_get(
    name_ptr: *const u8,
    name_len: u64,
) -> RuntimeValue {
    if name_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let name_bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
    let name_str = match std::str::from_utf8(name_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::env::var(name_str) {
        Ok(value) => {
            let bytes = value.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Set environment variable
#[no_mangle]
pub unsafe extern "C" fn rt_env_set(
    name_ptr: *const u8,
    name_len: u64,
    value_ptr: *const u8,
    value_len: u64,
) -> bool {
    if name_ptr.is_null() || value_ptr.is_null() {
        return false;
    }

    let name_bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
    let name_str = match std::str::from_utf8(name_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let value_bytes = std::slice::from_raw_parts(value_ptr, value_len as usize);
    let value_str = match std::str::from_utf8(value_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::env::set_var(name_str, value_str);
    true
}

/// Get current working directory
#[no_mangle]
pub unsafe extern "C" fn rt_env_cwd() -> RuntimeValue {
    match std::env::current_dir() {
        Ok(path) => {
            let path_str = path.to_string_lossy();
            let bytes = path_str.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

// ============================================================================
// Base64 encoding/decoding FFI functions
// ============================================================================

/// Decode base64 string to bytes
#[no_mangle]
pub unsafe extern "C" fn rt_base64_decode(
    input_ptr: *const u8,
    input_len: u64,
) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let input_bytes = std::slice::from_raw_parts(input_ptr, input_len as usize);
    let input_str = match std::str::from_utf8(input_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    // Simple base64 decoding implementation
    const DECODE_TABLE: [u8; 128] = [
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62, 255, 255, 255, 63,
        52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 0, 255, 255,
        255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
        15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255,
        255, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 255, 255, 255, 255, 255,
    ];

    let mut result = Vec::new();
    let input_chars: Vec<u8> = input_str.bytes().filter(|&b| !b.is_ascii_whitespace()).collect();

    let mut i = 0;
    while i < input_chars.len() {
        // Get 4 characters (or remaining)
        let mut chunk = [0u8; 4];
        let mut chunk_len = 0;

        while chunk_len < 4 && i < input_chars.len() {
            let c = input_chars[i];
            i += 1;

            if c == b'=' {
                chunk[chunk_len] = 0;
                chunk_len += 1;
            } else if (c as usize) < 128 && DECODE_TABLE[c as usize] != 255 {
                chunk[chunk_len] = DECODE_TABLE[c as usize];
                chunk_len += 1;
            }
        }

        if chunk_len >= 2 {
            result.push((chunk[0] << 2) | (chunk[1] >> 4));
        }
        if chunk_len >= 3 {
            result.push((chunk[1] << 4) | (chunk[2] >> 2));
        }
        if chunk_len >= 4 {
            result.push((chunk[2] << 6) | chunk[3]);
        }
    }

    // Remove padding bytes
    while result.last() == Some(&0) && input_str.ends_with('=') {
        result.pop();
    }

    // Convert to string (assuming UTF-8)
    match String::from_utf8(result) {
        Ok(decoded) => {
            let bytes = decoded.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Encode bytes to base64 string
#[no_mangle]
pub unsafe extern "C" fn rt_base64_encode(
    input_ptr: *const u8,
    input_len: u64,
) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let input_bytes = std::slice::from_raw_parts(input_ptr, input_len as usize);

    const ENCODE_TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    let mut result = Vec::new();
    let mut i = 0;

    while i < input_bytes.len() {
        let b1 = input_bytes[i];
        let b2 = if i + 1 < input_bytes.len() { input_bytes[i + 1] } else { 0 };
        let b3 = if i + 2 < input_bytes.len() { input_bytes[i + 2] } else { 0 };

        result.push(ENCODE_TABLE[(b1 >> 2) as usize]);
        result.push(ENCODE_TABLE[(((b1 & 0x03) << 4) | (b2 >> 4)) as usize]);

        if i + 1 < input_bytes.len() {
            result.push(ENCODE_TABLE[(((b2 & 0x0F) << 2) | (b3 >> 6)) as usize]);
        } else {
            result.push(b'=');
        }

        if i + 2 < input_bytes.len() {
            result.push(ENCODE_TABLE[(b3 & 0x3F) as usize]);
        } else {
            result.push(b'=');
        }

        i += 3;
    }

    match String::from_utf8(result) {
        Ok(encoded) => {
            let bytes = encoded.as_bytes();
            super::rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

// ============================================================================
// Date/Time FFI Functions
// ============================================================================

/// Get current Unix timestamp in microseconds since epoch (1970-01-01 00:00:00 UTC)
#[no_mangle]
pub extern "C" fn rt_time_now_unix_micros() -> i64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(duration) => {
            let secs = duration.as_secs() as i64;
            let micros = duration.subsec_micros() as i64;
            secs * 1_000_000 + micros
        }
        Err(_) => 0,
    }
}

/// Convert Unix timestamp (microseconds) to year
#[no_mangle]
pub extern "C" fn rt_timestamp_get_year(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    timestamp_days_to_year(days)
}

/// Convert Unix timestamp (microseconds) to month (1-12)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_month(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    let (_, month, _) = timestamp_days_to_ymd(days);
    month
}

/// Convert Unix timestamp (microseconds) to day of month (1-31)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_day(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    let (_, _, day) = timestamp_days_to_ymd(days);
    day
}

/// Convert Unix timestamp (microseconds) to hour (0-23)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_hour(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    (seconds_in_day / 3600) as i32
}

/// Convert Unix timestamp (microseconds) to minute (0-59)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_minute(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    ((seconds_in_day % 3600) / 60) as i32
}

/// Convert Unix timestamp (microseconds) to second (0-59)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_second(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    (seconds_in_day % 60) as i32
}

/// Convert Unix timestamp (microseconds) to microsecond (0-999999)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_microsecond(micros: i64) -> i32 {
    (micros % 1_000_000) as i32
}

/// Convert date/time components to Unix timestamp (microseconds)
#[no_mangle]
pub extern "C" fn rt_timestamp_from_components(
    year: i32,
    month: i32,
    day: i32,
    hour: i32,
    minute: i32,
    second: i32,
    microsecond: i32,
) -> i64 {
    let days = ymd_to_timestamp_days(year, month, day);
    let seconds_in_day = (hour as i64) * 3600 + (minute as i64) * 60 + (second as i64);
    days * 86400 * 1_000_000 + seconds_in_day * 1_000_000 + (microsecond as i64)
}

/// Add days to a Unix timestamp
#[no_mangle]
pub extern "C" fn rt_timestamp_add_days(micros: i64, days: i64) -> i64 {
    micros + days * 86400 * 1_000_000
}

/// Calculate difference in days between two timestamps
#[no_mangle]
pub extern "C" fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64 {
    (micros1 - micros2) / (86400 * 1_000_000)
}

// Helper: Check if year is leap year
fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

// Helper: Get days in month
fn days_in_month(year: i32, month: i32) -> i32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => if is_leap_year(year) { 29 } else { 28 },
        _ => 0,
    }
}

// Helper: Convert days since Unix epoch to year
fn timestamp_days_to_year(days: i64) -> i32 {
    // Unix epoch starts at 1970-01-01
    let mut year = 1970;
    let mut remaining_days = days;

    // Handle negative days (dates before 1970)
    if remaining_days < 0 {
        while remaining_days < 0 {
            year -= 1;
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            remaining_days += days_in_year as i64;
        }
        return year;
    }

    // Handle positive days (dates after 1970)
    loop {
        let days_in_year = if is_leap_year(year) { 366 } else { 365 };
        if remaining_days < days_in_year as i64 {
            break;
        }
        remaining_days -= days_in_year as i64;
        year += 1;
    }

    year
}

// Helper: Convert days since Unix epoch to (year, month, day)
fn timestamp_days_to_ymd(days: i64) -> (i32, i32, i32) {
    let mut year = 1970;
    let mut remaining_days = days;

    // Handle negative days (dates before 1970)
    if remaining_days < 0 {
        while remaining_days < 0 {
            year -= 1;
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            remaining_days += days_in_year as i64;
        }
    } else {
        // Handle positive days (dates after 1970)
        loop {
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            if remaining_days < days_in_year as i64 {
                break;
            }
            remaining_days -= days_in_year as i64;
            year += 1;
        }
    }

    // Now convert remaining days to month and day
    let mut month = 1;
    while month <= 12 {
        let days_in_current_month = days_in_month(year, month) as i64;
        if remaining_days < days_in_current_month {
            break;
        }
        remaining_days -= days_in_current_month;
        month += 1;
    }

    let day = remaining_days + 1; // Days are 1-indexed

    (year, month, day as i32)
}

// Helper: Convert (year, month, day) to days since Unix epoch
fn ymd_to_timestamp_days(year: i32, month: i32, day: i32) -> i64 {
    let mut days: i64 = 0;

    // Add days for all years from 1970 to year-1
    if year >= 1970 {
        for y in 1970..year {
            days += if is_leap_year(y) { 366 } else { 365 };
        }
    } else {
        for y in year..1970 {
            days -= if is_leap_year(y) { 366 } else { 365 };
        }
    }

    // Add days for all months in current year
    for m in 1..month {
        days += days_in_month(year, m) as i64;
    }

    // Add remaining days
    days += (day - 1) as i64;

    days
}
