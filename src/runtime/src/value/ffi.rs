//! Core FFI functions for value creation, extraction, and memory allocation.

use super::collections::RuntimeString;
use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

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

    // Contract violated - panic with error message
    let kind_name = match kind {
        0 => "Precondition",
        1 => "Postcondition",
        2 => "Error postcondition",
        3 => "Entry invariant",
        4 => "Exit invariant",
        _ => "Contract",
    };

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>".to_string()
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice)
            .unwrap_or("<invalid UTF-8>")
            .to_string()
    };

    panic!(
        "{} violation in function '{}': contract condition failed",
        kind_name, func_name
    );
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
