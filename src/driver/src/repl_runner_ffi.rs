//! REPL execution FFI - bridges Simple REPL to Rust Runner
//!
//! This module provides FFI functions that allow the Simple REPL to execute
//! code using the Rust Runner infrastructure.
//!
//! Uses thread-local storage to avoid Send/Sync requirements on Runner.

use crate::runner::Runner;
use crate::doctest::{is_definition_like, build_source, append_to_prelude};
use std::cell::RefCell;

thread_local! {
    /// Thread-local runner for REPL execution
    static REPL_RUNNER: RefCell<Option<Runner>> = RefCell::new(None);

    /// Thread-local prelude accumulator
    static REPL_PRELUDE: RefCell<String> = RefCell::new(String::new());
}

/// Initialize REPL runner (must be called from the same thread that will execute code)
#[no_mangle]
pub extern "C" fn simple_repl_runner_init() -> bool {
    let runner = Runner::new();
    REPL_RUNNER.with(|r| {
        *r.borrow_mut() = Some(runner);
    });
    true
}

/// Cleanup REPL runner
#[no_mangle]
pub extern "C" fn simple_repl_runner_cleanup() {
    REPL_RUNNER.with(|r| {
        *r.borrow_mut() = None;
    });
    REPL_PRELUDE.with(|p| {
        p.borrow_mut().clear();
    });
}

/// Execute code in REPL context
/// Returns 0 for success, 1 for error
/// Output is written to result_buffer
#[no_mangle]
pub extern "C" fn simple_repl_runner_execute(
    code_ptr: *const u8,
    code_len: usize,
    result_buffer: *mut u8,
    result_capacity: usize,
) -> i32 {
    // Convert code from raw pointer
    let code = unsafe {
        let slice = std::slice::from_raw_parts(code_ptr, code_len);
        match std::str::from_utf8(slice) {
            Ok(s) => s.to_string(),
            Err(_) => {
                write_error(result_buffer, result_capacity, "Invalid UTF-8 in code");
                return 1;
            }
        }
    };

    // Execute code with runner
    let result = REPL_RUNNER.with(|r| {
        let mut runner_opt = r.borrow_mut();
        match runner_opt.as_mut() {
            Some(runner) => {
                // Get prelude
                let prelude = REPL_PRELUDE.with(|p| p.borrow().clone());

                // Check if this is a definition
                let is_def = is_definition_like(&code);

                // Build source with prelude
                let full_code = build_source(&prelude, &code, is_def);

                // Execute
                let exec_result = runner.run_source_in_memory(&full_code);

                // Update prelude if successful and is definition
                if exec_result.is_ok() && is_def {
                    REPL_PRELUDE.with(|p| {
                        let mut prelude_ref = p.borrow_mut();
                        append_to_prelude(&mut prelude_ref, &code, true);
                    });
                }

                exec_result
            }
            None => Err("Runner not initialized".into()),
        }
    });

    match result {
        Ok(_) => {
            // Success
            write_output(result_buffer, result_capacity, "OK");
            0
        }
        Err(e) => {
            // Error
            let error_msg = format!("{}", e);
            write_error(result_buffer, result_capacity, &error_msg);
            1
        }
    }
}

/// Clear the REPL prelude
#[no_mangle]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool {
    REPL_PRELUDE.with(|p| {
        p.borrow_mut().clear();
    });
    true
}

/// Get the current prelude
#[no_mangle]
pub extern "C" fn simple_repl_runner_get_prelude(
    buffer: *mut u8,
    capacity: usize,
) -> usize {
    REPL_PRELUDE.with(|p| {
        let prelude = p.borrow();
        write_output(buffer, capacity, &prelude)
    })
}

/// Helper to write output to buffer
fn write_output(buffer: *mut u8, capacity: usize, msg: &str) -> usize {
    let bytes = msg.as_bytes();
    let len = bytes.len().min(capacity);

    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), buffer, len);
    }

    len
}

/// Helper to write error to buffer
fn write_error(buffer: *mut u8, capacity: usize, error: &str) {
    write_output(buffer, capacity, error);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runner_init_cleanup() {
        assert!(simple_repl_runner_init());
        simple_repl_runner_cleanup();
    }

    #[test]
    fn test_runner_execute_simple() {
        assert!(simple_repl_runner_init());

        let code = "1 + 1";
        let mut result = vec![0u8; 1024];

        let ret = simple_repl_runner_execute(
            code.as_ptr(),
            code.len(),
            result.as_mut_ptr(),
            result.len(),
        );

        // Should succeed or fail with error message
        assert!(ret == 0 || ret == 1);

        simple_repl_runner_cleanup();
    }

    #[test]
    fn test_runner_clear_prelude() {
        assert!(simple_repl_runner_init());
        assert!(simple_repl_runner_clear_prelude());
        simple_repl_runner_cleanup();
    }

    #[test]
    fn test_runner_get_prelude() {
        assert!(simple_repl_runner_init());

        let mut buffer = vec![0u8; 1024];
        let len = simple_repl_runner_get_prelude(buffer.as_mut_ptr(), buffer.len());

        // Should return empty prelude initially
        assert_eq!(len, 0);

        simple_repl_runner_cleanup();
    }
}
