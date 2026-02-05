//! Interpreter bridge FFI for hybrid execution.
//!
//! Provides function pointers that allow the runtime to call back into the interpreter
//! without circular dependencies. The compiler crate sets these handlers during initialization.
//!
//! ## Usage Pattern
//!
//! 1. Compiler crate calls `set_interp_call_handler` and `set_interp_eval_handler` during init
//! 2. Compiled code calls `rt_interp_call` or `rt_interp_eval` to invoke interpreter
//! 3. Runtime dispatches through the registered handler
//! 4. If no handler is set, returns NIL (no interpreter available)
//!
//! ## Thread Safety
//!
//! Handler pointers are stored in `AtomicPtr` with `SeqCst` ordering for thread-safe access.

use crate::value::core::RuntimeValue;
use std::sync::atomic::{AtomicPtr, Ordering};

/// Type for rt_interp_call handler function.
///
/// Takes function name, argument count, and argument array, returns RuntimeValue.
pub type InterpCallFn =
    unsafe extern "C" fn(name_ptr: *const u8, name_len: u64, argc: u64, argv: *const RuntimeValue) -> RuntimeValue;

/// Type for rt_interp_eval handler function.
///
/// Takes expression index, returns RuntimeValue.
pub type InterpEvalFn = extern "C" fn(expr_index: i64) -> RuntimeValue;

/// Default handler that returns NIL (no interpreter available).
unsafe extern "C" fn default_interp_call(
    _name_ptr: *const u8,
    _name_len: u64,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    RuntimeValue::NIL
}

/// Default handler that returns NIL (no interpreter available).
extern "C" fn default_interp_eval(_expr_index: i64) -> RuntimeValue {
    RuntimeValue::NIL
}

/// Global function pointer for rt_interp_call.
/// Set by compiler crate via `set_interp_call_handler`.
static INTERP_CALL_HANDLER: AtomicPtr<()> = AtomicPtr::new(default_interp_call as *const () as *mut ());

/// Global function pointer for rt_interp_eval.
/// Set by compiler crate via `set_interp_eval_handler`.
static INTERP_EVAL_HANDLER: AtomicPtr<()> = AtomicPtr::new(default_interp_eval as *const () as *mut ());

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_handlers_return_nil() {
        // Default handlers should return NIL
        unsafe {
            let result = rt_interp_call(std::ptr::null(), 0, 0, std::ptr::null());
            assert!(result.is_nil());
        }

        let result = rt_interp_eval(42);
        assert!(result.is_nil());
    }

    #[test]
    fn test_set_interp_call_handler() {
        unsafe extern "C" fn test_handler(
            _name_ptr: *const u8,
            _name_len: u64,
            _argc: u64,
            _argv: *const RuntimeValue,
        ) -> RuntimeValue {
            RuntimeValue::from_int(12345)
        }

        unsafe {
            set_interp_call_handler(test_handler);
            let result = rt_interp_call(std::ptr::null(), 0, 0, std::ptr::null());
            assert_eq!(result.as_int(), 12345);

            // Restore default
            set_interp_call_handler(default_interp_call);
        }
    }

    #[test]
    fn test_set_interp_eval_handler() {
        extern "C" fn test_handler(expr_index: i64) -> RuntimeValue {
            RuntimeValue::from_int(expr_index * 2)
        }

        unsafe {
            set_interp_eval_handler(test_handler);
        }

        let result = rt_interp_eval(21);
        assert_eq!(result.as_int(), 42);

        // Restore default
        unsafe {
            set_interp_eval_handler(default_interp_eval);
        }
    }

    #[test]
    fn test_interp_call_with_function_name() {
        unsafe extern "C" fn name_echo_handler(
            name_ptr: *const u8,
            name_len: u64,
            _argc: u64,
            _argv: *const RuntimeValue,
        ) -> RuntimeValue {
            if name_ptr.is_null() || name_len == 0 {
                return RuntimeValue::from_int(0);
            }
            // Return the length of the function name as proof we got it
            RuntimeValue::from_int(name_len as i64)
        }

        unsafe {
            set_interp_call_handler(name_echo_handler);

            let name = b"my_function";
            let result = rt_interp_call(name.as_ptr(), name.len() as u64, 0, std::ptr::null());
            assert_eq!(result.as_int(), 11); // Length of "my_function"

            // Restore default
            set_interp_call_handler(default_interp_call);
        }
    }

    #[test]
    fn test_interp_call_with_args() {
        unsafe extern "C" fn arg_sum_handler(
            _name_ptr: *const u8,
            _name_len: u64,
            argc: u64,
            argv: *const RuntimeValue,
        ) -> RuntimeValue {
            if argv.is_null() || argc == 0 {
                return RuntimeValue::from_int(0);
            }

            let mut sum = 0i64;
            for i in 0..argc {
                let arg = *argv.offset(i as isize);
                if arg.is_int() {
                    sum += arg.as_int();
                }
            }
            RuntimeValue::from_int(sum)
        }

        unsafe {
            set_interp_call_handler(arg_sum_handler);

            let args = [
                RuntimeValue::from_int(10),
                RuntimeValue::from_int(20),
                RuntimeValue::from_int(30),
            ];
            let result = rt_interp_call(std::ptr::null(), 0, 3, args.as_ptr());
            assert_eq!(result.as_int(), 60);

            // Restore default
            set_interp_call_handler(default_interp_call);
        }
    }
}
