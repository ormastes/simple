//! Error Creation FFI
//!
//! Allows Simple code to create CompileError values for proper error reporting
//! during interpretation. Errors are stored as opaque handles and can be
//! "thrown" back to the Rust interpreter.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};

// ============================================================================
// Error Handle Registry
// ============================================================================

static NEXT_ERROR_HANDLE: AtomicI64 = AtomicI64::new(1);

fn next_handle() -> i64 {
    NEXT_ERROR_HANDLE.fetch_add(1, Ordering::Relaxed)
}

thread_local! {
    static ERROR_REGISTRY: RefCell<HashMap<i64, CompileError>> = RefCell::new(HashMap::new());
}

/// Register an error and return its handle
pub fn register_error(err: CompileError) -> i64 {
    let handle = next_handle();
    ERROR_REGISTRY.with(|r| {
        r.borrow_mut().insert(handle, err);
    });
    handle
}

/// Retrieve and remove an error by handle
pub fn take_error(handle: i64) -> Option<CompileError> {
    ERROR_REGISTRY.with(|r| r.borrow_mut().remove(&handle))
}

fn get_handle(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    args.get(index)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{} expects argument at index {}", name, index),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()
}

fn get_string_arg(args: &[Value], index: usize, name: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(CompileError::semantic_with_context(
            format!("{} expects string argument at index {}", name, index),
            ErrorContext::new().with_code(codes::TYPE_MISMATCH),
        )),
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Create a semantic error: (message: str) -> error_handle
pub fn rt_error_semantic(args: &[Value]) -> Result<Value, CompileError> {
    let message = get_string_arg(args, 0, "rt_error_semantic")?;
    let err = CompileError::semantic_with_context(
        message,
        ErrorContext::new().with_code(codes::INVALID_OPERATION),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Create a type mismatch error: (message: str) -> error_handle
pub fn rt_error_type_mismatch(args: &[Value]) -> Result<Value, CompileError> {
    let message = get_string_arg(args, 0, "rt_error_type_mismatch")?;
    let err = CompileError::semantic_with_context(
        message,
        ErrorContext::new().with_code(codes::TYPE_MISMATCH),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Create an undefined variable error: (name: str) -> error_handle
pub fn rt_error_undefined_var(args: &[Value]) -> Result<Value, CompileError> {
    let name = get_string_arg(args, 0, "rt_error_undefined_var")?;
    let err = CompileError::semantic_with_context(
        format!("undefined variable: {}", name),
        ErrorContext::new().with_code(codes::UNDEFINED_VARIABLE),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Create an argument count mismatch error: (expected: i64, got: i64) -> error_handle
pub fn rt_error_arg_count(args: &[Value]) -> Result<Value, CompileError> {
    let expected = get_handle(args, 0, "rt_error_arg_count")?;
    let got = get_handle(args, 1, "rt_error_arg_count")?;
    let err = CompileError::semantic_with_context(
        format!("expected {} arguments, got {}", expected, got),
        ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Create a division by zero error: () -> error_handle
pub fn rt_error_division_by_zero(_args: &[Value]) -> Result<Value, CompileError> {
    let err = CompileError::semantic_with_context(
        "division by zero".to_string(),
        ErrorContext::new().with_code(codes::INVALID_OPERATION),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Create an index out of bounds error: (index: i64, len: i64) -> error_handle
pub fn rt_error_index_oob(args: &[Value]) -> Result<Value, CompileError> {
    let index = get_handle(args, 0, "rt_error_index_oob")?;
    let len = get_handle(args, 1, "rt_error_index_oob")?;
    let err = CompileError::semantic_with_context(
        format!("index {} out of bounds (length {})", index, len),
        ErrorContext::new().with_code(codes::INDEX_OUT_OF_BOUNDS),
    );
    let handle = register_error(err);
    Ok(Value::Int(handle))
}

/// Throw an error (convert handle to actual CompileError return):
/// (error_handle) -> never returns Ok
pub fn rt_error_throw(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_error_throw")?;
    let err = take_error(handle).unwrap_or_else(|| {
        CompileError::semantic_with_context(
            format!("rt_error_throw: invalid error handle {}", handle),
            ErrorContext::new().with_code(codes::INVALID_OPERATION),
        )
    });
    Err(err)
}

/// Get error message as string: (error_handle) -> str
pub fn rt_error_message(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_error_message")?;
    ERROR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let err = reg.get(&handle).ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("rt_error_message: invalid error handle {}", handle),
                ErrorContext::new().with_code(codes::INVALID_OPERATION),
            )
        })?;
        Ok(Value::Str(format!("{}", err)))
    })
}

/// Free an error handle
pub fn rt_error_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_error_free")?;
    ERROR_REGISTRY.with(|r| {
        r.borrow_mut().remove(&handle);
    });
    Ok(Value::Nil)
}
