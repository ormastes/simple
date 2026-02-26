//! Process control extern functions
//!
//! Functions for controlling process execution (exit, panic, etc.).

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

/// Exit the process with a status code
///
/// Callable from Simple as: `exit(code)`
///
/// # Arguments
/// * `args` - Evaluated arguments [optional exit_code]
///
/// # Returns
/// * Never returns - terminates the process
pub fn exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = args.first().map(|v| v.as_int()).transpose()?.unwrap_or(0) as i32;
    std::process::exit(code);
}

/// Panic with a message - used for assertion failures and unrecoverable errors
///
/// Callable from Simple as: `panic(message)`
///
/// # Arguments
/// * `args` - Evaluated arguments [message: text]
///
/// # Returns
/// * Always returns Err with the panic message
pub fn panic(args: &[Value]) -> Result<Value, CompileError> {
    let msg = args
        .first()
        .map(|v| v.to_display_string())
        .unwrap_or_else(|| "panic".to_string());

    let ctx = ErrorContext::new()
        .with_code(codes::ASSERTION_FAILED)
        .with_help("this panic was triggered by application code");

    Err(CompileError::semantic_with_context(format!("panic: {}", msg), ctx))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Can't test exit() as it terminates the process
    // Testing is done via integration tests that spawn child processes
}
