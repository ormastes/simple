//! Process control extern functions
//!
//! Functions for controlling process execution (exit, etc.).

use crate::error::CompileError;
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

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Can't test exit() as it terminates the process
    // Testing is done via integration tests that spawn child processes
}
