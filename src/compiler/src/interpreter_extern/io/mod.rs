//! I/O extern functions module
//!
//! Provides input/output operations for stdout, stderr, and stdin.
//!
//! ## Modules
//! - `print`: Functions for printing to stdout/stderr
//! - `input`: Functions for reading from stdin
//!
//! ## MCP Transport Operations
//! This module also provides low-level I/O operations for MCP stdio transport.

pub mod input;
pub mod print;

use crate::error::CompileError;
use crate::value::Value;

/// Write to stdout without newline (MCP transport)
///
/// Callable from Simple as: `stdout_write(s)`
///
/// # Effect
/// * Requires stdout write effect
pub fn stdout_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stdout_write")?;

    let s = args
        .first()
        .ok_or_else(|| CompileError::Semantic("stdout_write expects 1 argument".into()))?
        .to_display_string();

    unsafe {
        simple_runtime::value::rt_print_str(s.as_ptr(), s.len() as u64);
    }
    Ok(Value::Nil)
}

/// Flush stdout buffer (MCP transport)
///
/// Callable from Simple as: `stdout_flush()`
///
/// # Effect
/// * Requires stdout write effect
pub fn stdout_flush(_args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stdout_flush")?;

    use std::io::Write;
    if !simple_runtime::value::rt_is_stdout_capturing() {
        let _ = std::io::stdout().flush();
    }
    Ok(Value::Nil)
}

/// Write to stderr without newline (MCP transport)
///
/// Callable from Simple as: `stderr_write(s)`
///
/// # Effect
/// * Requires stderr write effect
pub fn stderr_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stderr_write")?;

    let s = args
        .first()
        .ok_or_else(|| CompileError::Semantic("stderr_write expects 1 argument".into()))?
        .to_display_string();

    unsafe {
        simple_runtime::value::rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
    Ok(Value::Nil)
}

/// Flush stderr buffer (MCP transport)
///
/// Callable from Simple as: `stderr_flush()`
///
/// # Effect
/// * Requires stderr write effect
pub fn stderr_flush(_args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stderr_flush")?;

    use std::io::Write;
    if !simple_runtime::value::rt_is_stderr_capturing() {
        let _ = std::io::stderr().flush();
    }
    Ok(Value::Nil)
}

// Re-export commonly used functions
pub use input::{input, stdin_read_char};
pub use print::{dprint, eprint, eprint_raw, eprintln, print, print_raw, println};
