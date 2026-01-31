//! Terminal operations extern functions
//!
//! Native terminal I/O operations for Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_io).

use crate::error::CompileError;
use crate::value::Value;
use super::super::interpreter_native_io as native_io;

/// Get stdin handle
///
/// No effect check - returns handle constant
pub fn native_stdin(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stdin(args)
}

/// Get stdout handle
///
/// No effect check - returns handle constant
pub fn native_stdout(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stdout(args)
}

/// Get stderr handle
///
/// No effect check - returns handle constant
pub fn native_stderr(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_stderr(args)
}

/// Check if file descriptor is a TTY
///
/// No effect check - query operation
pub fn native_is_tty(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_is_tty(args)
}

/// Enable raw terminal mode
///
/// No effect check - configuration operation
pub fn native_enable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_enable_raw_mode(args)
}

/// Disable raw terminal mode
///
/// No effect check - configuration operation
pub fn native_disable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_disable_raw_mode(args)
}

/// Get terminal size (columns, rows)
///
/// No effect check - query operation
pub fn native_get_term_size(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_get_term_size(args)
}

/// Write to terminal
///
/// # Effect
/// * Requires terminal write effect
pub fn native_term_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_write")?;
    native_io::native_term_write(args)
}

/// Read from terminal
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_read(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_read")?;
    native_io::native_term_read(args)
}

/// Read from terminal with timeout
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_read_timeout")?;
    native_io::native_term_read_timeout(args)
}

/// Flush terminal output
///
/// # Effect
/// * Requires terminal write effect
pub fn native_term_flush(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_flush")?;
    native_io::native_term_flush(args)
}

/// Poll terminal for input availability
///
/// # Effect
/// * Requires terminal read effect
pub fn native_term_poll(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_term_poll")?;
    native_io::native_term_poll(args)
}
