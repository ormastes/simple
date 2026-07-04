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

// ---------------------------------------------------------------------------
// `rt_*` name adapters
//
// src/lib/nogc_sync_mut/tui/terminal.spl (and other low-level TUI code)
// declares `extern fn rt_stdin_read_byte`, `rt_terminal_enable_raw_mode`,
// `rt_terminal_disable_raw_mode`, `rt_terminal_get_size` directly — these
// match the SFFI symbol names in
// src/compiler_rust/runtime/src/value/sffi/env_process.rs, used when a
// program JIT/AOT-compiles. When compilation instead falls back to this
// tree-walking interpreter (e.g. an unrelated HIR lowering failure elsewhere
// in the program), extern calls are dispatched by exact name through
// init_dispatch_table() in interpreter_extern/mod.rs — which only had the
// `native_*` names above (a legacy/pre-`rt_`-prefix naming convention), not
// the `rt_terminal_*`/`rt_stdin_read_byte` names. So a program that JIT-fails
// for any reason and directly calls these `rt_` externs previously hit
// "unknown extern function". These adapters close that gap. See
// doc/08_tracking/bug/raw_mode_extern_registry_2026-07-03.md.
// ---------------------------------------------------------------------------

/// `rt_stdin_read_byte` — read one byte from stdin (no args). Returns the
/// byte value (0-255) or -1 at EOF/error.
pub fn rt_stdin_read_byte(_args: &[Value]) -> Result<Value, CompileError> {
    use std::io::Read;
    let mut byte = [0u8; 1];
    match std::io::stdin().read(&mut byte) {
        Ok(1) => Ok(Value::Int(byte[0] as i64)),
        _ => Ok(Value::Int(-1)),
    }
}

/// `rt_terminal_enable_raw_mode` — bridges to `native_enable_raw_mode` on
/// stdin (handle 0), converting its `i64` status code (0 = ok) to the `bool`
/// the `rt_` extern declares.
pub fn rt_terminal_enable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    let result = native_io::native_enable_raw_mode(&[Value::Int(0)])?;
    Ok(Value::Bool(matches!(result, Value::Int(0))))
}

/// `rt_terminal_disable_raw_mode` — bridges to `native_disable_raw_mode` on
/// stdin (handle 0).
pub fn rt_terminal_disable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    let result = native_io::native_disable_raw_mode(&[Value::Int(0)])?;
    Ok(Value::Bool(matches!(result, Value::Int(0))))
}

/// `rt_terminal_get_size` — bridges to `native_get_term_size` on stdout
/// (handle 1, matching `fill_terminal_size`'s `STDOUT_FILENO` in
/// env_process.rs). `native_get_term_size` returns `[rows, cols]`; the `rt_`
/// extern (and `terminal_get_size()` in terminal.spl) expects `(cols, rows)`.
pub fn rt_terminal_get_size(_args: &[Value]) -> Result<Value, CompileError> {
    match native_io::native_get_term_size(&[Value::Int(1)])? {
        Value::Array(items) if items.len() == 2 => Ok(Value::Tuple(vec![items[1].clone(), items[0].clone()])),
        _ => Ok(Value::Tuple(vec![Value::Int(80), Value::Int(24)])),
    }
}
