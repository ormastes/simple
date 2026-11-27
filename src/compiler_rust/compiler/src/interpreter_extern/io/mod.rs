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

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

#[derive(Clone, Copy)]
enum StreamKind {
    Stdout,
    Stderr,
}

/// Write one `stdout_write`/`stderr_write` argument. A `[u8]` argument is
/// written as raw bytes; anything else keeps its display form. Previously a
/// byte array printed as `[110, 105, 10]` instead of `ni\n`.
fn write_text_or_bytes(value: &Value, stream: StreamKind) {
    let is_array = matches!(
        value,
        Value::Array(_) | Value::FrozenArray(_) | Value::FixedSizeArray { .. }
    ) || value.byte_array_view().is_some();
    let bytes = if is_array { value.try_array_bytes() } else { None };
    let Some(bytes) = bytes else {
        let s = value.to_display_string();
        unsafe {
            match stream {
                StreamKind::Stdout => simple_runtime::value::rt_print_str(s.as_ptr(), s.len() as u64),
                StreamKind::Stderr => simple_runtime::value::rt_eprint_str(s.as_ptr(), s.len() as u64),
            }
        }
        return;
    };
    let capturing = match stream {
        StreamKind::Stdout => simple_runtime::value::rt_is_stdout_capturing(),
        StreamKind::Stderr => simple_runtime::value::rt_is_stderr_capturing(),
    };
    if capturing {
        // Capture buffers hold text; non-UTF-8 bytes are replaced there only.
        let s = String::from_utf8_lossy(&bytes);
        unsafe {
            match stream {
                StreamKind::Stdout => simple_runtime::value::rt_print_str(s.as_ptr(), s.len() as u64),
                StreamKind::Stderr => simple_runtime::value::rt_eprint_str(s.as_ptr(), s.len() as u64),
            }
        }
        return;
    }
    use std::io::Write;
    let result = match stream {
        StreamKind::Stdout => {
            let mut out = std::io::stdout().lock();
            out.write_all(&bytes).and_then(|_| out.flush())
        }
        StreamKind::Stderr => {
            let mut err = std::io::stderr().lock();
            err.write_all(&bytes).and_then(|_| err.flush())
        }
    };
    if let Err(e) = result {
        if e.kind() == std::io::ErrorKind::BrokenPipe {
            std::process::exit(0);
        }
    }
}

/// Write to stdout without newline (MCP transport)
///
/// Callable from Simple as: `stdout_write(s)`
///
/// # Effect
/// * Requires stdout write effect
pub fn stdout_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stdout_write")?;

    let s = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("stdout_write expects exactly 1 argument");
        CompileError::semantic_with_context("stdout_write expects 1 argument".to_string(), ctx)
    })?;
    write_text_or_bytes(s, StreamKind::Stdout);
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

    let s = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("stderr_write expects exactly 1 argument");
        CompileError::semantic_with_context("stderr_write expects 1 argument".to_string(), ctx)
    })?;
    write_text_or_bytes(s, StreamKind::Stderr);
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

#[cfg(test)]
mod byte_write_tests {
    use super::*;
    use simple_runtime::value::{
        rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start, rt_capture_stdout_stop,
    };

    fn ints(bytes: &[u8]) -> Value {
        Value::array(bytes.iter().map(|b| Value::Int(*b as i64)).collect::<Vec<Value>>())
    }

    #[test]
    fn stderr_write_byte_array_writes_bytes_not_display_form() {
        rt_capture_stderr_start();
        let r = stderr_write(&[ints(b"ni\n")]);
        let out = rt_capture_stderr_stop();
        assert!(r.is_ok());
        assert_eq!(out, "ni\n");
    }

    #[test]
    fn stderr_write_packed_byte_array_writes_bytes() {
        rt_capture_stderr_start();
        let r = stderr_write(&[Value::byte_array(b"ok".to_vec())]);
        let out = rt_capture_stderr_stop();
        assert!(r.is_ok());
        assert_eq!(out, "ok");
    }

    #[test]
    fn stderr_write_text_unchanged() {
        rt_capture_stderr_start();
        let r = stderr_write(&[Value::text("hi")]);
        let out = rt_capture_stderr_stop();
        assert!(r.is_ok());
        assert_eq!(out, "hi");
    }

    #[test]
    fn stdout_write_byte_array_writes_bytes_not_display_form() {
        rt_capture_stdout_start();
        let r = stdout_write(&[ints(b"ab")]);
        let out = rt_capture_stdout_stop();
        assert!(r.is_ok());
        assert_eq!(out, "ab");
    }
}
