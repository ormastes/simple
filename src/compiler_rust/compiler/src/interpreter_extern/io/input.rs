//! Input extern functions
//!
//! Functions for reading user input from stdin.

use crate::error::CompileError;
use crate::value::Value;

/// Read a line of input from stdin
///
/// Callable from Simple as: `input()` or `input(prompt)`
///
/// If a prompt is provided, it will be printed before reading input.
///
/// # Arguments
/// * `args` - Evaluated arguments [optional prompt]
///
/// # Returns
/// * String containing the user input (without trailing newline)
///
/// # Effect
/// * Requires stdin read effect
pub fn input(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("input")?;

    // Print prompt if provided
    if let Some(prompt) = args.first() {
        // Use runtime print to respect capture mode
        let prompt_str = prompt.to_display_string();
        unsafe {
            simple_runtime::value::rt_print_str(prompt_str.as_ptr(), prompt_str.len() as u64);
        }
        use std::io::Write;
        if !simple_runtime::value::rt_is_stdout_capturing() {
            let _ = std::io::stdout().flush();
        }
    }

    use std::io::{self, BufRead};
    let stdin = io::stdin();
    let line = stdin
        .lock()
        .lines()
        .next()
        .transpose()
        .map_err(|e| crate::error::factory::input_error(&e))?
        .unwrap_or_default();
    Ok(Value::Str(line))
}

/// Read a single character from stdin
///
/// Callable from Simple as: `stdin_read_char()`
///
/// Used for low-level I/O operations (e.g., MCP stdio transport).
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * String containing single character, or empty string on EOF/error
///
/// # Effect
/// * Requires stdin read effect
pub fn stdin_read_char(_args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("stdin_read_char")?;

    use std::io::Read;
    let mut buf = [0u8; 1];
    match std::io::stdin().read(&mut buf) {
        Ok(0) => Ok(Value::Str(String::new())), // EOF
        Ok(_) => Ok(Value::Str(String::from_utf8_lossy(&buf).to_string())),
        Err(_) => Ok(Value::Str(String::new())), // Error treated as EOF
    }
}

/// Read exactly n bytes from stdin, returning a UTF-8 string
///
/// Callable from Simple as: `rt_stdin_read_n(n)`
///
/// Reads a byte buffer of size n, then decodes as UTF-8 (lossy).
/// This is the correct way to read Content-Length framed MCP messages,
/// since Content-Length specifies byte count, not character count.
///
/// # Arguments
/// * `args` - Evaluated arguments [n: i64 byte count]
///
/// # Returns
/// * String containing the decoded text, or empty string on EOF/error
///
/// # Effect
/// * Requires stdin read effect
pub fn rt_stdin_read_n(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("rt_stdin_read_n")?;

    let n = match args.first() {
        Some(Value::Int(i)) => *i as usize,
        _ => return Ok(Value::Str(String::new())),
    };

    if n == 0 {
        return Ok(Value::Str(String::new()));
    }

    use std::io::Read;
    let mut buf = vec![0u8; n];
    let mut total_read = 0;
    while total_read < n {
        match std::io::stdin().read(&mut buf[total_read..]) {
            Ok(0) => break,  // EOF
            Ok(bytes_read) => total_read += bytes_read,
            Err(_) => break,
        }
    }
    buf.truncate(total_read);
    Ok(Value::Str(String::from_utf8_lossy(&buf).to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: These functions require stdin interaction, so testing is limited
    // Integration tests should spawn child processes with stdin pipes
}
