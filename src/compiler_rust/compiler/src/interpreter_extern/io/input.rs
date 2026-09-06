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
    // `.lines().next()` yields `None` at EOF. Map that to `Value::Nil` rather
    // than `unwrap_or_default()`-ing it into `""` — a blank line and EOF must
    // stay distinguishable, matching the C runtime's `rt_stdin_read_line`
    // (src/runtime/runtime_native.c:2262, returns NULL at EOF) and the
    // `-> text?` extern contract declared at every `.spl` call site (e.g.
    // src/lib/nogc_sync_mut/io/pipe.spl:185). See
    // doc/08_tracking/bug/seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md.
    match stdin.lock().lines().next().transpose().map_err(|e| crate::error::factory::input_error(&e))? {
        Some(line) => Ok(Value::text(line)),
        None => Ok(Value::Nil),
    }
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
        Ok(0) => Ok(Value::text(String::new())), // EOF
        Ok(_) => Ok(Value::text(String::from_utf8_lossy(&buf).to_string())),
        Err(_) => Ok(Value::text(String::new())), // Error treated as EOF
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: These functions require stdin interaction, so testing is limited
    // Integration tests should spawn child processes with stdin pipes
}
