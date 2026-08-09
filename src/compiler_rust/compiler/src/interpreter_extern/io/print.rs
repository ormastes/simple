//! Print extern functions
//!
//! Functions for printing to stdout and stderr with capture support.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::{rt_is_stderr_capturing, rt_is_stdout_capturing};

// Helper functions for I/O that respect capture mode
fn print_to_stdout(s: &str) {
    unsafe {
        simple_runtime::value::rt_print_str(s.as_ptr(), s.len() as u64);
    }
}

fn print_to_stderr(s: &str) {
    unsafe {
        simple_runtime::value::rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
}

fn flush_stdout() {
    use std::io::Write;
    if !rt_is_stdout_capturing() {
        let _ = std::io::stdout().flush();
    }
}

fn flush_stderr() {
    use std::io::Write;
    if !rt_is_stderr_capturing() {
        let _ = std::io::stderr().flush();
    }
}

/// Print values to stdout with newline
///
/// Callable from Simple as: `print(values...)`
///
/// Prints space-separated values followed by a newline (Python-style).
///
/// # Arguments
/// * `args` - Evaluated arguments (values to print)
///
/// # Returns
/// * Nil
///
/// # Effect
/// * Requires stdout write effect
pub fn print(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("print")?;

    for (i, val) in args.iter().enumerate() {
        if i > 0 {
            print_to_stdout(" ");
        }
        print_to_stdout(&val.to_display_string());
    }
    print_to_stdout("\n");
    flush_stdout();
    Ok(Value::Nil)
}

/// Print values to stdout without newline
///
/// Callable from Simple as: `print_raw(values...)`
///
/// # Arguments
/// * `args` - Evaluated arguments (values to print)
///
/// # Returns
/// * Nil
///
/// # Effect
/// * Requires stdout write effect
pub fn print_raw(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("print_raw")?;

    for (i, val) in args.iter().enumerate() {
        if i > 0 {
            print_to_stdout(" ");
        }
        print_to_stdout(&val.to_display_string());
    }
    flush_stdout();
    Ok(Value::Nil)
}

/// Deprecated: Use `print` instead
///
/// This function has been deprecated because `print` now adds a newline
/// by default (like Python), making `println` redundant.
pub fn println(_args: &[Value]) -> Result<Value, CompileError> {
    Err(CompileError::runtime(
        "'println' is deprecated. Use 'print' instead (it now adds a newline by default, like Python). For no newline, use 'print_raw'."
    ))
}

/// Print values to stderr with newline
///
/// Callable from Simple as: `eprint(values...)`
///
/// # Arguments
/// * `args` - Evaluated arguments (values to print)
///
/// # Returns
/// * Nil
///
/// # Effect
/// * Requires stderr write effect
pub fn eprint(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("eprint")?;

    for (i, val) in args.iter().enumerate() {
        if i > 0 {
            print_to_stderr(" ");
        }
        print_to_stderr(&val.to_display_string());
    }
    print_to_stderr("\n");
    flush_stderr();
    Ok(Value::Nil)
}

/// Print values to stderr without newline
///
/// Callable from Simple as: `eprint_raw(values...)`
///
/// # Arguments
/// * `args` - Evaluated arguments (values to print)
///
/// # Returns
/// * Nil
///
/// # Effect
/// * Requires stderr write effect
pub fn eprint_raw(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("eprint_raw")?;

    for (i, val) in args.iter().enumerate() {
        if i > 0 {
            print_to_stderr(" ");
        }
        print_to_stderr(&val.to_display_string());
    }
    flush_stderr();
    Ok(Value::Nil)
}

/// Deprecated: Use `eprint` instead
///
/// This function has been deprecated because `eprint` now adds a newline
/// by default, making `eprintln` redundant.
pub fn eprintln(_args: &[Value]) -> Result<Value, CompileError> {
    Err(CompileError::runtime(
        "'eprintln' is deprecated. Use 'eprint' instead (it now adds a newline by default). For no newline, use 'eprint_raw'."
    ))
}

/// Debug print (only prints when debug mode is enabled)
///
/// Callable from Simple as: `dprint(values...)`
///
/// Prints with "[DEBUG]" prefix when debug mode is active.
///
/// # Arguments
/// * `args` - Evaluated arguments (values to print)
///
/// # Returns
/// * Nil
///
/// # Effect
/// * Requires stdout write effect (only when debug mode is enabled)
pub fn dprint(args: &[Value]) -> Result<Value, CompileError> {
    use super::super::is_debug_mode;

    if is_debug_mode() {
        use crate::effects::check_effect_violations;
        check_effect_violations("dprint")?;

        print_to_stdout("[DEBUG] ");
        for (i, val) in args.iter().enumerate() {
            if i > 0 {
                print_to_stdout(" ");
            }
            print_to_stdout(&val.to_display_string());
        }
        print_to_stdout("\n");
        flush_stdout();
    }
    Ok(Value::Nil)
}

/// Debug print - prints debug representation to stderr and returns the value
///
/// Callable from Simple as: `dbg(value)`
///
/// Prints `[file:line] expr = debug_repr` to stderr and returns the value unchanged.
/// This is useful for quick debugging without modifying control flow.
///
/// # Arguments
/// * `args` - Evaluated arguments (values to debug-print)
///
/// # Returns
/// * The last argument value (or Nil if no args), for pass-through usage
///
/// # Effect
/// * Requires stderr write effect
pub fn dbg(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("dbg")?;

    for val in args.iter() {
        let debug_str = val.to_debug_string();
        print_to_stderr(&format!("[dbg] {}\n", debug_str));
    }
    flush_stderr();

    // Return the last value (pass-through semantics like Rust's dbg!())
    Ok(args.last().cloned().unwrap_or(Value::Nil))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: These tests need effect checking disabled or proper test setup
    // They are included for completeness but may fail without proper context

    #[test]
    fn test_println_deprecated() {
        assert!(println(&[]).is_err());
    }

    #[test]
    fn test_eprintln_deprecated() {
        assert!(eprintln(&[]).is_err());
    }
}
