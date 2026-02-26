//! Effect checking utilities for extern functions
//!
//! This module consolidates effect checking logic to avoid duplication
//! across the extern function dispatcher. Instead of calling
//! `check_effect_violations` in each function arm, we can use a macro
//! to automatically add effect checking.

use crate::error::CompileError;
use crate::effects::check_effect_violations;

/// Check effect violations for a given function name
///
/// # Arguments
/// * `name` - The extern function name to check
///
/// # Returns
/// * `Ok(())` if no violations detected
/// * `Err(CompileError)` if effect violation detected
#[inline]
pub fn check_effect(name: &str) -> Result<(), CompileError> {
    check_effect_violations(name)
}

/// Macro to add effect checking to extern function implementations
///
/// # Usage
/// ```ignore
/// with_effect_check!("native_fs_read", {
///     // Function implementation
///     native_fs_read(&evaluated)
/// })
/// ```
#[macro_export]
macro_rules! with_effect_check {
    ($name:expr, $body:expr) => {{
        $crate::interpreter_extern::common::effect_check::check_effect($name)?;
        $body
    }};
}

/// Macro for functions that always require effect checking
///
/// This is a convenience macro for I/O operations that always check effects.
#[macro_export]
macro_rules! io_extern {
    ($name:expr, $body:expr) => {{
        with_effect_check!($name, $body)
    }};
}
