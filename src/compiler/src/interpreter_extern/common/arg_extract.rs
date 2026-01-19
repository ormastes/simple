//! Argument extraction utilities for extern functions
//!
//! This module provides helper functions to extract and validate arguments
//! from the evaluated argument vector, reducing boilerplate code.

use crate::error::CompileError;
use crate::value::Value;

/// Get a single argument by index
///
/// # Arguments
/// * `args` - The evaluated argument vector
/// * `index` - The argument index (0-based)
/// * `func_name` - The extern function name for error messages
///
/// # Returns
/// * `Ok(&Value)` if argument exists
/// * `Err(CompileError)` with descriptive message if missing
#[inline]
pub fn get_arg<'a>(args: &'a [Value], index: usize, func_name: &str) -> Result<&'a Value, CompileError> {
    args.get(index)
        .ok_or_else(|| crate::error::factory::func_expects_at_least(func_name, index + 1, args.len()))
}

/// Get an integer argument by index
///
/// # Arguments
/// * `args` - The evaluated argument vector
/// * `index` - The argument index (0-based)
/// * `func_name` - The extern function name for error messages
///
/// # Returns
/// * `Ok(i64)` if argument exists and is an integer
/// * `Err(CompileError)` if missing or wrong type
#[inline]
pub fn get_int(args: &[Value], index: usize, func_name: &str) -> Result<i64, CompileError> {
    get_arg(args, index, func_name)?.as_int()
}

/// Get a boolean argument by index
///
/// # Arguments
/// * `args` - The evaluated argument vector
/// * `index` - The argument index (0-based)
/// * `func_name` - The extern function name for error messages
///
/// # Returns
/// * `Ok(bool)` if argument exists and is a boolean
/// * `Err(CompileError)` if missing or wrong type
#[inline]
pub fn get_bool(args: &[Value], index: usize, func_name: &str) -> Result<bool, CompileError> {
    let val = get_arg(args, index, func_name)?;
    match val {
        Value::Bool(b) => Ok(*b),
        _ => Err(crate::error::factory::func_expects_type_at(func_name, "boolean", index)),
    }
}

/// Get a string argument by index
///
/// # Arguments
/// * `args` - The evaluated argument vector
/// * `index` - The argument index (0-based)
/// * `func_name` - The extern function name for error messages
///
/// # Returns
/// * `Ok(&String)` if argument exists and is a string
/// * `Err(CompileError)` if missing or wrong type
#[inline]
pub fn get_string<'a>(args: &'a [Value], index: usize, func_name: &str) -> Result<&'a String, CompileError> {
    let val = get_arg(args, index, func_name)?;
    match val {
        Value::Str(s) => Ok(s),
        _ => Err(crate::error::factory::func_expects_type_at(func_name, "string", index)),
    }
}

/// Get first argument (most common case)
#[inline]
pub fn get_first<'a>(args: &'a [Value], func_name: &str) -> Result<&'a Value, CompileError> {
    get_arg(args, 0, func_name)
}

/// Get first argument as integer
#[inline]
pub fn get_first_int(args: &[Value], func_name: &str) -> Result<i64, CompileError> {
    get_int(args, 0, func_name)
}

/// Get first argument as boolean
#[inline]
pub fn get_first_bool(args: &[Value], func_name: &str) -> Result<bool, CompileError> {
    get_bool(args, 0, func_name)
}

/// Get first argument as string
#[inline]
pub fn get_first_string<'a>(args: &'a [Value], func_name: &str) -> Result<&'a String, CompileError> {
    get_string(args, 0, func_name)
}

/// Validate exact argument count
///
/// # Arguments
/// * `args` - The evaluated argument vector
/// * `expected` - The expected number of arguments
/// * `func_name` - The extern function name for error messages
///
/// # Returns
/// * `Ok(())` if argument count matches
/// * `Err(CompileError)` if count doesn't match
#[inline]
pub fn require_args(args: &[Value], expected: usize, func_name: &str) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(crate::error::factory::func_expects_args(func_name, expected, args.len()));
    }
    Ok(())
}

/// Validate minimum argument count
#[inline]
pub fn require_at_least(args: &[Value], min: usize, func_name: &str) -> Result<(), CompileError> {
    if args.len() < min {
        return Err(crate::error::factory::func_expects_at_least(func_name, min, args.len()));
    }
    Ok(())
}
