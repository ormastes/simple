//! Error construction utilities for extern functions
//!
//! This module provides standardized error constructors to maintain
//! consistent error messages across extern function implementations.

use crate::error::{codes, CompileError, ErrorContext};

/// Create a semantic error with a formatted message
#[inline]
pub fn semantic_error(msg: impl Into<String>) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::INVALID_OPERATION)
        .with_help("check the operation arguments and types");
    CompileError::semantic_with_context(msg, ctx)
}

/// Create an error for unknown extern function
#[inline]
pub fn unknown_function(name: &str) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::UNDEFINED_FUNCTION)
        .with_help("check that the extern function name is spelled correctly");
    let msg = format!("unknown extern function: {}", name);
    CompileError::semantic_with_context(msg, ctx)
}

/// Create an error for wrong argument count
#[inline]
pub fn wrong_arg_count(func_name: &str, expected: usize, got: usize) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::ARGUMENT_COUNT_MISMATCH)
        .with_help(format!("function requires {} argument(s)", expected));
    let msg = format!("{} expects {} argument(s), got {}", func_name, expected, got);
    CompileError::semantic_with_context(msg, ctx)
}

/// Create an error for wrong argument type
#[inline]
pub fn wrong_arg_type(func_name: &str, position: usize, expected: &str) -> CompileError {
    let ctx = ErrorContext::new().with_code(codes::TYPE_MISMATCH).with_help(format!(
        "argument at position {} should be of type {}",
        position, expected
    ));
    let msg = format!("{} expects {} argument at position {}", func_name, expected, position);
    CompileError::semantic_with_context(msg, ctx)
}

/// Create an error for deprecated function
#[inline]
pub fn deprecated_function(old_name: &str, new_name: &str, reason: &str) -> CompileError {
    CompileError::runtime(format!(
        "'{}' is deprecated. Use '{}' instead. {}",
        old_name, new_name, reason
    ))
}

/// Create a runtime error
#[inline]
pub fn runtime_error(msg: impl Into<String>) -> CompileError {
    CompileError::runtime(msg.into())
}
