//! Error construction utilities for extern functions
//!
//! This module provides standardized error constructors to maintain
//! consistent error messages across extern function implementations.

use crate::error::CompileError;

/// Create a semantic error with a formatted message
#[inline]
pub fn semantic_error(msg: impl Into<String>) -> CompileError {
    CompileError::Semantic(msg.into())
}

/// Create an error for unknown extern function
#[inline]
pub fn unknown_function(name: &str) -> CompileError {
    CompileError::Semantic(format!("unknown extern function: {}", name))
}

/// Create an error for wrong argument count
#[inline]
pub fn wrong_arg_count(func_name: &str, expected: usize, got: usize) -> CompileError {
    CompileError::Semantic(format!("{} expects {} argument(s), got {}", func_name, expected, got))
}

/// Create an error for wrong argument type
#[inline]
pub fn wrong_arg_type(func_name: &str, position: usize, expected: &str) -> CompileError {
    CompileError::Semantic(format!(
        "{} expects {} argument at position {}",
        func_name, expected, position
    ))
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
