//! Memory management extern functions
//!
//! Functions for querying and configuring memory limits for runner threads.

use crate::error::CompileError;
use crate::value::Value;

/// Get current memory usage in bytes
///
/// Callable from Simple as: `memory_usage()`
///
/// # Returns
/// * Current memory usage in bytes as an integer
pub fn memory_usage(_args: &[Value]) -> Result<Value, CompileError> {
    // Get memory usage from the global memory tracker if available
    let usage = get_current_memory_usage();
    Ok(Value::Int(usage as i64))
}

/// Get memory limit in bytes (0 if unlimited)
///
/// Callable from Simple as: `memory_limit()`
///
/// # Returns
/// * Memory limit in bytes as an integer (0 = unlimited)
pub fn memory_limit(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    Ok(Value::Int(limit as i64))
}

/// Get memory usage as percentage of limit (0-100)
///
/// Callable from Simple as: `memory_usage_percent()`
///
/// # Returns
/// * Memory usage as percentage (0.0 if unlimited)
pub fn memory_usage_percent(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    if limit == 0 {
        return Ok(Value::Float(0.0));
    }
    let usage = get_current_memory_usage();
    let percent = (usage as f64 / limit as f64) * 100.0;
    Ok(Value::Float(percent))
}

/// Check if memory is limited
///
/// Callable from Simple as: `is_memory_limited()`
///
/// # Returns
/// * Bool indicating whether memory limit is enabled
pub fn is_memory_limited(_args: &[Value]) -> Result<Value, CompileError> {
    let limit = get_current_memory_limit();
    Ok(Value::Bool(limit > 0))
}

/// Get default memory limit constant (1 GB)
///
/// Callable from Simple as: `default_memory_limit()`
///
/// # Returns
/// * Default memory limit in bytes (1 GB)
pub fn default_memory_limit(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(simple_common::gc::DEFAULT_MEMORY_LIMIT as i64))
}

/// Format bytes as human-readable string
///
/// Callable from Simple as: `format_bytes(bytes)`
///
/// # Arguments
/// * `args` - [bytes: Int]
///
/// # Returns
/// * Formatted string (e.g., "1.5 GB", "256 MB", "1024 KB")
pub fn format_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let bytes = args
        .first()
        .ok_or_else(|| CompileError::runtime("format_bytes requires 1 argument (bytes)"))?
        .as_int()? as usize;

    let formatted = if bytes >= 1024 * 1024 * 1024 {
        format!("{:.2} GB", bytes as f64 / (1024.0 * 1024.0 * 1024.0))
    } else if bytes >= 1024 * 1024 {
        format!("{:.2} MB", bytes as f64 / (1024.0 * 1024.0))
    } else if bytes >= 1024 {
        format!("{:.2} KB", bytes as f64 / 1024.0)
    } else {
        format!("{} bytes", bytes)
    };

    Ok(Value::Str(formatted))
}

/// Parse a memory size string (e.g., "100M", "2G")
///
/// Callable from Simple as: `parse_memory_size(size_str)`
///
/// # Arguments
/// * `args` - [size_str: String]
///
/// # Returns
/// * Size in bytes as Int, or -1 if invalid
pub fn parse_memory_size(args: &[Value]) -> Result<Value, CompileError> {
    let size_str = args
        .first()
        .ok_or_else(|| CompileError::runtime("parse_memory_size requires 1 argument (size_str)"))?;

    let s = match size_str {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("parse_memory_size: argument must be a string")),
    };

    let result = parse_size_string(&s).unwrap_or(usize::MAX);
    if result == usize::MAX {
        Ok(Value::Int(-1))
    } else {
        Ok(Value::Int(result as i64))
    }
}

// Internal helper functions

fn get_current_memory_usage() -> usize {
    // Try to get from thread-local GC runtime if available
    // For now, return 0 as we don't have direct access to the allocator from here
    // In a full implementation, this would query the thread-local allocator
    0
}

fn get_current_memory_limit() -> usize {
    // Return the default memory limit
    // In a full implementation, this would query the thread-local allocator
    simple_common::gc::DEFAULT_MEMORY_LIMIT
}

fn parse_size_string(s: &str) -> Option<usize> {
    let s = s.trim().to_uppercase();

    if let Some(num) = s.strip_suffix("GB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix('G') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix("MB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix('M') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024 * 1024)
    } else if let Some(num) = s.strip_suffix("KB") {
        num.trim().parse::<usize>().ok().map(|n| n * 1024)
    } else if let Some(num) = s.strip_suffix('K') {
        num.trim().parse::<usize>().ok().map(|n| n * 1024)
    } else {
        s.parse::<usize>().ok()
    }
}
