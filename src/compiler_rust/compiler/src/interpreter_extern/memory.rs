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

// ============================================================================
// System Allocator Functions
// ============================================================================

/// Allocate memory with specified size and alignment
///
/// Callable from Simple as: `sys_malloc(size, align)`
///
/// # Arguments
/// * `args` - [size: usize, align: usize]
///
/// # Returns
/// * Byte array representing allocated memory pointer
pub fn sys_malloc(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("sys_malloc requires 2 arguments (size, align)"));
    }

    let size = args[0].as_int()? as usize;
    let align = args[1].as_int()? as usize;

    // Allocate memory using Rust's allocator
    let layout = std::alloc::Layout::from_size_align(size, align)
        .map_err(|_| CompileError::runtime("sys_malloc: invalid size or alignment"))?;

    unsafe {
        let ptr = std::alloc::alloc(layout);
        if ptr.is_null() {
            return Err(CompileError::runtime("sys_malloc: allocation failed"));
        }

        // Return pointer as a single-element byte array containing the pointer address
        // We use a trick: encode the pointer as an Int value
        Ok(Value::Int(ptr as i64))
    }
}

/// Free memory allocated by sys_malloc
///
/// Callable from Simple as: `sys_free(ptr, size, align)`
///
/// # Arguments
/// * `args` - [ptr: [u8], size: usize, align: usize]
pub fn sys_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "sys_free requires 3 arguments (ptr, size, align)",
        ));
    }

    let ptr_val = args[0].as_int()?;
    let size = args[1].as_int()? as usize;
    let align = args[2].as_int()? as usize;

    if ptr_val == 0 {
        // Null pointer - nothing to free
        return Ok(Value::Nil);
    }

    // Deallocate memory
    let layout = std::alloc::Layout::from_size_align(size, align)
        .map_err(|_| CompileError::runtime("sys_free: invalid size or alignment"))?;

    unsafe {
        let ptr = ptr_val as *mut u8;
        std::alloc::dealloc(ptr, layout);
    }

    Ok(Value::Nil)
}

/// Reallocate memory
///
/// Callable from Simple as: `sys_realloc(ptr, old_size, new_size, align)`
///
/// # Arguments
/// * `args` - [ptr: [u8], old_size: usize, new_size: usize, align: usize]
///
/// # Returns
/// * New pointer as byte array
pub fn sys_realloc(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime(
            "sys_realloc requires 4 arguments (ptr, old_size, new_size, align)",
        ));
    }

    let ptr_val = args[0].as_int()?;
    let old_size = args[1].as_int()? as usize;
    let new_size = args[2].as_int()? as usize;
    let align = args[3].as_int()? as usize;

    let old_layout = std::alloc::Layout::from_size_align(old_size, align)
        .map_err(|_| CompileError::runtime("sys_realloc: invalid old size or alignment"))?;

    unsafe {
        let old_ptr = ptr_val as *mut u8;
        let new_ptr = std::alloc::realloc(old_ptr, old_layout, new_size);

        if new_ptr.is_null() {
            return Err(CompileError::runtime("sys_realloc: reallocation failed"));
        }

        Ok(Value::Int(new_ptr as i64))
    }
}
