//! FFI functions for doctest file I/O operations
//!
//! This module provides minimal file system operations needed by the doctest
//! discovery module until the full `std.io` library is implemented.

use super::core::RuntimeValue;
use std::fs;
use std::path::Path;

// ============================================================================
// Helper functions
// ============================================================================

/// Extract string from RuntimeValue (heap pointer to RuntimeString)
unsafe fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr() as *const super::collections::RuntimeString;
    if ptr.is_null() {
        return None;
    }

    // Get bytes from RuntimeString
    let s = &*ptr;
    let bytes = s.as_bytes();
    String::from_utf8(bytes.to_vec()).ok()
}

/// Create RuntimeString from Rust String
fn string_to_runtime_value(s: &str) -> RuntimeValue {
    super::collections::rt_string_new(s.as_ptr(), s.len() as u64)
}

// ============================================================================
// File reading functions
// ============================================================================

/// Read entire file as string (FFI-safe)
///
/// Returns RuntimeString on success, NIL on error
#[no_mangle]
pub extern "C" fn doctest_read_file(path_val: RuntimeValue) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::NIL;
        };

        match fs::read_to_string(&path) {
            Ok(content) => string_to_runtime_value(&content),
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Check if path exists (FFI-safe)
#[no_mangle]
pub extern "C" fn doctest_path_exists(path_val: RuntimeValue) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::from_bool(false);
        };

        let exists = Path::new(&path).exists();
        RuntimeValue::from_bool(exists)
    }
}

/// Check if path is a file (FFI-safe)
#[no_mangle]
pub extern "C" fn doctest_is_file(path_val: RuntimeValue) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::from_bool(false);
        };

        let is_file = Path::new(&path).is_file();
        RuntimeValue::from_bool(is_file)
    }
}

/// Check if path is a directory (FFI-safe)
#[no_mangle]
pub extern "C" fn doctest_is_dir(path_val: RuntimeValue) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::from_bool(false);
        };

        let is_dir = Path::new(&path).is_dir();
        RuntimeValue::from_bool(is_dir)
    }
}

// ============================================================================
// Directory walking functions
// ============================================================================

/// Walk directory tree recursively and collect files matching patterns
///
/// Arguments:
/// - root: Root directory to search
/// - include_patterns: Array of glob patterns to include (e.g., "*.spl")
/// - exclude_patterns: Array of glob patterns to exclude
///
/// Returns: Array of file paths as strings
#[no_mangle]
pub extern "C" fn doctest_walk_directory(
    root_val: RuntimeValue,
    _include_patterns_val: RuntimeValue,
    _exclude_patterns_val: RuntimeValue,
) -> RuntimeValue {
    unsafe {
        let Some(root) = runtime_value_to_string(root_val) else {
            return RuntimeValue::NIL;
        };

        // Simple implementation: just walk and collect all files
        // TODO: Implement glob pattern matching
        let mut files = Vec::new();

        if let Ok(entries) = walk_dir_recursive(&root) {
            files = entries;
        }

        // Convert Vec<String> to RuntimeArray
        let array_val = super::collections::rt_array_new(files.len() as u64);
        for file_path in files {
            let path_str_val = string_to_runtime_value(&file_path);
            super::collections::rt_array_push(array_val, path_str_val);
        }

        array_val
    }
}

/// Recursive directory walker helper
fn walk_dir_recursive(dir: &str) -> Result<Vec<String>, std::io::Error> {
    let mut files = Vec::new();
    let path = Path::new(dir);

    if !path.is_dir() {
        return Ok(files);
    }

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let entry_path = entry.path();

        if entry_path.is_dir() {
            // Recurse into subdirectory
            if let Some(path_str) = entry_path.to_str() {
                if let Ok(sub_files) = walk_dir_recursive(path_str) {
                    files.extend(sub_files);
                }
            }
        } else if entry_path.is_file() {
            // Add file to results
            if let Some(path_str) = entry_path.to_str() {
                files.push(path_str.to_string());
            }
        }
    }

    Ok(files)
}

// ============================================================================
// Path manipulation functions
// ============================================================================

/// Check if file path ends with given extension
#[no_mangle]
pub extern "C" fn doctest_path_has_extension(
    path_val: RuntimeValue,
    ext_val: RuntimeValue,
) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::from_bool(false);
        };

        let Some(ext) = runtime_value_to_string(ext_val) else {
            return RuntimeValue::from_bool(false);
        };

        let has_ext = path.ends_with(&ext);
        RuntimeValue::from_bool(has_ext)
    }
}

/// Check if path contains substring (for exclude pattern matching)
#[no_mangle]
pub extern "C" fn doctest_path_contains(
    path_val: RuntimeValue,
    pattern_val: RuntimeValue,
) -> RuntimeValue {
    unsafe {
        let Some(path) = runtime_value_to_string(path_val) else {
            return RuntimeValue::from_bool(false);
        };

        let Some(pattern) = runtime_value_to_string(pattern_val) else {
            return RuntimeValue::from_bool(false);
        };

        let contains = path.contains(&pattern);
        RuntimeValue::from_bool(contains)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_exists() {
        let path = string_to_runtime_value("Cargo.toml");
        let result = doctest_path_exists(path);
        assert!(result.as_bool());
    }

    #[test]
    fn test_path_not_exists() {
        let path = string_to_runtime_value("nonexistent_file.txt");
        let result = doctest_path_exists(path);
        assert!(!result.as_bool());
    }

    #[test]
    fn test_is_file() {
        let path = string_to_runtime_value("Cargo.toml");
        let result = doctest_is_file(path);
        assert!(result.as_bool());
    }

    #[test]
    fn test_is_dir() {
        let path = string_to_runtime_value("src");
        let result = doctest_is_dir(path);
        assert!(result.as_bool());
    }

    #[test]
    fn test_path_has_extension() {
        let path = string_to_runtime_value("test.spl");
        let ext = string_to_runtime_value(".spl");
        let result = doctest_path_has_extension(path, ext);
        assert!(result.as_bool());
    }

    #[test]
    fn test_path_contains() {
        let path = string_to_runtime_value("std_lib/src/collections.spl");
        let pattern = string_to_runtime_value("/src/");
        let result = doctest_path_contains(path, pattern);
        assert!(result.as_bool());
    }

    #[test]
    fn test_read_file() {
        let path = string_to_runtime_value("Cargo.toml");
        let result = doctest_read_file(path);
        assert!(!result.is_nil());
        assert!(result.is_heap());
    }
}
