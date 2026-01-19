//! Path Manipulation Operations
//!
//! This module provides path manipulation utilities including:
//! - Basename: Get filename from path
//! - Dirname: Get directory from path
//! - Extension: Get file extension
//! - Absolute: Convert to absolute path
//! - Separator: Get platform-specific path separator

use crate::value::collections::rt_string_new;
use crate::value::RuntimeValue;
use std::path::Path;

/// Get basename (filename) from path
/// Returns the final component of the path
#[no_mangle]
pub unsafe extern "C" fn rt_path_basename(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);
    let basename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");

    rt_string_new(basename.as_ptr(), basename.len() as u64)
}

/// Get dirname (directory) from path
/// Returns the directory component of the path
#[no_mangle]
pub unsafe extern "C" fn rt_path_dirname(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);
    let dirname = path.parent().and_then(|p| p.to_str()).unwrap_or("");

    rt_string_new(dirname.as_ptr(), dirname.len() as u64)
}

/// Get file extension from path
/// Returns the extension without the leading dot
#[no_mangle]
pub unsafe extern "C" fn rt_path_ext(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);
    let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");

    rt_string_new(ext.as_ptr(), ext.len() as u64)
}

/// Convert path to absolute path
/// Returns the canonicalized absolute path
#[no_mangle]
pub unsafe extern "C" fn rt_path_absolute(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);

    // Try to canonicalize (resolve symlinks and make absolute)
    // If that fails, try to make it absolute without resolving symlinks
    let absolute = if let Ok(canonical) = path.canonicalize() {
        canonical.to_str().unwrap_or(path_str).to_string()
    } else {
        // Fallback: join with current directory
        match std::env::current_dir() {
            Ok(cwd) => {
                let abs_path = if path.is_absolute() {
                    path.to_path_buf()
                } else {
                    cwd.join(path)
                };
                abs_path.to_str().unwrap_or(path_str).to_string()
            }
            Err(_) => path_str.to_string(),
        }
    };

    rt_string_new(absolute.as_ptr(), absolute.len() as u64)
}

/// Get platform-specific path separator
/// Returns "/" on Unix, "\\" on Windows
#[no_mangle]
pub extern "C" fn rt_path_separator() -> RuntimeValue {
    #[cfg(target_os = "windows")]
    const SEPARATOR: &[u8] = b"\\";
    #[cfg(not(target_os = "windows"))]
    const SEPARATOR: &[u8] = b"/";

    unsafe { rt_string_new(SEPARATOR.as_ptr(), SEPARATOR.len() as u64) }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};

    // Helper to create string pointer for FFI
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    // Helper to extract string from RuntimeValue
    unsafe fn extract_string(val: RuntimeValue) -> String {
        if val.is_nil() {
            return String::new();
        }
        let len = rt_string_len(val);
        let ptr = rt_string_data(val);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

    #[test]
    fn test_path_basename() {
        unsafe {
            let (ptr, len) = str_to_ptr("/path/to/file.txt");
            let result = rt_path_basename(ptr, len);
            let basename = extract_string(result);
            assert_eq!(basename, "file.txt");
        }
    }

    #[test]
    fn test_path_dirname() {
        unsafe {
            let (ptr, len) = str_to_ptr("/path/to/file.txt");
            let result = rt_path_dirname(ptr, len);
            let dirname = extract_string(result);
            assert_eq!(dirname, "/path/to");
        }
    }

    #[test]
    fn test_path_ext() {
        unsafe {
            let (ptr, len) = str_to_ptr("file.txt");
            let result = rt_path_ext(ptr, len);
            let ext = extract_string(result);
            assert_eq!(ext, "txt");

            // Test file with no extension
            let (ptr2, len2) = str_to_ptr("README");
            let result2 = rt_path_ext(ptr2, len2);
            let ext2 = extract_string(result2);
            assert_eq!(ext2, "");

            // Test file with multiple dots
            let (ptr3, len3) = str_to_ptr("archive.tar.gz");
            let result3 = rt_path_ext(ptr3, len3);
            let ext3 = extract_string(result3);
            assert_eq!(ext3, "gz");
        }
    }

    #[test]
    fn test_path_separator() {
        unsafe {
            let result = rt_path_separator();
            let sep = extract_string(result);
            #[cfg(target_os = "windows")]
            assert_eq!(sep, "\\");
            #[cfg(not(target_os = "windows"))]
            assert_eq!(sep, "/");
        }
    }

    #[test]
    fn test_path_basename_edge_cases() {
        unsafe {
            // Root path - file_name() returns None
            let (ptr, len) = str_to_ptr("/");
            let result = rt_path_basename(ptr, len);
            let basename = extract_string(result);
            assert_eq!(basename, "");

            // Current directory - file_name() returns None
            let (ptr2, len2) = str_to_ptr(".");
            let result2 = rt_path_basename(ptr2, len2);
            let basename2 = extract_string(result2);
            assert_eq!(basename2, "");

            // Parent directory - file_name() returns None
            let (ptr3, len3) = str_to_ptr("..");
            let result3 = rt_path_basename(ptr3, len3);
            let basename3 = extract_string(result3);
            assert_eq!(basename3, "");
        }
    }

    #[test]
    fn test_path_dirname_edge_cases() {
        unsafe {
            // Root path
            let (ptr, len) = str_to_ptr("/");
            let result = rt_path_dirname(ptr, len);
            let dirname = extract_string(result);
            assert_eq!(dirname, "");

            // Relative path with no directory
            let (ptr2, len2) = str_to_ptr("file.txt");
            let result2 = rt_path_dirname(ptr2, len2);
            let dirname2 = extract_string(result2);
            assert_eq!(dirname2, "");
        }
    }
}
