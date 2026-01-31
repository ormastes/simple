//! Path Manipulation Operations
//!
//! This module provides path manipulation utilities including:
//! - Basename: Get filename from path
//! - Dirname: Get directory from path
//! - Extension: Get file extension
//! - Stem: Get filename without extension
//! - Absolute: Convert to absolute path
//! - Relative: Compute relative path
//! - Separator: Get platform-specific path separator

use crate::value::collections::rt_string_new;
use crate::value::RuntimeValue;
use std::path::Path;

/// Helper function for path operations that return strings
/// Handles null checks, UTF-8 conversion, and result wrapping
unsafe fn path_string_helper<F>(path_ptr: *const u8, path_len: u64, operation: F) -> RuntimeValue
where
    F: FnOnce(&Path) -> &str,
{
    if path_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);
    let result = operation(&path);

    rt_string_new(result.as_ptr(), result.len() as u64)
}

/// Get basename (filename) from path
/// Returns the final component of the path
#[no_mangle]
pub unsafe extern "C" fn rt_path_basename(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    path_string_helper(path_ptr, path_len, |path| {
        path.file_name().and_then(|s| s.to_str()).unwrap_or("")
    })
}

/// Get dirname (directory) from path
/// Returns the directory component of the path
#[no_mangle]
pub unsafe extern "C" fn rt_path_dirname(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    path_string_helper(path_ptr, path_len, |path| {
        path.parent().and_then(|p| p.to_str()).unwrap_or("")
    })
}

/// Get file extension from path
/// Returns the extension without the leading dot
#[no_mangle]
pub unsafe extern "C" fn rt_path_ext(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    path_string_helper(path_ptr, path_len, |path| {
        path.extension().and_then(|s| s.to_str()).unwrap_or("")
    })
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

/// Get file stem (filename without extension)
/// For "file.txt" returns "file", for "archive.tar.gz" returns "archive.tar"
#[no_mangle]
pub unsafe extern "C" fn rt_path_stem(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    path_string_helper(path_ptr, path_len, |path| {
        path.file_stem().and_then(|s| s.to_str()).unwrap_or("")
    })
}

/// Compute relative path from base to target
/// For target="/a/b/c" and base="/a", returns "b/c"
#[no_mangle]
pub unsafe extern "C" fn rt_path_relative(
    path_ptr: *const u8,
    path_len: u64,
    base_ptr: *const u8,
    base_len: u64,
) -> RuntimeValue {
    if path_ptr.is_null() || base_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let base_bytes = std::slice::from_raw_parts(base_ptr, base_len as usize);
    let base_str = match std::str::from_utf8(base_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    let path = Path::new(path_str);
    let base = Path::new(base_str);

    // Try to strip the base prefix
    match path.strip_prefix(base) {
        Ok(relative) => {
            let rel_str = relative.to_string_lossy();
            let bytes = rel_str.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => {
            // Paths don't share a common prefix - return original path
            rt_string_new(path_str.as_ptr(), path_str.len() as u64)
        }
    }
}

/// Join two paths together
#[no_mangle]
pub unsafe extern "C" fn rt_path_join(
    path1_ptr: *const u8,
    path1_len: u64,
    path2_ptr: *const u8,
    path2_len: u64,
) -> RuntimeValue {
    if path1_ptr.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    let path1_bytes = std::slice::from_raw_parts(path1_ptr, path1_len as usize);
    let path1_str = match std::str::from_utf8(path1_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(b"".as_ptr(), 0),
    };

    if path2_ptr.is_null() || path2_len == 0 {
        return rt_string_new(path1_str.as_ptr(), path1_str.len() as u64);
    }

    let path2_bytes = std::slice::from_raw_parts(path2_ptr, path2_len as usize);
    let path2_str = match std::str::from_utf8(path2_bytes) {
        Ok(s) => s,
        Err(_) => return rt_string_new(path1_str.as_ptr(), path1_str.len() as u64),
    };

    let joined = Path::new(path1_str).join(path2_str);
    let joined_str = joined.to_string_lossy();
    let bytes = joined_str.as_bytes();
    rt_string_new(bytes.as_ptr(), bytes.len() as u64)
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

    #[test]
    fn test_path_stem() {
        unsafe {
            // Simple file
            let (ptr, len) = str_to_ptr("file.txt");
            let result = rt_path_stem(ptr, len);
            let stem = extract_string(result);
            assert_eq!(stem, "file");

            // File with multiple dots
            let (ptr2, len2) = str_to_ptr("archive.tar.gz");
            let result2 = rt_path_stem(ptr2, len2);
            let stem2 = extract_string(result2);
            assert_eq!(stem2, "archive.tar");

            // No extension
            let (ptr3, len3) = str_to_ptr("README");
            let result3 = rt_path_stem(ptr3, len3);
            let stem3 = extract_string(result3);
            assert_eq!(stem3, "README");

            // Hidden file
            let (ptr4, len4) = str_to_ptr(".gitignore");
            let result4 = rt_path_stem(ptr4, len4);
            let stem4 = extract_string(result4);
            assert_eq!(stem4, ".gitignore");

            // Full path
            let (ptr5, len5) = str_to_ptr("/path/to/file.txt");
            let result5 = rt_path_stem(ptr5, len5);
            let stem5 = extract_string(result5);
            assert_eq!(stem5, "file");
        }
    }

    #[test]
    fn test_path_relative() {
        unsafe {
            // Simple relative path
            let (path_ptr, path_len) = str_to_ptr("/a/b/c/file.txt");
            let (base_ptr, base_len) = str_to_ptr("/a/b");
            let result = rt_path_relative(path_ptr, path_len, base_ptr, base_len);
            let relative = extract_string(result);
            assert_eq!(relative, "c/file.txt");

            // Same path
            let (path_ptr2, path_len2) = str_to_ptr("/a/b");
            let (base_ptr2, base_len2) = str_to_ptr("/a/b");
            let result2 = rt_path_relative(path_ptr2, path_len2, base_ptr2, base_len2);
            let relative2 = extract_string(result2);
            assert_eq!(relative2, "");

            // No common prefix - returns original
            let (path_ptr3, path_len3) = str_to_ptr("/x/y/z");
            let (base_ptr3, base_len3) = str_to_ptr("/a/b");
            let result3 = rt_path_relative(path_ptr3, path_len3, base_ptr3, base_len3);
            let relative3 = extract_string(result3);
            assert_eq!(relative3, "/x/y/z");
        }
    }

    #[test]
    fn test_path_join() {
        unsafe {
            // Simple join
            let (p1_ptr, p1_len) = str_to_ptr("/home/user");
            let (p2_ptr, p2_len) = str_to_ptr("file.txt");
            let result = rt_path_join(p1_ptr, p1_len, p2_ptr, p2_len);
            let joined = extract_string(result);
            assert_eq!(joined, "/home/user/file.txt");

            // Join with nested path
            let (p3_ptr, p3_len) = str_to_ptr("/home");
            let (p4_ptr, p4_len) = str_to_ptr("user/docs");
            let result2 = rt_path_join(p3_ptr, p3_len, p4_ptr, p4_len);
            let joined2 = extract_string(result2);
            assert_eq!(joined2, "/home/user/docs");

            // Second path is absolute (replaces first)
            let (p5_ptr, p5_len) = str_to_ptr("/home/user");
            let (p6_ptr, p6_len) = str_to_ptr("/etc/config");
            let result3 = rt_path_join(p5_ptr, p5_len, p6_ptr, p6_len);
            let joined3 = extract_string(result3);
            assert_eq!(joined3, "/etc/config");
        }
    }
}
