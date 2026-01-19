//! High-level File Operations
//!
//! This module provides high-level file operations including:
//! - Canonicalize: Resolve absolute paths with symbolic links
//! - Read/Write: High-level text file I/O
//! - Copy: Copy files from source to destination
//! - Remove: Delete files
//! - Rename: Move or rename files

use crate::value::collections::rt_string_new;
use crate::value::RuntimeValue;
use std::path::Path;

/// Normalize/canonicalize a file path
/// Returns the absolute path with all symbolic links resolved
#[no_mangle]
pub unsafe extern "C" fn rt_file_canonicalize(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::canonicalize(path_str) {
        Ok(canonical) => {
            let canonical_str = canonical.to_string_lossy();
            let bytes = canonical_str.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => {
            // If canonicalize fails, try to make it absolute without resolving symlinks
            match std::env::current_dir() {
                Ok(cwd) => {
                    let absolute = cwd.join(path_str);
                    let absolute_str = absolute.to_string_lossy();
                    let bytes = absolute_str.as_bytes();
                    rt_string_new(bytes.as_ptr(), bytes.len() as u64)
                }
                Err(_) => RuntimeValue::NIL,
            }
        }
    }
}

/// Read entire file as text
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_to_string(path_str) {
        Ok(content) => {
            let bytes = content.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Write text to file
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_text(
    path_ptr: *const u8,
    path_len: u64,
    content_ptr: *const u8,
    content_len: u64,
) -> bool {
    if path_ptr.is_null() || content_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let content_bytes = std::slice::from_raw_parts(content_ptr, content_len as usize);
    let content_str = match std::str::from_utf8(content_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::write(path_str, content_str).is_ok()
}

/// Copy file from src to dest
#[no_mangle]
pub unsafe extern "C" fn rt_file_copy(src_ptr: *const u8, src_len: u64, dest_ptr: *const u8, dest_len: u64) -> bool {
    if src_ptr.is_null() || dest_ptr.is_null() {
        return false;
    }

    let src_bytes = std::slice::from_raw_parts(src_ptr, src_len as usize);
    let src_str = match std::str::from_utf8(src_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let dest_bytes = std::slice::from_raw_parts(dest_ptr, dest_len as usize);
    let dest_str = match std::str::from_utf8(dest_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::copy(src_str, dest_str).is_ok()
}

/// Remove/delete a file
#[no_mangle]
pub unsafe extern "C" fn rt_file_remove(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::remove_file(path_str).is_ok()
}

/// Rename/move a file or directory
#[no_mangle]
pub unsafe extern "C" fn rt_file_rename(from_ptr: *const u8, from_len: u64, to_ptr: *const u8, to_len: u64) -> bool {
    if from_ptr.is_null() || to_ptr.is_null() {
        return false;
    }

    let from_bytes = std::slice::from_raw_parts(from_ptr, from_len as usize);
    let from_str = match std::str::from_utf8(from_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let to_bytes = std::slice::from_raw_parts(to_ptr, to_len as usize);
    let to_str = match std::str::from_utf8(to_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::rename(from_str, to_str).is_ok()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};
    use std::fs;
    use tempfile::TempDir;

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
    fn test_file_read_write_text() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        unsafe {
            // Write text
            let content = "Hello, World!";
            let (content_ptr, content_len) = str_to_ptr(content);
            assert!(rt_file_write_text(path_ptr, path_len, content_ptr, content_len));

            // Read text
            let result = rt_file_read_text(path_ptr, path_len);
            let read_content = extract_string(result);
            assert_eq!(read_content, content);
        }
    }

    #[test]
    fn test_file_copy() {
        let temp_dir = TempDir::new().unwrap();
        let src_path = temp_dir.path().join("source.txt");
        let dest_path = temp_dir.path().join("dest.txt");

        fs::write(&src_path, "test content").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_copy(src_ptr, src_len, dest_ptr, dest_len));
            assert!(dest_path.exists());

            let content = fs::read_to_string(&dest_path).unwrap();
            assert_eq!(content, "test content");
        }
    }

    #[test]
    fn test_file_remove() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("to_remove.txt");
        fs::write(&file_path, "test").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_file_remove(ptr, len));
            assert!(!file_path.exists());
        }
    }

    #[test]
    fn test_file_rename() {
        let temp_dir = TempDir::new().unwrap();
        let from_path = temp_dir.path().join("old.txt");
        let to_path = temp_dir.path().join("new.txt");

        fs::write(&from_path, "content").unwrap();

        let from_str = from_path.to_str().unwrap();
        let to_str = to_path.to_str().unwrap();

        unsafe {
            let (from_ptr, from_len) = str_to_ptr(from_str);
            let (to_ptr, to_len) = str_to_ptr(to_str);

            assert!(rt_file_rename(from_ptr, from_len, to_ptr, to_len));
            assert!(!from_path.exists());
            assert!(to_path.exists());
        }
    }
}
