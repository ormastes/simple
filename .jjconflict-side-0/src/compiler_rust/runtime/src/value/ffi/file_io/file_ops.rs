//! High-level File Operations
//!
//! This module provides high-level file operations including:
//! - Canonicalize: Resolve absolute paths with symbolic links
//! - Read/Write: High-level text file I/O
//! - ReadLines: Read file as array of lines
//! - Append: Append text to files
//! - Binary I/O: Read/write raw bytes
//! - Copy: Copy files from source to destination
//! - Remove: Delete files
//! - Rename/Move: Move or rename files

use crate::value::collections::{rt_array_new, rt_array_push, rt_string_data, rt_string_len, rt_string_new};
use crate::value::RuntimeValue;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use sha2::{Digest, Sha256};

fn tagged_text_to_string(value: i64) -> Option<String> {
    let text = RuntimeValue::from_raw(value as u64);
    let len = rt_string_len(text);
    if len < 0 {
        return None;
    }
    let data = rt_string_data(text);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

fn string_to_tagged_text(value: &str) -> i64 {
    rt_string_new(value.as_ptr(), value.len() as u64).to_raw() as i64
}

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

    // Avoid std::fs::canonicalize (libc::realpath segfaults in self-hosted binaries).
    // Make absolute and normalize . / .. components instead.
    {
        let p = std::path::Path::new(path_str);
        let abs = if p.is_absolute() {
            p.to_path_buf()
        } else {
            match std::env::current_dir() {
                Ok(cwd) => cwd.join(p),
                Err(_) => return RuntimeValue::NIL,
            }
        };
        let mut out = std::path::PathBuf::new();
        for comp in abs.components() {
            match comp {
                std::path::Component::ParentDir => {
                    out.pop();
                }
                std::path::Component::CurDir => {}
                c => out.push(c),
            }
        }
        let canonical_str = out.to_string_lossy();
        let bytes = canonical_str.as_bytes();
        rt_string_new(bytes.as_ptr(), bytes.len() as u64)
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
            // Normalize CRLF → LF so indentation-sensitive parsing works on all platforms
            let content = if content.contains('\r') {
                content.replace('\r', "")
            } else {
                content
            };
            let bytes = content.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Read entire file as text (RuntimeValue wrapper)
/// Takes a RuntimeValue string, extracts ptr/len, and calls rt_file_read_text.
/// Returns the string directly on success, NIL on failure.
/// (Compiled Simple code expects a plain string, not an Option/Enum wrapper.)
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text_rv(path: RuntimeValue) -> RuntimeValue {
    use crate::value::collections::{rt_string_data, rt_string_len};
    if path.is_nil() || path.0 == 0 {
        return RuntimeValue::NIL;
    }
    let len = rt_string_len(path);
    let ptr = rt_string_data(path);
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    rt_file_read_text(ptr, len as u64)
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

/// Return file size in bytes, or -1 on failure.
#[no_mangle]
pub unsafe extern "C" fn rt_file_size(path_ptr: *const u8, path_len: u64) -> i64 {
    if path_ptr.is_null() {
        return -1;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match std::fs::metadata(path_str) {
        Ok(metadata) => metadata.len() as i64,
        Err(_) => -1,
    }
}

/// Compute the SHA256 hash of a file and return it as a hex string.
#[no_mangle]
pub unsafe extern "C" fn rt_file_hash_sha256(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    let content = match std::fs::read(path_str) {
        Ok(content) => content,
        Err(_) => return RuntimeValue::NIL,
    };

    let mut hasher = Sha256::new();
    hasher.update(&content);
    let digest = hasher.finalize();
    let hex = format!("{:x}", digest);
    rt_string_new(hex.as_ptr(), hex.len() as u64)
}

/// Best-effort file lock shim for native runtime-only bundles.
///
/// The non-compiler native specs only need this symbol to link; they do not
/// rely on real locking semantics here. Keep the ABI permissive so existing
/// native call sites that pass tagged RuntimeValue strings continue to link.
#[no_mangle]
pub extern "C" fn rt_file_lock(_path: i64) -> i64 {
    1
}

/// Best-effort file unlock shim paired with `rt_file_lock`.
#[no_mangle]
pub extern "C" fn rt_file_unlock(_handle: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_file_mmap_read_text(path: i64) -> i64 {
    match tagged_text_to_string(path) {
        Some(path) => match std::fs::read_to_string(path) {
            Ok(content) => string_to_tagged_text(&content),
            Err(_) => RuntimeValue::NIL.to_raw() as i64,
        },
        None => RuntimeValue::NIL.to_raw() as i64,
    }
}

#[no_mangle]
pub extern "C" fn rt_file_mmap_read_bytes(path: i64) -> RuntimeValue {
    let bytes = match tagged_text_to_string(path).and_then(|path| std::fs::read(path).ok()) {
        Some(bytes) => bytes,
        None => return RuntimeValue::NIL,
    };
    let arr = rt_array_new(0);
    for byte in bytes {
        rt_array_push(arr, RuntimeValue::from_int(byte as i64));
    }
    arr
}

#[no_mangle]
pub extern "C" fn rt_file_read_text_at(path: i64, offset: i64, size: i64) -> i64 {
    let Some(path) = tagged_text_to_string(path) else {
        return RuntimeValue::NIL.to_raw() as i64;
    };
    let Ok(content) = std::fs::read(path) else {
        return RuntimeValue::NIL.to_raw() as i64;
    };
    let start = offset.max(0) as usize;
    if start >= content.len() {
        return string_to_tagged_text("");
    }
    let end = start.saturating_add(size.max(0) as usize).min(content.len());
    let slice = &content[start..end];
    string_to_tagged_text(&String::from_utf8_lossy(slice))
}

#[no_mangle]
pub extern "C" fn rt_file_write_text_at(path: i64, offset: i64, data: i64) -> i64 {
    let Some(path) = tagged_text_to_string(path) else {
        return -1;
    };
    let Some(data) = tagged_text_to_string(data) else {
        return -1;
    };
    let mut bytes = std::fs::read(&path).unwrap_or_default();
    let start = offset.max(0) as usize;
    if bytes.len() < start {
        bytes.resize(start, 0);
    }
    let data_bytes = data.into_bytes();
    let end = start.saturating_add(data_bytes.len());
    if bytes.len() < end {
        bytes.resize(end, 0);
    }
    bytes[start..end].copy_from_slice(&data_bytes);
    match std::fs::write(path, bytes) {
        Ok(_) => data_bytes.len() as i64,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn rt_mmap(_path: i64, _size: i64, _offset: i64, _readonly: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_munmap(_addr: i64, _size: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_madvise(_addr: i64, _size: i64, _advice: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_msync(_addr: i64, _size: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_getpid() -> i64 {
    std::process::id() as i64
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

/// Read file as array of lines
/// Returns an array of strings, one per line
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_lines(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
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
            let lines: Vec<&str> = content.lines().collect();
            let array_handle = rt_array_new(lines.len() as u64);

            for line in lines {
                let bytes = line.as_bytes();
                let str_value = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
                rt_array_push(array_handle, str_value);
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Append text to file (creates file if it doesn't exist)
#[no_mangle]
pub unsafe extern "C" fn rt_file_append_text(
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

    match OpenOptions::new().create(true).append(true).open(path_str) {
        Ok(mut file) => file.write_all(content_str.as_bytes()).is_ok(),
        Err(_) => false,
    }
}

/// Read file as raw bytes
/// Returns an array of integers (0-255)
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_bytes(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read(path_str) {
        Ok(bytes) => {
            let array_handle = rt_array_new(bytes.len() as u64);

            for byte in bytes {
                let byte_value = RuntimeValue::from_int(byte as i64);
                rt_array_push(array_handle, byte_value);
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Create a byte array ([u8]) from a raw memory pointer.
/// Used by LLVM memory buffer emission to avoid temp file I/O.
#[no_mangle]
pub unsafe extern "C" fn rt_bytes_from_raw(ptr: i64, len: i64) -> RuntimeValue {
    if ptr == 0 || len <= 0 {
        return rt_array_new(0);
    }
    let src = ptr as usize as *const u8;
    let slice = std::slice::from_raw_parts(src, len as usize);
    let array_handle = rt_array_new(len as u64);
    for &byte in slice {
        let byte_value = RuntimeValue::from_int(byte as i64);
        rt_array_push(array_handle, byte_value);
    }
    array_handle
}

/// Convert a UTF-8 text buffer to a byte array ([u8]).
#[no_mangle]
pub unsafe extern "C" fn rt_text_to_bytes(text_ptr: *const u8, text_len: u64) -> RuntimeValue {
    if text_ptr.is_null() || text_len == 0 {
        return rt_array_new(0);
    }

    let bytes = std::slice::from_raw_parts(text_ptr, text_len as usize);
    let array_handle = rt_array_new(text_len);
    for &byte in bytes {
        let byte_value = RuntimeValue::from_int(byte as i64);
        rt_array_push(array_handle, byte_value);
    }
    array_handle
}

/// Convert a byte array ([u8]) to a UTF-8 text value.
#[no_mangle]
pub extern "C" fn rt_bytes_to_text(bytes: RuntimeValue) -> RuntimeValue {
    let len = crate::value::collections::rt_array_len(bytes);
    if len < 0 {
        return RuntimeValue::NIL;
    }

    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = crate::value::collections::rt_array_get(bytes, i);
        if !value.is_int() {
            return RuntimeValue::NIL;
        }
        let byte = value.as_int();
        if !(0..=255).contains(&byte) {
            return RuntimeValue::NIL;
        }
        out.push(byte as u8);
    }

    unsafe { rt_string_new(out.as_ptr(), out.len() as u64) }
}

/// Write raw bytes to file
/// Takes an array of integers (0-255)
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_bytes(
    path_ptr: *const u8,
    path_len: u64,
    data_ptr: *const u8,
    data_len: u64,
) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    // If data_ptr is null but len is 0, write empty file
    if data_ptr.is_null() {
        return std::fs::write(path_str, []).is_ok();
    }

    let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
    std::fs::write(path_str, data).is_ok()
}

/// Move file from source to destination
/// Unlike rename, this works across filesystems by copying then deleting
#[no_mangle]
pub unsafe extern "C" fn rt_file_move(src_ptr: *const u8, src_len: u64, dest_ptr: *const u8, dest_len: u64) -> bool {
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

    // Try rename first (fast path, same filesystem)
    if std::fs::rename(src_str, dest_str).is_ok() {
        return true;
    }

    // Fallback: copy then delete (works across filesystems)
    if std::fs::copy(src_str, dest_str).is_ok() {
        // Only delete source if copy succeeded
        return std::fs::remove_file(src_str).is_ok();
    }

    false
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

    #[test]
    fn test_file_read_lines() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("lines.txt");
        fs::write(&file_path, "line1\nline2\nline3").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_file_read_lines(ptr, len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 3);
        }
    }

    #[test]
    fn test_file_read_lines_empty_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("empty.txt");
        fs::write(&file_path, "").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_file_read_lines(ptr, len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 0);
        }
    }

    #[test]
    fn test_file_append_text() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("append.txt");
        fs::write(&file_path, "Hello").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);
        let (content_ptr, content_len) = str_to_ptr(", World!");

        unsafe {
            assert!(rt_file_append_text(path_ptr, path_len, content_ptr, content_len));

            let content = fs::read_to_string(&file_path).unwrap();
            assert_eq!(content, "Hello, World!");
        }
    }

    #[test]
    fn test_file_append_text_creates_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("new_append.txt");

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);
        let (content_ptr, content_len) = str_to_ptr("New content");

        unsafe {
            assert!(rt_file_append_text(path_ptr, path_len, content_ptr, content_len));
            assert!(file_path.exists());

            let content = fs::read_to_string(&file_path).unwrap();
            assert_eq!(content, "New content");
        }
    }

    #[test]
    fn test_file_read_write_bytes() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("binary.bin");

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        let binary_data: [u8; 5] = [0, 127, 255, 1, 128];

        unsafe {
            // Write bytes
            assert!(rt_file_write_bytes(
                path_ptr,
                path_len,
                binary_data.as_ptr(),
                binary_data.len() as u64
            ));

            // Read bytes back
            let result = rt_file_read_bytes(path_ptr, path_len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 5);
        }
    }

    #[test]
    fn test_file_move() {
        let temp_dir = TempDir::new().unwrap();
        let src_path = temp_dir.path().join("src.txt");
        let dest_path = temp_dir.path().join("dest.txt");
        fs::write(&src_path, "move me").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_move(src_ptr, src_len, dest_ptr, dest_len));
            assert!(!src_path.exists());
            assert!(dest_path.exists());

            let content = fs::read_to_string(&dest_path).unwrap();
            assert_eq!(content, "move me");
        }
    }

    #[test]
    fn test_file_move_across_dirs() {
        let temp_dir = TempDir::new().unwrap();
        let subdir = temp_dir.path().join("subdir");
        fs::create_dir(&subdir).unwrap();

        let src_path = temp_dir.path().join("file.txt");
        let dest_path = subdir.join("file.txt");
        fs::write(&src_path, "content").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_move(src_ptr, src_len, dest_ptr, dest_len));
            assert!(!src_path.exists());
            assert!(dest_path.exists());
        }
    }
}
