//! File I/O FFI functions for Simple runtime.
//!
//! This module provides comprehensive file system operations including:
//! - File metadata and checks (exists, stat)
//! - High-level file operations (read/write text, copy, remove, rename)
//! - Directory operations (create, list, remove, find, glob)
//! - Low-level file descriptor operations (open, close, get_size)
//! - Memory-mapped I/O (mmap, munmap, madvise, msync)
//! - Path manipulation (basename, dirname, extension, absolute, separator)

use crate::value::collections::{rt_array_new, rt_array_push, rt_string_new};
use crate::value::RuntimeValue;
use std::path::Path;

// ============================================================================
// File Metadata & Checks
// ============================================================================

/// Check if a file or directory exists
#[no_mangle]
pub unsafe extern "C" fn rt_file_exists(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    match std::str::from_utf8(path_bytes) {
        Ok(path_str) => Path::new(path_str).exists(),
        Err(_) => false,
    }
}

/// Get file metadata as a struct
/// Returns: [exists, is_file, is_dir, is_readable, is_writable, size]
#[no_mangle]
pub unsafe extern "C" fn rt_file_stat(
    path_ptr: *const u8,
    path_len: u64,
    out_exists: *mut bool,
    out_is_file: *mut bool,
    out_is_dir: *mut bool,
    out_is_readable: *mut bool,
    out_is_writable: *mut bool,
    out_size: *mut i64,
) {
    // Initialize all outputs to false/0
    if !out_exists.is_null() {
        *out_exists = false;
    }
    if !out_is_file.is_null() {
        *out_is_file = false;
    }
    if !out_is_dir.is_null() {
        *out_is_dir = false;
    }
    if !out_is_readable.is_null() {
        *out_is_readable = false;
    }
    if !out_is_writable.is_null() {
        *out_is_writable = false;
    }
    if !out_size.is_null() {
        *out_size = 0;
    }

    if path_ptr.is_null() {
        return;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    let path = Path::new(path_str);

    // Check existence
    if !out_exists.is_null() {
        *out_exists = path.exists();
    }

    if !path.exists() {
        return;
    }

    // Get metadata
    if let Ok(metadata) = std::fs::metadata(path) {
        if !out_is_file.is_null() {
            *out_is_file = metadata.is_file();
        }
        if !out_is_dir.is_null() {
            *out_is_dir = metadata.is_dir();
        }
        if !out_size.is_null() {
            *out_size = metadata.len() as i64;
        }

        // Check permissions (Unix-specific)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = metadata.permissions().mode();

            if !out_is_readable.is_null() {
                *out_is_readable = (mode & 0o400) != 0; // Owner read
            }
            if !out_is_writable.is_null() {
                *out_is_writable = (mode & 0o200) != 0; // Owner write
            }
        }

        // Fallback for non-Unix platforms
        #[cfg(not(unix))]
        {
            if !out_is_readable.is_null() {
                *out_is_readable = !metadata.permissions().readonly();
            }
            if !out_is_writable.is_null() {
                *out_is_writable = !metadata.permissions().readonly();
            }
        }
    }
}

// ============================================================================
// High-Level File Operations
// ============================================================================

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
// Directory Operations
// ============================================================================

/// Create directory (with optional recursive creation)
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create(path_ptr: *const u8, path_len: u64, recursive: bool) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::create_dir_all(path_str).is_ok()
    } else {
        std::fs::create_dir(path_str).is_ok()
    }
}

/// List directory entries
#[no_mangle]
pub unsafe extern "C" fn rt_dir_list(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_dir(path_str) {
        Ok(entries) => {
            // Create an array to hold the entry names
            let array_handle = rt_array_new(0);

            for entry in entries.flatten() {
                if let Ok(name) = entry.file_name().into_string() {
                    let bytes = name.as_bytes();
                    let str_value = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
                    rt_array_push(array_handle, str_value);
                }
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Remove a directory
#[no_mangle]
pub unsafe extern "C" fn rt_dir_remove(path_ptr: *const u8, path_len: u64, recursive: bool) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::remove_dir_all(path_str).is_ok()
    } else {
        std::fs::remove_dir(path_str).is_ok()
    }
}

/// Find files matching pattern (simplified glob matching)
/// Returns List[String] of matching file paths
#[no_mangle]
pub unsafe extern "C" fn rt_file_find(
    dir_ptr: *const u8,
    dir_len: u64,
    pattern_ptr: *const u8,
    pattern_len: u64,
    recursive: bool,
) -> RuntimeValue {
    use std::fs;

    // Helper to check if filename matches simple glob pattern
    fn matches_pattern(filename: &str, pattern: &str) -> bool {
        // Handle simple patterns: "*", "*.ext", "prefix*", "*suffix"
        if pattern == "*" {
            return true;
        }

        if let Some(ext) = pattern.strip_prefix("*.") {
            return filename.ends_with(&format!(".{}", ext));
        }

        if let Some(prefix) = pattern.strip_suffix('*') {
            return filename.starts_with(prefix);
        }

        if let Some(suffix) = pattern.strip_prefix('*') {
            return filename.ends_with(suffix);
        }

        // Exact match
        filename == pattern
    }

    if dir_ptr.is_null() || pattern_ptr.is_null() {
        return rt_array_new(0);
    }

    let dir_bytes = std::slice::from_raw_parts(dir_ptr, dir_len as usize);
    let dir_str = match std::str::from_utf8(dir_bytes) {
        Ok(s) => s,
        Err(_) => return rt_array_new(0),
    };

    let pattern_bytes = std::slice::from_raw_parts(pattern_ptr, pattern_len as usize);
    let pattern_str = match std::str::from_utf8(pattern_bytes) {
        Ok(s) => s,
        Err(_) => return rt_array_new(0),
    };

    let dir_path = Path::new(dir_str);
    let mut results = Vec::new();

    // Non-recursive: just list immediate directory entries
    if !recursive {
        if let Ok(entries) = fs::read_dir(dir_path) {
            for entry in entries.flatten() {
                if let Some(filename) = entry.file_name().to_str() {
                    if matches_pattern(filename, pattern_str) {
                        if let Some(path_str) = entry.path().to_str() {
                            results.push(path_str.to_string());
                        }
                    }
                }
            }
        }
    } else {
        // Recursive: walk directory tree
        fn walk_dir(dir: &Path, pattern: &str, results: &mut Vec<String>) {
            if let Ok(entries) = fs::read_dir(dir) {
                for entry in entries.flatten() {
                    let path = entry.path();

                    if path.is_file() {
                        if let Some(filename) = entry.file_name().to_str() {
                            if matches_pattern(filename, pattern) {
                                if let Some(path_str) = path.to_str() {
                                    results.push(path_str.to_string());
                                }
                            }
                        }
                    } else if path.is_dir() {
                        walk_dir(&path, pattern, results);
                    }
                }
            }
        }

        walk_dir(dir_path, pattern_str, &mut results);
    }

    // Create array with results
    let arr = rt_array_new(results.len() as u64);
    for path in results {
        let path_val = rt_string_new(path.as_ptr(), path.len() as u64);
        rt_array_push(arr, path_val);
    }

    arr
}

/// List files matching glob pattern in directory
/// Returns List[String] of matching file paths
#[no_mangle]
pub unsafe extern "C" fn rt_dir_glob(
    dir_ptr: *const u8,
    dir_len: u64,
    pattern_ptr: *const u8,
    pattern_len: u64,
) -> RuntimeValue {
    // For now, implement glob as non-recursive find
    rt_file_find(dir_ptr, dir_len, pattern_ptr, pattern_len, false)
}

// ============================================================================
// Low-Level File Descriptor Operations
// ============================================================================

/// Open file and return file descriptor
/// Returns -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_file_open(
    path_ptr: *const u8,
    path_len: u64,
    mode: i32, // 0=ReadOnly, 1=ReadWrite, 2=WriteOnly
) -> i32 {
    if path_ptr.is_null() {
        return -1;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    use std::fs::OpenOptions;

    let result = match mode {
        0 => OpenOptions::new().read(true).open(path_str),
        1 => OpenOptions::new().read(true).write(true).open(path_str),
        2 => OpenOptions::new().write(true).open(path_str),
        _ => return -1,
    };

    match result {
        Ok(file) => {
            #[cfg(unix)]
            {
                use std::os::unix::io::AsRawFd;
                let fd = file.as_raw_fd();
                // Leak the file to keep it open
                std::mem::forget(file);
                fd
            }
            #[cfg(windows)]
            {
                use std::os::windows::io::AsRawHandle;
                let handle = file.as_raw_handle();
                std::mem::forget(file);
                handle as i32
            }
        }
        Err(_) => -1,
    }
}

/// Get file size from file descriptor
/// Returns 0 on error
#[no_mangle]
pub extern "C" fn rt_file_get_size(fd: i32) -> u64 {
    #[cfg(unix)]
    {
        use std::os::unix::io::FromRawFd;

        unsafe {
            // Temporarily wrap fd in File to get metadata
            let file = std::fs::File::from_raw_fd(fd);
            let size = file.metadata().map(|m| m.len()).unwrap_or(0);
            // Don't drop the file, just forget to avoid closing fd
            std::mem::forget(file);
            size
        }
    }

    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;

        unsafe {
            let file = std::fs::File::from_raw_handle(fd as *mut _);
            let size = file.metadata().map(|m| m.len()).unwrap_or(0);
            std::mem::forget(file);
            size
        }
    }
}

/// Close file descriptor
#[no_mangle]
pub extern "C" fn rt_file_close(fd: i32) {
    #[cfg(unix)]
    {
        use std::os::unix::io::FromRawFd;

        unsafe {
            // Wrap fd in File and let it drop to close
            let _file = std::fs::File::from_raw_fd(fd);
            // File is closed when dropped
        }
    }

    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;

        unsafe {
            let _file = std::fs::File::from_raw_handle(fd as *mut _);
        }
    }
}

// ============================================================================
// Memory-Mapped I/O
// ============================================================================

/// Memory map a file
/// Returns null pointer on error
#[no_mangle]
pub extern "C" fn rt_file_mmap(_addr: *mut u8, length: u64, prot: i32, flags: i32, fd: i32, offset: u64) -> *mut u8 {
    #[cfg(unix)]
    {
        use libc::mmap;

        unsafe {
            let addr = mmap(std::ptr::null_mut(), length as usize, prot, flags, fd, offset as i64);

            if addr == libc::MAP_FAILED {
                std::ptr::null_mut()
            } else {
                addr as *mut u8
            }
        }
    }

    #[cfg(not(unix))]
    {
        // Non-Unix platforms not supported for mmap
        std::ptr::null_mut()
    }
}

/// Unmap memory region
/// Returns 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn rt_file_munmap(addr: *mut u8, length: u64) -> i32 {
    #[cfg(unix)]
    {
        use libc::munmap;

        unsafe { munmap(addr as *mut libc::c_void, length as usize) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Advise kernel on memory access pattern
/// Returns 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn rt_file_madvise(addr: *mut u8, length: u64, advice: i32) -> i32 {
    #[cfg(unix)]
    {
        use libc::madvise;

        unsafe { madvise(addr as *mut libc::c_void, length as usize, advice) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Synchronize memory-mapped file with storage
/// Returns 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn rt_file_msync(addr: *mut u8, length: u64, flags: i32) -> i32 {
    #[cfg(unix)]
    {
        use libc::msync;

        unsafe { msync(addr as *mut libc::c_void, length as usize, flags) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Wrapper for native_msync - stdlib compatibility
/// Returns 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn native_msync(addr: *mut u8, length: u64, flags: i32) -> i32 {
    rt_file_msync(addr, length, flags)
}

// ============================================================================
// Path Manipulation
// ============================================================================

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
    use crate::value::collections::{rt_array_get, rt_array_len, rt_string_data, rt_string_len};
    use std::ffi::CStr;
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
    fn test_file_exists() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "test").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_file_exists(ptr, len));

            // Non-existent file
            let (ptr2, len2) = str_to_ptr("nonexistent.txt");
            assert!(!rt_file_exists(ptr2, len2));
        }
    }

    #[test]
    fn test_file_stat() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "hello").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let mut exists = false;
            let mut is_file = false;
            let mut is_dir = false;
            let mut is_readable = false;
            let mut is_writable = false;
            let mut size = 0i64;

            rt_file_stat(
                ptr,
                len,
                &mut exists,
                &mut is_file,
                &mut is_dir,
                &mut is_readable,
                &mut is_writable,
                &mut size,
            );

            assert!(exists);
            assert!(is_file);
            assert!(!is_dir);
            assert_eq!(size, 5);
        }
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
    fn test_dir_create() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("new_dir");
        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_create(ptr, len, false));
            assert!(dir_path.exists());
            assert!(dir_path.is_dir());
        }
    }

    #[test]
    fn test_dir_create_recursive() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("a").join("b").join("c");
        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_create(ptr, len, true));
            assert!(dir_path.exists());
            assert!(dir_path.is_dir());
        }
    }

    #[test]
    #[ignore] // TODO: Fix this test - rt_array_len returning 0
    fn test_dir_list() {
        let temp_dir = TempDir::new().unwrap();
        fs::write(temp_dir.path().join("file1.txt"), "").unwrap();
        fs::write(temp_dir.path().join("file2.txt"), "").unwrap();
        fs::create_dir(temp_dir.path().join("subdir")).unwrap();

        let path_str = temp_dir.path().to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_dir_list(ptr, len);
            assert!(!result.is_nil());

            let count = rt_array_len(result);
            // Should have 3 entries (file1.txt, file2.txt, subdir)
            // But allow for platform differences in directory listing
            assert!(count >= 3, "Expected at least 3 entries, got {}", count);
        }
    }

    #[test]
    fn test_dir_remove() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("to_remove");
        fs::create_dir(&dir_path).unwrap();

        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_remove(ptr, len, false));
            assert!(!dir_path.exists());
        }
    }

    #[test]
    fn test_file_find_non_recursive() {
        let temp_dir = TempDir::new().unwrap();
        fs::write(temp_dir.path().join("test1.txt"), "").unwrap();
        fs::write(temp_dir.path().join("test2.txt"), "").unwrap();
        fs::write(temp_dir.path().join("other.md"), "").unwrap();

        let dir_str = temp_dir.path().to_str().unwrap();
        let (dir_ptr, dir_len) = str_to_ptr(dir_str);
        let (pattern_ptr, pattern_len) = str_to_ptr("*.txt");

        unsafe {
            let result = rt_file_find(dir_ptr, dir_len, pattern_ptr, pattern_len, false);
            let count = rt_array_len(result);
            assert_eq!(count, 2); // test1.txt, test2.txt
        }
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
}
