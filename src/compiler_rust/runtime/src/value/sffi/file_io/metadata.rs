//! File metadata and existence checks.
//!
//! Provides operations for checking file/directory existence and
//! retrieving comprehensive file metadata (type, permissions, size).

use std::path::Path;
use std::time::UNIX_EPOCH;

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

/// Check if a path exists and is a directory.
#[no_mangle]
pub unsafe extern "C" fn rt_dir_exists(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    match std::str::from_utf8(path_bytes) {
        Ok(path_str) => Path::new(path_str).is_dir(),
        Err(_) => false,
    }
}

/// Get file modification time in seconds since epoch.
#[no_mangle]
pub unsafe extern "C" fn rt_file_stat(path_ptr: *const u8, path_len: u64) -> i64 {
    if path_ptr.is_null() {
        return 0;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return 0,
    };

    std::fs::metadata(Path::new(path_str))
        .and_then(|metadata| metadata.modified())
        .ok()
        .and_then(|modified| modified.duration_since(UNIX_EPOCH).ok())
        .map(|duration| duration.as_secs() as i64)
        .unwrap_or(0)
}

/// Get file metadata as a struct.
/// Returns: [exists, is_file, is_dir, is_readable, is_writable, size].
pub unsafe extern "C" fn rt_file_metadata(
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_file_exists_null_path() {
        unsafe {
            assert!(!rt_file_exists(std::ptr::null(), 0));
        }
    }

    #[test]
    fn test_file_stat_null_path() {
        unsafe {
            assert_eq!(rt_file_stat(std::ptr::null(), 0), 0);
        }
    }

    #[test]
    fn test_file_stat_existing_path_returns_mtime() {
        let path = std::env::temp_dir().join("simple_runtime_file_stat_mtime_test");
        std::fs::write(&path, b"mtime").unwrap();
        let path_string = path.to_string_lossy();

        unsafe {
            let mtime = rt_file_stat(path_string.as_ptr(), path_string.len() as u64);
            assert!(mtime > 0);
        }

        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn test_file_metadata_null_path() {
        unsafe {
            let mut exists = true;
            rt_file_metadata(
                std::ptr::null(),
                0,
                &mut exists,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            );
            assert!(!exists);
        }
    }
}
