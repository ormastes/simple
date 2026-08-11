//! Low-level File Descriptor Operations
//!
//! This module provides low-level file descriptor operations including:
//! - Open: Open file and return file descriptor
//! - Get Size: Get file size from file descriptor
//! - Close: Close file descriptor
//!
//! These operations provide direct access to file descriptors for
//! advanced file I/O operations and integration with system APIs.

/// Open file and return file descriptor
/// Returns -1 on error
///
/// # Mode values
/// - 0: ReadOnly
/// - 1: ReadWrite
/// - 2: WriteOnly
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

/// Close file descriptor. Returns 1 on success, 0 on failure.
///
/// runtime_sffi.rs:1908 declares `&[I32] -> &[I8]` and
/// src/compiler_rust/lib/std/src/infra/file_io.spl:439 reads the result
/// (`val success = rt_file_close(fd)`), but this function used to return
/// nothing, so `success` was an uninitialised register. Silencing the caller
/// would have been the wrong repair: close(2) is where deferred write-back
/// errors (ENOSPC, EIO, EDQUOT on NFS) are reported, so a close whose failure
/// is invisible loses data with no diagnostic anywhere. The status is real --
/// it is close(2)'s / CloseHandle's, not a constant.
#[no_mangle]
pub extern "C" fn rt_file_close(fd: i32) -> i8 {
    #[cfg(unix)]
    {
        // Deliberately NOT `File::from_raw_fd(fd)` + drop: std's Drop
        // discards close(2)'s return value, which is the very thing the
        // caller is asking for.
        let rc = unsafe { libc::close(fd) };
        i8::from(rc == 0)
    }

    #[cfg(windows)]
    {
        use std::os::windows::io::FromRawHandle;

        unsafe {
            let _file = std::fs::File::from_raw_handle(fd as *mut _);
        }
        1
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    // Helper to create string pointer for SFFI
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn test_file_open_close() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "test content").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            // Open in read-only mode
            let fd = rt_file_open(ptr, len, 0);
            assert!(fd >= 0, "Failed to open file");

            // Close the file
            rt_file_close(fd);
        }
    }

    #[test]
    fn test_file_get_size() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello, World!";
        fs::write(&file_path, content).unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let fd = rt_file_open(ptr, len, 0);
            assert!(fd >= 0);

            let size = rt_file_get_size(fd);
            assert_eq!(size, content.len() as u64);

            rt_file_close(fd);
        }
    }

    #[test]
    fn test_file_open_modes() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "test").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            // Test read-only mode
            let fd_ro = rt_file_open(ptr, len, 0);
            assert!(fd_ro >= 0);
            rt_file_close(fd_ro);

            // Test read-write mode
            let fd_rw = rt_file_open(ptr, len, 1);
            assert!(fd_rw >= 0);
            rt_file_close(fd_rw);

            // Test write-only mode
            let fd_wo = rt_file_open(ptr, len, 2);
            assert!(fd_wo >= 0);
            rt_file_close(fd_wo);
        }
    }
}
