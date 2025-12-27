//! Standard file I/O operations
//!
//! Provides native implementations for basic file operations:
//! - Open files with various modes (read, write, create, append)
//! - Read from file descriptors
//! - Write to file descriptors
//! - Close file descriptors
//! - Flush and sync file buffers
//! - Seek within files

use super::super::RuntimeValue;
use std::fs::File;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};

#[cfg(target_family = "unix")]
use std::os::unix::io::IntoRawFd;

// =============================================================================
// Standard File Operations
// =============================================================================

/// Open file and return file descriptor
///
/// # Arguments
/// * `path` - File path as RuntimeValue string
/// * `mode` - Open mode (0=read, 1=write, 2=create, 3=append)
///
/// # Returns
/// File descriptor as i64
#[no_mangle]
pub extern "C" fn native_fs_open(path: RuntimeValue, mode: i64) -> RuntimeValue {
    // Extract path string from RuntimeValue
    // TODO: Implement proper string extraction from RuntimeValue
    let path_str = "/tmp/test.txt";

    let file_result = match mode {
        0 => {
            // Read
            std::fs::File::open(path_str)
        }
        1 => {
            // Write
            std::fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(path_str)
        }
        2 => {
            // Create
            std::fs::File::create(path_str)
        }
        3 => {
            // Append
            std::fs::OpenOptions::new()
                .write(true)
                .append(true)
                .open(path_str)
        }
        _ => return RuntimeValue::NIL,
    };

    match file_result {
        Ok(file) => {
            #[cfg(target_family = "unix")]
            {
                let fd = file.into_raw_fd();
                RuntimeValue::from_int(fd as i64)
            }

            #[cfg(not(target_family = "unix"))]
            {
                RuntimeValue::NIL
            }
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Read from file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
/// * `buf` - Buffer to read into
///
/// # Returns
/// Number of bytes read
#[no_mangle]
pub extern "C" fn native_file_read(handle: i64, buf: RuntimeValue) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use std::io::Read;

        unsafe {
            let fd = handle as RawFd;
            let mut file = File::from_raw_fd(fd);

            // Get buffer - placeholder
            let mut buffer = vec![0u8; 4096];
            match file.read(&mut buffer) {
                Ok(n) => {
                    // Don't drop file (would close fd)
                    std::mem::forget(file);
                    RuntimeValue::from_int(n as i64)
                }
                Err(_) => {
                    std::mem::forget(file);
                    RuntimeValue::NIL
                }
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Write to file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
/// * `data` - Data to write
///
/// # Returns
/// Number of bytes written
#[no_mangle]
pub extern "C" fn native_file_write(handle: i64, data: RuntimeValue) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use std::io::Write;

        unsafe {
            let fd = handle as RawFd;
            let mut file = File::from_raw_fd(fd);

            // Get data - placeholder
            let buffer = b"test data";
            match file.write(buffer) {
                Ok(n) => {
                    std::mem::forget(file);
                    RuntimeValue::from_int(n as i64)
                }
                Err(_) => {
                    std::mem::forget(file);
                    RuntimeValue::NIL
                }
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Close file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_close(handle: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::close;

        unsafe {
            let fd = handle as RawFd;
            let result = close(fd);

            if result == 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::NIL
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Flush file buffers
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_flush(handle: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::fsync;

        unsafe {
            let fd = handle as RawFd;
            let result = fsync(fd);

            if result == 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::NIL
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Seek within file
///
/// # Arguments
/// * `handle` - File descriptor
/// * `offset` - Offset to seek to
/// * `whence` - Seek mode (0=start, 1=current, 2=end)
///
/// # Returns
/// New file position
#[no_mangle]
pub extern "C" fn native_file_seek(handle: i64, offset: i64, whence: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{lseek, SEEK_CUR, SEEK_END, SEEK_SET};

        unsafe {
            let fd = handle as RawFd;
            let whence_val = match whence {
                0 => SEEK_SET,
                1 => SEEK_CUR,
                2 => SEEK_END,
                _ => return RuntimeValue::NIL,
            };

            let result = lseek(fd, offset, whence_val);

            if result < 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::from_int(result as i64)
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Sync file to disk
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_sync(handle: i64) -> RuntimeValue {
    // Same as flush for now
    native_file_flush(handle)
}
