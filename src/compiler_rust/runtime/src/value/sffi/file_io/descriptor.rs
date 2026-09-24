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

/// Get file size from file descriptor.
/// Returns -1 on an invalid descriptor, metadata failure, or overflow.
#[no_mangle]
pub extern "C" fn rt_file_get_size(fd: i32) -> i64 {
    if fd < 0 {
        return -1;
    }
    #[cfg(unix)]
    {
        use std::os::unix::io::FromRawFd;

        unsafe {
            // Temporarily wrap fd in File to get metadata
            let file = std::fs::File::from_raw_fd(fd);
            let size = file
                .metadata()
                .ok()
                .and_then(|metadata| i64::try_from(metadata.len()).ok())
                .unwrap_or(-1);
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
            let size = file
                .metadata()
                .ok()
                .and_then(|metadata| i64::try_from(metadata.len()).ok())
                .unwrap_or(-1);
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
            assert_eq!(size, content.len() as i64);

            rt_file_close(fd);
        }

        let empty_path = temp_dir.path().join("empty.txt");
        fs::write(&empty_path, []).unwrap();
        let empty_path_str = empty_path.to_str().unwrap();
        let (empty_ptr, empty_len) = str_to_ptr(empty_path_str);
        unsafe {
            let empty_fd = rt_file_open(empty_ptr, empty_len, 0);
            assert!(empty_fd >= 0);
            assert_eq!(rt_file_get_size(empty_fd), 0);
            rt_file_close(empty_fd);
        }

        assert_eq!(rt_file_get_size(-1), -1);
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

/// Positioned read into a caller-owned buffer (exact `pread(2)` alias).
///
/// Returns the byte count read (0 at end of file), or `-errno` on failure —
/// the io_uring completion convention, chosen over `-1` + thread errno because
/// an interpreted caller cannot read errno before it is clobbered.
#[no_mangle]
pub unsafe extern "C" fn rt_fd_pread(fd: i32, buffer: *mut u8, len: i64, offset: i64) -> i64 {
    #[cfg(unix)]
    {
        if buffer.is_null() || len < 0 || offset < 0 {
            return -(libc::EINVAL as i64);
        }
        let n = libc::pread(fd, buffer as *mut libc::c_void, len as usize, offset as libc::off_t);
        if n < 0 {
            -(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO) as i64)
        } else {
            n as i64
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (fd, buffer, len, offset);
        // ENOSYS. Spelled literally rather than as `libc::ENOSYS` so this
        // non-unix branch does not depend on the libc crate exposing that
        // constant for Windows targets, which cannot be verified on the
        // aarch64 Linux host this landed from.
        -38
    }
}

/// Positioned write from a caller-owned buffer (exact `pwrite(2)` alias).
/// Same return convention as [`rt_fd_pread`].
#[no_mangle]
pub unsafe extern "C" fn rt_fd_pwrite(fd: i32, buffer: *const u8, len: i64, offset: i64) -> i64 {
    #[cfg(unix)]
    {
        if buffer.is_null() || len < 0 || offset < 0 {
            return -(libc::EINVAL as i64);
        }
        let n = libc::pwrite(fd, buffer as *const libc::c_void, len as usize, offset as libc::off_t);
        if n < 0 {
            -(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO) as i64)
        } else {
            n as i64
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (fd, buffer, len, offset);
        // ENOSYS. Spelled literally rather than as `libc::ENOSYS` so this
        // non-unix branch does not depend on the libc crate exposing that
        // constant for Windows targets, which cannot be verified on the
        // aarch64 Linux host this landed from.
        -38
    }
}

/// Linux `open(2)` flag bits shared by the SMF loader
/// (`src/compiler/99.loader/smf_mmap_native.spl`), the interpreter twin
/// (`interpreter_extern/file_io.rs`) and the core-C twin (`runtime_native.c`).
/// POSIX hosts pass them to `open(2)` unchanged; only Windows translates.
#[cfg(windows)]
const OPEN_FD_ACCESS_MASK: i64 = 0x3;
#[cfg(windows)]
const OPEN_FD_CREAT: i64 = 0x40;
#[cfg(windows)]
const OPEN_FD_TRUNC: i64 = 0x200;
#[cfg(windows)]
const OPEN_FD_APPEND: i64 = 0x400;

/// Path bytes of a boxed runtime string, or of an already-raw NUL-terminated
/// C string (same acceptance as `rt_interp_cstr`).
fn open_fd_path_bytes(path: crate::value::RuntimeValue) -> Option<Vec<u8>> {
    use crate::value::collections::{rt_string_data, rt_string_len};
    let data = rt_string_data(path);
    if !data.is_null() {
        let len = rt_string_len(path);
        if len < 0 {
            return None;
        }
        let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
        return Some(bytes.to_vec());
    }
    let raw = path.to_raw();
    if raw < 0x10000 {
        return None;
    }
    let cstr = unsafe { std::ffi::CStr::from_ptr(raw as usize as *const std::ffi::c_char) };
    Some(cstr.to_bytes().to_vec())
}

#[cfg(windows)]
extern "C" {
    fn _wopen(path: *const u16, oflag: i32, ...) -> i32;
    fn _close(fd: i32) -> i32;
}

/// Open a CRT/POSIX file descriptor for the SMF loader's mmap path.
/// Rust twin of `rt_open_fd` in `runtime_native.c`: Linux flag numbering;
/// POSIX passes the flags to `open(2)`, Windows translates them onto `_wopen`
/// (UTF-8 path -> UTF-16, `_O_BINARY | _O_NOINHERIT`) and returns the CRT
/// descriptor `rt_mmap_raw` maps. Returns -1 with `errno` set on failure.
#[no_mangle]
pub extern "C" fn rt_open_fd(path: crate::value::RuntimeValue, flags: i64, mode: i64) -> i64 {
    let Some(bytes) = open_fd_path_bytes(path) else {
        return -1;
    };
    #[cfg(unix)]
    {
        let Ok(c_path) = std::ffi::CString::new(bytes) else {
            return -1;
        };
        let fd = unsafe { libc::open(c_path.as_ptr(), flags as libc::c_int, mode as libc::c_uint) };
        i64::from(fd)
    }
    #[cfg(windows)]
    {
        let _ = mode; // OpenOptions and the C twin ignore the POSIX mode on Windows.
        const O_RDONLY: i32 = 0x0000;
        const O_WRONLY: i32 = 0x0001;
        const O_RDWR: i32 = 0x0002;
        const O_APPEND: i32 = 0x0008;
        const O_CREAT: i32 = 0x0100;
        const O_TRUNC: i32 = 0x0200;
        const O_NOINHERIT: i32 = 0x0080;
        const O_BINARY: i32 = 0x8000;
        const S_IREAD: i32 = 0x0100;
        const S_IWRITE: i32 = 0x0080;
        let Ok(text) = std::str::from_utf8(&bytes) else {
            return -1;
        };
        if text.contains('\0') {
            return -1;
        }
        let mut oflag = O_BINARY
            | O_NOINHERIT
            | match flags & OPEN_FD_ACCESS_MASK {
                0 => O_RDONLY,
                1 => O_WRONLY,
                _ => O_RDWR,
            };
        if flags & OPEN_FD_CREAT != 0 {
            oflag |= O_CREAT;
        }
        if flags & OPEN_FD_TRUNC != 0 {
            oflag |= O_TRUNC;
        }
        if flags & OPEN_FD_APPEND != 0 {
            oflag |= O_APPEND;
        }
        let wide: Vec<u16> = text.encode_utf16().chain(std::iter::once(0)).collect();
        i64::from(unsafe { _wopen(wide.as_ptr(), oflag, S_IREAD | S_IWRITE) })
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = (bytes, flags, mode);
        -1
    }
}

/// Close a descriptor returned by `rt_open_fd`. Invalid descriptors fail
/// closed with -1 (Rust twin of `rt_close_fd` in `runtime_native.c`).
#[no_mangle]
pub extern "C" fn rt_close_fd(fd: i64) -> i64 {
    if fd < 0 || fd > i64::from(i32::MAX) {
        return -1;
    }
    #[cfg(unix)]
    {
        i64::from(unsafe { libc::close(fd as libc::c_int) })
    }
    #[cfg(windows)]
    {
        i64::from(unsafe { _close(fd as i32) })
    }
    #[cfg(not(any(unix, windows)))]
    {
        -1
    }
}

#[cfg(test)]
mod open_fd_tests {
    use super::{rt_close_fd, rt_open_fd};
    use crate::value::collections::rt_string_new;

    #[test]
    fn open_write_read_close_with_linux_flags() {
        let path = std::env::temp_dir().join(format!("rt_open_fd_twin_{}.tmp", std::process::id()));
        let text = path.to_str().expect("utf8 temp path");
        let boxed = rt_string_new(text.as_ptr(), text.len() as u64);
        let wfd = rt_open_fd(boxed, 0x1 | 0x40 | 0x200, 0o644);
        assert!(wfd >= 0, "create+truncate");
        assert_eq!(rt_close_fd(wfd), 0);
        let rfd = rt_open_fd(boxed, 0x0, 0);
        assert!(rfd >= 0, "read-only reopen");
        assert_eq!(rt_close_fd(rfd), 0);
        let _ = std::fs::remove_file(&path);
        assert_eq!(rt_open_fd(boxed, 0x0, 0), -1, "missing file");
        assert_eq!(rt_close_fd(-1), -1);
    }
}
