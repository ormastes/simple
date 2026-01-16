//! PTY (Pseudo-Terminal) FFI functions for console I/O testing

use crate::value::RuntimeValue;
use std::os::unix::io::{AsRawFd, RawFd};

#[cfg(unix)]
use nix::pty::openpty;

/// Open a new pseudo-terminal pair
/// Returns: [master_fd, slave_fd]
#[no_mangle]
pub extern "C" fn native_pty_openpty() -> RuntimeValue {
    #[cfg(unix)]
    {
        match openpty(None, None) {
            Ok(result) => {
                // Get raw file descriptors from OwnedFd
                let master_fd = result.master.as_raw_fd();
                let slave_fd = result.slave.as_raw_fd();

                // Leak the OwnedFds so they aren't closed (caller will manage them)
                std::mem::forget(result.master);
                std::mem::forget(result.slave);

                // Return tuple of [master, slave]
                let tuple = super::collections::rt_tuple_new(2);
                super::collections::rt_tuple_set(tuple, 0, RuntimeValue::from_int(master_fd as i64));
                super::collections::rt_tuple_set(tuple, 1, RuntimeValue::from_int(slave_fd as i64));
                tuple
            }
            Err(e) => {
                eprintln!("Failed to open PTY: {}", e);
                RuntimeValue::NIL
            }
        }
    }

    #[cfg(not(unix))]
    {
        eprintln!("PTY not supported on non-Unix platforms");
        RuntimeValue::NIL
    }
}

/// Write data to a file descriptor (PTY)
#[no_mangle]
pub extern "C" fn native_pty_write(fd: i64, data: RuntimeValue) -> RuntimeValue {
    #[cfg(unix)]
    {
        let fd = fd as RawFd;

        // Convert RuntimeValue to string
        let text = unsafe {
            if let Some(s) = runtime_value_to_string(data) {
                s
            } else {
                return RuntimeValue::from_bool(false);
            }
        };

        unsafe {
            let result = libc::write(fd, text.as_ptr() as *const libc::c_void, text.len());
            if result >= 0 {
                RuntimeValue::from_bool(true)
            } else {
                eprintln!("PTY write error: {}", std::io::Error::last_os_error());
                RuntimeValue::from_bool(false)
            }
        }
    }

    #[cfg(not(unix))]
    {
        RuntimeValue::from_bool(false)
    }
}

/// Helper to extract string from RuntimeValue
#[cfg(unix)]
unsafe fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    let ptr = val.as_heap_ptr() as *const super::collections::RuntimeString;
    if ptr.is_null() {
        return None;
    }

    let s = &*ptr;
    let bytes = s.as_bytes();
    String::from_utf8(bytes.to_vec()).ok()
}

/// Read data from a file descriptor (PTY) with timeout
/// Returns string of data read, or empty string on timeout
#[no_mangle]
pub extern "C" fn native_pty_read(fd: i64, timeout_ms: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        use std::thread;
        use std::time::{Duration, Instant};

        let fd = fd as RawFd;
        let mut buffer = [0u8; 4096];

        unsafe {
            // Set non-blocking mode
            let flags = libc::fcntl(fd, libc::F_GETFL);
            if flags < 0 {
                eprintln!("PTY read error: failed to get flags");
                return string_to_runtime_value("");
            }
            let _ = libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);

            let start = Instant::now();
            let timeout_duration = Duration::from_millis(timeout_ms as u64);

            loop {
                let result = libc::read(fd, buffer.as_mut_ptr() as *mut libc::c_void, buffer.len());

                if result > 0 {
                    // Data read successfully
                    let _ = libc::fcntl(fd, libc::F_SETFL, flags); // Restore blocking mode
                    let text = String::from_utf8_lossy(&buffer[..result as usize]);
                    return string_to_runtime_value(&text);
                } else if result == 0 {
                    // EOF
                    let _ = libc::fcntl(fd, libc::F_SETFL, flags);
                    return string_to_runtime_value("");
                } else {
                    // Error or would block
                    let errno = *libc::__errno_location();
                    if errno == libc::EAGAIN || errno == libc::EWOULDBLOCK {
                        // No data available, check timeout
                        if start.elapsed() >= timeout_duration {
                            let _ = libc::fcntl(fd, libc::F_SETFL, flags);
                            return string_to_runtime_value("");
                        }
                        // Sleep briefly before retrying
                        thread::sleep(Duration::from_millis(10));
                    } else {
                        // Real error
                        eprintln!("PTY read error: {}", std::io::Error::last_os_error());
                        let _ = libc::fcntl(fd, libc::F_SETFL, flags);
                        return string_to_runtime_value("");
                    }
                }
            }
        }
    }

    #[cfg(not(unix))]
    {
        string_to_runtime_value("")
    }
}

/// Helper to create RuntimeValue from string
fn string_to_runtime_value(s: &str) -> RuntimeValue {
    super::collections::rt_string_new(s.as_ptr(), s.len() as u64)
}

/// Close a file descriptor
#[no_mangle]
pub extern "C" fn native_pty_close(fd: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        let fd = fd as RawFd;
        unsafe {
            if libc::close(fd) == 0 {
                RuntimeValue::from_bool(true)
            } else {
                eprintln!("PTY close error: {}", std::io::Error::last_os_error());
                RuntimeValue::from_bool(false)
            }
        }
    }

    #[cfg(not(unix))]
    {
        RuntimeValue::from_bool(false)
    }
}
