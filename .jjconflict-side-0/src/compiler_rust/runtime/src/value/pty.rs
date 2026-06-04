//! PTY (Pseudo-Terminal) SFFI functions for console I/O testing

use crate::value::heap::{get_typed_ptr, HeapObjectType};
use crate::value::RuntimeValue;
#[cfg(unix)]
use std::os::unix::io::{AsRawFd, RawFd};

#[cfg(unix)]
use nix::pty::openpty;

#[cfg(unix)]
mod pty_process {
    use std::collections::HashMap;
    use std::ffi::CString;
    use std::sync::Mutex;

    lazy_static::lazy_static! {
        static ref SLAVE_TABLE: Mutex<HashMap<i32, i32>> = Mutex::new(HashMap::new());
    }

    pub(super) fn open(rows: i32, cols: i32) -> i32 {
        let mut master_fd: libc::c_int = -1;
        let mut slave_fd: libc::c_int = -1;

        let mut ws = libc::winsize {
            ws_row: rows.max(1) as libc::c_ushort,
            ws_col: cols.max(1) as libc::c_ushort,
            ws_xpixel: 0,
            ws_ypixel: 0,
        };

        let ret = unsafe {
            libc::openpty(
                &mut master_fd,
                &mut slave_fd,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                &mut ws,
            )
        };

        if ret < 0 {
            return -1;
        }

        unsafe {
            let flags = libc::fcntl(master_fd, libc::F_GETFL, 0);
            if flags >= 0 {
                libc::fcntl(master_fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
            }
        }

        if let Ok(mut table) = SLAVE_TABLE.lock() {
            table.insert(master_fd, slave_fd);
        }

        master_fd
    }

    pub(super) fn spawn(master_fd: i32, shell: &str) -> i64 {
        if shell.is_empty() {
            return -1;
        }

        let slave_fd = match SLAVE_TABLE.lock().ok().and_then(|table| table.get(&master_fd).copied()) {
            Some(fd) => fd,
            None => return -1,
        };

        let shell_cstr = match CString::new(shell) {
            Ok(value) => value,
            Err(_) => return -1,
        };
        let argv0 = shell.rsplit('/').next().unwrap_or(shell);
        let argv0_cstr = match CString::new(argv0) {
            Ok(value) => value,
            Err(_) => return -1,
        };

        unsafe {
            libc::fflush(std::ptr::null_mut());

            let pid = libc::fork();
            if pid < 0 {
                return -1;
            }

            if pid == 0 {
                if libc::setsid() < 0 {
                    libc::_exit(1);
                }

                libc::ioctl(slave_fd, libc::TIOCSCTTY as libc::c_ulong, 0 as libc::c_int);
                libc::dup2(slave_fd, libc::STDIN_FILENO);
                libc::dup2(slave_fd, libc::STDOUT_FILENO);
                libc::dup2(slave_fd, libc::STDERR_FILENO);
                if slave_fd > libc::STDERR_FILENO {
                    libc::close(slave_fd);
                }
                libc::close(master_fd);

                libc::signal(libc::SIGINT, libc::SIG_DFL);
                libc::signal(libc::SIGTERM, libc::SIG_DFL);
                libc::signal(libc::SIGPIPE, libc::SIG_DFL);
                libc::signal(libc::SIGHUP, libc::SIG_DFL);

                let argv: &[*const libc::c_char] = &[argv0_cstr.as_ptr(), std::ptr::null()];
                libc::execvp(shell_cstr.as_ptr(), argv.as_ptr());
                libc::_exit(127);
            }

            libc::close(slave_fd);
            if let Ok(mut table) = SLAVE_TABLE.lock() {
                table.remove(&master_fd);
            }

            pid as i64
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_pty_open(rows: i32, cols: i32) -> i32 {
    #[cfg(unix)]
    {
        pty_process::open(rows, cols)
    }

    #[cfg(not(unix))]
    {
        let _ = (rows, cols);
        -1
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_pty_spawn(master_fd: i32, shell: *const std::os::raw::c_char) -> i64 {
    #[cfg(unix)]
    {
        if shell.is_null() {
            return -1;
        }
        let Ok(shell) = std::ffi::CStr::from_ptr(shell).to_str() else {
            return -1;
        };
        pty_process::spawn(master_fd, shell)
    }

    #[cfg(not(unix))]
    {
        let _ = (master_fd, shell);
        -1
    }
}

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
    let ptr = get_typed_ptr::<super::collections::RuntimeString>(val, HeapObjectType::String)?;
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
                    #[cfg(target_os = "linux")]
                    let errno = *libc::__errno_location();
                    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
                    let errno = *libc::__error();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rt_pty_spawn_rejects_invalid_inputs() {
        unsafe {
            assert_eq!(rt_pty_spawn(-1, std::ptr::null()), -1);
            assert_eq!(rt_pty_spawn(-1, c"/bin/sh".as_ptr()), -1);
            assert_eq!(rt_pty_spawn(-1, c"".as_ptr()), -1);
        }
    }

    #[test]
    #[cfg(unix)]
    fn rt_pty_write_rejects_forged_heap_data() {
        let forged_heap = RuntimeValue::from_raw(0x1001);

        assert_eq!(unsafe { runtime_value_to_string(forged_heap) }, None);
        assert_eq!(rt_pty_write(-1, forged_heap), RuntimeValue::FALSE);
    }
}
