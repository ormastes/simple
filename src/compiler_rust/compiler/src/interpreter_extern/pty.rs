//! PTY (Pseudo-Terminal) extern functions — interpreter mode.
//!
//! Provides Rust implementations of the raw `rt_pty_*` provider for
//! use in the interpreter.  The compiled/native path uses the Rust symbols in
//! `src/compiler_rust/runtime/src/value/pty.rs` (exported via `#[no_mangle]`);
//! `src/runtime/runtime_pty.c` is no longer compiled by any build path.
//! This module is the interpreter-only dispatch path.
//!
//! On Unix we call `openpty`/`fork`/`exec` via `libc`.
//! Windows uses ConPTY and exposes small logical handles rather than Win32
//! HANDLE values.  Shell selection and command policy remain in Simple.

use crate::error::CompileError;
use crate::value::Value;

/// `rt_pty_open(rows: i32, cols: i32) -> i32`
///
/// Opens a POSIX PTY pair.  Returns the master fd on success, -1 on error.
pub fn rt_pty_open(args: &[Value]) -> Result<Value, CompileError> {
    let rows = args.first().and_then(|v| v.as_int().ok()).unwrap_or(24) as i32;
    let cols = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(80) as i32;
    Ok(Value::Int(pty_open_impl(rows, cols) as i64))
}

/// `rt_pty_spawn(master_fd: i32, shell: text) -> i64`
///
/// Forks a shell process attached to the slave side of the PTY identified by
/// `master_fd`.  Returns the child PID on success, -1 on error.
pub fn rt_pty_spawn(args: &[Value]) -> Result<Value, CompileError> {
    let master_fd = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    let shell = args.get(1).map(value_text).unwrap_or_else(|| "/bin/sh".to_string());
    Ok(Value::Int(pty_spawn_impl(master_fd, &shell)))
}

/// `rt_pty_write(handle: i64, data: text) -> bool`
pub fn rt_pty_write(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    let data = args.get(1).map(value_text).unwrap_or_default();
    Ok(Value::Bool(pty_write_impl(handle, data.as_bytes())))
}

fn value_text(value: &Value) -> String {
    match value {
        Value::Str(text) => text.as_str().to_string(),
        other => other.to_display_string(),
    }
}

/// `rt_pty_read(handle: i64, timeout_ms: i64) -> text`
pub fn rt_pty_read(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    let timeout_ms = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(0).max(0) as u64;
    Ok(Value::text(pty_read_impl(handle, timeout_ms)))
}

/// `rt_pty_close(handle: i64) -> bool`
pub fn rt_pty_close(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    Ok(Value::Bool(pty_close_impl(handle)))
}

/// `rt_pty_is_running(handle: i64) -> bool`
pub fn rt_pty_is_running(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    Ok(Value::Bool(pty_is_running_impl(handle)))
}

/// `rt_pty_resize(handle: i64, rows: i32, cols: i32) -> bool`
pub fn rt_pty_resize(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args.first().and_then(|v| v.as_int().ok()).unwrap_or(-1) as i32;
    let rows = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(0) as i32;
    let cols = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as i32;
    Ok(Value::Bool(pty_resize_impl(handle, rows, cols)))
}

// -------------------------------------------------------------------------
// Platform implementations
// -------------------------------------------------------------------------

#[cfg(unix)]
mod unix_impl {
    use std::collections::HashMap;
    use std::ffi::CString;
    use std::sync::Mutex;

    /// Maps master_fd -> slave_fd so `pty_spawn_impl` can wire up the child.
    lazy_static::lazy_static! {
        static ref SLAVE_TABLE: Mutex<HashMap<i32, i32>> = Mutex::new(HashMap::new());
        static ref CHILD_TABLE: Mutex<HashMap<i32, libc::pid_t>> = Mutex::new(HashMap::new());
    }

    pub(super) fn pty_open(rows: i32, cols: i32) -> i32 {
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

        // Set master non-blocking so callers can poll without blocking.
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

    pub(super) fn pty_spawn(master_fd: i32, shell: &str) -> i64 {
        if shell.is_empty() {
            return -1;
        }

        let slave_fd = match SLAVE_TABLE.lock().ok().and_then(|t| t.get(&master_fd).copied()) {
            Some(fd) => fd,
            None => return -1,
        };

        let shell_cstr = match CString::new(shell) {
            Ok(s) => s,
            Err(_) => return -1,
        };

        // Extract argv[0] as the basename.
        let argv0 = shell.rsplit('/').next().unwrap_or(shell);
        let argv0_cstr = match CString::new(argv0) {
            Ok(s) => s,
            Err(_) => return -1,
        };

        unsafe {
            // Flush stdio before fork to avoid double output.
            libc::fflush(std::ptr::null_mut());

            let pid = libc::fork();
            if pid < 0 {
                return -1;
            }

            if pid == 0 {
                // ===== CHILD =====

                // New session — become session leader.
                if libc::setsid() < 0 {
                    libc::_exit(1);
                }

                // Acquire controlling terminal.
                // TIOCSCTTY is available on Linux, macOS, and BSDs via libc.
                #[cfg(not(target_os = "windows"))]
                {
                    libc::ioctl(slave_fd, libc::TIOCSCTTY as _, 0 as libc::c_int);
                }

                // Wire stdio.
                libc::dup2(slave_fd, libc::STDIN_FILENO);
                libc::dup2(slave_fd, libc::STDOUT_FILENO);
                libc::dup2(slave_fd, libc::STDERR_FILENO);
                if slave_fd > libc::STDERR_FILENO {
                    libc::close(slave_fd);
                }
                libc::close(master_fd);

                // Reset signal handlers.
                libc::signal(libc::SIGINT, libc::SIG_DFL);
                libc::signal(libc::SIGTERM, libc::SIG_DFL);
                libc::signal(libc::SIGPIPE, libc::SIG_DFL);
                libc::signal(libc::SIGHUP, libc::SIG_DFL);

                // exec shell — argv = [argv0, NULL]
                let argv: &[*const libc::c_char] = &[argv0_cstr.as_ptr(), std::ptr::null()];
                libc::execvp(shell_cstr.as_ptr(), argv.as_ptr());

                // exec failed.
                libc::_exit(127);
            }

            // ===== PARENT =====
            // Close slave — child holds it now.
            libc::close(slave_fd);
            if let Ok(mut table) = SLAVE_TABLE.lock() {
                table.remove(&master_fd);
            }
            if let Ok(mut table) = CHILD_TABLE.lock() {
                table.insert(master_fd, pid);
            }

            pid as i64
        }
    }

    pub(super) fn pty_write(fd: i32, data: &[u8]) -> bool {
        !data.is_empty() && unsafe { libc::write(fd, data.as_ptr().cast(), data.len()) == data.len() as isize }
    }

    pub(super) fn pty_read(fd: i32, timeout_ms: u64) -> String {
        let mut poll_fd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        if unsafe { libc::poll(&mut poll_fd, 1, timeout_ms.min(i32::MAX as u64) as i32) } <= 0 {
            return String::new();
        }
        let mut bytes = [0_u8; 4096];
        let count = unsafe { libc::read(fd, bytes.as_mut_ptr().cast(), bytes.len()) };
        if count <= 0 {
            String::new()
        } else {
            simple_runtime::value::pty::decode_pty_utf8(fd as i64, &bytes[..count as usize])
        }
    }

    pub(super) fn pty_close(fd: i32) -> bool {
        simple_runtime::value::pty::forget_pty_utf8(fd as i64);
        if let Ok(mut table) = SLAVE_TABLE.lock() {
            if let Some(slave) = table.remove(&fd) {
                unsafe {
                    libc::close(slave);
                }
            }
        }
        if let Ok(mut table) = CHILD_TABLE.lock() {
            table.remove(&fd);
        }
        unsafe { libc::close(fd) == 0 }
    }

    /// TIOCSWINSZ makes the kernel signal the foreground group; the direct
    /// SIGWINCH covers a child that is not (yet) that group.
    pub(super) fn pty_resize(fd: i32, rows: i32, cols: i32) -> bool {
        if fd < 0 || !(1..=u16::MAX as i32).contains(&rows) || !(1..=u16::MAX as i32).contains(&cols) {
            return false;
        }
        let ws = libc::winsize {
            ws_row: rows as libc::c_ushort,
            ws_col: cols as libc::c_ushort,
            ws_xpixel: 0,
            ws_ypixel: 0,
        };
        if unsafe { libc::ioctl(fd, libc::TIOCSWINSZ as _, &ws as *const libc::winsize) } != 0 {
            return false;
        }
        if let Some(pid) = CHILD_TABLE.lock().ok().and_then(|table| table.get(&fd).copied()) {
            unsafe {
                libc::kill(pid, libc::SIGWINCH);
            }
        }
        true
    }

    pub(super) fn pty_is_running(fd: i32) -> bool {
        let mut table = match CHILD_TABLE.lock() {
            Ok(value) => value,
            Err(_) => return false,
        };
        let pid = match table.get(&fd).copied() {
            Some(value) => value,
            None => return false,
        };
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        if result == 0 {
            return true;
        }
        if result == pid {
            table.remove(&fd);
        }
        false
    }
}

#[cfg(unix)]
fn pty_open_impl(rows: i32, cols: i32) -> i32 {
    unix_impl::pty_open(rows, cols)
}

#[cfg(unix)]
fn pty_spawn_impl(master_fd: i32, shell: &str) -> i64 {
    unix_impl::pty_spawn(master_fd, shell)
}

#[cfg(unix)]
fn pty_write_impl(handle: i32, data: &[u8]) -> bool {
    unix_impl::pty_write(handle, data)
}
#[cfg(unix)]
fn pty_read_impl(handle: i32, timeout_ms: u64) -> String {
    unix_impl::pty_read(handle, timeout_ms)
}
#[cfg(unix)]
fn pty_close_impl(handle: i32) -> bool {
    unix_impl::pty_close(handle)
}
#[cfg(unix)]
fn pty_is_running_impl(handle: i32) -> bool {
    unix_impl::pty_is_running(handle)
}

#[cfg(unix)]
fn pty_resize_impl(handle: i32, rows: i32, cols: i32) -> bool {
    unix_impl::pty_resize(handle, rows, cols)
}

// Windows PTY ownership lives in simple_runtime::value::pty. Keep this
// interpreter adapter as delegation rather than a second ConPTY/Win32 owner.
#[cfg(windows)]
fn pty_open_impl(rows: i32, cols: i32) -> i32 {
    simple_runtime::value::pty::host_pty_open(rows, cols)
}
#[cfg(windows)]
fn pty_spawn_impl(handle: i32, shell: &str) -> i64 {
    simple_runtime::value::pty::host_pty_spawn(handle, shell)
}
#[cfg(windows)]
fn pty_write_impl(handle: i32, data: &[u8]) -> bool {
    simple_runtime::value::pty::host_pty_write(handle as i64, data)
}
#[cfg(windows)]
fn pty_read_impl(handle: i32, timeout_ms: u64) -> String {
    simple_runtime::value::pty::host_pty_read(handle as i64, timeout_ms.min(i64::MAX as u64) as i64)
}
#[cfg(windows)]
fn pty_close_impl(handle: i32) -> bool {
    simple_runtime::value::pty::host_pty_close(handle as i64)
}
#[cfg(windows)]
fn pty_is_running_impl(handle: i32) -> bool {
    simple_runtime::value::pty::host_pty_is_running(handle as i64)
}

#[cfg(windows)]
fn pty_resize_impl(handle: i32, rows: i32, cols: i32) -> bool {
    simple_runtime::value::pty::host_pty_resize(handle as i64, rows, cols)
}

#[cfg(not(any(unix, windows)))]
fn pty_open_impl(_rows: i32, _cols: i32) -> i32 {
    -1
}
#[cfg(not(any(unix, windows)))]
fn pty_spawn_impl(_handle: i32, _shell: &str) -> i64 {
    -1
}
#[cfg(not(any(unix, windows)))]
fn pty_write_impl(_handle: i32, _data: &[u8]) -> bool {
    false
}
#[cfg(not(any(unix, windows)))]
fn pty_read_impl(_handle: i32, _timeout_ms: u64) -> String {
    String::new()
}
#[cfg(not(any(unix, windows)))]
fn pty_close_impl(_handle: i32) -> bool {
    false
}
#[cfg(not(any(unix, windows)))]
fn pty_is_running_impl(_handle: i32) -> bool {
    false
}

#[cfg(not(any(unix, windows)))]
fn pty_resize_impl(_handle: i32, _rows: i32, _cols: i32) -> bool {
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn invalid_handles_are_rejected() {
        assert_eq!(
            rt_pty_spawn(&[Value::Int(-1), Value::text("shell")]).unwrap(),
            Value::Int(-1)
        );
        assert_eq!(
            rt_pty_write(&[Value::Int(-1), Value::text("x")]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(rt_pty_read(&[Value::Int(-1), Value::Int(0)]).unwrap(), Value::text(""));
        assert_eq!(rt_pty_close(&[Value::Int(-1)]).unwrap(), Value::Bool(false));
        assert_eq!(rt_pty_is_running(&[Value::Int(-1)]).unwrap(), Value::Bool(false));
        assert_eq!(
            rt_pty_resize(&[Value::Int(-1), Value::Int(24), Value::Int(80)]).unwrap(),
            Value::Bool(false)
        );
    }
    #[test]
    fn empty_write_is_safe_for_invalid_handle() {
        assert_eq!(
            rt_pty_write(&[Value::Int(-1), Value::text("")]).unwrap(),
            Value::Bool(false)
        );
    }

    #[cfg(windows)]
    #[test]
    fn conpty_cmd_round_trip() {
        let handle = rt_pty_open(&[Value::Int(24), Value::Int(80)])
            .unwrap()
            .as_int()
            .unwrap() as i32;
        assert!(handle > 0);
        assert!(
            rt_pty_spawn(&[Value::Int(handle as i64), Value::text("cmd.exe")])
                .unwrap()
                .as_int()
                .unwrap()
                > 0
        );
        assert_eq!(
            rt_pty_write(&[
                Value::Int(handle as i64),
                Value::text("echo SIMPLE_CONPTY_OK\r\nexit\r\n"),
            ])
            .unwrap(),
            Value::Bool(true)
        );

        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let mut output = String::new();
        while std::time::Instant::now() < deadline && !output.contains("SIMPLE_CONPTY_OK") {
            output.push_str(&pty_read_impl(handle, 100));
        }
        assert!(output.contains("SIMPLE_CONPTY_OK"), "ConPTY output: {output:?}");
        assert!(pty_close_impl(handle));
    }
}
