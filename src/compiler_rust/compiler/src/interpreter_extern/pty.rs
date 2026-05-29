//! PTY (Pseudo-Terminal) extern functions — interpreter mode.
//!
//! Provides Rust implementations of `rt_pty_open` and `rt_pty_spawn` for
//! use in the interpreter.  The compiled/native path uses the Rust symbols in
//! `src/compiler_rust/runtime/src/value/pty.rs` (`#[no_mangle]` exports);
//! `src/runtime/runtime_pty.c` is no longer compiled by any build path.
//!
//! On Unix we call `openpty`/`fork`/`exec` via `libc`.
//! On Windows both functions return -1 (not supported).

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
    let shell = args
        .get(1)
        .map(|v| v.to_display_string())
        .unwrap_or_else(|| "/bin/sh".to_string());
    Ok(Value::Int(pty_spawn_impl(master_fd, &shell)))
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
                    libc::ioctl(slave_fd, libc::TIOCSCTTY as libc::c_ulong, 0 as libc::c_int);
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

            pid as i64
        }
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

#[cfg(not(unix))]
fn pty_open_impl(_rows: i32, _cols: i32) -> i32 {
    -1
}

#[cfg(not(unix))]
fn pty_spawn_impl(_master_fd: i32, _shell: &str) -> i64 {
    -1
}
