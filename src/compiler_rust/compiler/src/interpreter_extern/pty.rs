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
    let shell = args
        .get(1)
        .map(value_text)
        .unwrap_or_else(|| "/bin/sh".to_string());
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
            String::from_utf8_lossy(&bytes[..count as usize]).into_owned()
        }
    }

    pub(super) fn pty_close(fd: i32) -> bool {
        if let Ok(mut table) = SLAVE_TABLE.lock() {
            if let Some(slave) = table.remove(&fd) {
                unsafe {
                    libc::close(slave);
                }
            }
        }
        unsafe { libc::close(fd) == 0 }
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

#[cfg(windows)]
mod windows_impl {
    use std::collections::HashMap;
    use std::ffi::c_void;
    use std::sync::atomic::{AtomicI32, Ordering};
    use std::sync::Mutex;
    use std::time::{Duration, Instant};

    type Handle = *mut c_void;
    type Hpcon = *mut c_void;
    const INVALID_HANDLE_VALUE: Handle = -1_isize as Handle;
    const EXTENDED_STARTUPINFO_PRESENT: u32 = 0x0008_0000;
    const CREATE_UNICODE_ENVIRONMENT: u32 = 0x0000_0400;
    const STARTF_USESTDHANDLES: u32 = 0x0000_0100;
    const PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE: usize = 0x0002_0016;

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct Coord {
        x: i16,
        y: i16,
    }
    #[repr(C)]
    struct SecurityAttributes {
        length: u32,
        descriptor: *mut c_void,
        inherit: i32,
    }
    #[repr(C)]
    struct StartupInfoW {
        cb: u32,
        reserved: *mut u16,
        desktop: *mut u16,
        title: *mut u16,
        x: u32,
        y: u32,
        x_size: u32,
        y_size: u32,
        x_chars: u32,
        y_chars: u32,
        fill: u32,
        flags: u32,
        show: u16,
        reserved2_len: u16,
        reserved2: *mut u8,
        stdin: Handle,
        stdout: Handle,
        stderr: Handle,
    }
    #[repr(C)]
    struct StartupInfoExW {
        startup: StartupInfoW,
        attributes: *mut c_void,
    }
    #[repr(C)]
    struct ProcessInformation {
        process: Handle,
        thread: Handle,
        process_id: u32,
        thread_id: u32,
    }

    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn CreatePipe(read: *mut Handle, write: *mut Handle, attrs: *mut SecurityAttributes, size: u32) -> i32;
        fn CloseHandle(handle: Handle) -> i32;
        fn CreatePseudoConsole(size: Coord, input: Handle, output: Handle, flags: u32, console: *mut Hpcon) -> i32;
        fn ClosePseudoConsole(console: Hpcon);
        fn InitializeProcThreadAttributeList(list: *mut c_void, count: u32, flags: u32, bytes: *mut usize) -> i32;
        fn UpdateProcThreadAttribute(
            list: *mut c_void,
            flags: u32,
            attribute: usize,
            value: *mut c_void,
            size: usize,
            previous: *mut c_void,
            returned: *mut usize,
        ) -> i32;
        fn DeleteProcThreadAttributeList(list: *mut c_void);
        fn CreateProcessW(
            app: *const u16,
            command: *mut u16,
            process_attrs: *mut c_void,
            thread_attrs: *mut c_void,
            inherit: i32,
            flags: u32,
            environment: *mut c_void,
            directory: *const u16,
            startup: *mut StartupInfoW,
            info: *mut ProcessInformation,
        ) -> i32;
        fn WriteFile(
            file: Handle,
            buffer: *const c_void,
            bytes: u32,
            written: *mut u32,
            overlapped: *mut c_void,
        ) -> i32;
        fn PeekNamedPipe(
            pipe: Handle,
            buffer: *mut c_void,
            size: u32,
            read: *mut u32,
            available: *mut u32,
            left: *mut u32,
        ) -> i32;
        fn ReadFile(file: Handle, buffer: *mut c_void, bytes: u32, read: *mut u32, overlapped: *mut c_void) -> i32;
    }

    struct Pty {
        console: Hpcon,
        input: Handle,
        output: Handle,
        process: Option<Handle>,
    }
    unsafe impl Send for Pty {}
    lazy_static::lazy_static! { static ref PTYS: Mutex<HashMap<i32, Pty>> = Mutex::new(HashMap::new()); }
    static NEXT_HANDLE: AtomicI32 = AtomicI32::new(1);

    pub(super) fn open(rows: i32, cols: i32) -> i32 {
        unsafe {
            let mut con_in = INVALID_HANDLE_VALUE;
            let mut input = INVALID_HANDLE_VALUE;
            let mut output = INVALID_HANDLE_VALUE;
            let mut con_out = INVALID_HANDLE_VALUE;
            let mut attrs = SecurityAttributes {
                length: std::mem::size_of::<SecurityAttributes>() as u32,
                descriptor: std::ptr::null_mut(),
                inherit: 0,
            };
            if CreatePipe(&mut con_in, &mut input, &mut attrs, 0) == 0
                || CreatePipe(&mut output, &mut con_out, &mut attrs, 0) == 0
            {
                for h in [con_in, input, output, con_out] {
                    if h != INVALID_HANDLE_VALUE {
                        CloseHandle(h);
                    }
                }
                return -1;
            }
            let mut console = std::ptr::null_mut();
            let hr = CreatePseudoConsole(
                Coord {
                    x: cols.clamp(1, i16::MAX as i32) as i16,
                    y: rows.clamp(1, i16::MAX as i32) as i16,
                },
                con_in,
                con_out,
                0x2 | 0x4,
                &mut console,
            );
            CloseHandle(con_in);
            CloseHandle(con_out);
            if hr < 0 {
                CloseHandle(input);
                CloseHandle(output);
                return -1;
            }
            let id = NEXT_HANDLE.fetch_add(1, Ordering::Relaxed);
            if let Ok(mut table) = PTYS.lock() {
                table.insert(
                    id,
                    Pty {
                        console,
                        input,
                        output,
                        process: None,
                    },
                );
                id
            } else {
                ClosePseudoConsole(console);
                CloseHandle(input);
                CloseHandle(output);
                -1
            }
        }
    }

    pub(super) fn spawn(id: i32, shell: &str) -> i64 {
        if shell.is_empty() {
            return -1;
        }
        let Ok(mut table) = PTYS.lock() else {
            return -1;
        };
        let Some(pty) = table.get_mut(&id) else {
            return -1;
        };
        unsafe {
            let mut bytes = 0usize;
            InitializeProcThreadAttributeList(std::ptr::null_mut(), 1, 0, &mut bytes);
            let mut storage = vec![0u8; bytes];
            let list = storage.as_mut_ptr().cast();
            if InitializeProcThreadAttributeList(list, 1, 0, &mut bytes) == 0 {
                return -1;
            }
            if UpdateProcThreadAttribute(
                list,
                0,
                PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE,
                pty.console,
                std::mem::size_of::<Hpcon>(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            ) == 0
            {
                DeleteProcThreadAttributeList(list);
                return -1;
            }
            let mut startup: StartupInfoExW = std::mem::zeroed();
            startup.startup.cb = std::mem::size_of::<StartupInfoExW>() as u32;
            startup.startup.flags = STARTF_USESTDHANDLES;
            startup.startup.stdin = INVALID_HANDLE_VALUE;
            startup.startup.stdout = INVALID_HANDLE_VALUE;
            startup.startup.stderr = INVALID_HANDLE_VALUE;
            startup.attributes = list;
            let mut info: ProcessInformation = std::mem::zeroed();
            let mut command: Vec<u16> = shell.encode_utf16().chain(std::iter::once(0)).collect();
            let ok = CreateProcessW(
                std::ptr::null(),
                command.as_mut_ptr(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                0,
                EXTENDED_STARTUPINFO_PRESENT | CREATE_UNICODE_ENVIRONMENT,
                std::ptr::null_mut(),
                std::ptr::null(),
                &mut startup.startup,
                &mut info,
            );
            DeleteProcThreadAttributeList(list);
            if ok == 0 {
                return -1;
            }
            CloseHandle(info.thread);
            pty.process = Some(info.process);
            info.process_id as i64
        }
    }

    pub(super) fn write(id: i32, data: &[u8]) -> bool {
        if data.is_empty() {
            return true;
        }
        let Ok(table) = PTYS.lock() else { return false };
        let Some(pty) = table.get(&id) else { return false };
        let mut written = 0;
        unsafe {
            WriteFile(
                pty.input,
                data.as_ptr().cast(),
                data.len().min(u32::MAX as usize) as u32,
                &mut written,
                std::ptr::null_mut(),
            ) != 0
                && written as usize == data.len()
        }
    }

    pub(super) fn read(id: i32, timeout_ms: u64) -> String {
        let start = Instant::now();
        loop {
            let output = {
                let Ok(table) = PTYS.lock() else { return String::new() };
                let Some(pty) = table.get(&id) else {
                    return String::new();
                };
                pty.output
            };
            let mut available = 0;
            let ok = unsafe {
                PeekNamedPipe(
                    output,
                    std::ptr::null_mut(),
                    0,
                    std::ptr::null_mut(),
                    &mut available,
                    std::ptr::null_mut(),
                )
            };
            if ok == 0 {
                return String::new();
            }
            if available > 0 {
                let mut data = vec![0u8; (available as usize).min(4096)];
                let mut read = 0;
                if unsafe {
                    ReadFile(
                        output,
                        data.as_mut_ptr().cast(),
                        data.len() as u32,
                        &mut read,
                        std::ptr::null_mut(),
                    )
                } != 0
                {
                    data.truncate(read as usize);
                    return String::from_utf8_lossy(&data).into_owned();
                }
                return String::new();
            }
            if start.elapsed() >= Duration::from_millis(timeout_ms) {
                return String::new();
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    pub(super) fn close(id: i32) -> bool {
        let Ok(mut table) = PTYS.lock() else { return false };
        let Some(pty) = table.remove(&id) else { return false };
        unsafe {
            if let Some(process) = pty.process {
                CloseHandle(process);
            }
            ClosePseudoConsole(pty.console);
            CloseHandle(pty.input);
            CloseHandle(pty.output);
        }
        true
    }
}

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
        assert!(rt_pty_spawn(&[Value::Int(handle as i64), Value::text("cmd.exe")])
            .unwrap()
            .as_int()
            .unwrap() > 0);
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
