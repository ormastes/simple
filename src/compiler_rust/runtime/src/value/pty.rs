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
        static ref CHILD_TABLE: Mutex<HashMap<i32, libc::pid_t>> = Mutex::new(HashMap::new());
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

                libc::ioctl(slave_fd, libc::TIOCSCTTY as _, 0 as libc::c_int);
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

            if let Ok(mut table) = CHILD_TABLE.lock() {
                table.insert(master_fd, pid);
            }

            pid as i64
        }
    }

    pub(super) fn is_running(master_fd: i64) -> bool {
        let Ok(mut table) = CHILD_TABLE.lock() else {
            return false;
        };
        let Some(&pid) = table.get(&(master_fd as i32)) else {
            return false;
        };
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        if result == 0 {
            true
        } else {
            table.remove(&(master_fd as i32));
            false
        }
    }

    pub(super) fn forget(master_fd: i64) {
        if let Ok(mut table) = CHILD_TABLE.lock() {
            table.remove(&(master_fd as i32));
        }
        if let Some(slave_fd) = SLAVE_TABLE
            .lock()
            .ok()
            .and_then(|mut table| table.remove(&(master_fd as i32)))
        {
            unsafe {
                libc::close(slave_fd);
            }
        }
    }
}

#[cfg(windows)]
mod pty_process {
    use std::collections::HashMap;
    use std::ffi::c_void;
    use std::sync::Mutex;
    use std::time::{Duration, Instant};
    use windows::core::{PCWSTR, PWSTR};
    use windows::Win32::Foundation::{CloseHandle, HANDLE, INVALID_HANDLE_VALUE, WAIT_OBJECT_0, WAIT_TIMEOUT};
    use windows::Win32::Storage::FileSystem::{ReadFile, WriteFile};
    use windows::Win32::System::Console::{ClosePseudoConsole, CreatePseudoConsole, COORD, HPCON};
    use windows::Win32::System::Pipes::{CreatePipe, PeekNamedPipe};
    use windows::Win32::System::Threading::{
        CreateProcessW, DeleteProcThreadAttributeList, InitializeProcThreadAttributeList, TerminateProcess,
        UpdateProcThreadAttribute, WaitForSingleObject, CREATE_UNICODE_ENVIRONMENT, EXTENDED_STARTUPINFO_PRESENT,
        LPPROC_THREAD_ATTRIBUTE_LIST, PROCESS_INFORMATION, PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE, STARTF_USESTDHANDLES,
        STARTUPINFOEXW,
    };

    struct Session {
        input_write: isize,
        output_read: isize,
        pseudo_console: isize,
        process: Option<isize>,
    }

    impl Session {
        fn terminate_child(&mut self) -> bool {
            let Some(process) = self.process.take() else {
                return true;
            };
            let process = HANDLE(process as *mut c_void);
            unsafe {
                let already_exited = WaitForSingleObject(process, 0) == WAIT_OBJECT_0;
                let terminated = already_exited
                    || (TerminateProcess(process, 1).is_ok() && WaitForSingleObject(process, 2_000) == WAIT_OBJECT_0);
                let closed = CloseHandle(process).is_ok();
                terminated && closed
            }
        }
    }

    impl Drop for Session {
        fn drop(&mut self) {
            unsafe {
                let _ = self.terminate_child();
                ClosePseudoConsole(HPCON(self.pseudo_console));
                let _ = CloseHandle(HANDLE(self.input_write as *mut c_void));
                let _ = CloseHandle(HANDLE(self.output_read as *mut c_void));
            }
        }
    }

    lazy_static::lazy_static! {
        static ref SESSIONS: Mutex<HashMap<i32, Session>> = Mutex::new(HashMap::new());
    }
    static NEXT_HANDLE: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(1);

    pub(super) fn open(rows: i32, cols: i32) -> i32 {
        unsafe {
            let mut input_read = HANDLE::default();
            let mut input_write = HANDLE::default();
            let mut output_read = HANDLE::default();
            let mut output_write = HANDLE::default();
            if CreatePipe(&mut input_read, &mut input_write, None, 0).is_err() {
                return -1;
            }
            if CreatePipe(&mut output_read, &mut output_write, None, 0).is_err() {
                let _ = CloseHandle(input_read);
                let _ = CloseHandle(input_write);
                return -1;
            }
            let size = COORD {
                X: cols.clamp(1, i16::MAX as i32) as i16,
                Y: rows.clamp(1, i16::MAX as i32) as i16,
            };
            let pseudo_console = match CreatePseudoConsole(size, input_read, output_write, 0x2 | 0x4) {
                Ok(value) => value,
                Err(_) => {
                    let _ = CloseHandle(input_read);
                    let _ = CloseHandle(input_write);
                    let _ = CloseHandle(output_read);
                    let _ = CloseHandle(output_write);
                    return -1;
                }
            };
            let _ = CloseHandle(input_read);
            let _ = CloseHandle(output_write);

            let id = NEXT_HANDLE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let session = Session {
                input_write: input_write.0 as isize,
                output_read: output_read.0 as isize,
                pseudo_console: pseudo_console.0,
                process: None,
            };
            match SESSIONS.lock() {
                Ok(mut sessions) => {
                    sessions.insert(id, session);
                    id
                }
                Err(_) => -1,
            }
        }
    }

    pub(super) fn spawn(handle: i32, command: &str) -> i64 {
        if command.is_empty() {
            return -1;
        }
        let mut sessions = match SESSIONS.lock() {
            Ok(value) => value,
            Err(_) => return -1,
        };
        let session = match sessions.get_mut(&handle) {
            Some(value) if value.process.is_none() => value,
            _ => return -1,
        };

        unsafe {
            let mut attribute_bytes = 0usize;
            let _ =
                InitializeProcThreadAttributeList(LPPROC_THREAD_ATTRIBUTE_LIST::default(), 1, 0, &mut attribute_bytes);
            if attribute_bytes == 0 {
                return -1;
            }
            let mut attribute_storage = vec![0u8; attribute_bytes];
            let attributes = LPPROC_THREAD_ATTRIBUTE_LIST(attribute_storage.as_mut_ptr().cast());
            if InitializeProcThreadAttributeList(attributes, 1, 0, &mut attribute_bytes).is_err() {
                return -1;
            }
            if UpdateProcThreadAttribute(
                attributes,
                0,
                PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE as usize,
                Some(session.pseudo_console as *const c_void),
                std::mem::size_of::<HPCON>(),
                None,
                None,
            )
            .is_err()
            {
                DeleteProcThreadAttributeList(attributes);
                return -1;
            }

            let mut startup: STARTUPINFOEXW = std::mem::zeroed();
            startup.StartupInfo.cb = std::mem::size_of::<STARTUPINFOEXW>() as u32;
            startup.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
            startup.StartupInfo.hStdInput = INVALID_HANDLE_VALUE;
            startup.StartupInfo.hStdOutput = INVALID_HANDLE_VALUE;
            startup.StartupInfo.hStdError = INVALID_HANDLE_VALUE;
            startup.lpAttributeList = attributes;
            let mut process_info: PROCESS_INFORMATION = std::mem::zeroed();
            let mut command_line: Vec<u16> = command.encode_utf16().chain(Some(0)).collect();
            let result = CreateProcessW(
                PCWSTR::null(),
                PWSTR(command_line.as_mut_ptr()),
                None,
                None,
                false,
                EXTENDED_STARTUPINFO_PRESENT | CREATE_UNICODE_ENVIRONMENT,
                None,
                PCWSTR::null(),
                &startup.StartupInfo,
                &mut process_info,
            );
            DeleteProcThreadAttributeList(attributes);
            if result.is_err() {
                return -1;
            }
            let _ = CloseHandle(process_info.hThread);
            session.process = Some(process_info.hProcess.0 as isize);
            process_info.dwProcessId as i64
        }
    }

    pub(super) fn write(handle: i64, bytes: &[u8]) -> bool {
        let sessions = match SESSIONS.lock() {
            Ok(value) => value,
            Err(_) => return false,
        };
        let Some(session) = sessions.get(&(handle as i32)) else {
            return false;
        };
        let mut written = 0u32;
        unsafe {
            WriteFile(
                HANDLE(session.input_write as *mut c_void),
                Some(bytes),
                Some(&mut written),
                None,
            )
            .is_ok()
                && written as usize == bytes.len()
        }
    }

    pub(super) fn read(handle: i64, timeout_ms: i64) -> String {
        let start = Instant::now();
        let timeout = Duration::from_millis(timeout_ms.max(0) as u64);
        loop {
            let sessions = match SESSIONS.lock() {
                Ok(value) => value,
                Err(_) => return String::new(),
            };
            let Some(session) = sessions.get(&(handle as i32)) else {
                return String::new();
            };
            let pipe = HANDLE(session.output_read as *mut c_void);
            let mut available = 0u32;
            let peeked = unsafe { PeekNamedPipe(pipe, None, 0, None, Some(&mut available), None).is_ok() };
            if !peeked {
                return String::new();
            }
            if available > 0 {
                let mut buffer = vec![0u8; available.min(4096) as usize];
                let mut read = 0u32;
                if unsafe { ReadFile(pipe, Some(&mut buffer), Some(&mut read), None) }.is_ok() {
                    buffer.truncate(read as usize);
                    return String::from_utf8_lossy(&buffer).into_owned();
                }
                return String::new();
            }
            drop(sessions);
            if start.elapsed() >= timeout {
                return String::new();
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    pub(super) fn close(handle: i64) -> bool {
        let Some(mut session) = SESSIONS
            .lock()
            .ok()
            .and_then(|mut sessions| sessions.remove(&(handle as i32)))
        else {
            return false;
        };
        session.terminate_child()
    }

    pub(super) fn is_running(handle: i64) -> bool {
        let Ok(sessions) = SESSIONS.lock() else {
            return false;
        };
        let Some(process) = sessions.get(&(handle as i32)).and_then(|session| session.process) else {
            return false;
        };
        unsafe { WaitForSingleObject(HANDLE(process as *mut c_void), 0) == WAIT_TIMEOUT }
    }
}

#[no_mangle]
pub extern "C" fn rt_pty_open(rows: i32, cols: i32) -> i32 {
    #[cfg(any(unix, windows))]
    {
        pty_process::open(rows, cols)
    }

    #[cfg(not(any(unix, windows)))]
    {
        let _ = (rows, cols);
        -1
    }
}

#[cfg(windows)]
pub fn host_pty_open(rows: i32, cols: i32) -> i32 {
    pty_process::open(rows, cols)
}

#[cfg(windows)]
pub fn host_pty_spawn(handle: i32, command: &str) -> i64 {
    pty_process::spawn(handle, command)
}

#[cfg(windows)]
pub fn host_pty_write(handle: i64, bytes: &[u8]) -> bool {
    pty_process::write(handle, bytes)
}

#[cfg(windows)]
pub fn host_pty_read(handle: i64, timeout_ms: i64) -> String {
    pty_process::read(handle, timeout_ms)
}

#[cfg(windows)]
pub fn host_pty_close(handle: i64) -> bool {
    pty_process::close(handle)
}

#[cfg(windows)]
pub fn host_pty_is_running(handle: i64) -> bool {
    pty_process::is_running(handle)
}

#[no_mangle]
pub unsafe extern "C" fn rt_pty_spawn(master_fd: i32, shell: RuntimeValue) -> i64 {
    #[cfg(any(unix, windows))]
    {
        let Some(shell) = runtime_value_to_string(shell) else {
            return -1;
        };
        pty_process::spawn(master_fd, &shell)
    }

    #[cfg(not(any(unix, windows)))]
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
        #[cfg(windows)]
        {
            let text = unsafe {
                if let Some(s) = runtime_value_to_string(data) {
                    s
                } else {
                    return RuntimeValue::from_bool(false);
                }
            };
            return RuntimeValue::from_bool(pty_process::write(fd, text.as_bytes()));
        }
        #[cfg(not(windows))]
        RuntimeValue::from_bool(false)
    }
}

#[no_mangle]
pub extern "C" fn rt_pty_write(fd: i64, data: RuntimeValue) -> RuntimeValue {
    native_pty_write(fd, data)
}

/// Helper to extract string from RuntimeValue
#[cfg(any(unix, windows))]
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
                    let errno = nix::errno::Errno::last_raw();
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
        #[cfg(windows)]
        return string_to_runtime_value(&pty_process::read(fd, timeout_ms));
        #[cfg(not(windows))]
        string_to_runtime_value("")
    }
}

#[no_mangle]
pub extern "C" fn rt_pty_read(fd: i64, timeout_ms: i64) -> RuntimeValue {
    native_pty_read(fd, timeout_ms)
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
        pty_process::forget(fd as i64);
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
        #[cfg(windows)]
        return RuntimeValue::from_bool(pty_process::close(fd));
        #[cfg(not(windows))]
        RuntimeValue::from_bool(false)
    }
}

#[no_mangle]
pub extern "C" fn rt_pty_close(fd: i64) -> RuntimeValue {
    native_pty_close(fd)
}

#[no_mangle]
pub extern "C" fn rt_pty_is_running(handle: i64) -> RuntimeValue {
    #[cfg(any(unix, windows))]
    return RuntimeValue::from_bool(pty_process::is_running(handle));
    #[cfg(not(any(unix, windows)))]
    RuntimeValue::from_bool(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rt_pty_spawn_rejects_invalid_inputs() {
        unsafe {
            assert_eq!(rt_pty_spawn(-1, RuntimeValue::NIL), -1);
            assert_eq!(rt_pty_spawn(-1, RuntimeValue::from_raw(0x1001)), -1);
        }
    }

    #[test]
    #[cfg(unix)]
    fn rt_pty_write_rejects_forged_heap_data() {
        let forged_heap = RuntimeValue::from_raw(0x1001);

        assert_eq!(unsafe { runtime_value_to_string(forged_heap) }, None);
        assert_eq!(rt_pty_write(-1, forged_heap), RuntimeValue::FALSE);
    }

    #[test]
    #[cfg(windows)]
    fn conpty_spawns_and_round_trips_console_io() {
        let handle = pty_process::open(24, 80);
        assert!(handle > 0);
        assert!(pty_process::spawn(handle, "cmd.exe /Q") > 0);
        assert!(pty_process::write(handle as i64, b"echo SIMPLE_CONPTY_OK\r\nexit\r\n"));

        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let mut output = String::new();
        while std::time::Instant::now() < deadline && !output.contains("SIMPLE_CONPTY_OK") {
            output.push_str(&pty_process::read(handle as i64, 100));
        }
        assert!(output.contains("SIMPLE_CONPTY_OK"), "ConPTY output: {output:?}");
        assert!(pty_process::close(handle as i64));
    }

    #[test]
    #[cfg(windows)]
    fn conpty_close_terminates_an_active_child_within_its_bound() {
        let handle = pty_process::open(24, 80);
        assert!(handle > 0);
        assert!(pty_process::spawn(handle, "cmd.exe /Q") > 0);

        let started = std::time::Instant::now();
        assert!(pty_process::close(handle as i64));
        assert!(started.elapsed() < std::time::Duration::from_secs(3));
        assert!(!pty_process::close(handle as i64));
    }

    #[test]
    #[cfg(windows)]
    fn conpty_running_state_tracks_spawn_exit_and_close() {
        assert!(!pty_process::is_running(-1));
        let handle = pty_process::open(24, 80);
        assert!(handle > 0);
        assert!(!pty_process::is_running(handle as i64));
        assert!(pty_process::spawn(handle, "cmd.exe /Q") > 0);
        assert!(pty_process::is_running(handle as i64));
        assert!(pty_process::close(handle as i64));
        assert!(!pty_process::is_running(handle as i64));
    }
}
