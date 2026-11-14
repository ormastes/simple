//! PTY (Pseudo-Terminal) SFFI functions for console I/O testing

use crate::value::heap::{get_typed_ptr, HeapObjectType};
use crate::value::RuntimeValue;
#[cfg(unix)]
use std::os::unix::io::{AsRawFd, RawFd};

#[cfg(unix)]
use nix::pty::openpty;

// A read can end in the middle of a multi-byte UTF-8 character. Decoding each
// chunk on its own turned such a split into U+FFFD pairs (broken box drawing
// in agent TUIs), so the incomplete tail of a chunk is carried per fd and
// prefixed to the next read.
static PTY_UTF8_CARRY: std::sync::Mutex<Vec<(i64, Vec<u8>)>> = std::sync::Mutex::new(Vec::new());

/// Bytes at the end of `b` that start a UTF-8 sequence not yet complete.
fn incomplete_utf8_tail(b: &[u8]) -> usize {
    let n = b.len();
    for back in 1..=n.min(3) {
        let c = b[n - back];
        if c & 0xC0 == 0x80 {
            continue;
        }
        let need = match c {
            0xC2..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xF4 => 4,
            _ => return 0,
        };
        return if need > back { back } else { 0 };
    }
    0
}

/// Decodes one PTY read for `fd`, keeping a split trailing character for the next read.
pub fn decode_pty_utf8(fd: i64, chunk: &[u8]) -> String {
    let mut carry = PTY_UTF8_CARRY.lock().unwrap_or_else(|e| e.into_inner());
    let mut buf = match carry.iter().position(|(f, _)| *f == fd) {
        Some(i) => carry.swap_remove(i).1,
        None => Vec::new(),
    };
    buf.extend_from_slice(chunk);
    let keep = incomplete_utf8_tail(&buf);
    let tail = buf.split_off(buf.len() - keep);
    if !tail.is_empty() {
        carry.push((fd, tail));
    }
    String::from_utf8_lossy(&buf).into_owned()
}

/// Drops any carried partial character for a closed `fd`.
pub fn forget_pty_utf8(fd: i64) {
    let mut carry = PTY_UTF8_CARRY.lock().unwrap_or_else(|e| e.into_inner());
    carry.retain(|(f, _)| *f != fd);
}

/// Terminates and reaps a PTY child after its master fd was closed.
///
/// The close ABI reclaims synchronously (std.sys.pty `cleanup_pending` is 0),
/// but the POSIX close used to drop the child record without `waitpid`: the
/// hung-up child stayed a zombie forever and `kill(pid, 0)` kept reporting it
/// alive. `pid` must still be an unreaped child of this process (its zombie
/// pins the pid, so signalling it cannot hit a reused pid). The master close
/// already hung up the session; give it a bounded grace period, then SIGKILL
/// the child's session group and reap. Returns true once the child is reaped
/// (or was already reaped elsewhere: ECHILD).
#[cfg(unix)]
pub fn reap_pty_child(pid: libc::pid_t) -> bool {
    reap_pty_child_since(pid, std::time::Instant::now())
}

/// `reap_pty_child` whose 1 s grace period started at `grace_start` (the
/// moment the child was hung up). Batch teardown hangs every pane up first, so
/// the closes that follow share one grace period instead of paying one each.
#[cfg(unix)]
pub fn reap_pty_child_since(pid: libc::pid_t, grace_start: std::time::Instant) -> bool {
    if pid <= 1 {
        return false;
    }
    let reaped = |flags: libc::c_int| -> Option<bool> {
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid, &mut status, flags) };
        if result == pid {
            return Some(true);
        }
        if result < 0 {
            let err = std::io::Error::last_os_error().raw_os_error();
            if err == Some(libc::EINTR) {
                return None;
            }
            return Some(err == Some(libc::ECHILD));
        }
        None
    };
    let deadline = grace_start + std::time::Duration::from_millis(1000);
    loop {
        // Checked at least once, even when the shared grace already elapsed.
        if let Some(done) = reaped(libc::WNOHANG) {
            return done;
        }
        if std::time::Instant::now() >= deadline {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    unsafe {
        // The child is a session leader (setsid), so its pgid is its pid.
        libc::kill(-pid, libc::SIGKILL);
        libc::kill(pid, libc::SIGKILL);
    }
    let deadline = std::time::Instant::now() + std::time::Duration::from_millis(5000);
    while std::time::Instant::now() < deadline {
        if let Some(done) = reaped(libc::WNOHANG) {
            return done;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    false
}

/// What a WNOHANG probe says about a PTY child whose record is still held.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PtyChildProbe {
    /// Not reaped: keep the record (close still owns the reap).
    Running,
    /// Reaped by this probe (or already reaped elsewhere): drop the record.
    Gone,
}

/// One `waitpid(pid, WNOHANG)`: the result and, when it failed, its errno.
#[cfg(unix)]
pub fn waitpid_nohang(pid: libc::pid_t) -> (libc::pid_t, Option<i32>) {
    let mut status = 0;
    let result = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
    if result < 0 {
        (result, std::io::Error::last_os_error().raw_os_error())
    } else {
        (result, None)
    }
}

/// Classifies a WNOHANG probe of a PTY child. An interrupted wait (EINTR) is
/// retried: treating it as an exit dropped the record, so close never reaped
/// the child and it stayed a zombie. Any other failure keeps the record too
/// (close remains the reaper); only a reap or ECHILD (reaped elsewhere) ends it.
#[cfg(unix)]
pub fn probe_pty_child_with(
    pid: libc::pid_t,
    mut wait: impl FnMut(libc::pid_t) -> (libc::pid_t, Option<i32>),
) -> PtyChildProbe {
    for _ in 0..64 {
        let (result, err) = wait(pid);
        if result == 0 {
            return PtyChildProbe::Running;
        }
        if result == pid {
            return PtyChildProbe::Gone;
        }
        if result < 0 && err == Some(libc::EINTR) {
            continue;
        }
        if result < 0 && err == Some(libc::ECHILD) {
            return PtyChildProbe::Gone;
        }
        return PtyChildProbe::Running;
    }
    PtyChildProbe::Running
}

/// A spawned PTY child as both lanes' child tables hold it.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
pub struct PtyChildRecord {
    pub pid: libc::pid_t,
    /// When `hangup_pty_child` signalled it; its close's grace runs from here.
    pub hung_up_at: Option<std::time::Instant>,
}

#[cfg(unix)]
impl PtyChildRecord {
    pub fn new(pid: libc::pid_t) -> Self {
        PtyChildRecord { pid, hung_up_at: None }
    }
}

/// Sends SIGHUP to a PTY child's session group ahead of its close and stamps
/// the record, so a teardown that hangs up every pane first pays one grace
/// period in total. The caller must hold its child-table lock with `record`
/// still in it: the table's owner is the only reaper, so the unreaped child
/// pins the pid and the group signal cannot reach a reused pid. Idempotent.
#[cfg(unix)]
pub fn hangup_pty_child(record: &mut PtyChildRecord) -> bool {
    if record.pid <= 1 {
        return false;
    }
    if record.hung_up_at.is_none() {
        unsafe {
            // The child is a session leader (setsid), so its pgid is its pid.
            libc::kill(-record.pid, libc::SIGHUP);
            libc::kill(record.pid, libc::SIGHUP);
        }
        record.hung_up_at = Some(std::time::Instant::now());
    }
    true
}

/// Reaps a closed PTY child, its grace period running from its hangup.
#[cfg(unix)]
pub fn reap_pty_child_record(record: PtyChildRecord) -> bool {
    reap_pty_child_since(record.pid, record.hung_up_at.unwrap_or_else(std::time::Instant::now))
}

/// Marks a PTY fd close-on-exec. Without it every later pane's child inherited
/// this master, so closing it hung up nobody and each close paid the grace.
#[cfg(unix)]
pub fn set_pty_fd_cloexec(fd: libc::c_int) {
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFD);
        if flags >= 0 {
            libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC);
        }
    }
}

#[cfg(unix)]
mod pty_process {
    use std::collections::HashMap;
    use std::ffi::CString;
    use std::sync::Mutex;

    lazy_static::lazy_static! {
        static ref SLAVE_TABLE: Mutex<HashMap<i32, i32>> = Mutex::new(HashMap::new());
        static ref CHILD_TABLE: Mutex<HashMap<i32, super::PtyChildRecord>> = Mutex::new(HashMap::new());
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
        super::set_pty_fd_cloexec(master_fd);
        super::set_pty_fd_cloexec(slave_fd);

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

        // A command LINE ("/bin/sh -i") is not a path. Windows hands the line to
        // CreateProcess; here it is run through /bin/sh when the direct exec fails,
        // so one PTY interface takes the same command text on every platform.
        let line_cstr = match CString::new(format!("exec {}", shell)) {
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
                // A slave that already was fd 0-2 kept its close-on-exec flag through
                // the no-op dup2; clear it so exec keeps the standard streams.
                for std_fd in 0..=libc::STDERR_FILENO {
                    libc::fcntl(std_fd, libc::F_SETFD, 0);
                }
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
                let sh_argv: &[*const libc::c_char] =
                    &[c"sh".as_ptr(), c"-c".as_ptr(), line_cstr.as_ptr(), std::ptr::null()];
                libc::execv(c"/bin/sh".as_ptr(), sh_argv.as_ptr());
                libc::_exit(127);
            }

            libc::close(slave_fd);
            if let Ok(mut table) = SLAVE_TABLE.lock() {
                table.remove(&master_fd);
            }

            if let Ok(mut table) = CHILD_TABLE.lock() {
                table.insert(master_fd, super::PtyChildRecord::new(pid));
            }

            pid as i64
        }
    }

    pub(super) fn is_running(master_fd: i64) -> bool {
        is_running_with(master_fd, super::waitpid_nohang)
    }

    /// `is_running` with an injectable WNOHANG wait, so an interrupted wait
    /// (EINTR) can be exercised deterministically.
    pub(super) fn is_running_with(
        master_fd: i64,
        wait: impl FnMut(libc::pid_t) -> (libc::pid_t, Option<i32>),
    ) -> bool {
        let Ok(mut table) = CHILD_TABLE.lock() else {
            return false;
        };
        let Some(pid) = table.get(&(master_fd as i32)).map(|record| record.pid) else {
            return false;
        };
        match super::probe_pty_child_with(pid, wait) {
            super::PtyChildProbe::Running => true,
            super::PtyChildProbe::Gone => {
                table.remove(&(master_fd as i32));
                false
            }
        }
    }

    /// Hangs up the child of `master_fd` ahead of its close, under the table
    /// lock (see `hangup_pty_child`). False when no child is attached.
    pub(super) fn hangup(master_fd: i64) -> bool {
        let Ok(mut table) = CHILD_TABLE.lock() else {
            return false;
        };
        match table.get_mut(&(master_fd as i32)) {
            Some(record) => super::hangup_pty_child(record),
            None => false,
        }
    }

    /// TIOCSWINSZ makes the kernel signal the foreground group; the direct
    /// SIGWINCH covers a child that is not (yet) that group.
    pub(super) fn resize(master_fd: i64, rows: i32, cols: i32) -> bool {
        if master_fd < 0 || !(1..=u16::MAX as i32).contains(&rows) || !(1..=u16::MAX as i32).contains(&cols) {
            return false;
        }
        let ws = libc::winsize {
            ws_row: rows as libc::c_ushort,
            ws_col: cols as libc::c_ushort,
            ws_xpixel: 0,
            ws_ypixel: 0,
        };
        if unsafe { libc::ioctl(master_fd as i32, libc::TIOCSWINSZ as _, &ws as *const libc::winsize) } != 0 {
            return false;
        }
        if let Some(pid) = CHILD_TABLE
            .lock()
            .ok()
            .and_then(|table| table.get(&(master_fd as i32)).map(|record| record.pid))
        {
            unsafe {
                libc::kill(pid, libc::SIGWINCH);
            }
        }
        true
    }

    /// Drops the fd's records and returns the still-unreaped child, if any, so
    /// the caller can reap it after closing the master.
    pub(super) fn forget(master_fd: i64) -> Option<super::PtyChildRecord> {
        let child = CHILD_TABLE
            .lock()
            .ok()
            .and_then(|mut table| table.remove(&(master_fd as i32)));
        if let Some(slave_fd) = SLAVE_TABLE
            .lock()
            .ok()
            .and_then(|mut table| table.remove(&(master_fd as i32)))
        {
            unsafe {
                libc::close(slave_fd);
            }
        }
        child
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
    use windows::Win32::System::Console::{ClosePseudoConsole, CreatePseudoConsole, ResizePseudoConsole, COORD, HPCON};
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
        // Bytes of a UTF-8 sequence the last read cut in half; prefixed to the
        // next read so a split character is not decoded as U+FFFD.
        pending: Vec<u8>,
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
                pending: Vec::new(),
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

    /// Length of an incomplete UTF-8 sequence at the end of `bytes` (0..=3):
    /// a lead byte whose continuation bytes have not arrived yet.
    fn utf8_incomplete_tail(bytes: &[u8]) -> usize {
        let n = bytes.len();
        let mut back = 1;
        while back <= 3 && back <= n {
            let b = bytes[n - back];
            if b & 0xC0 != 0x80 {
                // Lead byte: how long is its sequence?
                let need = if b & 0xE0 == 0xC0 {
                    2
                } else if b & 0xF0 == 0xE0 {
                    3
                } else if b & 0xF8 == 0xF0 {
                    4
                } else {
                    1
                };
                return if need > back { back } else { 0 };
            }
            back += 1;
        }
        0
    }

    pub(super) fn read(handle: i64, timeout_ms: i64) -> String {
        let start = Instant::now();
        let timeout = Duration::from_millis(timeout_ms.max(0) as u64);
        loop {
            let mut sessions = match SESSIONS.lock() {
                Ok(value) => value,
                Err(_) => return String::new(),
            };
            let Some(session) = sessions.get_mut(&(handle as i32)) else {
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
                    let mut bytes = std::mem::take(&mut session.pending);
                    bytes.extend_from_slice(&buffer);
                    let cut = utf8_incomplete_tail(&bytes);
                    session.pending = bytes.split_off(bytes.len() - cut);
                    return String::from_utf8_lossy(&bytes).into_owned();
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

    pub(super) fn resize(handle: i64, rows: i32, cols: i32) -> bool {
        if !(1..=i16::MAX as i32).contains(&rows) || !(1..=i16::MAX as i32).contains(&cols) {
            return false;
        }
        let Ok(sessions) = SESSIONS.lock() else {
            return false;
        };
        let Some(session) = sessions.get(&(handle as i32)) else {
            return false;
        };
        let size = COORD {
            X: cols as i16,
            Y: rows as i16,
        };
        unsafe { ResizePseudoConsole(HPCON(session.pseudo_console), size).is_ok() }
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

#[cfg(windows)]
pub fn host_pty_resize(handle: i64, rows: i32, cols: i32) -> bool {
    pty_process::resize(handle, rows, cols)
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
                    let text = decode_pty_utf8(fd as i64, &buffer[..result as usize]);
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
        let child = pty_process::forget(fd as i64);
        forget_pty_utf8(fd as i64);
        let closed = unsafe { libc::close(fd) == 0 };
        if !closed {
            eprintln!("PTY close error: {}", std::io::Error::last_os_error());
        }
        // Closing the master hangs up the child; reap it so no zombie (or
        // survivor) outlives the close. The fd is gone either way, so a reap
        // failure is reported but not turned into a retryable close (a retry
        // would close a possibly reused fd number); pid liveness stays truthful.
        if let Some(record) = child {
            if !reap_pty_child_record(record) {
                eprintln!("PTY close: child {} could not be reaped", record.pid);
            }
        }
        RuntimeValue::from_bool(closed)
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

/// Hangs up the child attached to `handle` ahead of its `rt_pty_close`, which
/// stays the only closer and reaper. A teardown of N panes hangs them all up
/// first, then closes each: the closes share one ~1 s grace period for
/// children that ignore SIGHUP instead of paying one each. True when a child
/// was signalled; false for an unknown handle or no attached child. ConPTY
/// close terminates without a grace period, so Windows has nothing to batch
/// and answers false.
#[no_mangle]
pub extern "C" fn rt_pty_hangup(handle: i64) -> bool {
    #[cfg(unix)]
    return pty_process::hangup(handle);
    #[cfg(not(unix))]
    {
        let _ = handle;
        false
    }
}

/// Changes the viewport of the child attached to `handle`. False for an unknown
/// handle, a dimension the platform cannot represent, or a refused native call.
#[no_mangle]
pub extern "C" fn rt_pty_resize(handle: i64, rows: i32, cols: i32) -> bool {
    #[cfg(any(unix, windows))]
    return pty_process::resize(handle, rows, cols);
    #[cfg(not(any(unix, windows)))]
    {
        let _ = (handle, rows, cols);
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_pty_utf8_joins_a_character_split_across_reads() {
        // "─" is E2 94 80; split after its first byte, on a private fd.
        let fd = -4242;
        assert_eq!(decode_pty_utf8(fd, b"ab\xE2"), "ab");
        assert_eq!(decode_pty_utf8(fd, b"\x94\x80c"), "\u{2500}c");
        assert_eq!(decode_pty_utf8(fd, b"\xFF"), "\u{FFFD}");
        forget_pty_utf8(fd);
    }

    /// Closing the master must reap the hung-up child: before the fix the
    /// child stayed a zombie and `kill(pid, 0)` kept reporting it alive.
    #[test]
    #[cfg(unix)]
    fn rt_pty_close_reaps_the_child() {
        let handle = pty_process::open(24, 80);
        assert!(handle >= 0);
        let pid = pty_process::spawn(handle, "/bin/sh");
        assert!(pid > 0);
        assert!(pty_process::is_running(handle as i64));
        assert_eq!(rt_pty_close(handle as i64), RuntimeValue::TRUE);
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid as libc::pid_t, &mut status, libc::WNOHANG) };
        let err = std::io::Error::last_os_error().raw_os_error();
        assert!(result == -1 && err == Some(libc::ECHILD), "child {pid} not reaped by close");
        assert_eq!(unsafe { libc::kill(pid as libc::pid_t, 0) }, -1);
    }

    /// A command LINE with arguments must spawn on Unix as it does on Windows:
    /// the whole text used to be exec'd as one path, so `/bin/sh -i` died 127.
    #[test]
    #[cfg(unix)]
    fn rt_pty_spawn_accepts_a_command_line_with_arguments() {
        let handle = pty_process::open(24, 80);
        assert!(handle >= 0);
        let pid = pty_process::spawn(handle, "/bin/sh -c 'echo spawn_$((40+2)); sleep 5'");
        assert!(pid > 0);
        assert!(wait_for_output(handle, "spawn_42", 5000), "command line with arguments did not run");
        assert!(pty_process::is_running(handle as i64));
        assert_eq!(rt_pty_close(handle as i64), RuntimeValue::TRUE);
    }

    /// True once `needle` appeared on the master within `timeout_ms`.
    #[cfg(unix)]
    fn wait_for_output(handle: i32, needle: &str, timeout_ms: u64) -> bool {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(timeout_ms);
        let mut seen = String::new();
        let mut buf = [0u8; 4096];
        while std::time::Instant::now() < deadline {
            let n = unsafe { libc::read(handle, buf.as_mut_ptr().cast(), buf.len()) };
            if n > 0 {
                seen.push_str(&String::from_utf8_lossy(&buf[..n as usize]));
                if seen.contains(needle) {
                    return true;
                }
            } else {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
        }
        false
    }

    /// A provider stand-in that ignores SIGHUP (spawn resets SIGHUP to the
    /// default before exec, so the ignore must be installed by the child).
    #[cfg(unix)]
    fn sighup_ignoring_child() -> std::path::PathBuf {
        use std::os::unix::fs::PermissionsExt;
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("simple_pty_hup_ignore_{}_{}.sh", std::process::id(), n));
        std::fs::write(&path, "#!/bin/sh\ntrap '' HUP\necho READY\nwhile :; do sleep 1; done\n").unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
        path
    }

    #[cfg(unix)]
    fn assert_reaped(pid: i64) {
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid as libc::pid_t, &mut status, libc::WNOHANG) };
        let err = std::io::Error::last_os_error().raw_os_error();
        assert!(result == -1 && err == Some(libc::ECHILD), "child {pid} left unreaped");
    }

    /// Batch teardown: hanging every pane up first and then closing them all
    /// costs one grace period in total, not one per SIGHUP-ignoring child.
    #[test]
    #[cfg(unix)]
    fn hangup_then_close_of_n_sighup_ignoring_children_costs_one_grace() {
        let script = sighup_ignoring_child();
        let mut panes = Vec::new();
        for _ in 0..4 {
            let handle = pty_process::open(24, 80);
            assert!(handle >= 0);
            let pid = pty_process::spawn(handle, script.to_str().unwrap());
            assert!(pid > 0);
            assert!(wait_for_output(handle, "READY", 5000), "child {pid} never armed its HUP trap");
            panes.push((handle, pid));
        }
        let started = std::time::Instant::now();
        for &(handle, _) in &panes {
            assert!(rt_pty_hangup(handle as i64));
        }
        for &(handle, _) in &panes {
            assert_eq!(rt_pty_close(handle as i64), RuntimeValue::TRUE);
        }
        let elapsed = started.elapsed();
        for &(_, pid) in &panes {
            assert_reaped(pid);
        }
        let _ = std::fs::remove_file(&script);
        assert!(
            elapsed < std::time::Duration::from_millis(2500),
            "4 SIGHUP-ignoring panes took {elapsed:?} to close; expected one ~1 s grace in total"
        );
    }

    /// Closing a pane must hang up its own child even while a sibling pane's
    /// child is alive: a sibling that inherited this master fd kept the
    /// session from hanging up, so every close paid the full grace period.
    #[test]
    #[cfg(unix)]
    fn close_hangs_up_its_child_while_a_sibling_pane_is_alive() {
        let first = pty_process::open(24, 80);
        assert!(first >= 0);
        let first_pid = pty_process::spawn(first, "/bin/sh");
        assert!(first_pid > 0);
        let second = pty_process::open(24, 80);
        assert!(second >= 0);
        let second_pid = pty_process::spawn(second, "/bin/sh");
        assert!(second_pid > 0);
        assert!(pty_process::is_running(second as i64));

        let started = std::time::Instant::now();
        assert_eq!(rt_pty_close(first as i64), RuntimeValue::TRUE);
        let elapsed = started.elapsed();
        assert_reaped(first_pid);
        assert_eq!(rt_pty_close(second as i64), RuntimeValue::TRUE);
        assert_reaped(second_pid);
        assert!(
            elapsed < std::time::Duration::from_millis(900),
            "closing a /bin/sh pane took {elapsed:?}: its hangup never reached the child"
        );
    }

    /// An interrupted probe (EINTR) is not an exit: the record must survive so
    /// the child is still reported running and close still reaps it.
    #[test]
    #[cfg(unix)]
    fn is_running_keeps_the_child_record_when_the_wait_is_interrupted() {
        let handle = pty_process::open(24, 80);
        assert!(handle >= 0);
        let pid = pty_process::spawn(handle, "/bin/sh");
        assert!(pid > 0);
        let mut interrupted = false;
        let alive = pty_process::is_running_with(handle as i64, |p| {
            if !interrupted {
                interrupted = true;
                return (-1, Some(libc::EINTR));
            }
            waitpid_nohang(p)
        });
        assert!(interrupted);
        assert!(alive, "an interrupted wait reported a live child as gone");
        assert!(pty_process::is_running(handle as i64), "the child record was dropped on EINTR");
        assert_eq!(rt_pty_close(handle as i64), RuntimeValue::TRUE);
        assert_reaped(pid);
    }

    #[test]
    fn rt_pty_spawn_rejects_invalid_inputs() {
        unsafe {
            assert_eq!(rt_pty_spawn(-1, RuntimeValue::NIL), -1);
            assert_eq!(rt_pty_spawn(-1, RuntimeValue::from_raw(0x1001)), -1);
        }
        assert!(!rt_pty_hangup(-1));
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
    fn resize_refuses_unknown_handles_and_bad_dimensions() {
        assert!(!rt_pty_resize(-1, 24, 80));
        let handle = rt_pty_open(24, 80) as i64;
        assert!(handle >= 0);
        assert!(!rt_pty_resize(handle, 0, 80));
        assert!(!rt_pty_resize(handle, 24, -1));
        assert!(!rt_pty_resize(handle, 24, 70_000));
        assert!(rt_pty_resize(handle, 30, 100));
        rt_pty_close(handle);
        assert!(!rt_pty_resize(handle, 24, 80));
    }

    /// The child itself must report the new size; a true return is not proof.
    #[test]
    #[cfg(windows)]
    fn conpty_resize_changes_the_size_the_child_reports() {
        /// ConPTY may render the padding before a value as a cursor move, so
        /// control sequences go first and only then is the label's number read.
        fn strip_csi(text: &str) -> String {
            let mut out = String::new();
            let mut chars = text.chars();
            while let Some(c) = chars.next() {
                if c == '\u{1b}' {
                    if chars.next() == Some('[') {
                        for d in chars.by_ref() {
                            if ('@'..='~').contains(&d) {
                                break;
                            }
                        }
                    }
                    out.push(' ');
                } else {
                    out.push(c);
                }
            }
            out
        }
        fn field(text: &str, label: &str) -> Option<i32> {
            let rest = &text[text.rfind(label)? + label.len()..];
            let digits: String = rest.trim_start().chars().take_while(char::is_ascii_digit).collect();
            digits.parse().ok()
        }
        fn mode_con(handle: i64) -> (i32, i32) {
            assert!(pty_process::write(handle, b"mode con\r\n"));
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
            let mut raw = String::new();
            while std::time::Instant::now() < deadline {
                raw.push_str(&pty_process::read(handle, 100));
                if strip_csi(&raw).contains("Keyboard") {
                    break;
                }
            }
            let text = strip_csi(&raw);
            let lines = field(&text, "Lines:").unwrap_or_else(|| panic!("no Lines in {raw:?}"));
            let cols = field(&text, "Columns:").unwrap_or_else(|| panic!("no Columns in {raw:?}"));
            (lines, cols)
        }
        let handle = pty_process::open(24, 80) as i64;
        assert!(handle > 0);
        assert!(pty_process::spawn(handle as i32, "cmd.exe /Q") > 0);
        assert_eq!(mode_con(handle), (24, 80));
        assert!(pty_process::resize(handle, 31, 97));
        assert_eq!(mode_con(handle), (31, 97));
        assert!(pty_process::close(handle));
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
