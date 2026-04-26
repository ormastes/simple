// ============================================================================
// Unix-domain socket FFI functions
//
// Server-side externs (SJ-UDS-001 / D-4 of jj-wrapper-daemon design):
//   rt_unix_socket_listen(path, backlog) -> i64    (fd or negative errno)
//   rt_unix_socket_accept(fd) -> i64               (client-fd, -EAGAIN, or negative errno)
//   rt_unix_socket_send(fd, data) -> i64           (bytes written or negative errno)
//   rt_unix_socket_recv(fd, max_len) -> [u8]       (bytes read; empty on EOF or EAGAIN)
//   rt_unix_socket_close(fd) -> i32                (0 on success, negative errno)
//
// Client-side extern (used by std.qemu.qmp_client):
//   rt_unix_socket_connect(path) -> i64            (fd or negative errno)
//
// Sockets stored in a separate UDS_REGISTRY (raw fd -> UnixStream/UnixListener)
// keyed by raw fd to keep the integer handle == OS fd. This lets close() be a
// straight libc::close, and lets external code (e.g. select/poll) treat the
// handle as an fd if they need to.
// ============================================================================

// (`use` statements are inherited from net.rs because net_uds.rs is included
//  via `include!`. Do not add `use` here — they will duplicate net.rs's.)

// Errno-style negative return codes (subset; matches Linux/macOS values).
const NEG_EAGAIN: i64 = -11;
const NEG_EINVAL: i64 = -22;
const NEG_EBADF: i64 = -9;
const NEG_EIO: i64 = -5;

enum UdsEntry {
    Listener(UnixListener),
    Stream(UnixStream),
}

lazy_static! {
    static ref UDS_REGISTRY: Mutex<HashMap<i64, UdsEntry>> = Mutex::new(HashMap::new());
}

fn errno_from_io(err: &std::io::Error) -> i64 {
    use std::io::ErrorKind;
    match err.kind() {
        ErrorKind::WouldBlock => NEG_EAGAIN,
        ErrorKind::InvalidInput | ErrorKind::InvalidData => NEG_EINVAL,
        ErrorKind::NotFound | ErrorKind::AddrNotAvailable => -2,    // ENOENT / EADDRNOTAVAIL
        ErrorKind::AddrInUse => -98,                                // EADDRINUSE
        ErrorKind::PermissionDenied => -13,                         // EACCES
        ErrorKind::ConnectionRefused => -111,                       // ECONNREFUSED
        ErrorKind::BrokenPipe => -32,                               // EPIPE
        ErrorKind::TimedOut => -110,                                // ETIMEDOUT
        _ => err.raw_os_error().map(|e| -(e as i64)).unwrap_or(NEG_EIO),
    }
}

unsafe fn ptr_to_str(ptr: i64, len: i64) -> Option<String> {
    if ptr == 0 || len <= 0 {
        return None;
    }
    let slice = std::slice::from_raw_parts(ptr as *const u8, len as usize);
    std::str::from_utf8(slice).ok().map(str::to_owned)
}

// ----------------------------------------------------------------------------
// Server-side
// ----------------------------------------------------------------------------

/// Bind a UnixListener to `path` (removing any stale socket file first), set
/// the listen backlog and non-blocking mode, register it, and return its fd.
///
/// # Safety
/// `path_ptr` must point to `path_len` valid UTF-8 bytes.
#[no_mangle]
pub unsafe extern "C" fn rt_unix_socket_listen(path_ptr: i64, path_len: i64, backlog: i32) -> i64 {
    let path = match ptr_to_str(path_ptr, path_len) {
        Some(s) => s,
        None => return NEG_EINVAL,
    };
    // Best-effort cleanup of stale socket file. Ignore errors (file may not exist).
    let _ = std::fs::remove_file(&path);
    let listener = match UnixListener::bind(&path) {
        Ok(l) => l,
        Err(e) => return errno_from_io(&e),
    };
    if let Err(e) = listener.set_nonblocking(true) {
        return errno_from_io(&e);
    }
    // std::os::unix::net::UnixListener::bind defaults to backlog=128. We can't
    // easily change it via std without socket2, so we accept the default and
    // honor `backlog` only as a hint (logged for caller awareness).
    let _ = backlog; // currently unused; kept for ABI stability + future tuning
    let fd = listener.as_raw_fd() as i64;
    UDS_REGISTRY.lock().unwrap().insert(fd, UdsEntry::Listener(listener));
    fd
}

/// Non-blocking accept on a registered UnixListener. Returns the new client
/// fd on success, `NEG_EAGAIN` if no pending connection, or negative errno.
#[no_mangle]
pub extern "C" fn rt_unix_socket_accept(fd: i64) -> i64 {
    let mut reg = UDS_REGISTRY.lock().unwrap();
    let listener = match reg.get(&fd) {
        Some(UdsEntry::Listener(l)) => l,
        Some(_) => return NEG_EBADF,
        None => return NEG_EBADF,
    };
    match listener.accept() {
        Ok((stream, _addr)) => {
            if let Err(e) = stream.set_nonblocking(true) {
                return errno_from_io(&e);
            }
            let cfd = stream.as_raw_fd() as i64;
            reg.insert(cfd, UdsEntry::Stream(stream));
            cfd
        }
        Err(e) => errno_from_io(&e),
    }
}

/// Write `data` to a registered UnixStream. Returns bytes written or negative errno.
///
/// # Safety
/// `data_ptr` must point to `data_len` valid bytes.
#[no_mangle]
pub unsafe extern "C" fn rt_unix_socket_send(fd: i64, data_ptr: i64, data_len: i64) -> i64 {
    if data_ptr == 0 || data_len < 0 {
        return NEG_EINVAL;
    }
    let mut reg = UDS_REGISTRY.lock().unwrap();
    let stream = match reg.get_mut(&fd) {
        Some(UdsEntry::Stream(s)) => s,
        Some(_) => return NEG_EBADF,
        None => return NEG_EBADF,
    };
    let buf = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
    match stream.write(buf) {
        Ok(n) => n as i64,
        Err(e) => errno_from_io(&e),
    }
}

/// Read up to `max_len` bytes from a registered UnixStream into a heap buffer.
/// Writes the resulting length into `*out_len` and returns the buffer pointer
/// (caller frees via `rt_unix_socket_free_buf`). On EOF or EAGAIN returns a
/// valid 0-length buffer with `*out_len = 0`. On error, sets `*out_len` to a
/// negative errno and returns 0.
///
/// # Safety
/// `out_len` must be a writable `*mut i64`.
#[no_mangle]
pub unsafe extern "C" fn rt_unix_socket_recv(fd: i64, max_len: i64, out_len: *mut i64) -> i64 {
    if max_len <= 0 || out_len.is_null() {
        if !out_len.is_null() {
            *out_len = NEG_EINVAL;
        }
        return 0;
    }
    let mut reg = UDS_REGISTRY.lock().unwrap();
    let stream = match reg.get_mut(&fd) {
        Some(UdsEntry::Stream(s)) => s,
        Some(_) => {
            *out_len = NEG_EBADF;
            return 0;
        }
        None => {
            *out_len = NEG_EBADF;
            return 0;
        }
    };
    let mut buf: Vec<u8> = vec![0u8; max_len as usize];
    match stream.read(&mut buf) {
        Ok(n) => {
            buf.truncate(n);
            buf.shrink_to_fit();
            *out_len = n as i64;
            let ptr = buf.as_ptr() as i64;
            std::mem::forget(buf);
            ptr
        }
        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
            *out_len = 0;
            0
        }
        Err(e) => {
            *out_len = errno_from_io(&e);
            0
        }
    }
}

/// Free a buffer returned by `rt_unix_socket_recv`.
///
/// # Safety
/// `ptr`/`len` must be a buffer originally returned by `rt_unix_socket_recv`.
#[no_mangle]
pub unsafe extern "C" fn rt_unix_socket_free_buf(ptr: i64, len: i64) {
    if ptr == 0 || len <= 0 {
        return;
    }
    let _ = Vec::from_raw_parts(ptr as *mut u8, len as usize, len as usize);
}

/// Close a registered UnixListener or UnixStream. Returns 0 on success or
/// `NEG_EBADF` if the fd is unknown.
#[no_mangle]
pub extern "C" fn rt_unix_socket_close(fd: i64) -> i32 {
    let mut reg = UDS_REGISTRY.lock().unwrap();
    match reg.remove(&fd) {
        Some(UdsEntry::Listener(l)) => {
            drop(l); // UnixListener::Drop closes the fd
            0
        }
        Some(UdsEntry::Stream(s)) => {
            drop(s);
            0
        }
        None => NEG_EBADF as i32,
    }
}

// ----------------------------------------------------------------------------
// Client-side (used by std.qemu.qmp_client; impl was missing in the seed runtime)
// ----------------------------------------------------------------------------

/// Connect to a UDS at `path`. Returns fd or negative errno.
///
/// # Safety
/// `path_ptr` must point to `path_len` valid UTF-8 bytes.
#[no_mangle]
pub unsafe extern "C" fn rt_unix_socket_connect(path_ptr: i64, path_len: i64) -> i64 {
    let path = match ptr_to_str(path_ptr, path_len) {
        Some(s) => s,
        None => return NEG_EINVAL,
    };
    match UnixStream::connect(&path) {
        Ok(stream) => {
            if let Err(e) = stream.set_nonblocking(true) {
                return errno_from_io(&e);
            }
            let fd = stream.as_raw_fd() as i64;
            UDS_REGISTRY.lock().unwrap().insert(fd, UdsEntry::Stream(stream));
            fd
        }
        Err(e) => errno_from_io(&e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn listen_accept_send_recv_close_roundtrip() {
        // Avoid tempfile dep — use a /tmp path with the test PID for uniqueness.
        let path = format!("/tmp/sj-net-uds-test-{}.sock", std::process::id());
        let _ = std::fs::remove_file(&path);
        let pp = path.as_ptr() as i64;
        let pl = path.len() as i64;
        let lfd = unsafe { rt_unix_socket_listen(pp, pl, 16) };
        assert!(lfd > 0, "listen returned {lfd}");
        // No connection yet -> EAGAIN
        let r = rt_unix_socket_accept(lfd);
        assert_eq!(r, NEG_EAGAIN);
        // Connect a client
        let cfd = unsafe { rt_unix_socket_connect(pp, pl) };
        assert!(cfd > 0, "connect returned {cfd}");
        // Server-side accept eventually succeeds (small loop for ordering)
        let mut sfd = -1i64;
        for _ in 0..50 {
            let r = rt_unix_socket_accept(lfd);
            if r > 0 {
                sfd = r;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        assert!(sfd > 0, "server-side accept did not succeed");
        // Send + recv
        let payload = b"hello-uds";
        let n = unsafe { rt_unix_socket_send(cfd, payload.as_ptr() as i64, payload.len() as i64) };
        assert_eq!(n, payload.len() as i64);
        let mut out_len: i64 = 0;
        // small loop to allow scheduling
        let mut ptr: i64 = 0;
        for _ in 0..50 {
            ptr = unsafe { rt_unix_socket_recv(sfd, 1024, &mut out_len as *mut i64) };
            if out_len > 0 {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        assert!(out_len > 0, "recv produced no bytes; out_len={out_len}");
        let got = unsafe { std::slice::from_raw_parts(ptr as *const u8, out_len as usize) };
        assert_eq!(got, payload);
        unsafe { rt_unix_socket_free_buf(ptr, out_len) };
        // Close all
        assert_eq!(rt_unix_socket_close(cfd), 0);
        assert_eq!(rt_unix_socket_close(sfd), 0);
        assert_eq!(rt_unix_socket_close(lfd), 0);
    }
}
