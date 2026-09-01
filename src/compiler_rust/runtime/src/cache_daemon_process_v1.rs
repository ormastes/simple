//! Bounded, fail-closed cache-daemon transport.
//!
//! The socket and lock are rooted below an already selected absolute cache
//! directory.  A client performs one connect, at most one launch and one
//! reconnect.  Failure always selects the descriptor-anchored spool lane.

#[cfg(target_os = "linux")]
mod unix {
    use sha2::{Digest, Sha256};
    use std::ffi::OsStr;
    use std::io::{Read, Write};
    use std::os::fd::{AsRawFd, FromRawFd, RawFd};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::path::{Path, PathBuf};
    use std::time::{Duration, Instant};

    const INVALID: i64 = -1;
    const ROUTE_DAEMON: i64 = 1;
    const ROUTE_SPOOL: i64 = 2;
    const CONNECT_BUDGET_MS: i32 = 250;
    const IDLE_MIN_MS: u64 = 10_000;
    const IDLE_MAX_MS: u64 = 12_000;
    const SOCKET_NAME: &str = ".simple-cache-daemon-v1.sock";
    const LOCK_NAME: &[u8] = b".simple-cache-daemon-v1.lock\0";
    const REQ_MAGIC: &[u8; 8] = b"SCREQV1\0";
    const ACK_MAGIC: &[u8; 8] = b"SCACKV1\0";

    fn bytes<'a>(p: *const u8, n: i64) -> Option<&'a [u8]> {
        if p.is_null() || n <= 0 || n > 32_768 {
            return None;
        }
        Some(unsafe { std::slice::from_raw_parts(p, n as usize) })
    }

    fn absolute_root(p: *const u8, n: i64) -> Option<PathBuf> {
        let raw = bytes(p, n)?;
        if raw.contains(&0) {
            return None;
        }
        let path = PathBuf::from(OsStr::from_bytes(raw));
        if !path.is_absolute() {
            return None;
        }
        Some(path)
    }

    fn open_root_checked(path: &Path) -> RawFd {
        let mut v = path.as_os_str().as_bytes().to_vec();
        v.push(0);
        unsafe {
            libc::open(
                v.as_ptr().cast(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        }
    }

    fn socket_path(root_fd: RawFd) -> PathBuf {
        PathBuf::from(format!("/proc/self/fd/{root_fd}/{SOCKET_NAME}"))
    }

    fn random_nonce() -> Option<[u8; 32]> {
        let mut out = [0u8; 32];
        let rc = unsafe { libc::getrandom(out.as_mut_ptr().cast(), out.len(), 0) };
        (rc == out.len() as isize).then_some(out)
    }

    fn peer(stream: &UnixStream) -> Option<(u32, i32)> {
        let mut cred: libc::ucred = unsafe { std::mem::zeroed() };
        let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        let rc = unsafe {
            libc::getsockopt(
                stream.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                (&mut cred as *mut libc::ucred).cast(),
                &mut len,
            )
        };
        (rc == 0 && len as usize == std::mem::size_of::<libc::ucred>()).then_some((cred.uid, cred.pid))
    }

    fn exchange(mut stream: UnixStream) -> bool {
        let io_budget = Some(Duration::from_millis(50));
        if stream.set_read_timeout(io_budget).is_err() || stream.set_write_timeout(io_budget).is_err() {
            return false;
        }
        let Some(nonce) = random_nonce() else { return false };
        let mut req = [0u8; 40];
        req[..8].copy_from_slice(REQ_MAGIC);
        req[8..].copy_from_slice(&nonce);
        if stream.write_all(&req).is_err() {
            return false;
        }
        let mut ack = [0u8; 80];
        if stream.read_exact(&mut ack).is_err() || &ack[..8] != ACK_MAGIC || ack[8..40] != nonce {
            return false;
        }
        let Some((uid, pid)) = peer(&stream) else { return false };
        let ack_pid = i32::from_le_bytes(ack[40..44].try_into().unwrap());
        let ack_uid = u32::from_le_bytes(ack[44..48].try_into().unwrap());
        let digest = Sha256::digest(&ack[..48]);
        uid == unsafe { libc::geteuid() } && uid == ack_uid && pid == ack_pid && digest[..32] == ack[48..80]
    }

    fn try_connect(root_fd: RawFd) -> bool {
        UnixStream::connect(socket_path(root_fd)).ok().is_some_and(exchange)
    }

    fn anchored_spool(root_fd: RawFd) -> bool {
        unsafe {
            if libc::mkdirat(root_fd, b"spool\0".as_ptr().cast(), 0o700) != 0
                && *libc::__errno_location() != libc::EEXIST
            {
                return false;
            }
            let fd = libc::openat(
                root_fd,
                b"spool\0".as_ptr().cast(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            );
            if fd < 0 {
                return false;
            }
            let ok = libc::fsync(fd) == 0;
            libc::close(fd);
            ok
        }
    }

    fn lock(root_fd: RawFd) -> RawFd {
        unsafe {
            let fd = libc::openat(
                root_fd,
                LOCK_NAME.as_ptr().cast(),
                libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0o600,
            );
            if fd < 0 || libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) != 0 {
                if fd >= 0 {
                    libc::close(fd);
                }
                return -1;
            }
            fd
        }
    }

    fn advance_epoch(lock_fd: RawFd) -> Option<u64> {
        let mut raw = [0u8; 8];
        let read = unsafe { libc::pread(lock_fd, raw.as_mut_ptr().cast(), raw.len(), 0) };
        let previous = if read == raw.len() as isize {
            u64::from_le_bytes(raw)
        } else {
            0
        };
        let next = previous.checked_add(1)?;
        let encoded = next.to_le_bytes();
        let written = unsafe { libc::pwrite(lock_fd, encoded.as_ptr().cast(), encoded.len(), 0) };
        if written != encoded.len() as isize || unsafe { libc::fdatasync(lock_fd) } != 0 {
            return None;
        }
        Some(next)
    }

    fn serve_client(mut stream: UnixStream, epoch: u64) -> bool {
        let io_budget = Some(Duration::from_millis(50));
        if stream.set_read_timeout(io_budget).is_err() || stream.set_write_timeout(io_budget).is_err() {
            return false;
        }
        let Some((uid, _)) = peer(&stream) else { return false };
        if uid != unsafe { libc::geteuid() } {
            return false;
        }
        let mut req = [0u8; 40];
        if stream.read_exact(&mut req).is_err() || &req[..8] != REQ_MAGIC {
            return false;
        }
        let mut ack = [0u8; 80];
        ack[..8].copy_from_slice(ACK_MAGIC);
        ack[8..40].copy_from_slice(&req[8..40]);
        ack[40..44].copy_from_slice(&(unsafe { libc::getpid() }).to_le_bytes());
        ack[44..48].copy_from_slice(&(unsafe { libc::geteuid() }).to_le_bytes());
        let digest = Sha256::digest(&ack[..48]);
        ack[48..].copy_from_slice(&digest);
        let _ = epoch; // Epoch remains lock-owned; journal operations bind it separately.
        stream.write_all(&ack).is_ok()
    }

    fn serve(root_fd: RawFd, ready_fd: RawFd, idle_min_ms: u64, idle_max_ms: u64) -> i64 {
        let lock_fd = lock(root_fd);
        if lock_fd < 0 {
            return INVALID;
        }
        let Some(epoch) = advance_epoch(lock_fd) else {
            unsafe {
                libc::flock(lock_fd, libc::LOCK_UN);
                libc::close(lock_fd);
            }
            return INVALID;
        };
        let sock = socket_path(root_fd);
        unsafe {
            libc::unlinkat(root_fd, format!("{SOCKET_NAME}\0").as_ptr().cast(), 0);
        }
        let listener = match UnixListener::bind(&sock) {
            Ok(v) => v,
            Err(_) => {
                unsafe { libc::close(lock_fd) };
                return INVALID;
            }
        };
        unsafe {
            libc::fchmodat(root_fd, format!("{SOCKET_NAME}\0").as_ptr().cast(), 0o600, 0);
        }
        if listener.set_nonblocking(true).is_err() {
            return INVALID;
        }
        if ready_fd >= 0 {
            unsafe {
                libc::write(ready_fd, b"R".as_ptr().cast(), 1);
                libc::close(ready_fd);
            }
        }
        let mut idle_since = Instant::now();
        loop {
            let elapsed = idle_since.elapsed();
            if elapsed >= Duration::from_millis(idle_min_ms) {
                break;
            }
            let remain = Duration::from_millis(idle_min_ms).saturating_sub(elapsed);
            let wait = remain.min(Duration::from_millis(idle_max_ms));
            let mut pfd = libc::pollfd {
                fd: listener.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            let rc = unsafe { libc::poll(&mut pfd, 1, wait.as_millis().min(i32::MAX as u128) as i32) };
            if rc < 0 {
                break;
            }
            if rc == 0 {
                continue;
            }
            while let Ok((stream, _)) = listener.accept() {
                let _ = serve_client(stream, epoch);
                idle_since = Instant::now();
            }
        }
        drop(listener);
        unsafe {
            libc::unlinkat(root_fd, format!("{SOCKET_NAME}\0").as_ptr().cast(), 0);
            libc::fsync(root_fd); // checkpoint before releasing writer receipt
            libc::flock(lock_fd, libc::LOCK_UN);
            libc::close(lock_fd);
        }
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_daemon_serve_v1(path: *const u8, len: i64) -> i64 {
        let Some(root) = absolute_root(path, len) else {
            return INVALID;
        };
        let root_fd = open_root_checked(&root);
        if root_fd < 0 {
            return INVALID;
        }
        let rc = serve(root_fd, -1, IDLE_MIN_MS, IDLE_MAX_MS);
        libc::close(root_fd);
        rc
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_daemon_route_v1(path: *const u8, len: i64) -> i64 {
        let Some(root) = absolute_root(path, len) else {
            return INVALID;
        };
        let root_fd = open_root_checked(&root);
        if root_fd < 0 {
            return INVALID;
        }
        if try_connect(root_fd) {
            libc::close(root_fd);
            return ROUTE_DAEMON;
        }
        let mut signal = [0; 2];
        if libc::pipe2(signal.as_mut_ptr(), libc::O_CLOEXEC) == 0 {
            let pid = libc::fork();
            if pid == 0 {
                libc::close(signal[0]);
                let rc = serve(root_fd, signal[1], IDLE_MIN_MS, IDLE_MAX_MS);
                libc::_exit(if rc == 0 { 0 } else { 1 });
            }
            libc::close(signal[1]);
            if pid > 0 {
                let mut pfd = libc::pollfd {
                    fd: signal[0],
                    events: libc::POLLIN,
                    revents: 0,
                };
                let _ = libc::poll(&mut pfd, 1, CONNECT_BUDGET_MS);
                let mut byte = 0u8;
                let ready = libc::read(signal[0], (&mut byte as *mut u8).cast(), 1) == 1 && byte == b'R';
                libc::close(signal[0]);
                if ready && try_connect(root_fd) {
                    libc::close(root_fd);
                    return ROUTE_DAEMON;
                }
            } else {
                libc::close(signal[0]);
            }
        }
        let spool = anchored_spool(root_fd);
        libc::close(root_fd);
        if spool {
            ROUTE_SPOOL
        } else {
            INVALID
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::os::unix::net::UnixListener;

        #[test]
        fn hostile_socket_is_replaced_by_locked_authenticated_daemon_within_budget() {
            let dir = tempfile::tempdir().unwrap();
            let fd = open_root_checked(dir.path());
            let hostile = UnixListener::bind(socket_path(fd)).unwrap();
            let start = Instant::now();
            let bytes = dir.path().as_os_str().as_bytes();
            let route = unsafe { rt_cache_daemon_route_v1(bytes.as_ptr(), bytes.len() as i64) };
            assert_eq!(route, ROUTE_DAEMON);
            assert!(start.elapsed() < Duration::from_millis(500));
            drop(hostile);
            unsafe { libc::close(fd) };
        }

        #[test]
        fn singleton_handshake_and_idle_exit_are_process_real() {
            let dir = tempfile::tempdir().unwrap();
            let fd = open_root_checked(dir.path());
            let mut signal = [0; 2];
            unsafe { assert_eq!(libc::pipe2(signal.as_mut_ptr(), libc::O_CLOEXEC), 0) };
            let child_fd = fd;
            let join = std::thread::spawn(move || serve(child_fd, signal[1], 100, 120));
            let mut b = 0u8;
            unsafe { assert_eq!(libc::read(signal[0], (&mut b as *mut u8).cast(), 1), 1) };
            assert!(try_connect(fd));
            assert_eq!(lock(fd), -1);
            assert_eq!(join.join().unwrap(), 0);
            assert!(!socket_path(fd).exists());
            unsafe {
                libc::close(signal[0]);
                libc::close(fd);
            }
        }

        #[test]
        #[ignore = "production idle timing takes at least ten seconds"]
        fn production_idle_exit_respects_ten_to_twelve_second_contract() {
            let dir = tempfile::tempdir().unwrap();
            let fd = open_root_checked(dir.path());
            let mut signal = [0; 2];
            unsafe { assert_eq!(libc::pipe2(signal.as_mut_ptr(), libc::O_CLOEXEC), 0) };
            let child_fd = fd;
            let start = Instant::now();
            let join = std::thread::spawn(move || {
                serve(child_fd, signal[1], IDLE_MIN_MS, IDLE_MAX_MS)
            });
            let mut ready = 0u8;
            unsafe {
                assert_eq!(libc::read(signal[0], (&mut ready as *mut u8).cast(), 1), 1)
            };
            assert!(try_connect(fd));
            assert_eq!(join.join().unwrap(), 0);
            let elapsed = start.elapsed();
            assert!(elapsed >= Duration::from_millis(IDLE_MIN_MS));
            assert!(elapsed <= Duration::from_millis(IDLE_MAX_MS + 1_000));
            assert!(!socket_path(fd).exists());
            unsafe {
                libc::close(signal[0]);
                libc::close(fd);
            }
        }

        #[test]
        fn killed_daemon_leaves_no_authority_and_restart_is_equivalent() {
            let dir = tempfile::tempdir().unwrap();
            let fd = open_root_checked(dir.path());
            let mut first = [0; 2];
            unsafe { assert_eq!(libc::pipe2(first.as_mut_ptr(), libc::O_CLOEXEC), 0) };
            let pid = unsafe { libc::fork() };
            if pid == 0 {
                unsafe { libc::close(first[0]) };
                let rc = serve(fd, first[1], 10_000, 12_000);
                unsafe { libc::_exit(if rc == 0 { 0 } else { 1 }) }
            }
            let mut b = 0u8;
            unsafe { assert_eq!(libc::read(first[0], (&mut b as *mut u8).cast(), 1), 1) };
            assert!(try_connect(fd));
            unsafe {
                libc::kill(pid, libc::SIGKILL);
                libc::waitpid(pid, std::ptr::null_mut(), 0);
                libc::close(first[0]);
            }
            assert!(!try_connect(fd));

            let mut second = [0; 2];
            unsafe { assert_eq!(libc::pipe2(second.as_mut_ptr(), libc::O_CLOEXEC), 0) };
            let child_fd = fd;
            let join = std::thread::spawn(move || serve(child_fd, second[1], 100, 120));
            unsafe { assert_eq!(libc::read(second[0], (&mut b as *mut u8).cast(), 1), 1) };
            assert!(try_connect(fd));
            assert_eq!(join.join().unwrap(), 0);
            unsafe {
                libc::close(second[0]);
                libc::close(fd);
            }
        }

        #[test]
        fn unavailable_singleton_falls_back_to_anchored_spool_within_budget() {
            let dir = tempfile::tempdir().unwrap();
            let fd = open_root_checked(dir.path());
            let mut signal = [0; 2];
            unsafe { assert_eq!(libc::pipe2(signal.as_mut_ptr(), libc::O_CLOEXEC), 0) };
            let holder = unsafe { libc::fork() };
            if holder == 0 {
                unsafe { libc::close(signal[0]) };
                let held = lock(fd);
                if held >= 0 {
                    unsafe {
                        libc::write(signal[1], b"L".as_ptr().cast(), 1);
                        libc::sleep(2);
                        libc::_exit(0)
                    }
                }
                unsafe { libc::_exit(1) }
            }
            let mut ready = 0u8;
            unsafe { assert_eq!(libc::read(signal[0], (&mut ready as *mut u8).cast(), 1), 1) };
            let bytes = dir.path().as_os_str().as_bytes();
            let start = Instant::now();
            let route = unsafe { rt_cache_daemon_route_v1(bytes.as_ptr(), bytes.len() as i64) };
            assert_eq!(route, ROUTE_SPOOL);
            assert!(start.elapsed() <= Duration::from_millis(CONNECT_BUDGET_MS as u64));
            unsafe {
                libc::kill(holder, libc::SIGKILL);
                libc::waitpid(holder, std::ptr::null_mut(), 0);
                libc::close(signal[0]);
                libc::close(fd);
            }
        }
    }
}

#[cfg(target_os = "linux")]
pub use unix::*;

#[cfg(not(target_os = "linux"))]
mod unsupported {
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_daemon_serve_v1(_: *const u8, _: i64) -> i64 {
        -1
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_daemon_route_v1(_: *const u8, _: i64) -> i64 {
        -1
    }
}
#[cfg(not(target_os = "linux"))]
pub use unsupported::*;
