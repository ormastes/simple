//! Native cache-daemon authority receipts, version 1.
//!
//! Linux binds authority to a descriptor-anchored cache root, SO_PEERCRED,
//! flock, the kernel boot id, a durable monotonic epoch, and a nonce-bound
//! readiness record. Other hosts deliberately fail closed.

#[cfg(target_os = "linux")]
mod linux {
    use sha2::{Digest, Sha256};
    use std::collections::HashMap;
    use std::io::Read;
    use std::os::fd::RawFd;
    use std::sync::{Mutex, OnceLock};

    const INVALID: i64 = -1;
    const LOCK_NAME: &[u8] = b".simple-cache-writer.lock\0";
    const EPOCH_NAME: &[u8] = b".simple-cache-writer.epoch\0";
    const READY_NAME: &[u8] = b".simple-cache-ready\0";
    const EPOCH_MAGIC: &[u8; 8] = b"SCEPOCH1";
    const READY_MAGIC: &[u8; 8] = b"SCREADY1";

    #[derive(Debug)]
    struct Peer {
        socket_fd: RawFd,
        root_fd: RawFd,
        pid: i32,
        uid: u32,
        root_dev: u64,
        root_ino: u64,
    }
    #[derive(Debug)]
    struct Lock {
        root_fd: RawFd,
        lock_fd: RawFd,
        pid: i32,
        uid: u32,
        root_dev: u64,
        root_ino: u64,
        issued_epoch: u64,
    }
    #[derive(Debug)]
    enum Receipt {
        Peer(Peer),
        Lock(Lock),
        Boot { lock: i64, identity: [u8; 16] },
    }
    static RECEIPTS: OnceLock<Mutex<HashMap<i64, Receipt>>> = OnceLock::new();
    fn receipts() -> &'static Mutex<HashMap<i64, Receipt>> {
        RECEIPTS.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn random_positive() -> Option<i64> {
        let mut bytes = [0u8; 8];
        std::fs::File::open("/dev/urandom").ok()?.read_exact(&mut bytes).ok()?;
        Some((i64::from_ne_bytes(bytes) & i64::MAX).max(1))
    }
    fn insert(receipt: Receipt) -> i64 {
        let mut guard = match receipts().lock() {
            Ok(v) => v,
            Err(_) => return INVALID,
        };
        loop {
            let Some(token) = random_positive() else { return INVALID };
            if let std::collections::hash_map::Entry::Vacant(slot) = guard.entry(token) {
                slot.insert(receipt);
                return token;
            }
        }
    }
    fn fd_identity(fd: RawFd) -> Option<(u64, u64)> {
        let mut stat: libc::stat = unsafe { std::mem::zeroed() };
        if unsafe { libc::fstat(fd, &mut stat) } != 0 || (stat.st_mode & libc::S_IFMT) != libc::S_IFDIR {
            return None;
        }
        Some((stat.st_dev as u64, stat.st_ino as u64))
    }
    fn boot_identity() -> Option<[u8; 16]> {
        let text = std::fs::read_to_string("/proc/sys/kernel/random/boot_id").ok()?;
        let hex: Vec<u8> = text
            .bytes()
            .filter(|b| *b != b'-' && !b.is_ascii_whitespace())
            .collect();
        if hex.len() != 32 {
            return None;
        }
        let mut out = [0u8; 16];
        for index in 0..16 {
            out[index] = (hex_value(hex[index * 2])? << 4) | hex_value(hex[index * 2 + 1])?;
        }
        Some(out)
    }
    fn hex_value(value: u8) -> Option<u8> {
        match value {
            b'0'..=b'9' => Some(value - b'0'),
            b'a'..=b'f' => Some(value - b'a' + 10),
            b'A'..=b'F' => Some(value - b'A' + 10),
            _ => None,
        }
    }
    unsafe fn nonce<'a>(ptr: *const u8, len: i64) -> Option<&'a [u8]> {
        if ptr.is_null() || !(16..=256).contains(&len) {
            None
        } else {
            Some(std::slice::from_raw_parts(ptr, len as usize))
        }
    }
    fn pwrite_all(fd: RawFd, bytes: &[u8]) -> bool {
        let mut offset = 0;
        while offset < bytes.len() {
            let count = unsafe {
                libc::pwrite(
                    fd,
                    bytes[offset..].as_ptr().cast(),
                    bytes.len() - offset,
                    offset as libc::off_t,
                )
            };
            if count <= 0 {
                return false;
            }
            offset += count as usize;
        }
        unsafe { libc::ftruncate(fd, bytes.len() as libc::off_t) == 0 && libc::fsync(fd) == 0 }
    }
    fn pread_exact(fd: RawFd, out: &mut [u8]) -> bool {
        let mut offset = 0;
        while offset < out.len() {
            let count = unsafe {
                libc::pread(
                    fd,
                    out[offset..].as_mut_ptr().cast(),
                    out.len() - offset,
                    offset as libc::off_t,
                )
            };
            if count <= 0 {
                return false;
            }
            offset += count as usize;
        }
        let mut stat: libc::stat = unsafe { std::mem::zeroed() };
        unsafe { libc::fstat(fd, &mut stat) == 0 && stat.st_size == out.len() as libc::off_t }
    }
    fn epoch_bytes(epoch: u64, boot: [u8; 16]) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..8].copy_from_slice(EPOCH_MAGIC);
        out[8..16].copy_from_slice(&epoch.to_le_bytes());
        out[16..32].copy_from_slice(&boot);
        let digest = Sha256::digest(&out[..32]);
        out[32..].copy_from_slice(&digest);
        out
    }
    fn parse_epoch(bytes: &[u8; 64]) -> Option<u64> {
        if &bytes[..8] != EPOCH_MAGIC || Sha256::digest(&bytes[..32])[..] != bytes[32..] {
            return None;
        }
        Some(u64::from_le_bytes(bytes[8..16].try_into().ok()?))
    }
    fn ready_bytes(token: i64, epoch: i64, pid: i32, uid: u32, boot: [u8; 16], nonce: &[u8]) -> [u8; 96] {
        let mut out = [0u8; 96];
        out[..8].copy_from_slice(READY_MAGIC);
        out[8..16].copy_from_slice(&(token as u64).to_le_bytes());
        out[16..24].copy_from_slice(&(epoch as u64).to_le_bytes());
        out[24..28].copy_from_slice(&uid.to_le_bytes());
        out[28..32].copy_from_slice(&pid.to_le_bytes());
        out[32..48].copy_from_slice(&boot);
        out[48..80].copy_from_slice(&Sha256::digest(nonce));
        let sum = Sha256::digest(&out[..80]);
        out[80..].copy_from_slice(&sum[..16]);
        out
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_authenticate_peer_v1(root: i64, transport_peer: i64) -> i64 {
        let Some(root_fd) = crate::cache_host_authority_v1::duplicate_root_fd(root) else {
            return INVALID;
        };
        let fd = transport_peer as RawFd;
        let mut cred: libc::ucred = std::mem::zeroed();
        let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        if fd < 0
            || libc::getsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                (&mut cred as *mut libc::ucred).cast(),
                &mut len,
            ) != 0
            || len as usize != std::mem::size_of::<libc::ucred>()
            || cred.uid != libc::geteuid()
        {
            libc::close(root_fd);
            return INVALID;
        }
        let socket_fd = libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3);
        let Some((root_dev, root_ino)) = fd_identity(root_fd) else {
            libc::close(root_fd);
            return INVALID;
        };
        if socket_fd < 0 {
            libc::close(root_fd);
            return INVALID;
        }
        insert(Receipt::Peer(Peer {
            socket_fd,
            root_fd,
            pid: cred.pid,
            uid: cred.uid,
            root_dev,
            root_ino,
        }))
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_acquire_exclusive_lock_v1(root: i64, peer: i64) -> i64 {
        let Some(root_fd) = crate::cache_host_authority_v1::duplicate_root_fd(root) else {
            return INVALID;
        };
        let Some((dev, ino)) = fd_identity(root_fd) else {
            libc::close(root_fd);
            return INVALID;
        };
        let (pid, uid) = match receipts().lock().ok().and_then(|g| match g.get(&peer) {
            Some(Receipt::Peer(p)) if p.root_dev == dev && p.root_ino == ino => Some((p.pid, p.uid)),
            _ => None,
        }) {
            Some(v) => v,
            None => {
                libc::close(root_fd);
                return INVALID;
            }
        };
        let lock_fd = libc::openat(
            root_fd,
            LOCK_NAME.as_ptr().cast(),
            libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        let mut lock_stat: libc::stat = std::mem::zeroed();
        let lock_is_private_regular = lock_fd >= 0
            && libc::fstat(lock_fd, &mut lock_stat) == 0
            && (lock_stat.st_mode & libc::S_IFMT) == libc::S_IFREG
            && lock_stat.st_nlink == 1
            && lock_stat.st_uid == libc::geteuid();
        if !lock_is_private_regular || libc::flock(lock_fd, libc::LOCK_EX | libc::LOCK_NB) != 0 {
            if lock_fd >= 0 {
                libc::close(lock_fd);
            }
            libc::close(root_fd);
            return INVALID;
        }
        insert(Receipt::Lock(Lock {
            root_fd,
            lock_fd,
            pid: libc::getpid(),
            uid: libc::geteuid(),
            root_dev: dev,
            root_ino: ino,
            issued_epoch: 0,
        }))
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_boot_identity_v1(lock: i64) -> i64 {
        let Some(identity) = boot_identity() else {
            return INVALID;
        };
        let valid = receipts()
            .lock()
            .ok()
            .map(|g| matches!(g.get(&lock), Some(Receipt::Lock(_))))
            .unwrap_or(false);
        if valid {
            insert(Receipt::Boot { lock, identity })
        } else {
            INVALID
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_advance_writer_epoch_v1(lock: i64, boot: i64) -> i64 {
        let current = match boot_identity() {
            Some(v) => v,
            None => return INVALID,
        };
        let root_fd = {
            let guard = match receipts().lock() {
                Ok(v) => v,
                Err(_) => return INVALID,
            };
            match (guard.get(&lock), guard.get(&boot)) {
                (Some(Receipt::Lock(v)), Some(Receipt::Boot { lock: owner, identity }))
                    if *owner == lock && *identity == current =>
                {
                    libc::fcntl(v.root_fd, libc::F_DUPFD_CLOEXEC, 3)
                }
                _ => return INVALID,
            }
        };
        if root_fd < 0 {
            return INVALID;
        }
        let fd = libc::openat(
            root_fd,
            EPOCH_NAME.as_ptr().cast(),
            libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        if fd < 0 {
            libc::close(root_fd);
            return INVALID;
        }
        let mut stat: libc::stat = std::mem::zeroed();
        let valid =
            libc::fstat(fd, &mut stat) == 0 && (stat.st_mode & libc::S_IFMT) == libc::S_IFREG && stat.st_nlink == 1;
        let previous = if valid && stat.st_size == 0 {
            0
        } else if valid && stat.st_size == 64 {
            let mut b = [0u8; 64];
            if !pread_exact(fd, &mut b) {
                libc::close(fd);
                libc::close(root_fd);
                return INVALID;
            }
            match parse_epoch(&b) {
                Some(v) => v,
                None => {
                    libc::close(fd);
                    libc::close(root_fd);
                    return INVALID;
                }
            }
        } else {
            libc::close(fd);
            libc::close(root_fd);
            return INVALID;
        };
        let Some(next) = previous.checked_add(1) else {
            libc::close(fd);
            libc::close(root_fd);
            return INVALID;
        };
        let ok = pwrite_all(fd, &epoch_bytes(next, current)) && libc::fsync(root_fd) == 0;
        libc::close(fd);
        libc::close(root_fd);
        if !ok || next > i64::MAX as u64 {
            return INVALID;
        }
        let updated = receipts().lock().ok().map(|mut guard| {
            match guard.get_mut(&lock) {
                Some(Receipt::Lock(value)) => {
                    value.issued_epoch = next;
                    true
                }
                _ => false,
            }
        }).unwrap_or(false);
        if updated { next as i64 } else { INVALID }
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_publish_readiness_v1(
        lock: i64,
        epoch: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
    ) -> i64 {
        let Some(nonce) = nonce(nonce_ptr, nonce_len) else {
            return INVALID;
        };
        if epoch <= 0 {
            return INVALID;
        }
        let (root_fd, pid, uid) = {
            let guard = match receipts().lock() {
                Ok(v) => v,
                Err(_) => return INVALID,
            };
            match guard.get(&lock) {
                Some(Receipt::Lock(v)) if v.issued_epoch == epoch as u64 => {
                    (libc::fcntl(v.root_fd, libc::F_DUPFD_CLOEXEC, 3), v.pid, v.uid)
                }
                _ => return INVALID,
            }
        };
        if root_fd < 0 {
            return INVALID;
        }
        let Some(token) = random_positive() else {
            libc::close(root_fd);
            return INVALID;
        };
        let Some(boot) = boot_identity() else {
            libc::close(root_fd);
            return INVALID;
        };
        let temp = format!(".simple-cache-ready.{}.tmp\0", token);
        let fd = libc::openat(
            root_fd,
            temp.as_ptr().cast(),
            libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        if fd < 0 {
            libc::close(root_fd);
            return INVALID;
        }
        let mut ok = pwrite_all(fd, &ready_bytes(token, epoch, pid, uid, boot, nonce));
        libc::close(fd);
        if ok {
            ok = libc::renameat(root_fd, temp.as_ptr().cast(), root_fd, READY_NAME.as_ptr().cast()) == 0
                && libc::fsync(root_fd) == 0
        }
        if !ok {
            libc::unlinkat(root_fd, temp.as_ptr().cast(), 0);
        }
        libc::close(root_fd);
        if ok {
            token
        } else {
            INVALID
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_validate_readiness_v1(
        peer: i64,
        readiness: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
        epoch: i64,
    ) -> i64 {
        let Some(nonce) = nonce(nonce_ptr, nonce_len) else {
            return INVALID;
        };
        if readiness <= 0 || epoch <= 0 {
            return INVALID;
        }
        let (root_fd, pid, uid) = {
            let guard = match receipts().lock() {
                Ok(v) => v,
                Err(_) => return INVALID,
            };
            match guard.get(&peer) {
                Some(Receipt::Peer(v)) => (libc::fcntl(v.root_fd, libc::F_DUPFD_CLOEXEC, 3), v.pid, v.uid),
                _ => return INVALID,
            }
        };
        if root_fd < 0 {
            return INVALID;
        }
        let fd = libc::openat(
            root_fd,
            READY_NAME.as_ptr().cast(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        );
        libc::close(root_fd);
        if fd < 0 {
            return INVALID;
        }
        let mut b = [0u8; 96];
        let ok = pread_exact(fd, &mut b);
        libc::close(fd);
        if !ok || &b[..8] != READY_MAGIC || Sha256::digest(&b[..80])[..16] != b[80..] {
            return INVALID;
        }
        let token = u64::from_le_bytes(b[8..16].try_into().unwrap());
        let stored_epoch = u64::from_le_bytes(b[16..24].try_into().unwrap());
        let stored_uid = u32::from_le_bytes(b[24..28].try_into().unwrap());
        let stored_pid = i32::from_le_bytes(b[28..32].try_into().unwrap());
        let Some(boot) = boot_identity() else { return INVALID };
        if token == readiness as u64
            && stored_epoch == epoch as u64
            && stored_uid == uid
            && stored_pid == pid
            && b[32..48] == boot
            && b[48..80] == Sha256::digest(nonce)[..]
        {
            1
        } else {
            INVALID
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_release_daemon_receipt_v1(handle: i64) -> i64 {
        let receipt = match receipts().lock() {
            Ok(mut v) => v.remove(&handle),
            Err(_) => None,
        };
        match receipt {
            Some(Receipt::Peer(v)) => {
                let a = libc::close(v.socket_fd);
                let b = libc::close(v.root_fd);
                if a == 0 && b == 0 {
                    0
                } else {
                    INVALID
                }
            }
            Some(Receipt::Boot { .. }) => 0,
            Some(Receipt::Lock(v)) => {
                libc::unlinkat(v.root_fd, READY_NAME.as_ptr().cast(), 0);
                libc::fsync(v.root_fd);
                libc::flock(v.lock_fd, libc::LOCK_UN);
                let a = libc::close(v.lock_fd);
                let b = libc::close(v.root_fd);
                if a == 0 && b == 0 {
                    0
                } else {
                    INVALID
                }
            }
            None => INVALID,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::cache_host_authority_v1::{rt_cache_host_close_v1, rt_cache_host_open_root_v1};
        use std::os::unix::ffi::OsStrExt;
        #[test]
        fn authority_is_exclusive_durable_nonce_bound_and_releasable() {
            unsafe {
                let dir = tempfile::tempdir().unwrap();
                let p = dir.path().as_os_str().as_bytes();
                let root = rt_cache_host_open_root_v1(p.as_ptr(), p.len() as i64);
                let mut sockets = [0; 2];
                assert_eq!(
                    libc::socketpair(
                        libc::AF_UNIX,
                        libc::SOCK_STREAM | libc::SOCK_CLOEXEC,
                        0,
                        sockets.as_mut_ptr()
                    ),
                    0
                );
                let peer = rt_cache_host_authenticate_peer_v1(root, sockets[0] as i64);
                let lock = rt_cache_host_acquire_exclusive_lock_v1(root, peer);
                assert!(peer > 0 && lock > 0);
                assert_eq!(rt_cache_host_acquire_exclusive_lock_v1(root, peer), INVALID);
                let boot = rt_cache_host_boot_identity_v1(lock);
                let epoch = rt_cache_host_advance_writer_epoch_v1(lock, boot);
                let n = b"0123456789abcdef";
                let ready = rt_cache_host_publish_readiness_v1(lock, epoch, n.as_ptr(), 16);
                assert_eq!(
                    rt_cache_host_validate_readiness_v1(peer, ready, n.as_ptr(), 16, epoch),
                    1
                );
                assert_eq!(
                    rt_cache_host_validate_readiness_v1(peer, ready, b"fedcba9876543210".as_ptr(), 16, epoch),
                    INVALID
                );
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(lock), 0);
                assert!(!dir.path().join(".simple-cache-ready").exists());
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(peer), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(boot), 0);
                libc::close(sockets[0]);
                libc::close(sockets[1]);
                rt_cache_host_close_v1(root);
            }
        }
    }
}
#[cfg(target_os = "linux")]
pub use linux::*;

#[cfg(not(target_os = "linux"))]
mod unsupported {
    const UNSUPPORTED: i64 = -1;
    macro_rules! f{($n:ident($($a:ident:$t:ty),*))=>{#[no_mangle]pub unsafe extern "C" fn $n($($a:$t),*)->i64{$(let _=$a;)*UNSUPPORTED}};}
    f!(rt_cache_host_authenticate_peer_v1(root:i64,transport_peer:i64));
    f!(rt_cache_host_acquire_exclusive_lock_v1(root:i64,peer:i64));
    f!(rt_cache_host_boot_identity_v1(lock:i64));
    f!(rt_cache_host_advance_writer_epoch_v1(lock:i64,boot:i64));
    f!(rt_cache_host_publish_readiness_v1(lock:i64,epoch:i64,nonce:*const u8,nonce_len:i64));
    f!(rt_cache_host_validate_readiness_v1(peer:i64,readiness:i64,nonce:*const u8,nonce_len:i64,epoch:i64));
    f!(rt_cache_host_release_daemon_receipt_v1(handle:i64));
}
#[cfg(not(target_os = "linux"))]
pub use unsupported::*;
