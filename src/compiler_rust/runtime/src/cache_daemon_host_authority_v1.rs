//! Native cache-daemon authority receipts, version 1.
//!
//! Linux binds authority to a descriptor-anchored cache root, SO_PEERCRED,
//! flock, the kernel boot id, a durable monotonic epoch, and a nonce-bound
//! readiness record. Other hosts deliberately fail closed.

#[cfg(target_os = "linux")]
mod linux {
    use sha2::{Digest, Sha256};
    use std::collections::HashMap;
    use std::ffi::CString;
    use std::io::Read;
    use std::os::fd::RawFd;
    use std::sync::{Arc, Mutex, OnceLock};

    const INVALID: i64 = -1;
    const LOCK_NAME: &[u8] = b".simple-cache-writer.lock\0";
    const EPOCH_NAME: &[u8] = b".simple-cache-writer.epoch\0";
    const READY_NAME: &[u8] = b".simple-cache-ready\0";
    const JOURNAL_NAME: &[u8] = b".simple-action-root.journal-v1\0";
    const EPOCH_MAGIC: &[u8; 8] = b"SCEPOCH1";
    const READY_MAGIC: &[u8; 8] = b"SCREADY1";
    const MAX_JOURNAL_BYTES: i64 = 16 * 1024 * 1024;
    // Admission remains closed until every canonical CAS namespace mutator
    // participates in the same cross-process exclusion protocol.  An
    // authenticated writer lock is necessary, but is not by itself proof that
    // publishers outside this module cooperate.
    const GC_COOPERATIVE_NAMESPACE_ADMITTED: bool = false;
    const MAX_APPEND_BYTES: i64 = 64 * 1024;
    const GC_NAMESPACE_LOCK_NAME: &[u8] = b".simple-cache-gc-v2.lock\0";
    const GC_READER_EPOCH_NAME: &[u8] = b".simple-cache-gc-v2.epoch\0";
    const GC_MAX_ROOTS: i64 = 65_536;
    const GC_MAX_PAGE_BYTES: i64 = 1024 * 1024;
    const GC_MAX_CANDIDATES: i64 = 65_536;

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
        mutation_gate: Arc<Mutex<()>>,
        active_gc_window: Option<i64>,
    }
    #[derive(Debug)]
    struct DurableHeadV2 {
        lock: i64,
        peer: i64,
        readiness: i64,
        readiness_nonce: Vec<u8>,
        writer_epoch: i64,
        root_fd: RawFd,
        root_dev: u64,
        root_ino: u64,
        journal_fd: RawFd,
        journal_dev: u64,
        journal_ino: u64,
        journal_bytes: i64,
        journal_digest: [u8; 32],
        journal_generation: i64,
        selected_superblock_generation: i64,
        selected_superblock_digest: [u8; 32],
        root_count: i64,
        active_window: Option<i64>,
    }
    #[derive(Debug)]
    struct GcWindowV2 {
        lock: i64,
        head: i64,
        root_fd: RawFd,
        namespace_lock_fd: RawFd,
        epoch_fd: RawFd,
        odd_epoch: i64,
        journal_bytes: i64,
        root_count: i64,
        max_page_bytes: i64,
        max_candidates: i64,
        candidate_count: i64,
        pending_even_epoch: Option<i64>,
    }
    #[derive(Debug)]
    struct GcCandidateV2 {
        window: i64,
        object_fd: RawFd,
        parent_fd: RawFd,
        leaf: CString,
        device: u64,
        inode: u64,
    }
    #[derive(Debug)]
    enum Receipt {
        Peer(Peer),
        Lock(Lock),
        Boot { lock: i64, identity: [u8; 16] },
        DurableHeadV2(DurableHeadV2),
        GcWindowV2(GcWindowV2),
        GcCandidateV2(GcCandidateV2),
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
    fn regular_identity(fd: RawFd) -> Option<(u64, u64, i64)> {
        let mut stat: libc::stat = unsafe { std::mem::zeroed() };
        if unsafe { libc::fstat(fd, &mut stat) } != 0
            || (stat.st_mode & libc::S_IFMT) != libc::S_IFREG
            || stat.st_nlink != 1
            || stat.st_uid != unsafe { libc::geteuid() }
            || stat.st_size < 0
        {
            return None;
        }
        Some((stat.st_dev as u64, stat.st_ino as u64, stat.st_size))
    }
    fn lower_hex(bytes: &[u8], length: usize) -> bool {
        bytes.len() == length
            && bytes
                .iter()
                .all(|value| value.is_ascii_digit() || (b'a'..=b'f').contains(value))
    }
    fn cache_kind(bytes: &[u8]) -> bool {
        matches!(
            bytes,
            b"source_blob" | b"compile_snapshot" | b"public_summary" | b"file_ast" | b"semantic_read_set"
        )
    }
    fn read_gc_epoch(fd: RawFd) -> Option<i64> {
        let (_, _, size) = regular_identity(fd)?;
        if size != 8 {
            return None;
        }
        let mut raw = [0u8; 8];
        if unsafe { libc::pread(fd, raw.as_mut_ptr().cast(), raw.len(), 0) } != raw.len() as isize {
            return None;
        }
        let value = i64::from_le_bytes(raw);
        (value >= 0).then_some(value)
    }
    fn write_gc_epoch(fd: RawFd, value: i64) -> bool {
        if value < 0 {
            return false;
        }
        let raw = value.to_le_bytes();
        unsafe {
            libc::pwrite(fd, raw.as_ptr().cast(), raw.len(), 0) == raw.len() as isize
                && libc::ftruncate(fd, raw.len() as libc::off_t) == 0
                && libc::fsync(fd) == 0
        }
    }
    unsafe fn open_gc_namespace(root_fd: RawFd, expected_even: i64) -> Option<(RawFd, RawFd, i64)> {
        if expected_even < 0 || expected_even % 2 != 0 || expected_even > i64::MAX - 2 {
            return None;
        }
        let lock_fd = libc::openat(
            root_fd,
            GC_NAMESPACE_LOCK_NAME.as_ptr().cast(),
            libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        if lock_fd < 0 || regular_identity(lock_fd).is_none() {
            if lock_fd >= 0 {
                libc::close(lock_fd);
            }
            return None;
        }
        // Nonblocking is deliberate: a live reader retains its shared flock,
        // so collection refuses instead of hiding a potentially unbounded wait.
        if libc::flock(lock_fd, libc::LOCK_EX | libc::LOCK_NB) != 0 {
            libc::close(lock_fd);
            return None;
        }
        let epoch_fd = libc::openat(
            root_fd,
            GC_READER_EPOCH_NAME.as_ptr().cast(),
            libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        if epoch_fd < 0 || regular_identity(epoch_fd).is_none() {
            if epoch_fd >= 0 {
                libc::close(epoch_fd);
            }
            libc::flock(lock_fd, libc::LOCK_UN);
            libc::close(lock_fd);
            return None;
        }
        let size = match regular_identity(epoch_fd) {
            Some((_, _, value)) => value,
            None => {
                libc::close(epoch_fd);
                libc::flock(lock_fd, libc::LOCK_UN);
                libc::close(lock_fd);
                return None;
            }
        };
        if size == 0 && !write_gc_epoch(epoch_fd, expected_even) {
            libc::close(epoch_fd);
            libc::flock(lock_fd, libc::LOCK_UN);
            libc::close(lock_fd);
            return None;
        }
        if read_gc_epoch(epoch_fd) != Some(expected_even) {
            libc::close(epoch_fd);
            libc::flock(lock_fd, libc::LOCK_UN);
            libc::close(lock_fd);
            return None;
        }
        let odd = expected_even.checked_add(1)?;
        if !write_gc_epoch(epoch_fd, odd) || libc::fsync(root_fd) != 0 {
            let _ = write_gc_epoch(epoch_fd, expected_even);
            libc::close(epoch_fd);
            libc::flock(lock_fd, libc::LOCK_UN);
            libc::close(lock_fd);
            return None;
        }
        Some((lock_fd, epoch_fd, odd))
    }
    fn mutation_gate(lock: i64) -> Option<Arc<Mutex<()>>> {
        receipts().lock().ok().and_then(|guard| match guard.get(&lock) {
            Some(Receipt::Lock(value)) => Some(value.mutation_gate.clone()),
            _ => None,
        })
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
    unsafe fn digest32(ptr: *const u8, len: i64) -> Option<[u8; 32]> {
        if ptr.is_null() || len != 64 {
            return None;
        }
        let encoded = std::slice::from_raw_parts(ptr, len as usize);
        let mut out = [0u8; 32];
        for index in 0..32 {
            out[index] = (hex_value(encoded[index * 2])? << 4) | hex_value(encoded[index * 2 + 1])?;
        }
        Some(out)
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
            mutation_gate: Arc::new(Mutex::new(())),
            active_gc_window: None,
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
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
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
                    if *owner == lock && *identity == current && v.active_gc_window.is_none() =>
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
        let updated = receipts()
            .lock()
            .ok()
            .map(|mut guard| match guard.get_mut(&lock) {
                Some(Receipt::Lock(value)) => {
                    value.issued_epoch = next;
                    true
                }
                _ => false,
            })
            .unwrap_or(false);
        if updated {
            next as i64
        } else {
            INVALID
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_publish_readiness_v1(
        lock: i64,
        epoch: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
    ) -> i64 {
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
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
                Some(Receipt::Lock(v)) if v.issued_epoch == epoch as u64 && v.active_gc_window.is_none() => {
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
    pub extern "C" fn rt_cache_host_mutation_scope_available_v1() -> i64 {
        1
    }

    fn mutation_root_fd(lock: i64, peer: i64, epoch: i64) -> Option<RawFd> {
        let guard = receipts().lock().ok()?;
        match (guard.get(&lock), guard.get(&peer)) {
            (Some(Receipt::Lock(owner)), Some(Receipt::Peer(caller)))
                if epoch > 0
                    && owner.issued_epoch == epoch as u64
                    && owner.active_gc_window.is_none()
                    && owner.root_dev == caller.root_dev
                    && owner.root_ino == caller.root_ino =>
            {
                let fd = unsafe { libc::fcntl(owner.root_fd, libc::F_DUPFD_CLOEXEC, 3) };
                if fd >= 0 {
                    Some(fd)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn pread_range(fd: RawFd, offset: i64, out: &mut [u8]) -> bool {
        let mut copied = 0usize;
        while copied < out.len() {
            let count = unsafe {
                libc::pread(
                    fd,
                    out[copied..].as_mut_ptr().cast(),
                    out.len() - copied,
                    offset as libc::off_t + copied as libc::off_t,
                )
            };
            if count <= 0 {
                return false;
            }
            copied += count as usize;
        }
        true
    }

    fn journal_prefix_digest(fd: RawFd, length: i64) -> Option<[u8; 32]> {
        if !(0..=MAX_JOURNAL_BYTES).contains(&length) {
            return None;
        }
        let mut hasher = Sha256::new();
        let mut offset = 0i64;
        let mut buffer = [0u8; 4096];
        while offset < length {
            let wanted = std::cmp::min(buffer.len() as i64, length - offset) as usize;
            if !pread_range(fd, offset, &mut buffer[..wanted]) {
                return None;
            }
            hasher.update(&buffer[..wanted]);
            offset += wanted as i64;
        }
        Some(hasher.finalize().into())
    }

    unsafe fn named_journal_matches(
        root_fd: RawFd,
        expected_dev: u64,
        expected_ino: u64,
        expected_bytes: i64,
        expected_digest: [u8; 32],
    ) -> bool {
        let fd = libc::openat(
            root_fd,
            JOURNAL_NAME.as_ptr().cast(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        if fd < 0 {
            return false;
        }
        let matches = regular_identity(fd)
            .is_some_and(|(dev, ino, size)| dev == expected_dev && ino == expected_ino && size == expected_bytes)
            && journal_prefix_digest(fd, expected_bytes) == Some(expected_digest);
        libc::close(fd);
        matches
    }

    // The host owns only exclusion, exact-offset byte append and durability.
    // Simple owns record semantics, operation identity, replay and recovery.
    // 1 = appended, 2 = exact retry/partial-tail completion, 0 = stale head,
    // -2 = append may have reached durable authority, -1 = invalid/unsupported.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_commit_journal_v1(
        lock: i64,
        peer: i64,
        readiness: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
        epoch: i64,
        expected_bytes: i64,
        expected_prefix_digest_ptr: *const u8,
        expected_prefix_digest_len: i64,
        append_ptr: *const u8,
        append_len: i64,
    ) -> i64 {
        let Some(nonce_bytes) = nonce(nonce_ptr, nonce_len) else {
            return INVALID;
        };
        let Some(expected_prefix_digest) = digest32(expected_prefix_digest_ptr, expected_prefix_digest_len) else {
            return INVALID;
        };
        if append_ptr.is_null()
            || append_len <= 0
            || append_len > MAX_APPEND_BYTES
            || expected_bytes < 0
            || expected_bytes > MAX_JOURNAL_BYTES - append_len
        {
            return INVALID;
        }
        let append = std::slice::from_raw_parts(append_ptr, append_len as usize);
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let Some(root_fd) = mutation_root_fd(lock, peer, epoch) else {
            return INVALID;
        };
        if rt_cache_host_validate_readiness_v1(peer, readiness, nonce_bytes.as_ptr(), nonce_bytes.len() as i64, epoch)
            != 1
        {
            libc::close(root_fd);
            return INVALID;
        }
        let fd = libc::openat(
            root_fd,
            JOURNAL_NAME.as_ptr().cast(),
            libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        );
        if fd < 0 {
            libc::close(root_fd);
            return INVALID;
        }
        let mut stat: libc::stat = std::mem::zeroed();
        let valid = libc::fstat(fd, &mut stat) == 0
            && (stat.st_mode & libc::S_IFMT) == libc::S_IFREG
            && stat.st_nlink == 1
            && stat.st_uid == libc::geteuid()
            && stat.st_size >= expected_bytes
            && stat.st_size <= expected_bytes + append_len;
        if !valid {
            libc::close(fd);
            libc::close(root_fd);
            return 0;
        }
        if journal_prefix_digest(fd, expected_bytes) != Some(expected_prefix_digest) {
            libc::close(fd);
            libc::close(root_fd);
            return 0;
        }
        let present = stat.st_size - expected_bytes;
        if present > 0 {
            let mut prior = vec![0u8; present as usize];
            if !pread_range(fd, expected_bytes, &mut prior) || prior.as_slice() != &append[..present as usize] {
                libc::close(fd);
                libc::close(root_fd);
                return 0;
            }
        }
        let mut offset = present as usize;
        let mut mutated = false;
        while offset < append.len() {
            let count = libc::pwrite(
                fd,
                append[offset..].as_ptr().cast(),
                append.len() - offset,
                expected_bytes as libc::off_t + offset as libc::off_t,
            );
            if count <= 0 {
                libc::close(fd);
                libc::close(root_fd);
                return if mutated { -2 } else { INVALID };
            }
            mutated = true;
            offset += count as usize;
        }
        let durable =
            libc::ftruncate(fd, expected_bytes + append_len) == 0 && libc::fsync(fd) == 0 && libc::fsync(root_fd) == 0;
        libc::close(fd);
        libc::close(root_fd);
        if !durable {
            -2
        } else if present == 0 {
            1
        } else {
            2
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_read_journal_v1(
        lock: i64,
        peer: i64,
        readiness: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
        epoch: i64,
        out_ptr: *mut u8,
        out_capacity: i64,
    ) -> i64 {
        let Some(nonce_bytes) = nonce(nonce_ptr, nonce_len) else {
            return INVALID;
        };
        if out_capacity < 0 || out_capacity > MAX_JOURNAL_BYTES || (out_capacity > 0 && out_ptr.is_null()) {
            return INVALID;
        }
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let Some(root_fd) = mutation_root_fd(lock, peer, epoch) else {
            return INVALID;
        };
        if rt_cache_host_validate_readiness_v1(peer, readiness, nonce_bytes.as_ptr(), nonce_bytes.len() as i64, epoch)
            != 1
        {
            libc::close(root_fd);
            return INVALID;
        }
        let fd = libc::openat(
            root_fd,
            JOURNAL_NAME.as_ptr().cast(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        );
        libc::close(root_fd);
        if fd < 0 {
            return if *libc::__errno_location() == libc::ENOENT {
                0
            } else {
                INVALID
            };
        }
        let mut before: libc::stat = std::mem::zeroed();
        let size_limit = if out_capacity == 0 {
            MAX_JOURNAL_BYTES
        } else {
            out_capacity
        };
        let valid = libc::fstat(fd, &mut before) == 0
            && (before.st_mode & libc::S_IFMT) == libc::S_IFREG
            && before.st_nlink == 1
            && before.st_uid == libc::geteuid()
            && before.st_size >= 0
            && before.st_size <= size_limit;
        if !valid {
            libc::close(fd);
            return INVALID;
        }
        if out_capacity == 0 {
            libc::close(fd);
            return before.st_size;
        }
        let out = std::slice::from_raw_parts_mut(out_ptr, before.st_size as usize);
        let ok = pread_range(fd, 0, out);
        let mut after: libc::stat = std::mem::zeroed();
        let stable = libc::fstat(fd, &mut after) == 0
            && before.st_dev == after.st_dev
            && before.st_ino == after.st_ino
            && before.st_size == after.st_size
            && before.st_mtime == after.st_mtime
            && before.st_ctime == after.st_ctime;
        libc::close(fd);
        if ok && stable {
            before.st_size
        } else {
            INVALID
        }
    }

    fn pread_vec(fd: RawFd, length: i64) -> Option<Vec<u8>> {
        if !(0..=MAX_JOURNAL_BYTES).contains(&length) {
            return None;
        }
        let mut out = vec![0u8; length as usize];
        if !out.is_empty() && !pread_range(fd, 0, &mut out) {
            return None;
        }
        Some(out)
    }

    /// Capture a writer-issued physical head. The caller is the canonical
    /// Simple writer, which has already decoded the prefix and selected the
    /// superblock. The host independently binds those semantic selections to
    /// the live writer receipts and exact anchored journal bytes.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_capture_durable_head_v2(
        lock: i64,
        peer: i64,
        readiness: i64,
        nonce_ptr: *const u8,
        nonce_len: i64,
        writer_epoch: i64,
        expected_journal_bytes: i64,
        expected_journal_digest_ptr: *const u8,
        expected_journal_digest_len: i64,
        journal_generation: i64,
        selected_superblock_generation: i64,
        selected_superblock_digest_ptr: *const u8,
        selected_superblock_digest_len: i64,
        root_count: i64,
    ) -> i64 {
        let Some(nonce_bytes) = nonce(nonce_ptr, nonce_len) else {
            return INVALID;
        };
        let (Some(expected_journal_digest), Some(selected_superblock_digest)) = (
            digest32(expected_journal_digest_ptr, expected_journal_digest_len),
            digest32(selected_superblock_digest_ptr, selected_superblock_digest_len),
        ) else {
            return INVALID;
        };
        if !(0..=MAX_JOURNAL_BYTES).contains(&expected_journal_bytes)
            || journal_generation < 0
            || selected_superblock_generation < 0
            || !(0..=GC_MAX_ROOTS).contains(&root_count)
        {
            return INVALID;
        }
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let Some(root_fd) = mutation_root_fd(lock, peer, writer_epoch) else {
            return INVALID;
        };
        if rt_cache_host_validate_readiness_v1(
            peer,
            readiness,
            nonce_bytes.as_ptr(),
            nonce_bytes.len() as i64,
            writer_epoch,
        ) != 1
        {
            libc::close(root_fd);
            return INVALID;
        }
        let Some((root_dev, root_ino)) = fd_identity(root_fd) else {
            libc::close(root_fd);
            return INVALID;
        };
        let journal_fd = libc::openat(
            root_fd,
            JOURNAL_NAME.as_ptr().cast(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        );
        if journal_fd < 0 {
            libc::close(root_fd);
            return INVALID;
        }
        let Some((journal_dev, journal_ino, size)) = regular_identity(journal_fd) else {
            libc::close(journal_fd);
            libc::close(root_fd);
            return INVALID;
        };
        if size != expected_journal_bytes {
            libc::close(journal_fd);
            libc::close(root_fd);
            return 0;
        }
        let (Some(actual_digest), Some(output_bytes)) = (
            journal_prefix_digest(journal_fd, expected_journal_bytes),
            pread_vec(journal_fd, expected_journal_bytes),
        ) else {
            libc::close(journal_fd);
            libc::close(root_fd);
            return INVALID;
        };
        if actual_digest != expected_journal_digest {
            libc::close(journal_fd);
            libc::close(root_fd);
            return 0;
        }
        let stable = regular_identity(journal_fd).is_some_and(|(dev, ino, current_size)| {
            dev == journal_dev && ino == journal_ino && current_size == expected_journal_bytes
        }) && Sha256::digest(&output_bytes)[..] == expected_journal_digest;
        if !stable {
            libc::close(journal_fd);
            libc::close(root_fd);
            return 0;
        }
        insert(Receipt::DurableHeadV2(DurableHeadV2 {
            lock,
            peer,
            readiness,
            readiness_nonce: nonce_bytes.to_vec(),
            writer_epoch,
            root_fd,
            root_dev,
            root_ino,
            journal_fd,
            journal_dev,
            journal_ino,
            journal_bytes: expected_journal_bytes,
            journal_digest: expected_journal_digest,
            journal_generation,
            selected_superblock_generation,
            selected_superblock_digest,
            root_count,
            active_window: None,
        }))
    }

    /// Atomically bind the descriptor-rooted durable head to one odd reader
    /// epoch and one live writer. Journal and superblock scalars are accepted
    /// only by capture above; this mutation boundary accepts the opaque head.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_begin_v2(
        root: i64,
        durable_head: i64,
        expected_even_reader_epoch: i64,
        max_root_count: i64,
        max_page_bytes: i64,
        max_candidates: i64,
    ) -> i64 {
        if expected_even_reader_epoch < 0
            || expected_even_reader_epoch % 2 != 0
            || expected_even_reader_epoch > i64::MAX - 2
            || !(0..=GC_MAX_ROOTS).contains(&max_root_count)
            || !(1..=GC_MAX_PAGE_BYTES).contains(&max_page_bytes)
            || !(0..=GC_MAX_CANDIDATES).contains(&max_candidates)
        {
            return INVALID;
        }
        let (
            lock,
            peer,
            readiness,
            readiness_nonce,
            writer_epoch,
            root_dev,
            root_ino,
            journal_dev,
            journal_ino,
            journal_fd,
            journal_bytes,
            journal_digest,
            root_count,
        ) = {
            let guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            match guard.get(&durable_head) {
                Some(Receipt::DurableHeadV2(head)) if head.active_window.is_none() => (
                    head.lock,
                    head.peer,
                    head.readiness,
                    head.readiness_nonce.clone(),
                    head.writer_epoch,
                    head.root_dev,
                    head.root_ino,
                    head.journal_dev,
                    head.journal_ino,
                    libc::fcntl(head.journal_fd, libc::F_DUPFD_CLOEXEC, 3),
                    head.journal_bytes,
                    head.journal_digest,
                    head.root_count,
                ),
                _ => return INVALID,
            }
        };
        if journal_fd < 0 || root_count > max_root_count {
            if journal_fd >= 0 {
                libc::close(journal_fd);
            }
            return INVALID;
        }
        let Some(gate) = mutation_gate(lock) else {
            libc::close(journal_fd);
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else {
            libc::close(journal_fd);
            return INVALID;
        };
        if rt_cache_host_validate_readiness_v1(
            peer,
            readiness,
            readiness_nonce.as_ptr(),
            readiness_nonce.len() as i64,
            writer_epoch,
        ) != 1
        {
            libc::close(journal_fd);
            return INVALID;
        }
        let root_fd = match crate::cache_host_authority_v1::duplicate_root_fd(root) {
            Some(fd) => fd,
            None => {
                libc::close(journal_fd);
                return INVALID;
            }
        };
        let journal_stable = regular_identity(journal_fd)
            .is_some_and(|(dev, ino, size)| dev == journal_dev && ino == journal_ino && size == journal_bytes)
            && journal_prefix_digest(journal_fd, journal_bytes) == Some(journal_digest);
        let named_journal_stable =
            named_journal_matches(root_fd, journal_dev, journal_ino, journal_bytes, journal_digest);
        if fd_identity(root_fd) != Some((root_dev, root_ino)) || !journal_stable || !named_journal_stable {
            libc::close(root_fd);
            libc::close(journal_fd);
            return 0;
        }
        let lock_live = receipts().lock().ok().is_some_and(|guard| {
            matches!(guard.get(&lock), Some(Receipt::Lock(owner))
                if owner.issued_epoch == writer_epoch as u64
                    && owner.active_gc_window.is_none()
                    && owner.root_dev == root_dev
                    && owner.root_ino == root_ino)
                && matches!(guard.get(&durable_head), Some(Receipt::DurableHeadV2(head))
                    if head.active_window.is_none())
        });
        if !lock_live {
            libc::close(root_fd);
            libc::close(journal_fd);
            return INVALID;
        }
        if !GC_COOPERATIVE_NAMESPACE_ADMITTED {
            libc::close(root_fd);
            libc::close(journal_fd);
            return 0;
        }
        let Some((namespace_lock_fd, reader_epoch_fd, odd_epoch)) =
            open_gc_namespace(root_fd, expected_even_reader_epoch)
        else {
            libc::close(root_fd);
            libc::close(journal_fd);
            return 0;
        };
        let handle = match random_positive() {
            Some(value) => value,
            None => {
                let _ = write_gc_epoch(reader_epoch_fd, expected_even_reader_epoch);
                libc::close(reader_epoch_fd);
                libc::flock(namespace_lock_fd, libc::LOCK_UN);
                libc::close(namespace_lock_fd);
                libc::close(root_fd);
                libc::close(journal_fd);
                return INVALID;
            }
        };
        let inserted = receipts().lock().ok().is_some_and(|mut guard| {
            if guard.contains_key(&handle) {
                return false;
            }
            let valid = matches!(guard.get(&lock), Some(Receipt::Lock(owner))
                    if owner.active_gc_window.is_none() && owner.issued_epoch == writer_epoch as u64)
                && matches!(guard.get(&durable_head), Some(Receipt::DurableHeadV2(head))
                    if head.active_window.is_none());
            if !valid {
                return false;
            }
            guard.insert(
                handle,
                Receipt::GcWindowV2(GcWindowV2 {
                    lock,
                    head: durable_head,
                    root_fd,
                    namespace_lock_fd,
                    epoch_fd: reader_epoch_fd,
                    odd_epoch,
                    journal_bytes,
                    root_count,
                    max_page_bytes,
                    max_candidates,
                    candidate_count: 0,
                    pending_even_epoch: None,
                }),
            );
            if let Some(Receipt::Lock(owner)) = guard.get_mut(&lock) {
                owner.active_gc_window = Some(handle);
            }
            if let Some(Receipt::DurableHeadV2(head)) = guard.get_mut(&durable_head) {
                head.active_window = Some(handle);
            }
            true
        });
        if !inserted {
            let _ = write_gc_epoch(reader_epoch_fd, expected_even_reader_epoch);
            libc::close(reader_epoch_fd);
            libc::flock(namespace_lock_fd, libc::LOCK_UN);
            libc::close(namespace_lock_fd);
            libc::close(root_fd);
            libc::close(journal_fd);
            return INVALID;
        }
        libc::close(journal_fd);
        handle
    }

    /// Page the exact writer-admitted journal prefix while the opaque window
    /// owns exclusion. Simple performs record decoding and semantic traversal.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_root_page_v2(
        window: i64,
        byte_cursor: i64,
        out_ptr: *mut u8,
        out_capacity: i64,
    ) -> i64 {
        if byte_cursor < 0 || out_capacity <= 0 || out_ptr.is_null() {
            return INVALID;
        }
        let (fd, total, page_limit) = {
            let guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            match guard.get(&window) {
                Some(Receipt::GcWindowV2(value)) => match guard.get(&value.head) {
                    Some(Receipt::DurableHeadV2(head)) => (
                        libc::fcntl(head.journal_fd, libc::F_DUPFD_CLOEXEC, 3),
                        value.journal_bytes,
                        value.max_page_bytes,
                    ),
                    _ => return INVALID,
                },
                _ => return INVALID,
            }
        };
        if fd < 0 || byte_cursor > total || out_capacity > page_limit {
            if fd >= 0 {
                libc::close(fd);
            }
            return INVALID;
        }
        let wanted = std::cmp::min(out_capacity, total - byte_cursor) as usize;
        let out = std::slice::from_raw_parts_mut(out_ptr, wanted);
        let ok = wanted == 0 || pread_range(fd, byte_cursor, out);
        libc::close(fd);
        if ok {
            wanted as i64
        } else {
            INVALID
        }
    }

    /// Successful begin owns the exclusive reader namespace, therefore the
    /// complete live-pin page is empty. A live pin makes begin return busy
    /// instead of being omitted from a fabricated snapshot.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_pin_page_v2(
        window: i64,
        cursor: i64,
        out_ptr: *mut u8,
        out_capacity: i64,
    ) -> i64 {
        if cursor != 0 || out_capacity < 0 || (out_capacity > 0 && out_ptr.is_null()) {
            return INVALID;
        }
        let _ = out_ptr;
        if receipts()
            .lock()
            .ok()
            .is_some_and(|guard| matches!(guard.get(&window), Some(Receipt::GcWindowV2(_))))
        {
            0
        } else {
            INVALID
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_open_candidate_v2(
        window: i64,
        kind_ptr: *const u8,
        kind_len: i64,
        digest_ptr: *const u8,
        digest_len: i64,
    ) -> i64 {
        if kind_ptr.is_null() || digest_ptr.is_null() || kind_len <= 0 || digest_len != 64 {
            return INVALID;
        }
        let kind = std::slice::from_raw_parts(kind_ptr, kind_len as usize);
        let digest = std::slice::from_raw_parts(digest_ptr, digest_len as usize);
        if !cache_kind(kind) || !lower_hex(digest, 64) {
            return INVALID;
        }
        let lock = match receipts().lock().ok().and_then(|guard| match guard.get(&window) {
            Some(Receipt::GcWindowV2(value)) => Some(value.lock),
            _ => None,
        }) {
            Some(value) => value,
            None => return INVALID,
        };
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let (root_fd, current_candidates, max_candidates) = {
            let guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            let Some(Receipt::GcWindowV2(value)) = guard.get(&window) else {
                return INVALID;
            };
            (
                libc::fcntl(value.root_fd, libc::F_DUPFD_CLOEXEC, 3),
                value.candidate_count,
                value.max_candidates,
            )
        };
        if root_fd < 0 || current_candidates >= max_candidates {
            if root_fd >= 0 {
                libc::close(root_fd);
            }
            return INVALID;
        }
        let cas = CString::new("cas").unwrap();
        let kind_name = match CString::new(kind) {
            Ok(value) => value,
            Err(_) => {
                libc::close(root_fd);
                return INVALID;
            }
        };
        let first = CString::new(&digest[..2]).unwrap();
        let second = CString::new(&digest[2..4]).unwrap();
        let leaf = CString::new(&digest[4..]).unwrap();
        let cas_fd = libc::openat(
            root_fd,
            cas.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        libc::close(root_fd);
        if cas_fd < 0 {
            return INVALID;
        }
        let kind_fd = libc::openat(
            cas_fd,
            kind_name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        libc::close(cas_fd);
        if kind_fd < 0 {
            return INVALID;
        }
        let first_fd = libc::openat(
            kind_fd,
            first.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        libc::close(kind_fd);
        if first_fd < 0 {
            return INVALID;
        }
        let parent_fd = libc::openat(
            first_fd,
            second.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        libc::close(first_fd);
        if parent_fd < 0 {
            return INVALID;
        }
        let fd = libc::openat(
            parent_fd,
            leaf.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        if fd < 0 {
            libc::close(parent_fd);
            return INVALID;
        }
        let Some((dev, ino, _)) = regular_identity(fd) else {
            libc::close(fd);
            libc::close(parent_fd);
            return INVALID;
        };
        let candidate = insert(Receipt::GcCandidateV2(GcCandidateV2 {
            window,
            object_fd: fd,
            parent_fd,
            leaf,
            device: dev,
            inode: ino,
        }));
        if candidate > 0 {
            if let Ok(mut guard) = receipts().lock() {
                if let Some(Receipt::GcWindowV2(value)) = guard.get_mut(&window) {
                    value.candidate_count += 1;
                }
            }
        }
        candidate
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_unlink_candidate_v2(window: i64, candidate: i64) -> i64 {
        let lock = match receipts().lock().ok().and_then(|guard| match guard.get(&window) {
            Some(Receipt::GcWindowV2(value)) => Some(value.lock),
            _ => None,
        }) {
            Some(value) => value,
            None => return INVALID,
        };
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let (epoch_fd, object_fd, parent_fd, leaf, expected_device, expected_inode, expected_odd) = {
            let guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            let Some(Receipt::GcWindowV2(scope)) = guard.get(&window) else {
                return INVALID;
            };
            let Some(Receipt::GcCandidateV2(object)) = guard.get(&candidate) else {
                return INVALID;
            };
            if object.window != window {
                return INVALID;
            }
            (
                libc::fcntl(scope.epoch_fd, libc::F_DUPFD_CLOEXEC, 3),
                libc::fcntl(object.object_fd, libc::F_DUPFD_CLOEXEC, 3),
                libc::fcntl(object.parent_fd, libc::F_DUPFD_CLOEXEC, 3),
                object.leaf.clone(),
                object.device,
                object.inode,
                scope.odd_epoch,
            )
        };
        if epoch_fd < 0 || object_fd < 0 || parent_fd < 0 {
            if epoch_fd >= 0 {
                libc::close(epoch_fd);
            }
            if object_fd >= 0 {
                libc::close(object_fd);
            }
            if parent_fd >= 0 {
                libc::close(parent_fd);
            }
            return INVALID;
        }
        let Some((device, inode, _)) = regular_identity(object_fd) else {
            libc::close(epoch_fd);
            libc::close(object_fd);
            libc::close(parent_fd);
            return INVALID;
        };
        let mut named: libc::stat = std::mem::zeroed();
        let valid = read_gc_epoch(epoch_fd) == Some(expected_odd)
            && device == expected_device
            && inode == expected_inode
            && libc::fstatat(parent_fd, leaf.as_ptr(), &mut named, libc::AT_SYMLINK_NOFOLLOW) == 0
            && (named.st_mode & libc::S_IFMT) == libc::S_IFREG
            && named.st_dev as u64 == expected_device
            && named.st_ino as u64 == expected_inode;
        libc::close(epoch_fd);
        libc::close(object_fd);
        if !valid {
            libc::close(parent_fd);
            return 0;
        }
        let unlinked = libc::unlinkat(parent_fd, leaf.as_ptr(), 0) == 0 && libc::fsync(parent_fd) == 0;
        libc::close(parent_fd);
        if !unlinked {
            return INVALID;
        }
        let entry = receipts().lock().ok().and_then(|mut guard| guard.remove(&candidate));
        if let Some(Receipt::GcCandidateV2(object)) = entry {
            libc::close(object.object_fd);
            libc::close(object.parent_fd);
            1
        } else {
            INVALID
        }
    }

    unsafe fn end_gc_window_v2(window: i64, expected_odd_epoch: i64, abort: bool) -> i64 {
        if expected_odd_epoch < 0 || expected_odd_epoch % 2 != 1 {
            return INVALID;
        }
        let lock = match receipts().lock().ok().and_then(|guard| match guard.get(&window) {
            Some(Receipt::GcWindowV2(value)) => Some(value.lock),
            _ => None,
        }) {
            Some(value) => value,
            None => return INVALID,
        };
        let Some(gate) = mutation_gate(lock) else {
            return INVALID;
        };
        let Ok(_mutation) = gate.lock() else { return INVALID };
        let even_epoch = match expected_odd_epoch.checked_add(1) {
            Some(value) => value,
            None => return INVALID,
        };
        let (reader_epoch_fd, durable_head, pending_even, has_candidates) = {
            let guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            let Some(Receipt::GcWindowV2(value)) = guard.get(&window) else {
                return INVALID;
            };
            if value.odd_epoch != expected_odd_epoch {
                return 0;
            }
            let candidates = guard
                .values()
                .any(|entry| matches!(entry, Receipt::GcCandidateV2(candidate) if candidate.window == window));
            let (epoch_fd, head, pending) = (value.epoch_fd, value.head, value.pending_even_epoch);
            if !matches!(guard.get(&lock), Some(Receipt::Lock(owner))
                if owner.active_gc_window == Some(window))
                || !matches!(guard.get(&head), Some(Receipt::DurableHeadV2(owner))
                    if owner.active_window == Some(window))
                || (!abort && candidates)
            {
                return 0;
            }
            if pending.is_some() && pending != Some(even_epoch) {
                return INVALID;
            }
            (epoch_fd, head, pending, candidates)
        };
        let disk_epoch = read_gc_epoch(reader_epoch_fd);
        if disk_epoch != Some(expected_odd_epoch)
            && !(pending_even == Some(even_epoch) && disk_epoch == Some(even_epoch))
        {
            return 0;
        }
        if disk_epoch == Some(expected_odd_epoch) {
            let mut guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            if !matches!(guard.get(&window), Some(Receipt::GcWindowV2(value))
                if value.odd_epoch == expected_odd_epoch
                    && (value.pending_even_epoch.is_none()
                        || value.pending_even_epoch == Some(even_epoch)))
            {
                return INVALID;
            }
            if let Some(Receipt::GcWindowV2(value)) = guard.get_mut(&window) {
                value.pending_even_epoch = Some(even_epoch);
            }
        }
        let transitioned = if disk_epoch == Some(even_epoch) {
            libc::fsync(reader_epoch_fd) == 0
        } else {
            write_gc_epoch(reader_epoch_fd, even_epoch)
        };
        if !transitioned {
            return INVALID;
        }
        let (entry, candidates) = {
            let mut guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            if !matches!(guard.get(&window), Some(Receipt::GcWindowV2(value))
                if value.odd_epoch == expected_odd_epoch
                    && value.pending_even_epoch == Some(even_epoch))
            {
                return INVALID;
            }
            if let Some(Receipt::Lock(owner)) = guard.get_mut(&lock) {
                if owner.active_gc_window != Some(window) {
                    return INVALID;
                }
                owner.active_gc_window = None;
            } else {
                return INVALID;
            }
            if let Some(Receipt::DurableHeadV2(head)) = guard.get_mut(&durable_head) {
                if head.active_window != Some(window) {
                    return INVALID;
                }
                head.active_window = None;
            } else {
                return INVALID;
            }
            let candidates = if abort && has_candidates {
                let ids: Vec<i64> = guard
                    .iter()
                    .filter_map(|(id, entry)| match entry {
                        Receipt::GcCandidateV2(candidate) if candidate.window == window => Some(*id),
                        _ => None,
                    })
                    .collect();
                ids.into_iter().filter_map(|id| guard.remove(&id)).collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            (guard.remove(&window), candidates)
        };
        for entry in candidates {
            if let Receipt::GcCandidateV2(candidate) = entry {
                libc::close(candidate.object_fd);
                libc::close(candidate.parent_fd);
            }
        }
        if let Some(Receipt::GcWindowV2(value)) = entry {
            libc::close(value.epoch_fd);
            libc::flock(value.namespace_lock_fd, libc::LOCK_UN);
            libc::close(value.namespace_lock_fd);
            libc::close(value.root_fd);
            even_epoch
        } else {
            INVALID
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_finish_v2(window: i64, expected_odd_epoch: i64) -> i64 {
        end_gc_window_v2(window, expected_odd_epoch, false)
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_gc_abort_v2(window: i64, expected_odd_epoch: i64) -> i64 {
        end_gc_window_v2(window, expected_odd_epoch, true)
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_release_durable_head_v2(head: i64) -> i64 {
        let entry = {
            let mut guard = match receipts().lock() {
                Ok(value) => value,
                Err(_) => return INVALID,
            };
            if !matches!(guard.get(&head), Some(Receipt::DurableHeadV2(value))
                if value.active_window.is_none())
            {
                return INVALID;
            }
            guard.remove(&head)
        };
        if let Some(Receipt::DurableHeadV2(value)) = entry {
            libc::close(value.journal_fd);
            libc::close(value.root_fd);
            0
        } else {
            INVALID
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_release_daemon_receipt_v1(handle: i64) -> i64 {
        let lock_gate = mutation_gate(handle);
        let _mutation = match lock_gate.as_ref() {
            Some(gate) => match gate.lock() {
                Ok(value) => Some(value),
                Err(_) => return INVALID,
            },
            None => None,
        };
        let receipt = match receipts().lock() {
            Ok(mut v) => {
                let referenced = v.values().any(|entry| match entry {
                    Receipt::DurableHeadV2(head) => head.lock == handle || head.peer == handle,
                    Receipt::GcWindowV2(window) => window.lock == handle,
                    _ => false,
                });
                let protected = matches!(
                    v.get(&handle),
                    Some(Receipt::DurableHeadV2(_)) | Some(Receipt::GcWindowV2(_)) | Some(Receipt::GcCandidateV2(_))
                ) || matches!(v.get(&handle), Some(Receipt::Lock(owner))
                        if owner.active_gc_window.is_some())
                    || referenced;
                if protected {
                    None
                } else {
                    v.remove(&handle)
                }
            }
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
            Some(Receipt::DurableHeadV2(_)) | Some(Receipt::GcWindowV2(_)) | Some(Receipt::GcCandidateV2(_)) => INVALID,
            None => INVALID,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::cache_host_authority_v1::{
            rt_cache_host_begin_reader_pin_v1, rt_cache_host_close_v1, rt_cache_host_open_root_v1,
            rt_cache_host_release_reader_pin_v1,
        };
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
                let frame = b"0|aaaaaaaa|public_summary|bbbbbbbb|cccccccc|checksum\n";
                let empty_digest = b"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
                assert_eq!(
                    rt_cache_host_commit_journal_v1(
                        lock,
                        peer,
                        ready,
                        n.as_ptr(),
                        16,
                        epoch,
                        0,
                        empty_digest.as_ptr(),
                        empty_digest.len() as i64,
                        frame.as_ptr(),
                        frame.len() as i64,
                    ),
                    1
                );
                assert_eq!(
                    rt_cache_host_commit_journal_v1(
                        lock,
                        peer,
                        ready,
                        n.as_ptr(),
                        16,
                        epoch,
                        0,
                        empty_digest.as_ptr(),
                        empty_digest.len() as i64,
                        frame.as_ptr(),
                        frame.len() as i64,
                    ),
                    2
                );
                let divergent_prefix = [b'0'; 64];
                let second = b"1|different\n";
                assert_eq!(
                    rt_cache_host_commit_journal_v1(
                        lock,
                        peer,
                        ready,
                        n.as_ptr(),
                        16,
                        epoch,
                        frame.len() as i64,
                        divergent_prefix.as_ptr(),
                        divergent_prefix.len() as i64,
                        second.as_ptr(),
                        second.len() as i64,
                    ),
                    0
                );
                let mut journal = vec![0u8; 4096];
                assert_eq!(
                    rt_cache_host_read_journal_v1(
                        lock,
                        peer,
                        ready,
                        n.as_ptr(),
                        16,
                        epoch,
                        journal.as_mut_ptr(),
                        journal.len() as i64,
                    ),
                    frame.len() as i64
                );
                assert_eq!(&journal[..frame.len()], frame);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(lock), 0);
                assert!(!dir.path().join(".simple-cache-ready").exists());
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(peer), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(boot), 0);
                libc::close(sockets[0]);
                libc::close(sockets[1]);
                rt_cache_host_close_v1(root);
            }
        }

        #[test]
        fn concurrent_commit_and_revoke_is_all_or_nothing() {
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
                        sockets.as_mut_ptr(),
                    ),
                    0
                );
                let peer = rt_cache_host_authenticate_peer_v1(root, sockets[0] as i64);
                let lock = rt_cache_host_acquire_exclusive_lock_v1(root, peer);
                let boot = rt_cache_host_boot_identity_v1(lock);
                let epoch = rt_cache_host_advance_writer_epoch_v1(lock, boot);
                let nonce = b"0123456789abcdef";
                let ready = rt_cache_host_publish_readiness_v1(lock, epoch, nonce.as_ptr(), 16);
                assert_eq!(
                    rt_cache_host_validate_readiness_v1(peer, ready, nonce.as_ptr(), 16, epoch),
                    1
                );

                let barrier = Arc::new(std::sync::Barrier::new(2));
                let worker_barrier = barrier.clone();
                let worker = std::thread::spawn(move || {
                    let frame = [b'x'; 65536];
                    let nonce = b"0123456789abcdef";
                    let empty_digest = b"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
                    worker_barrier.wait();
                    unsafe {
                        rt_cache_host_commit_journal_v1(
                            lock,
                            peer,
                            ready,
                            nonce.as_ptr(),
                            16,
                            epoch,
                            0,
                            empty_digest.as_ptr(),
                            empty_digest.len() as i64,
                            frame.as_ptr(),
                            frame.len() as i64,
                        )
                    }
                });
                barrier.wait();
                let released = rt_cache_host_release_daemon_receipt_v1(lock);
                let committed = worker.join().unwrap();
                assert_eq!(released, 0);
                assert!(committed == 1 || committed == INVALID);
                let journal = dir.path().join(".simple-action-root.journal-v1");
                let durable_len = std::fs::metadata(journal).map(|m| m.len()).unwrap_or(0);
                assert!(durable_len == 0 || durable_len == 65536);

                assert_eq!(rt_cache_host_release_daemon_receipt_v1(peer), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(boot), 0);
                libc::close(sockets[0]);
                libc::close(sockets[1]);
                rt_cache_host_close_v1(root);
            }
        }

        #[test]
        fn host_gc_v2_refuses_before_epoch_mutation_without_namespace_capability() {
            unsafe {
                let dir = tempfile::tempdir().unwrap();
                let digest = b"aabb0123456789abcdef0123456789abcdef0123456789abcdef0123456789ab";
                let leaf = &digest[4..];
                let candidate_path = dir
                    .path()
                    .join("cas/source_blob/aa/bb")
                    .join(std::str::from_utf8(leaf).unwrap());
                std::fs::create_dir_all(candidate_path.parent().unwrap()).unwrap();
                std::fs::write(&candidate_path, b"candidate").unwrap();

                let path = dir.path().as_os_str().as_bytes();
                let root = rt_cache_host_open_root_v1(path.as_ptr(), path.len() as i64);
                let mut sockets = [0; 2];
                assert_eq!(
                    libc::socketpair(
                        libc::AF_UNIX,
                        libc::SOCK_STREAM | libc::SOCK_CLOEXEC,
                        0,
                        sockets.as_mut_ptr(),
                    ),
                    0
                );
                let peer = rt_cache_host_authenticate_peer_v1(root, sockets[0] as i64);
                let lock = rt_cache_host_acquire_exclusive_lock_v1(root, peer);
                let boot = rt_cache_host_boot_identity_v1(lock);
                let writer_epoch = rt_cache_host_advance_writer_epoch_v1(lock, boot);
                let nonce = b"0123456789abcdef";
                let ready = rt_cache_host_publish_readiness_v1(lock, writer_epoch, nonce.as_ptr(), nonce.len() as i64);
                let frame = b"0|aaaaaaaa|public_summary|bbbbbbbb|cccccccc|checksum\n";
                let empty_digest = b"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
                assert_eq!(
                    rt_cache_host_commit_journal_v1(
                        lock,
                        peer,
                        ready,
                        nonce.as_ptr(),
                        nonce.len() as i64,
                        writer_epoch,
                        0,
                        empty_digest.as_ptr(),
                        empty_digest.len() as i64,
                        frame.as_ptr(),
                        frame.len() as i64,
                    ),
                    1
                );
                let journal_digest = format!("{:x}", Sha256::digest(frame));
                let superblock_digest = b"cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
                let head = rt_cache_host_capture_durable_head_v2(
                    lock,
                    peer,
                    ready,
                    nonce.as_ptr(),
                    nonce.len() as i64,
                    writer_epoch,
                    frame.len() as i64,
                    journal_digest.as_ptr(),
                    journal_digest.len() as i64,
                    7,
                    4,
                    superblock_digest.as_ptr(),
                    superblock_digest.len() as i64,
                    1,
                );
                assert!(head > 0);
                assert_eq!(rt_cache_host_gc_begin_v2(root, head + 1, 8, 1, 4096, 1), INVALID);

                let manifest = b"dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
                let pin = rt_cache_host_begin_reader_pin_v1(
                    root,
                    8,
                    7,
                    manifest.as_ptr(),
                    manifest.len() as i64,
                    b"process".as_ptr(),
                    7,
                    b"boot".as_ptr(),
                    4,
                    b"namespace".as_ptr(),
                    9,
                    100,
                    10,
                );
                assert!(pin > 0);
                assert_eq!(rt_cache_host_gc_begin_v2(root, head, 8, 1, 4096, 1), 0);
                assert_eq!(
                    rt_cache_host_release_reader_pin_v1(
                        pin,
                        8,
                        7,
                        manifest.as_ptr(),
                        manifest.len() as i64,
                        b"process".as_ptr(),
                        7,
                        b"boot".as_ptr(),
                        4,
                        b"namespace".as_ptr(),
                        9,
                    ),
                    0
                );

                if !GC_COOPERATIVE_NAMESPACE_ADMITTED {
                    assert_eq!(rt_cache_host_gc_begin_v2(root, head, 8, 1, 4096, 1), 0);
                    assert!(!dir.path().join(".simple-cache-gc-v2.epoch").exists());
                    assert!(candidate_path.exists());
                    assert_eq!(rt_cache_host_release_durable_head_v2(head), 0);
                    assert_eq!(rt_cache_host_release_daemon_receipt_v1(lock), 0);
                    assert_eq!(rt_cache_host_release_daemon_receipt_v1(peer), 0);
                    assert_eq!(rt_cache_host_release_daemon_receipt_v1(boot), 0);
                    libc::close(sockets[0]);
                    libc::close(sockets[1]);
                    rt_cache_host_close_v1(root);
                    return;
                }

                let window = rt_cache_host_gc_begin_v2(root, head, 8, 1, 4096, 1);
                assert!(window > 0);
                let mut page = [0u8; 4096];
                assert_eq!(
                    rt_cache_host_gc_root_page_v2(window, 0, page.as_mut_ptr(), page.len() as i64),
                    frame.len() as i64
                );
                assert_eq!(&page[..frame.len()], frame);
                assert_eq!(
                    rt_cache_host_gc_pin_page_v2(window, 0, page.as_mut_ptr(), page.len() as i64),
                    0
                );
                let candidate = rt_cache_host_gc_open_candidate_v2(
                    window,
                    b"source_blob".as_ptr(),
                    11,
                    digest.as_ptr(),
                    digest.len() as i64,
                );
                assert!(candidate > 0);
                assert_eq!(rt_cache_host_gc_finish_v2(window, 11), 0);
                assert_eq!(rt_cache_host_gc_unlink_candidate_v2(window, candidate), 1);
                assert!(!candidate_path.exists());
                assert_eq!(rt_cache_host_gc_finish_v2(window, 9), 10);

                let abort_window = rt_cache_host_gc_begin_v2(root, head, 10, 1, 4096, 1);
                assert!(abort_window > 0);
                assert_eq!(rt_cache_host_gc_abort_v2(abort_window, 9), 0);
                assert_eq!(rt_cache_host_gc_abort_v2(abort_window, 11), 12);
                assert_eq!(rt_cache_host_release_durable_head_v2(head), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(lock), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(peer), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(boot), 0);
                libc::close(sockets[0]);
                libc::close(sockets[1]);
                rt_cache_host_close_v1(root);
            }
        }

        #[test]
        fn host_gc_v2_revalidates_the_current_named_journal() {
            unsafe {
                let dir = tempfile::tempdir().unwrap();
                let frame = b"0|root\n";
                std::fs::write(dir.path().join(".simple-action-root.journal-v1"), frame).unwrap();
                let path = dir.path().as_os_str().as_bytes();
                let root = rt_cache_host_open_root_v1(path.as_ptr(), path.len() as i64);
                let mut sockets = [0; 2];
                assert_eq!(
                    libc::socketpair(
                        libc::AF_UNIX,
                        libc::SOCK_STREAM | libc::SOCK_CLOEXEC,
                        0,
                        sockets.as_mut_ptr(),
                    ),
                    0
                );
                let peer = rt_cache_host_authenticate_peer_v1(root, sockets[0] as i64);
                let lock = rt_cache_host_acquire_exclusive_lock_v1(root, peer);
                let boot = rt_cache_host_boot_identity_v1(lock);
                let writer_epoch = rt_cache_host_advance_writer_epoch_v1(lock, boot);
                let nonce = b"0123456789abcdef";
                let ready = rt_cache_host_publish_readiness_v1(lock, writer_epoch, nonce.as_ptr(), 16);
                let journal_digest = format!("{:x}", Sha256::digest(frame));
                let superblock_digest = b"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
                let head = rt_cache_host_capture_durable_head_v2(
                    lock,
                    peer,
                    ready,
                    nonce.as_ptr(),
                    16,
                    writer_epoch,
                    frame.len() as i64,
                    journal_digest.as_ptr(),
                    journal_digest.len() as i64,
                    0,
                    0,
                    superblock_digest.as_ptr(),
                    superblock_digest.len() as i64,
                    1,
                );
                assert!(head > 0);
                let (captured_root_fd, captured_dev, captured_ino, captured_bytes, captured_digest) = {
                    let guard = receipts().lock().unwrap();
                    let Receipt::DurableHeadV2(value) = guard.get(&head).unwrap() else {
                        panic!("durable-head receipt missing")
                    };
                    (
                        libc::fcntl(value.root_fd, libc::F_DUPFD_CLOEXEC, 3),
                        value.journal_dev,
                        value.journal_ino,
                        value.journal_bytes,
                        value.journal_digest,
                    )
                };
                assert!(captured_root_fd >= 0);
                assert!(named_journal_matches(
                    captured_root_fd,
                    captured_dev,
                    captured_ino,
                    captured_bytes,
                    captured_digest,
                ));
                let journal_path = dir.path().join(".simple-action-root.journal-v1");
                std::fs::rename(&journal_path, dir.path().join("old-journal")).unwrap();
                std::fs::write(&journal_path, frame).unwrap();
                assert!(!named_journal_matches(
                    captured_root_fd,
                    captured_dev,
                    captured_ino,
                    captured_bytes,
                    captured_digest,
                ));
                libc::close(captured_root_fd);
                assert_eq!(rt_cache_host_gc_begin_v2(root, head, 0, 1, 4096, 1), 0);
                assert!(!dir.path().join(".simple-cache-gc-v2.epoch").exists());
                assert_eq!(rt_cache_host_release_durable_head_v2(head), 0);
                assert_eq!(rt_cache_host_release_daemon_receipt_v1(lock), 0);
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
    #[no_mangle]
    pub extern "C" fn rt_cache_host_mutation_scope_available_v1() -> i64 {
        UNSUPPORTED
    }
    f!(rt_cache_host_commit_journal_v1(lock:i64,peer:i64,readiness:i64,nonce:*const u8,nonce_len:i64,epoch:i64,expected:i64,prefix:*const u8,prefix_len:i64,append:*const u8,append_len:i64));
    f!(rt_cache_host_read_journal_v1(lock:i64,peer:i64,readiness:i64,nonce:*const u8,nonce_len:i64,epoch:i64,out:*mut u8,cap:i64));
    f!(rt_cache_host_capture_durable_head_v2(lock:i64,peer:i64,readiness:i64,nonce:*const u8,nonce_len:i64,writer_epoch:i64,expected_journal_bytes:i64,expected_journal_digest:*const u8,expected_journal_digest_len:i64,journal_generation:i64,selected_superblock_generation:i64,selected_superblock_digest:*const u8,selected_superblock_digest_len:i64,root_count:i64));
    f!(rt_cache_host_gc_begin_v2(root:i64,durable_head:i64,expected_even_reader_epoch:i64,max_root_count:i64,max_page_bytes:i64,max_candidates:i64));
    f!(rt_cache_host_gc_root_page_v2(window:i64,byte_cursor:i64,out:*mut u8,out_capacity:i64));
    f!(rt_cache_host_gc_pin_page_v2(window:i64,cursor:i64,out:*mut u8,out_capacity:i64));
    f!(rt_cache_host_gc_open_candidate_v2(window:i64,kind:*const u8,kind_len:i64,digest:*const u8,digest_len:i64));
    f!(rt_cache_host_gc_unlink_candidate_v2(window:i64,candidate:i64));
    f!(rt_cache_host_gc_finish_v2(window:i64,expected_odd_epoch:i64));
    f!(rt_cache_host_gc_abort_v2(window:i64,expected_odd_epoch:i64));
    f!(rt_cache_host_release_durable_head_v2(head:i64));
    f!(rt_cache_host_release_daemon_receipt_v1(handle:i64));
}
#[cfg(not(target_os = "linux"))]
pub use unsupported::*;
