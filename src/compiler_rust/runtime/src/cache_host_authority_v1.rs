//! Opaque, descriptor-anchored cache filesystem authority (ABI version 1).
//!
//! Relative names are never treated as security receipts.  Successful reads
//! are authorized by an opened root descriptor and return only after fstat,
//! pread, and fstat have completed on the same object descriptor.

#[cfg(unix)]
mod unix {
    use std::collections::HashMap;
    use std::ffi::CString;
    use std::os::fd::RawFd;
    use std::io::Read;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Mutex, OnceLock};

    const INVALID: i64 = -1;
    static NEXT_TEMP: AtomicU64 = AtomicU64::new(1);
    static HANDLES: OnceLock<Mutex<HashMap<i64, Entry>>> = OnceLock::new();
    #[cfg(test)]
    static READ_TEST_BARRIER: OnceLock<Mutex<Option<std::sync::Arc<std::sync::Barrier>>>> = OnceLock::new();

    #[derive(Debug)]
    enum Entry {
        Root(RawFd),
        Dir(RawFd),
        Read(RawFd),
        Temp { fd: RawFd, root_fd: RawFd, name: CString },
    }

    fn handles() -> &'static Mutex<HashMap<i64, Entry>> {
        HANDLES.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn insert(entry: Entry) -> i64 {
        let mut guard = handles().lock().expect("cache authority handle lock");
        loop {
            let mut bytes = [0u8; 8];
            if std::fs::File::open("/dev/urandom")
                .and_then(|mut f| f.read_exact(&mut bytes))
                .is_err()
            {
                return INVALID;
            }
            let handle = (i64::from_ne_bytes(bytes) & i64::MAX).max(1);
            if let std::collections::hash_map::Entry::Vacant(slot) = guard.entry(handle) {
                slot.insert(entry);
                return handle;
            }
        }
    }

    unsafe fn input(ptr: *const u8, len: i64) -> Option<CString> {
        if ptr.is_null() || len <= 0 || len > 32_768 {
            return None;
        }
        let bytes = std::slice::from_raw_parts(ptr, len as usize);
        if bytes.contains(&0) {
            return None;
        }
        CString::new(bytes).ok()
    }

    fn relative_name(name: &CString) -> bool {
        let b = name.as_bytes();
        !b.is_empty() && b[0] != b'/' && !b.split(|c| *c == b'/').any(|p| p.is_empty() || p == b"." || p == b"..")
    }

    fn dup_fd(fd: RawFd) -> RawFd {
        unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) }
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    fn stat_nsec_equal(a: &libc::stat, b: &libc::stat) -> bool {
        a.st_mtime_nsec == b.st_mtime_nsec && a.st_ctime_nsec == b.st_ctime_nsec
    }

    #[cfg(target_os = "freebsd")]
    fn stat_nsec_equal(a: &libc::stat, b: &libc::stat) -> bool {
        a.st_mtime_nsec == b.st_mtime_nsec && a.st_ctime_nsec == b.st_ctime_nsec
    }

    #[cfg(any(target_os = "macos", target_os = "ios"))]
    fn stat_nsec_equal(a: &libc::stat, b: &libc::stat) -> bool {
        a.st_mtimespec.tv_nsec == b.st_mtimespec.tv_nsec && a.st_ctimespec.tv_nsec == b.st_ctimespec.tv_nsec
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    unsafe fn errno() -> i32 {
        *libc::__errno_location()
    }

    #[cfg(any(target_os = "freebsd", target_os = "macos", target_os = "ios"))]
    unsafe fn errno() -> i32 {
        *libc::__error()
    }

    fn open_beneath(root: RawFd, path: &CString, flags: i32, mode: libc::mode_t) -> RawFd {
        if !relative_name(path) {
            return -1;
        }
        let parts: Vec<&[u8]> = path.as_bytes().split(|c| *c == b'/').collect();
        let mut parent = dup_fd(root);
        if parent < 0 {
            return -1;
        }
        for part in &parts[..parts.len() - 1] {
            let component = CString::new(*part).expect("validated component");
            let next = unsafe {
                libc::openat(
                    parent,
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                )
            };
            unsafe { libc::close(parent) };
            if next < 0 {
                return -1;
            }
            parent = next;
        }
        let leaf = CString::new(parts[parts.len() - 1]).expect("validated leaf");
        let fd = unsafe {
            libc::openat(
                parent,
                leaf.as_ptr(),
                flags | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                mode as libc::c_uint,
            )
        };
        unsafe { libc::close(parent) };
        fd
    }

    fn open_absolute_root(path: &CString) -> RawFd {
        let bytes = path.as_bytes();
        if bytes.first() != Some(&b'/') {
            return -1;
        }
        let mut fd = unsafe {
            libc::open(
                b"/\0".as_ptr().cast(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            return -1;
        }
        for part in bytes[1..].split(|c| *c == b'/') {
            if part.is_empty() || part == b"." || part == b".." {
                unsafe { libc::close(fd) };
                return -1;
            }
            let component = CString::new(part).expect("validated root component");
            let next = unsafe {
                libc::openat(
                    fd,
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                )
            };
            unsafe { libc::close(fd) };
            if next < 0 {
                return -1;
            }
            fd = next;
        }
        fd
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_open_root_v1(path: *const u8, len: i64) -> i64 {
        let Some(path) = input(path, len) else { return INVALID };
        let fd = open_absolute_root(&path);
        if fd < 0 {
            INVALID
        } else {
            insert(Entry::Root(fd))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_open_read_v1(root: i64, path: *const u8, len: i64) -> i64 {
        let Some(path) = input(path, len) else { return INVALID };
        let guard = handles().lock().expect("cache authority handle lock");
        let root_fd = match guard.get(&root) {
            Some(Entry::Root(fd)) | Some(Entry::Dir(fd)) => *fd,
            _ => return INVALID,
        };
        let fd = open_beneath(root_fd, &path, libc::O_RDONLY, 0);
        drop(guard);
        if fd < 0 {
            INVALID
        } else {
            insert(Entry::Read(fd))
        }
    }

    /// Derive a fixed child-directory capability without exposing its path.
    /// Root children are restricted to cache-owned namespaces; descendants are
    /// single canonical shard components.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_open_child_v1(parent: i64, name: *const u8, len: i64, create: i64) -> i64 {
        let Some(name) = input(name, len) else { return INVALID };
        if !relative_name(&name) || name.as_bytes().contains(&b'/') {
            return INVALID;
        }
        let guard = handles().lock().expect("cache authority handle lock");
        let parent_fd = match guard.get(&parent) {
            Some(Entry::Root(fd)) => {
                if !matches!(name.as_bytes(), b"db" | b"cas" | b"journal" | b"spool" | b"quarantine") {
                    return INVALID;
                }
                *fd
            }
            Some(Entry::Dir(fd)) => {
                if name.as_bytes().len() > 64 || !name.as_bytes().iter().all(|b| b.is_ascii_hexdigit() || *b == b'-') {
                    return INVALID;
                }
                *fd
            }
            _ => return INVALID,
        };
        if create != 0 && libc::mkdirat(parent_fd, name.as_ptr(), 0o700) != 0 && errno() != libc::EEXIST {
            return INVALID;
        }
        let fd = libc::openat(
            parent_fd,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        drop(guard);
        if fd < 0 {
            INVALID
        } else {
            insert(Entry::Dir(fd))
        }
    }

    /// Reads exactly one complete bounded file. Returns its complete byte
    /// count, -1 on bounds/I/O failure, or -2 if its same-handle receipt
    /// changed. Partial/chunked reads are deliberately unsupported.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_pread_receipt_v1(handle: i64, offset: i64, out: *mut u8, cap: i64) -> i64 {
        if out.is_null() || offset != 0 || cap < 0 || cap > 64 * 1024 * 1024 {
            return INVALID;
        }
        let guard = handles().lock().expect("cache authority handle lock");
        let fd = match guard.get(&handle) {
            Some(Entry::Read(fd)) => *fd,
            _ => return INVALID,
        };
        let mut before: libc::stat = std::mem::zeroed();
        let mut after: libc::stat = std::mem::zeroed();
        if libc::fstat(fd, &mut before) != 0 || (before.st_mode & libc::S_IFMT) != libc::S_IFREG {
            return INVALID;
        }
        if before.st_size < 0 || before.st_size > cap {
            return INVALID;
        }
        let expected = before.st_size as usize;
        let mut count = 0usize;
        while count < expected {
            let read_len = (expected - count).min(4096);
            let read = libc::pread(fd, out.add(count).cast(), read_len, count as libc::off_t);
            if read <= 0 {
                return INVALID;
            }
            count += read as usize;
            #[cfg(test)]
            if count == read_len && count < expected {
                if let Some(barrier) = READ_TEST_BARRIER
                    .get_or_init(|| Mutex::new(None))
                    .lock()
                    .unwrap()
                    .clone()
                {
                    barrier.wait();
                    barrier.wait();
                }
            }
        }
        let mut verified = 0usize;
        let mut scratch = [0u8; 4096];
        while verified < expected {
            let want = (expected - verified).min(scratch.len());
            let read = libc::pread(fd, scratch.as_mut_ptr().cast(), want, verified as libc::off_t);
            if read != want as isize || std::slice::from_raw_parts(out.add(verified), want) != &scratch[..want] {
                return -2;
            }
            verified += want;
        }
        if libc::fstat(fd, &mut after) != 0 {
            return INVALID;
        }
        if before.st_dev != after.st_dev
            || before.st_ino != after.st_ino
            || before.st_size != after.st_size
            || before.st_mtime != after.st_mtime
            || before.st_ctime != after.st_ctime
            || !stat_nsec_equal(&before, &after)
        {
            -2
        } else {
            expected as i64
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_secure_temp_v1(root: i64) -> i64 {
        let guard = handles().lock().expect("cache authority handle lock");
        let root_fd = match guard.get(&root) {
            Some(Entry::Root(fd)) | Some(Entry::Dir(fd)) => *fd,
            _ => return INVALID,
        };
        let owned_root = dup_fd(root_fd);
        drop(guard);
        if owned_root < 0 {
            return INVALID;
        }
        for _ in 0..128 {
            let serial = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let name = CString::new(format!(".simple-cache-tmp-{}-{serial}", libc::getpid())).expect("temp name");
            let fd = libc::openat(
                owned_root,
                name.as_ptr(),
                libc::O_RDWR | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0o600,
            );
            if fd >= 0 {
                return insert(Entry::Temp {
                    fd,
                    root_fd: owned_root,
                    name,
                });
            }
            if errno() != libc::EEXIST {
                break;
            }
        }
        libc::close(owned_root);
        INVALID
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_write_temp_v1(handle: i64, offset: i64, data: *const u8, len: i64) -> i64 {
        if data.is_null() || offset < 0 || len < 0 || len > 64 * 1024 * 1024 {
            return INVALID;
        }
        let guard = handles().lock().expect("cache authority handle lock");
        let Some(Entry::Temp { fd, .. }) = guard.get(&handle) else {
            return INVALID;
        };
        libc::pwrite(*fd, data.cast(), len as usize, offset as libc::off_t) as i64
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_publish_noreplace_v1(handle: i64, dest: *const u8, len: i64) -> i64 {
        let Some(dest) = input(dest, len) else { return INVALID };
        if !relative_name(&dest) || dest.as_bytes().contains(&b'/') {
            return INVALID;
        }
        let mut guard = handles().lock().expect("cache authority handle lock");
        let Some(Entry::Temp { fd, root_fd, name }) = guard.get(&handle) else {
            return INVALID;
        };
        if libc::fsync(*fd) != 0 || libc::fchmod(*fd, 0o444) != 0 {
            return INVALID;
        }
        #[cfg(target_os = "linux")]
        let rc = libc::syscall(
            libc::SYS_renameat2,
            *root_fd,
            name.as_ptr(),
            *root_fd,
            dest.as_ptr(),
            libc::RENAME_NOREPLACE,
        ) as i32;
        #[cfg(not(target_os = "linux"))]
        let rc = { libc::linkat(*root_fd, name.as_ptr(), *root_fd, dest.as_ptr(), 0) };
        if rc != 0 {
            return if errno() == libc::EEXIST { 0 } else { INVALID };
        }
        #[cfg(not(target_os = "linux"))]
        libc::unlinkat(*root_fd, name.as_ptr(), 0);
        libc::fsync(*root_fd);
        if let Some(Entry::Temp { fd, root_fd, .. }) = guard.remove(&handle) {
            libc::close(fd);
            libc::close(root_fd);
        }
        1
    }

    /// Descriptor-bound quarantine: create a no-replace hard link from the
    /// already-open object, then fsync the root.  The original name is not
    /// unlinked here because doing so by pathname would weaken the receipt.
    #[cfg(target_os = "linux")]
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_quarantine_v1(root: i64, object: i64, dest: *const u8, len: i64) -> i64 {
        let Some(dest) = input(dest, len) else { return INVALID };
        if !relative_name(&dest) || dest.as_bytes().contains(&b'/') {
            return INVALID;
        }
        let guard = handles().lock().expect("cache authority handle lock");
        let root_fd = match guard.get(&root) {
            Some(Entry::Root(fd)) | Some(Entry::Dir(fd)) => *fd,
            _ => return INVALID,
        };
        let Some(Entry::Read(object_fd)) = guard.get(&object) else {
            return INVALID;
        };
        let empty = b"\0";
        let rc = libc::linkat(
            *object_fd,
            empty.as_ptr().cast(),
            root_fd,
            dest.as_ptr(),
            libc::AT_EMPTY_PATH,
        );
        if rc != 0 {
            return if errno() == libc::EEXIST { 0 } else { INVALID };
        }
        libc::fsync(root_fd);
        1
    }

    #[cfg(not(target_os = "linux"))]
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_quarantine_v1(_root: i64, _object: i64, _dest: *const u8, _len: i64) -> i64 {
        // Without AT_EMPTY_PATH this operation cannot stay object-bound.
        INVALID
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_fsync_v1(handle: i64) -> i64 {
        let guard = handles().lock().expect("cache authority handle lock");
        let fd = match guard.get(&handle) {
            Some(Entry::Root(fd)) | Some(Entry::Dir(fd)) | Some(Entry::Read(fd)) | Some(Entry::Temp { fd, .. }) => *fd,
            None => return INVALID,
        };
        if libc::fsync(fd) == 0 {
            1
        } else {
            INVALID
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_close_v1(handle: i64) -> i64 {
        let Some(entry) = handles().lock().expect("cache authority handle lock").remove(&handle) else {
            return INVALID;
        };
        match entry {
            Entry::Root(fd) | Entry::Dir(fd) | Entry::Read(fd) => libc::close(fd) as i64,
            Entry::Temp { fd, root_fd, name } => {
                libc::unlinkat(root_fd, name.as_ptr(), 0);
                libc::close(root_fd);
                libc::close(fd) as i64
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::fs;
        use std::os::unix::fs::symlink;
        use std::sync::{Arc, Barrier};
        use std::thread;

        fn root(path: &std::path::Path) -> i64 {
            let bytes = path.as_os_str().as_encoded_bytes();
            unsafe { rt_cache_host_open_root_v1(bytes.as_ptr(), bytes.len() as i64) }
        }

        #[test]
        fn hostile_ancestor_and_leaf_symlinks_are_rejected() {
            let dir = tempfile::tempdir().unwrap();
            fs::create_dir(dir.path().join("safe")).unwrap();
            fs::write(dir.path().join("safe/object"), b"good").unwrap();
            symlink("safe", dir.path().join("ancestor")).unwrap();
            symlink("object", dir.path().join("safe/leaf")).unwrap();
            symlink("safe", dir.path().join("root-link")).unwrap();
            let linked_root = dir.path().join("root-link");
            assert_eq!(root(&linked_root), INVALID);
            for alias in ["/", "/tmp/", "/tmp//cache", "/tmp/./cache", "/tmp/../cache"] {
                assert_eq!(root(std::path::Path::new(alias)), INVALID);
            }
            let r = root(dir.path());
            for name in [
                b"ancestor/object".as_slice(),
                b"safe/leaf".as_slice(),
                b"../escape".as_slice(),
            ] {
                assert_eq!(
                    unsafe { rt_cache_host_open_read_v1(r, name.as_ptr(), name.len() as i64) },
                    INVALID
                );
            }
            assert_eq!(unsafe { rt_cache_host_close_v1(r) }, 0);
        }

        #[test]
        fn child_capabilities_are_fixed_and_descriptor_anchored() {
            let dir = tempfile::tempdir().unwrap();
            fs::create_dir(dir.path().join("outside")).unwrap();
            symlink("outside", dir.path().join("spool")).unwrap();
            let r = root(dir.path());
            assert_eq!(
                unsafe { rt_cache_host_open_child_v1(r, b"spool".as_ptr(), 5, 1) },
                INVALID
            );
            assert_eq!(
                unsafe { rt_cache_host_open_child_v1(r, b"arbitrary".as_ptr(), 9, 1) },
                INVALID
            );
            fs::remove_file(dir.path().join("spool")).unwrap();
            let cas = unsafe { rt_cache_host_open_child_v1(r, b"cas".as_ptr(), 3, 1) };
            assert!(cas > 0);
            let shard = unsafe { rt_cache_host_open_child_v1(cas, b"a9".as_ptr(), 2, 1) };
            assert!(shard > 0);
            assert_ne!(cas.wrapping_add(1), shard);
            unsafe {
                rt_cache_host_close_v1(shard);
                rt_cache_host_close_v1(cas);
                rt_cache_host_close_v1(r);
            }
        }

        #[test]
        fn concurrent_publish_is_no_replace() {
            let dir = tempfile::tempdir().unwrap();
            let r = root(dir.path());
            let a = unsafe { rt_cache_host_secure_temp_v1(r) };
            let b = unsafe { rt_cache_host_secure_temp_v1(r) };
            let gate = Arc::new(Barrier::new(3));
            let mut joins = Vec::new();
            for h in [a, b] {
                let gate = gate.clone();
                joins.push(thread::spawn(move || {
                    gate.wait();
                    unsafe { rt_cache_host_publish_noreplace_v1(h, b"object".as_ptr(), 6) }
                }));
            }
            gate.wait();
            let results: Vec<i64> = joins.into_iter().map(|j| j.join().unwrap()).collect();
            assert_eq!(results.iter().filter(|v| **v == 1).count(), 1);
            assert_eq!(results.iter().filter(|v| **v == 0).count(), 1);
            unsafe {
                rt_cache_host_close_v1(r);
            }
        }

        #[test]
        fn same_size_same_second_multi_chunk_mutation_is_rejected() {
            let dir = tempfile::tempdir().unwrap();
            let object_path = dir.path().join("object");
            fs::write(&object_path, vec![b'a'; 8192]).unwrap();
            let r = root(dir.path());
            let object = unsafe { rt_cache_host_open_read_v1(r, b"object".as_ptr(), 6) };
            let barrier = Arc::new(Barrier::new(2));
            *READ_TEST_BARRIER.get_or_init(|| Mutex::new(None)).lock().unwrap() = Some(barrier.clone());
            let mut out = vec![0u8; 8192];
            let mutator = thread::spawn(move || {
                barrier.wait();
                let file = fs::OpenOptions::new().write(true).open(object_path).unwrap();
                use std::os::unix::fs::FileExt;
                file.write_all_at(&vec![b'b'; 4096], 0).unwrap();
                file.sync_all().unwrap();
                barrier.wait();
            });
            let result = unsafe { rt_cache_host_pread_receipt_v1(object, 0, out.as_mut_ptr(), out.len() as i64) };
            mutator.join().unwrap();
            *READ_TEST_BARRIER.get().unwrap().lock().unwrap() = None;
            assert_eq!(result, -2);
            unsafe {
                rt_cache_host_close_v1(object);
                rt_cache_host_close_v1(r);
            }
        }
    }
}

#[cfg(unix)]
pub use unix::*;

#[cfg(windows)]
mod windows_unsupported {
    //! ABI-complete fail-closed Windows seam.
    //!
    //! The admitted implementation must traverse with CreateFileW and
    //! FILE_FLAG_OPEN_REPARSE_POINT, prove containment with
    //! GetFinalPathNameByHandleW, receipt FileIdInfo/size/write-time on the same
    //! handle, and publish with FILE_RENAME_INFO_EX +
    //! FILE_RENAME_FLAG_FAIL_IF_EXISTS.  Pathname-only emulation is forbidden.
    const UNSUPPORTED: i64 = -1;

    macro_rules! unsupported {
        ($name:ident($($arg:ident: $ty:ty),*)) => {
            #[no_mangle]
            pub unsafe extern "C" fn $name($($arg: $ty),*) -> i64 {
                $(let _ = $arg;)*
                UNSUPPORTED
            }
        };
    }

    unsupported!(rt_cache_host_open_root_v1(path: *const u8, len: i64));
    unsupported!(rt_cache_host_open_read_v1(root: i64, path: *const u8, len: i64));
    unsupported!(rt_cache_host_open_child_v1(parent: i64, name: *const u8, len: i64, create: i64));
    unsupported!(rt_cache_host_pread_receipt_v1(handle: i64, offset: i64, out: *mut u8, cap: i64));
    unsupported!(rt_cache_host_secure_temp_v1(root: i64));
    unsupported!(rt_cache_host_write_temp_v1(handle: i64, offset: i64, data: *const u8, len: i64));
    unsupported!(rt_cache_host_publish_noreplace_v1(handle: i64, dest: *const u8, len: i64));
    unsupported!(rt_cache_host_quarantine_v1(root: i64, object: i64, dest: *const u8, len: i64));
    unsupported!(rt_cache_host_fsync_v1(handle: i64));
    unsupported!(rt_cache_host_close_v1(handle: i64));
}

#[cfg(windows)]
pub use windows_unsupported::*;
