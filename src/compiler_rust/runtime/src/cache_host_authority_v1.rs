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
    use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
    use std::sync::{Mutex, OnceLock};

    const INVALID: i64 = -1;
    static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);
    static NEXT_TEMP: AtomicU64 = AtomicU64::new(1);
    static HANDLES: OnceLock<Mutex<HashMap<i64, Entry>>> = OnceLock::new();

    #[derive(Debug)]
    enum Entry {
        Root(RawFd),
        Read(RawFd),
        Temp { fd: RawFd, root_fd: RawFd, name: CString },
    }

    fn handles() -> &'static Mutex<HashMap<i64, Entry>> {
        HANDLES.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn insert(entry: Entry) -> i64 {
        let handle = NEXT_HANDLE.fetch_add(1, Ordering::Relaxed);
        handles()
            .lock()
            .expect("cache authority handle lock")
            .insert(handle, entry);
        handle
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
        let fd = unsafe { libc::openat(parent, leaf.as_ptr(), flags | libc::O_NOFOLLOW | libc::O_CLOEXEC, mode) };
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
        let Some(Entry::Root(root_fd)) = guard.get(&root) else {
            return INVALID;
        };
        let fd = open_beneath(*root_fd, &path, libc::O_RDONLY, 0);
        drop(guard);
        if fd < 0 {
            INVALID
        } else {
            insert(Entry::Read(fd))
        }
    }

    /// Returns bytes read, -1 on I/O failure, or -2 if the same-handle
    /// pre/read/post metadata receipt changed.  The caller must reject -2.
    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_pread_receipt_v1(handle: i64, offset: i64, out: *mut u8, cap: i64) -> i64 {
        if out.is_null() || offset < 0 || cap < 0 || cap > 64 * 1024 * 1024 {
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
        let count = libc::pread(fd, out.cast(), cap as usize, offset as libc::off_t);
        if count < 0 || libc::fstat(fd, &mut after) != 0 {
            return INVALID;
        }
        if before.st_dev != after.st_dev
            || before.st_ino != after.st_ino
            || before.st_size != after.st_size
            || before.st_mtime != after.st_mtime
            || before.st_ctime != after.st_ctime
        {
            -2
        } else {
            count as i64
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_cache_host_secure_temp_v1(root: i64) -> i64 {
        let guard = handles().lock().expect("cache authority handle lock");
        let Some(Entry::Root(root_fd)) = guard.get(&root) else {
            return INVALID;
        };
        let owned_root = dup_fd(*root_fd);
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
            if *libc::__errno_location() != libc::EEXIST {
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
            return if *libc::__errno_location() == libc::EEXIST {
                0
            } else {
                INVALID
            };
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
        let Some(Entry::Root(root_fd)) = guard.get(&root) else {
            return INVALID;
        };
        let Some(Entry::Read(object_fd)) = guard.get(&object) else {
            return INVALID;
        };
        let empty = b"\0";
        let rc = libc::linkat(
            *object_fd,
            empty.as_ptr().cast(),
            *root_fd,
            dest.as_ptr(),
            libc::AT_EMPTY_PATH,
        );
        if rc != 0 {
            return if *libc::__errno_location() == libc::EEXIST {
                0
            } else {
                INVALID
            };
        }
        libc::fsync(*root_fd);
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
            Some(Entry::Root(fd)) | Some(Entry::Read(fd)) | Some(Entry::Temp { fd, .. }) => *fd,
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
            Entry::Root(fd) | Entry::Read(fd) => libc::close(fd) as i64,
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
