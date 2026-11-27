//! Open-time confinement under a trusted root (todo 479).
//!
//! `read_under_root` / `write_under_root` walk `rel` one component at a time
//! below `root`, refusing a reparse point (Windows) or symlink (POSIX) at EVERY
//! component at open time, and keep each directory open until the final
//! operation completes. A held directory cannot be renamed, deleted or
//! replaced (Windows: no share-delete; POSIX: operations are fd-relative), so a
//! junction swapped in after the check cannot redirect the final open/write.
//! `root` itself is trusted but must not be a link at its own final component.
//! Failure codes mirror the `READ_NF_*` arms (4 open, 5 metadata, 6 not
//! regular, 7 too large, 8 reparse/symlink, 9 read, 2 bad args).

use std::io::{Read, Write};
use std::sync::atomic::{AtomicU64, Ordering};

pub const UR_BAD_ARGS: i64 = 2;
pub const UR_OPEN: i64 = 4;
pub const UR_METADATA: i64 = 5;
pub const UR_NOT_REGULAR: i64 = 6;
pub const UR_TOO_LARGE: i64 = 7;
pub const UR_REPARSE: i64 = 8;
pub const UR_READ: i64 = 9;

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn segments(rel: &str) -> Option<Vec<&str>> {
    if rel.is_empty() || rel.contains('\\') || rel.contains('\0') || rel.starts_with('/') {
        return None;
    }
    let segs: Vec<&str> = rel.split('/').collect();
    for seg in &segs {
        if seg.is_empty() || *seg == "." || *seg == ".." {
            return None;
        }
        #[cfg(windows)]
        if seg.contains(':') {
            return None;
        }
    }
    Some(segs)
}

fn temp_name() -> String {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    format!(
        ".simple-under-root-{}-{}-{}.tmp",
        std::process::id(),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed),
        nanos
    )
}

fn bounded_read(file: &mut impl Read, max_bytes: i64) -> Result<Vec<u8>, i64> {
    let limit = (max_bytes as u64).checked_add(1).ok_or(UR_TOO_LARGE)?;
    let mut raw = Vec::new();
    if file.take(limit).read_to_end(&mut raw).is_err() {
        return Err(UR_READ);
    }
    if raw.len() as i64 > max_bytes {
        return Err(UR_TOO_LARGE);
    }
    Ok(raw)
}

#[cfg(windows)]
mod plat {
    //! Every step after the trusted root is an `NtCreateFile` RELATIVE to the
    //! parent directory handle (`OBJECT_ATTRIBUTES.RootDirectory`), so no step
    //! re-resolves a path by name. Holding a directory without share-delete
    //! does NOT stop `FSCTL_SET_REPARSE_POINT` (it needs only
    //! `FILE_WRITE_ATTRIBUTES`), but a relative open goes through the held
    //! handle's own directory object and never through a reparse point set on
    //! it later. That alone is NOT enough: a relative open still FOLLOWS a
    //! reparse point set on the held directory (a relative symlink target is
    //! resolved against the held directory's own path), so
    //! every open also sets `OBJ_DONT_REPARSE`, which fails the open with
    //! `STATUS_REPARSE_POINT_ENCOUNTERED` (reported as the link arm) instead.
    //! Each opened handle is additionally checked for a reparse attribute.
    use super::*;
    use std::ffi::c_void;
    use std::fs::{File, OpenOptions};
    use std::os::windows::fs::{MetadataExt, OpenOptionsExt};
    use std::os::windows::io::{AsRawHandle, FromRawHandle, RawHandle};
    use std::ptr::null_mut;

    #[repr(C)]
    struct UnicodeString {
        length: u16,
        maximum_length: u16,
        buffer: *mut u16,
    }
    #[repr(C)]
    struct ObjectAttributes {
        length: u32,
        root_directory: RawHandle,
        object_name: *mut UnicodeString,
        attributes: u32,
        security_descriptor: *mut c_void,
        security_quality_of_service: *mut c_void,
    }
    #[repr(C)]
    struct RenameHeader {
        replace_if_exists: u32,
        root_directory: RawHandle,
        file_name_length: u32,
    }
    #[repr(C)]
    struct IoStatusBlock {
        status: isize,
        information: usize,
    }

    #[link(name = "ntdll")]
    extern "system" {
        fn NtCreateFile(
            handle: *mut RawHandle,
            access: u32,
            attributes: *mut ObjectAttributes,
            io_status: *mut IoStatusBlock,
            allocation_size: *mut i64,
            file_attributes: u32,
            share: u32,
            disposition: u32,
            options: u32,
            ea_buffer: *mut c_void,
            ea_length: u32,
        ) -> i32;
        fn NtSetInformationFile(
            handle: RawHandle,
            io_status: *mut IoStatusBlock,
            info: *mut c_void,
            length: u32,
            class: u32,
        ) -> i32;
    }

    const LIST_DIR: u32 = 0x1;
    const ADD_FILE: u32 = 0x2;
    const ADD_SUBDIR: u32 = 0x4;
    const READ_DATA: u32 = 0x1;
    const READ_ATTR: u32 = 0x80;
    const SYNC: u32 = 0x0010_0000;
    const DELETE: u32 = 0x0001_0000;
    const GENERIC_WRITE: u32 = 0x4000_0000;
    const DIRECTORY_FILE: u32 = 0x1;
    const SYNC_IO: u32 = 0x20;
    const NON_DIRECTORY_FILE: u32 = 0x40;
    const OPEN_REPARSE: u32 = 0x0020_0000;
    const FILE_OPEN: u32 = 1;
    const FILE_CREATE: u32 = 2;
    const SHARE_RW: u32 = 0x1 | 0x2;
    const SHARE_ALL: u32 = 0x1 | 0x2 | 0x4;
    const BACKUP_SEMANTICS: u32 = 0x0200_0000;
    const OPEN_REPARSE_POINT: u32 = 0x0020_0000;
    const ATTR_REPARSE: u32 = 0x400;
    const STATUS_NOT_A_DIRECTORY: u32 = 0xC000_0103;
    const STATUS_FILE_IS_A_DIRECTORY: u32 = 0xC000_00BA;
    const FILE_RENAME_INFORMATION: u32 = 10;
    const STATUS_SHARING_VIOLATION: u32 = 0xC000_0043;
    // Replacing a leaf that any other handle has open (even a share-all reader).
    const STATUS_ACCESS_DENIED: u32 = 0xC000_0022;
    // A reparse point (symlink/mount point) met while OBJ_DONT_REPARSE is set.
    const STATUS_REPARSE_POINT_ENCOUNTERED: u32 = 0xC000_050B;
    const STATUS_REPARSE_POINT_NOT_RESOLVED: u32 = 0xC000_0280;
    const OBJ_CASE_INSENSITIVE: u32 = 0x40;
    const OBJ_DONT_REPARSE: u32 = 0x1000;

    /// One `NtCreateFile` relative to `parent`; `Err` is an arm code.
    fn open_rel(parent: RawHandle, name: &str, access: u32, share: u32, disposition: u32, options: u32) -> Result<File, i64> {
        let wide: Vec<u16> = name.encode_utf16().collect();
        if wide.is_empty() || wide.len() > 255 {
            return Err(UR_BAD_ARGS);
        }
        let mut us = UnicodeString {
            length: (wide.len() * 2) as u16,
            maximum_length: (wide.len() * 2) as u16,
            buffer: wide.as_ptr() as *mut u16,
        };
        let mut oa = ObjectAttributes {
            length: std::mem::size_of::<ObjectAttributes>() as u32,
            root_directory: parent,
            object_name: &mut us,
            attributes: OBJ_CASE_INSENSITIVE | OBJ_DONT_REPARSE,
            security_descriptor: null_mut(),
            security_quality_of_service: null_mut(),
        };
        let mut iosb = IoStatusBlock { status: 0, information: 0 };
        let mut handle: RawHandle = null_mut();
        let status = unsafe {
            NtCreateFile(
                &mut handle,
                access,
                &mut oa,
                &mut iosb,
                null_mut(),
                0x80, // FILE_ATTRIBUTE_NORMAL
                share,
                disposition,
                options | SYNC_IO | OPEN_REPARSE,
                null_mut(),
                0,
            )
        };
        if status < 0 {
            let code = status as u32;
            if code == STATUS_REPARSE_POINT_ENCOUNTERED || code == STATUS_REPARSE_POINT_NOT_RESOLVED {
                return Err(UR_REPARSE);
            }
            return Err(if code == STATUS_NOT_A_DIRECTORY || code == STATUS_FILE_IS_A_DIRECTORY {
                UR_NOT_REGULAR
            } else {
                UR_OPEN
            });
        }
        Ok(unsafe { File::from_raw_handle(handle) })
    }

    /// `Ok` when the opened handle is a non-link of the wanted kind.
    fn check(file: &File, want_dir: bool) -> Result<(), i64> {
        let meta = file.metadata().map_err(|_| UR_METADATA)?;
        if meta.file_attributes() & ATTR_REPARSE != 0 {
            return Err(UR_REPARSE);
        }
        if meta.is_dir() != want_dir {
            return Err(UR_NOT_REGULAR);
        }
        Ok(())
    }

    /// Open the trusted `root` by name, then each directory relative to its
    /// parent. Every handle is returned so the whole chain stays open.
    fn walk(root: &str, dirs: &[&str], create: bool) -> Result<Vec<File>, i64> {
        let access = LIST_DIR | READ_ATTR | SYNC | if create { ADD_FILE | ADD_SUBDIR } else { 0 };
        let root_file = OpenOptions::new()
            .access_mode(access)
            .share_mode(SHARE_RW)
            .custom_flags(BACKUP_SEMANTICS | OPEN_REPARSE_POINT)
            .open(root)
            .map_err(|_| UR_OPEN)?;
        check(&root_file, true)?;
        let mut held = vec![root_file];
        for seg in dirs {
            let parent = held[held.len() - 1].as_raw_handle();
            let next = match open_rel(parent, seg, access, SHARE_RW, FILE_OPEN, DIRECTORY_FILE) {
                Ok(file) => file,
                // A concurrent writer may create the directory first: retry as an open.
                Err(UR_OPEN) if create => open_rel(parent, seg, access, SHARE_RW, FILE_CREATE, DIRECTORY_FILE)
                    .or_else(|_| open_rel(parent, seg, access, SHARE_RW, FILE_OPEN, DIRECTORY_FILE))?,
                Err(code) => return Err(code),
            };
            check(&next, true)?;
            held.push(next);
        }
        Ok(held)
    }

    pub fn read(root: &str, rel: &str, max_bytes: i64) -> Result<Vec<u8>, i64> {
        let segs = segments(rel).ok_or(UR_BAD_ARGS)?;
        let (leaf, dirs) = segs.split_last().ok_or(UR_BAD_ARGS)?;
        let held = walk(root, dirs, false)?;
        let parent = held[held.len() - 1].as_raw_handle();
        let mut file = open_rel(parent, leaf, READ_DATA | READ_ATTR | SYNC, SHARE_ALL, FILE_OPEN, NON_DIRECTORY_FILE)?;
        check(&file, false)?;
        let meta = file.metadata().map_err(|_| UR_METADATA)?;
        if meta.len() > max_bytes as u64 {
            return Err(UR_TOO_LARGE);
        }
        bounded_read(&mut file, max_bytes)
    }

    pub fn write(root: &str, rel: &str, data: &[u8]) -> bool {
        let Some(segs) = segments(rel) else { return false };
        let Some((leaf, dirs)) = segs.split_last() else { return false };
        let Ok(held) = walk(root, dirs, true) else { return false };
        let parent = held[held.len() - 1].as_raw_handle();
        // An existing leaf must be a plain file; a link or directory is refused.
        match open_rel(parent, leaf, READ_ATTR | SYNC, SHARE_ALL, FILE_OPEN, 0) {
            Ok(existing) => {
                if check(&existing, false).is_err() {
                    return false;
                }
            }
            Err(UR_OPEN) => {}
            Err(_) => return false,
        }
        let temp_name = super::temp_name();
        let Ok(mut temp) = open_rel(
            parent,
            &temp_name,
            GENERIC_WRITE | DELETE | READ_ATTR | SYNC,
            SHARE_RW,
            FILE_CREATE,
            NON_DIRECTORY_FILE,
        ) else {
            return false;
        };
        if temp.write_all(data).is_err() || temp.sync_all().is_err() {
            dispose(&temp);
            return false;
        }
        // INVARIANT (do not weaken): the rename cannot carry OBJ_DONT_REPARSE and
        // DOES follow a reparse point set on `RootDirectory`. It is safe only
        // because `temp` stays open WITHOUT FILE_SHARE_DELETE across the rename,
        // which keeps the parent non-empty, so FSCTL_SET_REPARSE_POINT on it
        // fails (error 145, directory not empty). Adding share-delete to the temp
        // or closing it before the rename reopens the write escape.
        // Publish by a handle-relative rename (NtSetInformationFile with
        // RootDirectory = parent and a bare name; the Win32 wrapper rejects a
        // RootDirectory with ERROR_INVALID_PARAMETER).
        let wide: Vec<u16> = leaf.encode_utf16().collect();
        let name_bytes = wide.len() * 2;
        // FILE_RENAME_INFORMATION: the name starts right after FileNameLength.
        let name_at = std::mem::offset_of!(RenameHeader, file_name_length) + 4;
        let total = name_at + name_bytes + 2;
        let mut backing = vec![0u64; total.div_ceil(8)];
        let base = backing.as_mut_ptr() as *mut u8;
        unsafe {
            (base as *mut RenameHeader).write(RenameHeader {
                replace_if_exists: 1,
                root_directory: parent,
                file_name_length: name_bytes as u32,
            });
            std::ptr::copy_nonoverlapping(wide.as_ptr() as *const u8, base.add(name_at), name_bytes);
        }
        let mut renamed = false;
        for attempt in 0..8u32 {
            let mut iosb = IoStatusBlock { status: 0, information: 0 };
            let status = unsafe {
                NtSetInformationFile(
                    temp.as_raw_handle(),
                    &mut iosb,
                    base as *mut c_void,
                    total as u32,
                    FILE_RENAME_INFORMATION,
                )
            };
            if status >= 0 {
                renamed = true;
                break;
            }
            // Only a sharing violation or an access-denied from another open handle
            // on the target can clear by itself; anything else is permanent.
            let code = status as u32;
            if code != STATUS_SHARING_VIOLATION && code != STATUS_ACCESS_DENIED {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(1 << attempt));
        }
        if !renamed {
            dispose(&temp);
        }
        renamed
    }

    /// Mark the still-open temp file delete-on-close.
    fn dispose(file: &File) {
        let mut iosb = IoStatusBlock { status: 0, information: 0 };
        let mut flag: u32 = 1; // FILE_DISPOSITION_INFORMATION.DeleteFile
        unsafe {
            NtSetInformationFile(file.as_raw_handle(), &mut iosb, &mut flag as *mut u32 as *mut c_void, 4, 13);
        }
    }
}

#[cfg(unix)]
mod plat {
    use super::*;
    use std::ffi::CString;
    use std::fs::File;
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

    fn cstr(value: &str) -> Result<CString, i64> {
        CString::new(value).map_err(|_| UR_BAD_ARGS)
    }

    fn open_dir_at(dirfd: libc::c_int, name: &CString) -> Result<OwnedFd, i64> {
        let flags = libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC;
        let fd = unsafe { libc::openat(dirfd, name.as_ptr(), flags) };
        if fd < 0 {
            let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
            return Err(if errno == libc::ELOOP || errno == libc::ENOTDIR { UR_REPARSE } else { UR_OPEN });
        }
        Ok(unsafe { OwnedFd::from_raw_fd(fd) })
    }

    fn walk(root: &str, dirs: &[&str], create: bool) -> Result<OwnedFd, i64> {
        let root_c = cstr(root)?;
        let mut current = open_dir_at(libc::AT_FDCWD, &root_c)?;
        for seg in dirs {
            let name = cstr(seg)?;
            let next = match open_dir_at(current.as_raw_fd(), &name) {
                Ok(fd) => fd,
                Err(code) if create && code == UR_OPEN => {
                    unsafe { libc::mkdirat(current.as_raw_fd(), name.as_ptr(), 0o755) };
                    open_dir_at(current.as_raw_fd(), &name)?
                }
                Err(code) => return Err(code),
            };
            current = next;
        }
        Ok(current)
    }

    pub fn read(root: &str, rel: &str, max_bytes: i64) -> Result<Vec<u8>, i64> {
        let segs = segments(rel).ok_or(UR_BAD_ARGS)?;
        let (leaf, dirs) = segs.split_last().ok_or(UR_BAD_ARGS)?;
        let parent = walk(root, dirs, false)?;
        let name = cstr(leaf)?;
        let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK;
        let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
        if fd < 0 {
            let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
            return Err(if errno == libc::ELOOP { UR_REPARSE } else { UR_OPEN });
        }
        let mut file = unsafe { File::from_raw_fd(fd) };
        let meta = file.metadata().map_err(|_| UR_METADATA)?;
        if !meta.is_file() {
            return Err(UR_NOT_REGULAR);
        }
        if meta.len() > max_bytes as u64 {
            return Err(UR_TOO_LARGE);
        }
        bounded_read(&mut file, max_bytes)
    }

    pub fn write(root: &str, rel: &str, data: &[u8]) -> bool {
        let Some(segs) = segments(rel) else { return false };
        let Some((leaf, dirs)) = segs.split_last() else { return false };
        let Ok(parent) = walk(root, dirs, true) else { return false };
        let (Ok(leaf_c), Ok(temp_c)) = (cstr(leaf), cstr(&super::temp_name())) else { return false };
        let dirfd = parent.as_raw_fd();
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        if unsafe { libc::fstatat(dirfd, leaf_c.as_ptr(), &mut st, libc::AT_SYMLINK_NOFOLLOW) } == 0 {
            let kind = st.st_mode & libc::S_IFMT;
            if kind == libc::S_IFDIR || kind == libc::S_IFLNK {
                return false;
            }
        }
        let flags = libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC;
        let fd = unsafe { libc::openat(dirfd, temp_c.as_ptr(), flags, 0o644 as libc::c_uint) };
        if fd < 0 {
            return false;
        }
        let mut file = unsafe { File::from_raw_fd(fd) };
        let written = file.write_all(data).and_then(|_| file.sync_all());
        drop(file);
        if written.is_err() || unsafe { libc::renameat(dirfd, temp_c.as_ptr(), dirfd, leaf_c.as_ptr()) } != 0 {
            unsafe { libc::unlinkat(dirfd, temp_c.as_ptr(), 0) };
            return false;
        }
        true
    }
}

#[cfg(not(any(unix, windows)))]
mod plat {
    use super::*;
    pub fn read(_root: &str, _rel: &str, _max_bytes: i64) -> Result<Vec<u8>, i64> {
        Err(UR_READ)
    }
    pub fn write(_root: &str, _rel: &str, _data: &[u8]) -> bool {
        false
    }
}

/// Read `rel` under `root`; `Err(code)` is a `READ_NF_*`-style arm.
pub fn read_under_root(root: &str, rel: &str, max_bytes: i64) -> Result<Vec<u8>, i64> {
    if root.is_empty() || root.contains('\0') || max_bytes < 0 {
        return Err(UR_BAD_ARGS);
    }
    plat::read(root, rel, max_bytes)
}

/// Atomically write `data` to `rel` under `root`, creating missing directories.
pub fn write_under_root(root: &str, rel: &str, data: &[u8]) -> bool {
    if root.is_empty() || root.contains('\0') {
        return false;
    }
    plat::write(root, rel, data)
}
