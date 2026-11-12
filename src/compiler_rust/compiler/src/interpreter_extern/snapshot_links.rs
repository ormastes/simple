//! Interpreter providers for the snapshot owner's no-follow operations.
//!
//! The lexical contract (absolute-path shape, root confinement, exact raw
//! link text) is shared. The Unix implementation is descriptor-based
//! (openat/readlinkat/fchmod); the Windows implementation mirrors the C
//! runtime contract in `src/runtime/runtime_core_host_services.c`
//! (`runtime_win_long_path.h` widen + real-parents walk, reparse-point
//! attribute checks, `FSCTL_GET_REPARSE_POINT` exact raw-target readback, and
//! `CreateSymbolicLinkW` with `SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE`).
use crate::{error::CompileError, value::Value};

#[cfg(unix)]
use std::ffi::CString;
#[cfg(unix)]
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

fn text(args: &[Value], index: usize) -> Option<&str> {
    let Value::Str(value) = args.get(index)? else { return None; };
    let value = value.as_str();
    (!value.is_empty() && value.len() < 4096 && !value.as_bytes().contains(&0)).then_some(value)
}
fn kind(args: &[Value], index: usize) -> Option<i64> {
    match args.get(index) { Some(Value::Int(value @ (1 | 2))) => Some(*value), _ => None }
}

// `core_snapshot_absolute` in the C runtime: on Unix every component is a real
// path segment below the root slash; on Windows the snapshot owner only
// emits drive-absolute forward-slash paths (`X:/...`).
#[cfg(unix)]
fn absolute(path: &str) -> bool {
    path.len() >= 2 && path.len() < 4096 && path.starts_with('/') && !path.ends_with('/')
        && !path.contains('\\') && !path.as_bytes().contains(&0)
        && path[1..].split('/').all(|part| !matches!(part, "" | "." | ".."))
}
#[cfg(windows)]
fn absolute(path: &str) -> bool {
    let bytes = path.as_bytes();
    bytes.len() >= 3 && bytes.len() < 4096
        && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' && bytes[2] == b'/'
        && !path.ends_with('/')
        && !path.contains('\\') && !bytes.contains(&0)
        && path[3..].split('/').all(|part| !matches!(part, "" | "." | ".."))
}

// On Windows both separator spellings reach the extern boundary (the runtime
// `rt_path_absolute`/`rt_path_join` emit the platform-native separator), so
// the absolute-path arguments are normalized to the contract's forward-slash
// form before validation. The raw link TARGET is never normalized: it is
// stored verbatim and compared byte-exact on readback.
#[cfg(unix)]
fn normalize_absolute(path: &str) -> std::borrow::Cow<'_, str> {
    std::borrow::Cow::Borrowed(path)
}
#[cfg(windows)]
fn normalize_absolute(path: &str) -> std::borrow::Cow<'_, str> {
    if path.contains('\\') { std::borrow::Cow::Owned(path.replace('\\', "/")) } else { std::borrow::Cow::Borrowed(path) }
}

// `core_snapshot_target`: resolve the raw relative target lexically with
// bounded '..'; the resolved path must stay at or below the root.
fn resolved(root: &str, link: &str, target: &str) -> Option<String> {
    if !absolute(root) || !absolute(link) || !link.starts_with(&format!("{root}/"))
        || target.starts_with('/') || target.ends_with('/') || target.contains(['\\', ':']) {
        return None;
    }
    let (parent, _) = link.rsplit_once('/')?;
    let mut result = parent.to_owned();
    for part in target.split('/') {
        match part {
            "" => return None,
            "." => {},
            ".." => {
                if result.len() <= root.len() { return None; }
                result.truncate(result.rfind('/')?);
                if result.len() < root.len() { return None; }
            },
            name => { result.push('/'); result.push_str(name); },
        }
    }
    absolute(&result).then_some(result)
}
fn link_args(args: &[Value]) -> Option<(std::borrow::Cow<'_, str>, std::borrow::Cow<'_, str>, &str, i64, String)> {
    let (root, link, target, kind) = (text(args, 0)?, text(args, 1)?, text(args, 2)?, kind(args, 3)?);
    let resolved = resolved(&normalize_absolute(root), &normalize_absolute(link), target)?;
    Some((normalize_absolute(root), normalize_absolute(link), target, kind, resolved))
}

#[cfg(unix)]
fn parent(path: &str) -> Option<(OwnedFd, CString)> {
    if !absolute(path) { return None; }
    let (directory, leaf) = path.rsplit_once('/')?;
    let fd = super::file_io::safe_artifact_open_root(if directory.is_empty() { "/" } else { directory })?;
    let owner = unsafe { OwnedFd::from_raw_fd(fd) };
    Some((owner, CString::new(leaf).ok()?))
}
#[cfg(unix)]
fn has_kind(path: &str, kind: i64) -> bool {
    let Some((directory, leaf)) = parent(path) else { return false; };
    let mut info: libc::stat = unsafe { std::mem::zeroed() };
    (unsafe { libc::fstatat(directory.as_raw_fd(), leaf.as_ptr(), &mut info, libc::AT_SYMLINK_NOFOLLOW) == 0 })
        && info.st_mode & libc::S_IFMT == if kind == 1 { libc::S_IFREG } else { libc::S_IFDIR }
}
#[cfg(unix)]
fn exact_link(link: &str, target: &str) -> bool {
    let Some((directory, leaf)) = parent(link) else { return false; };
    let mut info: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstatat(directory.as_raw_fd(), leaf.as_ptr(), &mut info, libc::AT_SYMLINK_NOFOLLOW) } != 0
        || info.st_mode & libc::S_IFMT != libc::S_IFLNK { return false; }
    let mut raw = [0u8; 4096];
    let length = unsafe { libc::readlinkat(directory.as_raw_fd(), leaf.as_ptr(), raw.as_mut_ptr().cast(), raw.len()) };
    length >= 0 && length as usize == target.len() && &raw[..length as usize] == target.as_bytes()
}
#[cfg(unix)]
pub fn matches(args: &[Value]) -> Result<Value, CompileError> {
    let ok = link_args(args).is_some_and(|(_, link, target, kind, resolved)|
        has_kind(&resolved, kind) && exact_link(&link, target));
    Ok(Value::Int(if ok { 0 } else { -1 }))
}
#[cfg(unix)]
pub fn create(args: &[Value]) -> Result<Value, CompileError> {
    let Some((_, link, target, kind, resolved)) = link_args(args) else { return Ok(Value::Int(-1)); };
    if !has_kind(&resolved, kind) { return Ok(Value::Int(-1)); }
    let Some((directory, leaf)) = parent(&link) else { return Ok(Value::Int(-1)); };
    let target_c = CString::new(target).expect("validated target has no NUL");
    if unsafe { libc::symlinkat(target_c.as_ptr(), directory.as_raw_fd(), leaf.as_ptr()) } != 0 {
        return Ok(Value::Int(-1));
    }
    matches(args)
}
#[cfg(unix)]
pub fn readonly(args: &[Value]) -> Result<Value, CompileError> {
    let Some(path) = text(args, 0) else { return Ok(Value::Int(-1)); };
    let Some(kind) = kind(args, 1) else { return Ok(Value::Int(-1)); };
    let Some((directory, leaf)) = parent(path) else { return Ok(Value::Int(-1)); };
    let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK
        | if kind == 2 { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(directory.as_raw_fd(), leaf.as_ptr(), flags) };
    if fd < 0 { return Ok(Value::Int(-1)); }
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    let mut before: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd.as_raw_fd(), &mut before) } != 0
        || before.st_mode & libc::S_IFMT != if kind == 1 { libc::S_IFREG } else { libc::S_IFDIR } {
        return Ok(Value::Int(-1));
    }
    let desired = before.st_mode & 0o7777 & !0o222;
    let mut after: libc::stat = unsafe { std::mem::zeroed() };
    let ok = unsafe { libc::fchmod(fd.as_raw_fd(), desired) == 0
        && libc::fstat(fd.as_raw_fd(), &mut after) == 0 } && after.st_mode & 0o222 == 0;
    Ok(Value::Int(if ok { 0 } else { -1 }))
}

#[cfg(windows)]
mod windows {
    use super::{absolute, link_args, normalize_absolute, text, kind};
    use crate::{error::CompileError, value::Value};
    use std::os::raw::c_void;

    type Handle = *mut c_void;
    const INVALID_HANDLE_VALUE: Handle = (-1isize) as Handle;
    const INVALID_FILE_ATTRIBUTES: u32 = 0xFFFF_FFFF;

    const CP_UTF8: u32 = 65_001;
    const MB_ERR_INVALID_CHARS: u32 = 0x8;
    const WC_ERR_INVALID_CHARS: u32 = 0x400;

    const FILE_ATTRIBUTE_READONLY: u32 = 0x1;
    const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x10;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x400;
    const FILE_ATTRIBUTE_DEVICE: u32 = 0x40;

    const FILE_READ_ATTRIBUTES: u32 = 0x80;
    const FILE_WRITE_ATTRIBUTES: u32 = 0x100;
    const FILE_SHARE_READ: u32 = 0x1;
    const FILE_SHARE_WRITE: u32 = 0x2;
    const FILE_SHARE_DELETE: u32 = 0x4;
    const OPEN_EXISTING: u32 = 3;
    const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
    const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;

    const SYMBOLIC_LINK_FLAG_DIRECTORY: u32 = 0x1;
    // CreateSymbolicLinkW fails with ERROR_INVALID_PARAMETER on hosts that
    // predate the flag; the C runtime retries without it in that case.
    const SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE: u32 = 0x2;
    const ERROR_INVALID_PARAMETER: u32 = 87;

    const FSCTL_GET_REPARSE_POINT: u32 = 0x0009_00A8;
    const IO_REPARSE_TAG_SYMLINK: u32 = 0xA000_000C;
    const SYMLINK_FLAG_RELATIVE: u32 = 0x1;
    const MAX_REPARSE_DATA: usize = 16 * 1024;
    const FILE_BASIC_INFO_CLASS: i32 = 0; // FileBasicInfo

    #[repr(C)]
    struct ByHandleFileInformation {
        file_attributes: u32,
        creation_time: i64,
        last_access_time: i64,
        last_write_time: i64,
        last_change_time: i64,
        volume_serial_number: u32,
        file_size_high: u32,
        file_size_low: u32,
        number_of_links: u32,
        file_index_high: u32,
        file_index_low: u32,
    }

    #[repr(C)]
    struct FileBasicInfo {
        creation_time: i64,
        last_access_time: i64,
        last_write_time: i64,
        change_time: i64,
        file_attributes: u32,
    }

    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn MultiByteToWideChar(code_page: u32, flags: u32, source: *const u8, source_len: i32,
            target: *mut u16, target_len: i32) -> i32;
        fn WideCharToMultiByte(code_page: u32, flags: u32, source: *const u16, source_len: i32,
            target: *mut u8, target_len: i32, default_char: *const u8,
            used_default_char: *mut i32) -> i32;
        fn GetFullPathNameW(path: *const u16, capacity: u32, buffer: *mut u16,
            file_part: *mut *mut u16) -> u32;
        fn GetFileAttributesW(path: *const u16) -> u32;
        fn CreateFileW(name: *const u16, access: u32, sharing: u32, security: *mut c_void,
            disposition: u32, attributes_and_flags: u32, template: Handle) -> Handle;
        fn GetFileInformationByHandle(file: Handle, info: *mut ByHandleFileInformation) -> i32;
        fn DeviceIoControl(file: Handle, control_code: u32, in_buffer: *mut c_void, in_size: u32,
            out_buffer: *mut c_void, out_size: u32, returned: *mut u32,
            overlapped: *mut c_void) -> i32;
        fn CreateSymbolicLinkW(link: *const u16, target: *const u16, flags: u32) -> u8;
        fn GetFileInformationByHandleEx(file: Handle, class: i32, info: *mut c_void, size: u32) -> i32;
        fn SetFileInformationByHandle(file: Handle, class: i32, info: *const c_void, size: u32) -> i32;
        fn CloseHandle(handle: Handle) -> i32;
        fn GetLastError() -> u32;
    }

    /// `rt_win_long_path_widen`: UTF-8 -> UTF-16, normalizing separators and
    /// adding the `\\?\` prefix only when the resolved path can hit MAX_PATH.
    fn widen(path: &str) -> Option<Vec<u16>> {
        let bytes = path.as_bytes();
        // With an explicit source length MultiByteToWideChar converts exactly
        // `len` bytes and does NOT append a NUL; the returned count excludes
        // it. Reserve the terminator explicitly or every Win32 call below
        // would read a garbage suffix off the heap.
        let count = unsafe {
            MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, bytes.as_ptr(), bytes.len() as i32,
                std::ptr::null_mut(), 0)
        };
        if count <= 0 { return None; }
        let mut wide = vec![0u16; count as usize + 1];
        if unsafe {
            MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, bytes.as_ptr(), bytes.len() as i32,
                wide.as_mut_ptr(), count)
        } == 0 { return None; }
        // `wide` carries the NUL terminator at index `count`.
        let sep: u16 = 92; // '\\'
        if wide[0] == sep && wide[1] == sep { return Some(wide); }
        if count < 248 && count > 3 && wide[1] == b':' as u16
            && (wide[2] == sep || wide[2] == b'/' as u16) { return Some(wide); }
        for ch in wide.iter_mut() { if *ch == b'/' as u16 { *ch = sep; } }
        let need = unsafe { GetFullPathNameW(wide.as_ptr(), 0, std::ptr::null_mut(), std::ptr::null_mut()) };
        if need == 0 { return Some(wide); }
        let mut full = vec![0u16; need as usize + 8];
        let written = unsafe { GetFullPathNameW(wide.as_ptr(), need, full.as_mut_ptr(), std::ptr::null_mut()) };
        if written == 0 || written >= need { return Some(wide); }
        if written < 248 { return Some(wide); }
        let mut out = Vec::with_capacity(written as usize + 8);
        out.extend_from_slice(&[sep, sep, b'?' as u16, sep]);
        out.extend_from_slice(&full[..written as usize]);
        out.push(0);
        Some(out)
    }

    /// `core_snapshot_windows_raw_target`: widen only — the raw link text is
    /// stored verbatim so the no-follow readback can compare it byte-exact.
    fn raw_wide(text_value: &str) -> Option<Vec<u16>> {
        let bytes = text_value.as_bytes();
        let count = unsafe {
            MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, bytes.as_ptr(), bytes.len() as i32,
                std::ptr::null_mut(), 0)
        };
        if count <= 0 { return None; }
        let mut wide = vec![0u16; count as usize + 1];
        if unsafe {
            MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, bytes.as_ptr(), bytes.len() as i32,
                wide.as_mut_ptr(), count)
        } == 0 { return None; }
        Some(wide)
    }

    fn path_slice(wide: &[u16]) -> &[u16] {
        let end = wide.iter().position(|&ch| ch == 0).unwrap_or(wide.len());
        &wide[..end]
    }

    fn attrs_prefix(path: &[u16], end: usize) -> u32 {
        let mut buffer = Vec::with_capacity(end + 1);
        buffer.extend_from_slice(&path[..end]);
        buffer.push(0);
        unsafe { GetFileAttributesW(buffer.as_ptr()) }
    }

    /// `rt_win_profile_path_parents_are_real`: every ancestor must be an
    /// existing directory that is not itself a reparse point.
    fn parents_are_real(path: &[u16]) -> bool {
        let sep: u16 = 92; // '\\'
        let start = if path.len() >= 7 && path[0] == sep && path[1] == sep && path[2] == b'?' as u16
            && path[3] == sep && path[5] == b':' as u16 && path[6] == sep {
            7
        } else if path.len() >= 3 && path[1] == b':' as u16
            && (path[2] == sep || path[2] == b'/' as u16) {
            3
        } else {
            return false;
        };
        let real_dir = |end: usize| {
            let attrs = attrs_prefix(path, end);
            attrs != INVALID_FILE_ATTRIBUTES
                && attrs & FILE_ATTRIBUTE_DIRECTORY != 0
                && attrs & FILE_ATTRIBUTE_REPARSE_POINT == 0
        };
        if !real_dir(start) { return false; }
        for i in start..path.len() {
            if path[i] != sep && path[i] != b'/' as u16 { continue; }
            if !real_dir(i) { return false; }
        }
        true
    }

    /// `core_snapshot_windows_target_kind`: the resolved target must exist,
    /// must not be a reparse point, and must have the requested kind.
    fn target_kind(path: &str, kind: i64) -> bool {
        let Some(wide) = widen(path) else { return false; };
        if !parents_are_real(path_slice(&wide)) { return false; }
        let attrs = unsafe { GetFileAttributesW(wide.as_ptr()) };
        attrs != INVALID_FILE_ATTRIBUTES
            && attrs & FILE_ATTRIBUTE_REPARSE_POINT == 0
            && if kind == 2 { attrs & FILE_ATTRIBUTE_DIRECTORY != 0 }
               else { attrs & FILE_ATTRIBUTE_DIRECTORY == 0 && attrs & FILE_ATTRIBUTE_DEVICE == 0 }
    }

    /// `core_snapshot_windows_match`: open the leaf without following, demand
    /// the reparse-point attribute and the requested kind, then compare the
    /// raw relative link text from `FSCTL_GET_REPARSE_POINT` byte-exact.
    fn exact_link(link: &str, target: &str, kind: i64) -> bool {
        let Some(wide) = widen(link) else { return false; };
        if !parents_are_real(path_slice(&wide)) { return false; }
        let handle = unsafe {
            CreateFileW(wide.as_ptr(), FILE_READ_ATTRIBUTES,
                FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, std::ptr::null_mut(),
                OPEN_EXISTING, FILE_FLAG_OPEN_REPARSE_POINT | FILE_FLAG_BACKUP_SEMANTICS,
                std::ptr::null_mut())
        };
        if handle == INVALID_HANDLE_VALUE { return false; }
        let mut info: ByHandleFileInformation = unsafe { std::mem::zeroed() };
        let mut bytes = [0u8; MAX_REPARSE_DATA];
        let mut returned: u32 = 0;
        let open_ok = unsafe { GetFileInformationByHandle(handle, &mut info) } != 0
            && info.file_attributes & FILE_ATTRIBUTE_REPARSE_POINT != 0
            && if kind == 2 { info.file_attributes & FILE_ATTRIBUTE_DIRECTORY != 0 }
               else { info.file_attributes & FILE_ATTRIBUTE_DIRECTORY == 0 }
            && unsafe {
                DeviceIoControl(handle, FSCTL_GET_REPARSE_POINT, std::ptr::null_mut(), 0,
                    bytes.as_mut_ptr().cast(), MAX_REPARSE_DATA as u32, &mut returned,
                    std::ptr::null_mut())
            } != 0;
        unsafe { CloseHandle(handle) };
        if !open_ok || returned < 20 { return false; }
        // MinGW does not publish REPARSE_DATA_BUFFER. The symlink wire layout
        // is 8-byte header, four USHORT offsets/lengths, ULONG flags,
        // UTF-16 path — parse it manually exactly like the C runtime.
        let tag = u32::from_le_bytes(bytes[0..4].try_into().expect("wire tag"));
        let wire_length = u16::from_le_bytes(bytes[4..6].try_into().expect("wire length")) as usize;
        let offset = u16::from_le_bytes(bytes[12..14].try_into().expect("wire offset")) as usize;
        let length = u16::from_le_bytes(bytes[14..16].try_into().expect("wire length")) as usize;
        let flags = u32::from_le_bytes(bytes[16..20].try_into().expect("wire flags"));
        if tag != IO_REPARSE_TAG_SYMLINK
            || flags & SYMLINK_FLAG_RELATIVE == 0
            || wire_length + 8 > returned as usize
            || offset & 1 != 0
            || length & 1 != 0
            || 20 + offset + length > returned as usize
            || 20 + offset + length > wire_length + 8
            || length > 8192 {
            return false;
        }
        let raw: Vec<u16> = bytes[20 + offset..20 + offset + length]
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect();
        let count = unsafe {
            WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, raw.as_ptr(),
                (length / 2) as i32, std::ptr::null_mut(), 0, std::ptr::null(), std::ptr::null_mut())
        };
        if count <= 0 { return false; }
        let mut text_bytes = vec![0u8; count as usize];
        let written = unsafe {
            WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, raw.as_ptr(),
                (length / 2) as i32, text_bytes.as_mut_ptr(), count, std::ptr::null(), std::ptr::null_mut())
        };
        written == count && text_bytes == target.as_bytes()
    }

    pub fn matches(args: &[Value]) -> Result<Value, CompileError> {
        let ok = link_args(args).is_some_and(|(_, link, target, kind, resolved)|
            target_kind(&resolved, kind) && exact_link(&link, target, kind));
        Ok(Value::Int(if ok { 0 } else { -1 }))
    }

    pub fn create(args: &[Value]) -> Result<Value, CompileError> {
        let Some((_, link, target, kind, resolved)) = link_args(args) else { return Ok(Value::Int(-1)); };
        if !target_kind(&resolved, kind) { return Ok(Value::Int(-1)); }
        let (Some(wide_link), Some(wide_target)) = (widen(&link), raw_wide(target)) else {
            return Ok(Value::Int(-1));
        };
        if !parents_are_real(path_slice(&wide_link)) { return Ok(Value::Int(-1)); }
        // Exclusive create: refuse to replace an existing leaf.
        if unsafe { GetFileAttributesW(wide_link.as_ptr()) } != INVALID_FILE_ATTRIBUTES {
            return Ok(Value::Int(-1));
        }
        let flags = if kind == 2 { SYMBOLIC_LINK_FLAG_DIRECTORY } else { 0 };
        // Fail-closed when SeCreateSymbolicLinkPrivilege / Developer Mode is
        // unavailable: CreateSymbolicLinkW returns 0 and the op reports -1.
        let mut created = unsafe {
            CreateSymbolicLinkW(wide_link.as_ptr(), wide_target.as_ptr(),
                flags | SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE)
        };
        if created == 0 && unsafe { GetLastError() } == ERROR_INVALID_PARAMETER {
            created = unsafe { CreateSymbolicLinkW(wide_link.as_ptr(), wide_target.as_ptr(), flags) };
        }
        if created == 0 { return Ok(Value::Int(-1)); }
        matches(args)
    }

    pub fn readonly(args: &[Value]) -> Result<Value, CompileError> {
        let Some(path) = text(args, 0) else { return Ok(Value::Int(-1)); };
        let Some(kind) = kind(args, 1) else { return Ok(Value::Int(-1)); };
        // DIRECTORY READONLY is ignored for child creation by Windows.
        // Returning success there would invent a physical seal, so only
        // files are supported — same call the C runtime makes.
        if kind != 1 { return Ok(Value::Int(-1)); }
        let path = normalize_absolute(path);
        if !absolute(&path) { return Ok(Value::Int(-1)); }
        let Some(wide) = widen(&path) else { return Ok(Value::Int(-1)); };
        if !parents_are_real(path_slice(&wide)) { return Ok(Value::Int(-1)); }
        let handle = unsafe {
            CreateFileW(wide.as_ptr(), FILE_READ_ATTRIBUTES | FILE_WRITE_ATTRIBUTES,
                FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, std::ptr::null_mut(),
                OPEN_EXISTING, FILE_FLAG_OPEN_REPARSE_POINT, std::ptr::null_mut())
        };
        if handle == INVALID_HANDLE_VALUE { return Ok(Value::Int(-1)); }
        let info_size = std::mem::size_of::<FileBasicInfo>() as u32;
        let mut info: FileBasicInfo = unsafe { std::mem::zeroed() };
        let mut ok = unsafe {
            GetFileInformationByHandleEx(handle, FILE_BASIC_INFO_CLASS,
                (&mut info as *mut FileBasicInfo).cast(), info_size)
        } != 0
            && info.file_attributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT
                | FILE_ATTRIBUTE_DEVICE) == 0;
        if ok {
            info.file_attributes |= FILE_ATTRIBUTE_READONLY;
            ok = unsafe {
                SetFileInformationByHandle(handle, FILE_BASIC_INFO_CLASS,
                    (&info as *const FileBasicInfo).cast(), info_size)
            } != 0 && unsafe {
                GetFileInformationByHandleEx(handle, FILE_BASIC_INFO_CLASS,
                    (&mut info as *mut FileBasicInfo).cast(), info_size)
            } != 0
                && info.file_attributes & FILE_ATTRIBUTE_READONLY != 0
                && info.file_attributes & FILE_ATTRIBUTE_REPARSE_POINT == 0;
        }
        unsafe { CloseHandle(handle) };
        Ok(Value::Int(if ok { 0 } else { -1 }))
    }
}

#[cfg(windows)]
pub use windows::{create, matches, readonly};
