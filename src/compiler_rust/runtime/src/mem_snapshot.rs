//! Bootstrap-runtime implementation of the compiler memory-snapshot ABI.
//!
//! The pure-Simple native path gets these symbols from `runtime.c`.  Bootstrap
//! compiler binaries link `libsimple_native_all.a`, so they need the same real
//! provider here rather than falling through to linker stubs.

use std::ffi::CString;
#[cfg(not(windows))]
use std::sync::OnceLock;
#[cfg(not(windows))]
use std::time::Instant;

use crate::value::heap::{rt_heap_live_bytes, rt_heap_peak_bytes};

#[cfg(unix)]
unsafe fn input_bytes<'a>(ptr: *const u8, len: i64) -> Option<&'a [u8]> {
    if ptr.is_null() || len <= 0 || len > 4095 {
        return None;
    }
    Some(std::slice::from_raw_parts(ptr, len as usize))
}

#[cfg(unix)]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_open(path_ptr: *const u8, path_len: i64) -> i64 {
    let path = match input_bytes(path_ptr, path_len) {
        Some(path) if !path.contains(&0) => path,
        _ => return -1,
    };
    let absolute = path.first() == Some(&b'/');
    let parts: Vec<&[u8]> = path
        .split(|byte| *byte == b'/')
        .filter(|part| !part.is_empty())
        .collect();
    let (leaf, parents) = match parts.split_last() {
        Some((leaf, parents)) if *leaf != b"." && *leaf != b".." => (*leaf, parents),
        _ => return -1,
    };
    let start = if absolute { c"/" } else { c"." };
    let mut parent_fd = libc::open(
        start.as_ptr(),
        libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
    );
    if parent_fd < 0 {
        return -1;
    }
    for part in parents {
        if *part == b"." {
            continue;
        }
        if *part == b".." {
            libc::close(parent_fd);
            return -1;
        }
        let part = match CString::new(*part) {
            Ok(part) => part,
            Err(_) => {
                libc::close(parent_fd);
                return -1;
            }
        };
        let next = libc::openat(
            parent_fd,
            part.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        );
        libc::close(parent_fd);
        if next < 0 {
            return -1;
        }
        parent_fd = next;
    }
    let leaf = match CString::new(leaf) {
        Ok(leaf) => leaf,
        Err(_) => {
            libc::close(parent_fd);
            return -1;
        }
    };
    let fd = libc::openat(
        parent_fd,
        leaf.as_ptr(),
        libc::O_WRONLY
            | libc::O_CREAT
            | libc::O_EXCL
            | libc::O_APPEND
            | libc::O_NOFOLLOW
            | libc::O_CLOEXEC,
        0o600,
    );
    libc::close(parent_fd);
    if fd < 0 {
        return -1;
    }
    let mut stat: libc::stat = std::mem::zeroed();
    if libc::fstat(fd, &mut stat) != 0 || (stat.st_mode & libc::S_IFMT) != libc::S_IFREG {
        libc::close(fd);
        return -1;
    }
    fd as i64
}

#[cfg(windows)]
mod windows_sink {
    use std::os::windows::io::{FromRawHandle, IntoRawHandle, OwnedHandle};
    use windows_sys::Win32::Foundation::{CloseHandle, HANDLE, INVALID_HANDLE_VALUE};
    use windows_sys::Win32::Storage::FileSystem::{
        CreateFileW, GetFileInformationByHandle, GetFileType, BY_HANDLE_FILE_INFORMATION,
        FILE_ATTRIBUTE_DIRECTORY, FILE_ATTRIBUTE_NORMAL, FILE_ATTRIBUTE_REPARSE_POINT,
        FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT, FILE_LIST_DIRECTORY,
        FILE_READ_ATTRIBUTES, FILE_SHARE_READ, FILE_TYPE_DISK, OPEN_EXISTING,
    };

    #[repr(C)]
    #[derive(Default)]
    struct ProcessMemoryCounters {
        cb: u32,
        page_fault_count: u32,
        peak_working_set: usize,
        working_set: usize,
        quota_peak_paged_pool: usize,
        quota_paged_pool: usize,
        quota_peak_nonpaged_pool: usize,
        quota_nonpaged_pool: usize,
        pagefile: usize,
        peak_pagefile: usize,
        private_usage: usize,
    }

    #[cfg(target_pointer_width = "64")]
    const _: () = {
        assert!(std::mem::size_of::<ProcessMemoryCounters>() == 80);
        assert!(std::mem::offset_of!(ProcessMemoryCounters, peak_working_set) == 8);
        assert!(std::mem::offset_of!(ProcessMemoryCounters, working_set) == 16);
    };

    #[link(name = "kernel32")]
    extern "system" {
        fn WriteFile(
            handle: HANDLE,
            bytes: *const u8,
            count: u32,
            written: *mut u32,
            overlapped: *mut std::ffi::c_void,
        ) -> i32;
        fn FlushFileBuffers(handle: HANDLE) -> i32;
        fn GetCurrentProcess() -> HANDLE;
        fn GetTickCount64() -> u64;
        fn K32GetProcessMemoryInfo(
            handle: HANDLE,
            counters: *mut ProcessMemoryCounters,
            bytes: u32,
        ) -> i32;
    }

    // Exact winternl.h (Windows SDK10.0.26100.0) ABI. Only final acquisition
    // uses NtCreateFile: OBJ_DONT_REPARSE rejects a reparse at any ancestor
    // atomically instead of relying on attribute-only handles' sharing rules.
    #[repr(C)]
    struct UnicodeString {
        length: u16,
        maximum_length: u16,
        buffer: *mut u16,
    }
    #[repr(C)]
    struct ObjectAttributes {
        length: u32,
        root_directory: HANDLE,
        object_name: *mut UnicodeString,
        attributes: u32,
        security_descriptor: *mut std::ffi::c_void,
        security_quality_of_service: *mut std::ffi::c_void,
    }
    #[repr(C)]
    struct IoStatusBlock {
        status_or_pointer: usize,
        information: usize,
    }
    #[cfg(target_pointer_width = "64")]
    const _: () = {
        assert!(std::mem::size_of::<UnicodeString>() == 16);
        assert!(std::mem::offset_of!(UnicodeString, buffer) == 8);
        assert!(std::mem::size_of::<ObjectAttributes>() == 48);
        assert!(std::mem::offset_of!(ObjectAttributes, object_name) == 16);
        assert!(std::mem::offset_of!(ObjectAttributes, attributes) == 24);
        assert!(std::mem::size_of::<IoStatusBlock>() == 16);
        assert!(std::mem::offset_of!(IoStatusBlock, information) == 8);
    };
    #[cfg(target_pointer_width = "32")]
    const _: () = {
        assert!(std::mem::size_of::<UnicodeString>() == 8);
        assert!(std::mem::size_of::<ObjectAttributes>() == 24);
        assert!(std::mem::size_of::<IoStatusBlock>() == 8);
    };
    #[link(name = "ntdll")]
    extern "system" {
        fn NtCreateFile(
            handle: *mut HANDLE,
            access: u32,
            attributes: *mut ObjectAttributes,
            status: *mut IoStatusBlock,
            allocation_size: *mut i64,
            file_attributes: u32,
            share: u32,
            disposition: u32,
            options: u32,
            ea: *mut std::ffi::c_void,
            ea_length: u32,
        ) -> i32;
    }

    unsafe fn create_without_reparse(path: &str) -> HANDLE {
        // The caller already refused relative/UNC/device/ADS/traversal input.
        // Construct an NT DOS-device local-drive path; never accept one raw.
        let mut name: Vec<u16> = format!("\\??\\{path}").encode_utf16().collect();
        let bytes = match u16::try_from(name.len() * 2) {
            Ok(n) => n,
            Err(_) => return INVALID_HANDLE_VALUE,
        };
        let mut unicode = UnicodeString {
            length: bytes,
            maximum_length: bytes,
            buffer: name.as_mut_ptr(),
        };
        let mut attributes = ObjectAttributes {
            length: std::mem::size_of::<ObjectAttributes>() as u32,
            root_directory: std::ptr::null_mut(),
            object_name: &mut unicode,
            attributes: 0x40 | 0x1000, // OBJ_CASE_INSENSITIVE | OBJ_DONT_REPARSE
            security_descriptor: std::ptr::null_mut(),
            security_quality_of_service: std::ptr::null_mut(),
        };
        let mut status = IoStatusBlock {
            status_or_pointer: 0,
            information: 0,
        };
        let mut handle = INVALID_HANDLE_VALUE;
        let result = NtCreateFile(
            &mut handle,
            0x4000_0000 | 0x0010_0000 | FILE_READ_ATTRIBUTES,
            &mut attributes,
            &mut status,
            std::ptr::null_mut(),
            FILE_ATTRIBUTE_NORMAL,
            FILE_SHARE_READ,
            2, // Exclusive FILE_CREATE; readers allowed, writers/deleters denied.
            0x20 | 0x40 | 0x0020_0000, // SYNC_NONALERT | NON_DIRECTORY | OPEN_REPARSE_POINT
            std::ptr::null_mut(),
            0,
        );
        if result < 0
            || (status.status_or_pointer as u32 as i32) < 0
            || status.information != 2
            || handle.is_null()
            || handle == INVALID_HANDLE_VALUE
        {
            if !handle.is_null() && handle != INVALID_HANDLE_VALUE {
                CloseHandle(handle);
            }
            return INVALID_HANDLE_VALUE;
        }
        handle
    }

    fn wide(path: &str) -> Vec<u16> {
        // Only validated local drive paths enter here. Extended spelling avoids
        // MAX_PATH without accepting caller-supplied UNC/device namespaces.
        format!("\\\\?\\{path}")
            .encode_utf16()
            .chain(Some(0))
            .collect()
    }

    unsafe fn attributes(handle: HANDLE) -> Option<u32> {
        let mut info: BY_HANDLE_FILE_INFORMATION = std::mem::zeroed();
        if GetFileInformationByHandle(handle, &mut info) == 0 {
            None
        } else {
            Some(info.dwFileAttributes)
        }
    }

    pub unsafe fn open(ptr: *const u8, len: i64) -> i64 {
        open_impl(ptr, len, || {})
    }

    #[cfg(test)]
    pub(super) unsafe fn open_with_hook<F: FnOnce()>(
        ptr: *const u8,
        len: i64,
        before_create: F,
    ) -> i64 {
        open_impl(ptr, len, before_create)
    }

    unsafe fn open_impl<F: FnOnce()>(ptr: *const u8, len: i64, before_create: F) -> i64 {
        if ptr.is_null() || len <= 0 || len > 4095 {
            return -1;
        }
        let bytes = std::slice::from_raw_parts(ptr, len as usize);
        let text = match std::str::from_utf8(bytes) {
            Ok(s) if !s.contains('\0') => s.replace('/', "\\"),
            _ => return -1,
        };
        let b = text.as_bytes();
        if b.len() < 4 || !b[0].is_ascii_alphabetic() || b[1] != b':' || b[2] != b'\\' {
            return -1;
        }
        let parts: Vec<&str> = text[3..].split('\\').collect();
        if parts.iter().any(|p| {
            p.is_empty()
                || *p == "."
                || *p == ".."
                || p.contains(':')
                || p.ends_with('.')
                || p.ends_with(' ')
        }) {
            return -1;
        }
        let (leaf, parents) = match parts.split_last() {
            Some(p) => p,
            None => return -1,
        };
        let mut path = text[..3].to_owned();
        let mut locks: Vec<OwnedHandle> = Vec::new();
        // Retain every ancestor handle without FILE_SHARE_WRITE/DELETE until leaf
        // creation finishes. Merely checking path attributes would race a
        // junction/directory substitution between validation and CREATE_NEW.
        for part in std::iter::once("").chain(parents.iter().copied()) {
            if !part.is_empty() {
                path.push_str(part);
                path.push('\\');
            }
            let name = wide(&path);
            let handle = CreateFileW(
                name.as_ptr(),
                FILE_READ_ATTRIBUTES | FILE_LIST_DIRECTORY,
                FILE_SHARE_READ,
                std::ptr::null(),
                OPEN_EXISTING,
                FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT,
                std::ptr::null_mut(),
            );
            if handle == INVALID_HANDLE_VALUE {
                return -1;
            }
            let owner = OwnedHandle::from_raw_handle(handle);
            if !attributes(handle).is_some_and(|a| {
                a & FILE_ATTRIBUTE_DIRECTORY != 0 && a & FILE_ATTRIBUTE_REPARSE_POINT == 0
            }) {
                return -1;
            }
            locks.push(owner);
        }
        path.push_str(leaf);
        before_create();
        let handle = create_without_reparse(&path);
        if handle == INVALID_HANDLE_VALUE {
            return -1;
        }
        let owner = OwnedHandle::from_raw_handle(handle);
        if GetFileType(handle) != FILE_TYPE_DISK
            || !attributes(handle)
                .is_some_and(|a| a & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT) == 0)
        {
            return -1;
        }
        owner.into_raw_handle() as i64
    }

    pub fn append_flush(fd: i64, bytes: &[u8]) -> bool {
        if fd <= 0 || bytes.is_empty() || bytes.len() > 9215 || bytes.last() != Some(&b'\n') {
            return false;
        }
        let handle = fd as HANDLE;
        let mut done = 0;
        while done < bytes.len() {
            let mut written = 0;
            if unsafe {
                WriteFile(
                    handle,
                    bytes[done..].as_ptr(),
                    (bytes.len() - done) as u32,
                    &mut written,
                    std::ptr::null_mut(),
                )
            } == 0
                || written == 0
                || written as usize > bytes.len() - done
            {
                return false;
            }
            done += written as usize;
        }
        unsafe { FlushFileBuffers(handle) != 0 }
    }

    pub fn memory_kib() -> (i64, i64) {
        let mut counters = ProcessMemoryCounters::default();
        counters.cb = std::mem::size_of::<ProcessMemoryCounters>() as u32;
        let size = counters.cb;
        if unsafe { K32GetProcessMemoryInfo(GetCurrentProcess(), &mut counters, size) } == 0 {
            return (-1, -1);
        }
        match (
            i64::try_from(counters.working_set / 1024),
            i64::try_from(counters.peak_working_set / 1024),
        ) {
            (Ok(current), Ok(peak)) => (current, peak),
            _ => (-1, -1),
        }
    }

    pub fn monotonic_ms() -> Option<i64> {
        i64::try_from(unsafe { GetTickCount64() })
            .ok()
            .filter(|v| *v > 0)
    }

    pub fn close(fd: i64) -> i8 {
        if fd <= 0 {
            0
        } else {
            (unsafe { CloseHandle(fd as HANDLE) } != 0) as i8
        }
    }
}

#[cfg(windows)]
pub fn windows_append_flush(fd: i64, record: &[u8]) -> bool {
    windows_sink::append_flush(fd, record)
}

#[cfg(windows)]
pub fn windows_process_memory_kib() -> (i64, i64) {
    windows_sink::memory_kib()
}

#[cfg(windows)]
pub fn windows_monotonic_ms() -> Option<i64> {
    windows_sink::monotonic_ms()
}

#[cfg(windows)]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_open(path_ptr: *const u8, path_len: i64) -> i64 {
    windows_sink::open(path_ptr, path_len)
}

#[cfg(not(any(unix, windows)))]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_open(_path_ptr: *const u8, _path_len: i64) -> i64 {
    -1
}

fn token(ptr: *const u8, len: i64, capacity: usize) -> Option<Vec<u8>> {
    if len < 0 || len as u64 >= capacity as u64 || (len > 0 && ptr.is_null()) {
        return None;
    }
    let bytes = if len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }
    };
    let mut out = Vec::with_capacity(bytes.len());
    for &byte in bytes {
        if matches!(byte, b'%' | b' ' | b'=' | b'\n' | b'\r') {
            const HEX: &[u8; 16] = b"0123456789ABCDEF";
            out.extend_from_slice(&[b'%', HEX[(byte >> 4) as usize], HEX[(byte & 15) as usize]]);
        } else {
            out.push(byte);
        }
        if out.len() >= capacity {
            return None;
        }
    }
    Some(out)
}

/// `run_id` field of the `simple.compiler.mem_snapshot.v1` record, percent-encoded
/// with the same rules as `token`. Unset or unencodable reads as `none`,
/// matching `runtime.c:2282-2283` (`if (!run_id || !*run_id) run_id = "none";`)
/// and the interpreter extern at `compiler/src/interpreter_extern/file_io.rs:697`.
///
/// This field is REQUIRED by the schema. `runtime.c`'s `rt_mem_snapshot_record`
/// emits `run_id=%s`, and the Stage-3 evidence validator
/// (`scripts/check/lib/bootstrap-stage3-rss-evidence.c:77-83`) rejects any line
/// that does not carry all 25 named fields, additionally matching `run_id`
/// against the expected run. This Rust copy previously emitted only 24 fields,
/// so its records could never satisfy that validator.
fn run_id_token() -> String {
    let raw = std::env::var("SIMPLE_EVIDENCE_RUN_ID").unwrap_or_default();
    if raw.is_empty() {
        return "none".to_string();
    }
    match token(raw.as_ptr(), raw.len() as i64, 256) {
        Some(encoded) => String::from_utf8_lossy(&encoded).into_owned(),
        None => "none".to_string(),
    }
}

fn status_kib(key: &str) -> i64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|text| {
            text.lines().find_map(|line| {
                line.strip_prefix(key)?
                    .split_whitespace()
                    .next()?
                    .parse()
                    .ok()
            })
        })
        .unwrap_or(-1)
}

/// Rust twin of the C runtime's `rt_process_rss_kib`: -1 when unavailable.
#[no_mangle]
pub extern "C" fn rt_process_rss_kib() -> i64 {
    #[cfg(windows)]
    return windows_process_memory_kib().0;
    #[cfg(not(windows))]
    status_kib("VmRSS:")
}

/// Rust twin of the C runtime's `rt_process_hwm_kib`: -1 when unavailable.
#[no_mangle]
pub extern "C" fn rt_process_hwm_kib() -> i64 {
    #[cfg(windows)]
    return windows_process_memory_kib().1;
    #[cfg(not(windows))]
    status_kib("VmHWM:")
}

#[cfg(not(windows))]
fn monotonic_ms() -> u128 {
    static START: OnceLock<Instant> = OnceLock::new();
    START.get_or_init(Instant::now).elapsed().as_millis()
}

#[allow(clippy::too_many_arguments)]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_record(
    fd: i64,
    seq: i64,
    event: *const u8,
    event_len: i64,
    phase: *const u8,
    phase_len: i64,
    source_index: i64,
    path: *const u8,
    path_len: i64,
    retained: i64,
    keys: i64,
    values: i64,
    traits: i64,
    names: i64,
    symbols: i64,
    functions: i64,
    constants: i64,
    enums: i64,
    structs: i64,
    classes: i64,
) -> i8 {
    #[cfg(not(any(unix, windows)))]
    {
        let _ = (
            fd,
            seq,
            event,
            event_len,
            phase,
            phase_len,
            source_index,
            path,
            path_len,
            retained,
            keys,
            values,
            traits,
            names,
            symbols,
            functions,
            constants,
            enums,
            structs,
            classes,
        );
        return 0;
    }
    #[cfg(windows)]
    {
        let (event, phase, path) = match (
            token(event, event_len, 64),
            token(phase, phase_len, 4096),
            token(path, path_len, 4096),
        ) {
            (Some(e), Some(p), Some(s)) => (e, p, s),
            _ => return 0,
        };
        let raw_run = std::env::var("SIMPLE_EVIDENCE_RUN_ID").unwrap_or_default();
        let run = if raw_run.is_empty() { "none" } else { &raw_run };
        let run = match token(run.as_ptr(), run.len() as i64, 128) {
            Some(r) => r,
            None => return 0,
        };
        // Keep the authoritative Rust 25-field schema accepted by the current
        // evidence parser. No unavailable Windows Job charge is invented.
        let (rss, hwm) = windows_process_memory_kib();
        let monotonic = match windows_monotonic_ms() {
            Some(ms) => ms,
            None => return 0,
        };
        let line = format!("schema=simple.compiler.mem_snapshot.v1 run_id={} seq={seq} pid={} monotonic_ms={} event={} phase={} source_index={source_index} source_path_kind={} source_path={} retained_modules={retained} validation_keys={keys} validation_values={values} shared_traits={traits} hir_names={names} hir_symbols={symbols} hir_functions={functions} hir_constants={constants} hir_enums={enums} hir_structs={structs} hir_classes={classes} heap_live_bytes={} heap_peak_bytes={} rss_kib={rss} hwm_kib={hwm}\n",
            String::from_utf8_lossy(&run), std::process::id(), monotonic, String::from_utf8_lossy(&event), String::from_utf8_lossy(&phase),
            if path_len > 0 { "recorded" } else { "none" }, if path_len > 0 { String::from_utf8_lossy(&path) } else { "-".into() }, rt_heap_live_bytes(), rt_heap_peak_bytes());
        windows_append_flush(fd, line.as_bytes()) as i8
    }
    #[cfg(unix)]
    {
        if fd < 0 || fd > i32::MAX as i64 {
            return 0;
        }
        let (event, phase, path) = match (
            token(event, event_len, 64),
            token(phase, phase_len, 128),
            token(path, path_len, 4096),
        ) {
            (Some(event), Some(phase), Some(path)) => (event, phase, path),
            _ => return 0,
        };
        let event = String::from_utf8_lossy(&event);
        let phase = String::from_utf8_lossy(&phase);
        let path = String::from_utf8_lossy(&path);
        let run_id = run_id_token();
        let line = format!("schema=simple.compiler.mem_snapshot.v1 run_id={run_id} seq={seq} pid={} monotonic_ms={} event={event} phase={phase} source_index={source_index} source_path_kind={} source_path={} retained_modules={retained} validation_keys={keys} validation_values={values} shared_traits={traits} hir_names={names} hir_symbols={symbols} hir_functions={functions} hir_constants={constants} hir_enums={enums} hir_structs={structs} hir_classes={classes} heap_live_bytes={} heap_peak_bytes={} rss_kib={} hwm_kib={}\n",
            libc::getpid(), monotonic_ms(), if path_len > 0 { "recorded" } else { "none" }, if path_len > 0 { path.as_ref() } else { "-" },
            rt_heap_live_bytes(), rt_heap_peak_bytes(), status_kib("VmRSS:"), status_kib("VmHWM:"));
        if line.len() >= 6144 {
            return 0;
        }
        let mut written = 0;
        while written < line.len() {
            let count = libc::write(
                fd as i32,
                line.as_ptr().add(written).cast(),
                line.len() - written,
            );
            if count <= 0 {
                return 0;
            }
            written += count as usize;
        }
        (libc::fsync(fd as i32) == 0) as i8
    }
}

#[no_mangle]
pub extern "C" fn rt_mem_snapshot_close(fd: i64) -> i8 {
    #[cfg(unix)]
    {
        if fd < 0 || fd > i32::MAX as i64 {
            0
        } else {
            (unsafe { libc::close(fd as i32) } == 0) as i8
        }
    }
    #[cfg(windows)]
    {
        windows_sink::close(fd)
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = fd;
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(windows)]
    unsafe fn open_windows(path: &std::path::Path) -> i64 {
        let path = path.to_str().unwrap();
        rt_mem_snapshot_open(path.as_ptr(), path.len() as i64)
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshot_is_exclusive_durable_and_measures_process_memory() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("evidence.log");
        let fd = unsafe { open_windows(&path) };
        assert!(fd > 0);
        assert_eq!(unsafe { open_windows(&path) }, -1);
        let before = windows_monotonic_ms().unwrap();
        assert_eq!(
            unsafe {
                rt_mem_snapshot_record(
                    fd,
                    1,
                    b"stage 3".as_ptr(),
                    7,
                    b"lower=check".as_ptr(),
                    11,
                    2,
                    std::ptr::null(),
                    0,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                )
            },
            1
        );
        let after = windows_monotonic_ms().unwrap();
        assert!(windows_append_flush(fd, b"second-record\n"));
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        assert_eq!(rt_mem_snapshot_close(-1), 0);
        assert_eq!(rt_mem_snapshot_close(0), 0);
        let text = std::fs::read_to_string(&path).unwrap();
        let mut lines = text.lines();
        let record = lines.next().unwrap();
        assert!(record.starts_with("schema=simple.compiler.mem_snapshot.v1 run_id="));
        assert!(record.contains("event=stage%203 phase=lower%3Dcheck"));
        assert!(record.contains("source_path_kind=none source_path=-"));
        assert!(record.contains("retained_modules=3 validation_keys=4 validation_values=5"));
        assert_eq!(record.split(' ').count(), 25);
        let timestamp: i64 = record
            .split(' ')
            .find_map(|s| s.strip_prefix("monotonic_ms="))
            .unwrap()
            .parse()
            .unwrap();
        assert!(timestamp > 0 && timestamp >= before && timestamp <= after);
        assert_eq!(lines.next(), Some("second-record"));
        assert!(lines.next().is_none());
        let (rss, peak) = windows_process_memory_kib();
        assert!(rss > 0 && peak >= rss);
        for key in ["rss_kib=", "hwm_kib="] {
            let value: i64 = record
                .split(' ')
                .find_map(|s| s.strip_prefix(key))
                .unwrap()
                .parse()
                .unwrap();
            assert!(value > 0);
        }
        assert_eq!(unsafe { open_windows(&path) }, -1);
        assert_eq!(std::fs::read_to_string(path).unwrap(), text);
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshot_rejects_invalid_paths_tokens_and_directory_leaf() {
        let dir = tempfile::tempdir().unwrap();
        for spelling in [
            "relative.log",
            "C:relative.log",
            "\\\\server\\share\\file",
            "\\\\?\\C:\\file",
            "C:\\dir\\..\\file",
            "C:\\dir\\file:stream",
            "C:\\dir\\nul\0file",
        ] {
            assert_eq!(
                unsafe { rt_mem_snapshot_open(spelling.as_ptr(), spelling.len() as i64) },
                -1,
                "{spelling:?}"
            );
        }
        assert_eq!(unsafe { rt_mem_snapshot_open(std::ptr::null(), 1) }, -1);
        assert_eq!(unsafe { open_windows(dir.path()) }, -1);
        let path = dir.path().join("tokens.log");
        let fd = unsafe { open_windows(&path) };
        assert!(fd > 0);
        // Refuse before any raw-slice read or allocation, even for an invalid
        // pointer paired with an over-capacity length.
        assert!(token(std::ptr::dangling(), i64::MAX, 64).is_none());
        assert_eq!(
            unsafe {
                rt_mem_snapshot_record(
                    fd,
                    0,
                    std::ptr::dangling(),
                    i64::MAX,
                    b"p".as_ptr(),
                    1,
                    0,
                    std::ptr::null(),
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                )
            },
            0
        );
        assert!(!windows_append_flush(-1, b"bad"));
        assert!(!windows_append_flush(0, b"bad"));
        assert!(!windows_append_flush(fd, b""));
        assert!(!windows_append_flush(fd, b"missing-newline"));
        assert!(!windows_append_flush(fd, &vec![b'x'; 9216]));
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 0);
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshot_refuses_an_ancestor_with_an_existing_writer() {
        use std::os::windows::fs::OpenOptionsExt;
        let dir = tempfile::tempdir().unwrap();
        let parent = dir.path().join("parent");
        std::fs::create_dir(&parent).unwrap();
        let writer = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .share_mode(7)
            .custom_flags(0x0200_0000)
            .open(&parent)
            .unwrap();
        let path = parent.join("evidence.log");
        // Omitting FILE_SHARE_DELETE only would still admit this writer and
        // permit an in-place reparse mutation while creation validates parents.
        assert_eq!(unsafe { open_windows(&path) }, -1);
        assert!(!path.exists());
        drop(writer);
        let fd = unsafe { open_windows(&path) };
        assert!(fd > 0);
        assert!(windows_append_flush(fd, b"writer-free\n"));
        assert_eq!(std::fs::read(&path).unwrap(), b"writer-free\n");
        assert_eq!(unsafe { open_windows(&path) }, -1);
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        assert_eq!(std::fs::read(path).unwrap(), b"writer-free\n");
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshot_refuses_an_ancestor_metadata_only_reparse_after_validation() {
        use std::os::windows::io::{FromRawHandle, OwnedHandle};
        use windows_sys::Win32::Foundation::{HANDLE, INVALID_HANDLE_VALUE};
        use windows_sys::Win32::Storage::FileSystem::{
            CreateFileW, FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT,
            FILE_WRITE_ATTRIBUTES, OPEN_EXISTING,
        };
        #[link(name = "kernel32")]
        extern "system" {
            fn DeviceIoControl(
                handle: HANDLE,
                code: u32,
                input: *const u8,
                input_len: u32,
                output: *mut u8,
                output_len: u32,
                returned: *mut u32,
                overlapped: *mut std::ffi::c_void,
            ) -> i32;
        }
        let dir = tempfile::tempdir().unwrap();
        let parent = dir.path().join("parent");
        let redirect = dir.path().join("redirect");
        std::fs::create_dir(&parent).unwrap();
        std::fs::create_dir(&redirect).unwrap();
        let wide: Vec<u16> = parent
            .to_str()
            .unwrap()
            .encode_utf16()
            .chain(Some(0))
            .collect();
        let handle = unsafe {
            CreateFileW(
                wide.as_ptr(),
                FILE_WRITE_ATTRIBUTES,
                7,
                std::ptr::null(),
                OPEN_EXISTING,
                FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT,
                std::ptr::null_mut(),
            )
        };
        assert_ne!(handle, INVALID_HANDLE_VALUE);
        let owner = unsafe { OwnedHandle::from_raw_handle(handle) };
        // Actual IO_REPARSE_TAG_MOUNT_POINT buffer from winnt.h/winioctl.h:
        // substitute NT name and printable DOS name, both UTF16 terminated.
        let print = redirect.to_str().unwrap();
        let substitute: Vec<u16> = format!("\\??\\{print}")
            .encode_utf16()
            .chain(Some(0))
            .collect();
        let printable: Vec<u16> = print.encode_utf16().chain(Some(0)).collect();
        let mut names = Vec::new();
        for c in substitute.iter().chain(printable.iter()) {
            names.extend_from_slice(&c.to_le_bytes());
        }
        let mut reparse = Vec::new();
        reparse.extend_from_slice(&0xa000_0003u32.to_le_bytes());
        reparse.extend_from_slice(&u16::try_from(8 + names.len()).unwrap().to_le_bytes());
        reparse.extend_from_slice(&0u16.to_le_bytes());
        for n in [
            0,
            (substitute.len() - 1) * 2,
            substitute.len() * 2,
            (printable.len() - 1) * 2,
        ] {
            reparse.extend_from_slice(&u16::try_from(n).unwrap().to_le_bytes());
        }
        reparse.extend_from_slice(&names);
        let remove = [3u8, 0, 0, 0xa0, 0, 0, 0, 0];
        let ioctl = |code, bytes: &[u8]| {
            let mut returned = 0;
            unsafe {
                DeviceIoControl(
                    handle,
                    code,
                    bytes.as_ptr(),
                    bytes.len() as u32,
                    std::ptr::null_mut(),
                    0,
                    &mut returned,
                    std::ptr::null_mut(),
                )
            }
        };
        // Establish a genuine metadata-only mutation before testing the race.
        assert_ne!(
            ioctl(0x0009_00a4, &reparse),
            0,
            "metadata-only junction setup: {}",
            std::io::Error::last_os_error()
        );
        assert_ne!(ioctl(0x0009_00ac, &remove), 0);
        let leaf = parent.join("evidence.log");
        let spelling = leaf.to_str().unwrap();
        let mut mutation = 0;
        let fd = unsafe {
            windows_sink::open_with_hook(spelling.as_ptr(), spelling.len() as i64, || {
                mutation = ioctl(0x0009_00a4, &reparse);
            })
        };
        // Clean the owned junction through its original metadata handle before
        // assertions or TempDir teardown can traverse the redirected spelling.
        let cleaned = if mutation != 0 {
            ioctl(0x0009_00ac, &remove)
        } else {
            1
        };
        if fd > 0 {
            assert_eq!(rt_mem_snapshot_close(fd), 1);
        }
        assert_ne!(cleaned, 0);
        assert_ne!(
            mutation, 0,
            "control did not exercise a post-validation metadata mutation"
        );
        assert_eq!(fd, -1);
        assert!(!redirect.join("evidence.log").exists());
        assert!(!leaf.exists());
        drop(owner);
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshot_rejects_a_junction_ancestor() {
        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("target");
        let link = dir.path().join("junction");
        std::fs::create_dir(&target).unwrap();
        // Junctions require no symlink privilege. Both operands are owned,
        // absent/real temporary directories and never shell-composed strings.
        let output = std::process::Command::new("cmd.exe")
            .args(["/d", "/c", "mklink", "/J"])
            .arg(&link)
            .arg(&target)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "junction creation failed: {:?}",
            output
        );
        let leaf = link.join("evidence.log");
        assert_eq!(unsafe { open_windows(&leaf) }, -1);
        assert!(!target.join("evidence.log").exists());
        // Remove just the junction; recursive teardown must not walk its target.
        std::fs::remove_dir(&link).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_provider_creates_records_and_rejects_reopen() {
        let path = std::env::temp_dir().join(format!(
            "simple-mem-snapshot-{}-{}.log",
            std::process::id(),
            monotonic_ms()
        ));
        let bytes = path.as_os_str().as_encoded_bytes();
        let fd = unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) };
        assert!(fd >= 0);
        assert_eq!(
            unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) },
            -1
        );
        assert_eq!(
            unsafe {
                rt_mem_snapshot_record(
                    fd,
                    1,
                    b"stage 3".as_ptr(),
                    7,
                    b"lower=check".as_ptr(),
                    11,
                    2,
                    std::ptr::null(),
                    0,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                )
            },
            1
        );
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        let text = std::fs::read_to_string(&path).unwrap();
        assert!(text.contains("event=stage%203 phase=lower%3Dcheck"));
        // 25-field schema: `run_id` sits between `schema` and `seq`, matching
        // runtime.c and what the Stage-3 evidence validator parses.
        let last = text.lines().last().unwrap();
        assert!(last.starts_with("schema=simple.compiler.mem_snapshot.v1 run_id="));
        assert_eq!(last.split(' ').count(), 25);
        assert!(text.ends_with('\n'));
        std::fs::remove_file(path).unwrap();
    }

    /// Moved here from `simple-native-all`'s duplicate provider
    /// (native_all/src/mem_snapshot_provider.rs), which defined a second
    /// `rt_mem_snapshot_open`/`_record`/`_close` triple. This crate's copy is
    /// the authoritative one, so its hardening coverage must live here too.
    #[cfg(unix)]
    #[test]
    fn secure_open_is_exclusive_and_rejects_symlinked_parent() {
        use std::os::unix::ffi::OsStrExt;

        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("evidence.log");
        let bytes = target.as_os_str().as_bytes();
        let fd = unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) };
        assert!(fd >= 0);
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        assert_eq!(
            unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) },
            -1
        );

        let link = dir.path().join("link");
        std::os::unix::fs::symlink(dir.path(), &link).unwrap();
        let linked_target = link.join("other.log");
        let linked = linked_target.as_os_str().as_bytes();
        assert_eq!(
            unsafe { rt_mem_snapshot_open(linked.as_ptr(), linked.len() as i64) },
            -1
        );
    }
}
