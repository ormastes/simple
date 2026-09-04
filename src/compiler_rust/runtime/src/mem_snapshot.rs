//! Bootstrap-runtime implementation of the compiler memory-snapshot ABI.
//!
//! The pure-Simple native path gets these symbols from `runtime.c`.  Bootstrap
//! compiler binaries link `libsimple_native_all.a`, so they need the same real
//! provider here rather than falling through to linker stubs.

use std::ffi::CString;
use std::sync::OnceLock;
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
    let mut parent_fd = libc::open(start.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC);
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
        libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_APPEND | libc::O_NOFOLLOW | libc::O_CLOEXEC,
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

#[cfg(not(unix))]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_open(_path_ptr: *const u8, _path_len: i64) -> i64 {
    -1
}

fn token(ptr: *const u8, len: i64, capacity: usize) -> Option<Vec<u8>> {
    if len < 0 || (len > 0 && ptr.is_null()) {
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

fn status_kib(key: &str) -> i64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|text| {
            text.lines()
                .find_map(|line| line.strip_prefix(key)?.split_whitespace().next()?.parse().ok())
        })
        .unwrap_or(-1)
}

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
    #[cfg(not(unix))]
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
        let line = format!("schema=simple.compiler.mem_snapshot.v1 seq={seq} pid={} monotonic_ms={} event={event} phase={phase} source_index={source_index} source_path_kind={} source_path={} retained_modules={retained} validation_keys={keys} validation_values={values} shared_traits={traits} hir_names={names} hir_symbols={symbols} hir_functions={functions} hir_constants={constants} hir_enums={enums} hir_structs={structs} hir_classes={classes} heap_live_bytes={} heap_peak_bytes={} rss_kib={} hwm_kib={}\n",
            libc::getpid(), monotonic_ms(), if path_len > 0 { "recorded" } else { "none" }, if path_len > 0 { path.as_ref() } else { "-" },
            rt_heap_live_bytes(), rt_heap_peak_bytes(), status_kib("VmRSS:"), status_kib("VmHWM:"));
        if line.len() >= 6144 {
            return 0;
        }
        let mut written = 0;
        while written < line.len() {
            let count = libc::write(fd as i32, line.as_ptr().add(written).cast(), line.len() - written);
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
    #[cfg(not(unix))]
    {
        let _ = fd;
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) }, -1);
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
        assert!(text.ends_with('\n'));
        std::fs::remove_file(path).unwrap();
    }
}
