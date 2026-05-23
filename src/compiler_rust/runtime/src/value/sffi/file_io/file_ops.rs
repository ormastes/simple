//! High-level File Operations
//!
//! This module provides high-level file operations including:
//! - Canonicalize: Resolve absolute paths with symbolic links
//! - Read/Write: High-level text file I/O
//! - ReadLines: Read file as array of lines
//! - Append: Append text to files
//! - Binary I/O: Read/write raw bytes
//! - Copy: Copy files from source to destination
//! - Remove: Delete files
//! - Rename/Move: Move or rename files

use crate::value::collections::{
    alloc_runtime_string, rt_array_new, rt_array_push, rt_byte_array_new, rt_string_data, rt_string_len, rt_string_new,
    rt_string_new_with_len_hash, RuntimeArray,
};
use crate::value::{HeapHeader, RuntimeValue};
use memmap2::MmapOptions;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
#[cfg(unix)]
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::{Mutex, OnceLock};
use std::time::SystemTime;

const READ_FILE_CAPABILITY_ID: u64 = 0x2e97_865a_b851_28c3;
const WRITE_FILE_CAPABILITY_ID: u64 = 0x2fa1_6c1d_95e4_306a;

struct WriteAtCache {
    path: String,
    file: File,
    position: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct FileStamp {
    len: u64,
    modified: Option<SystemTime>,
}

struct ReadTextCache {
    path: String,
    stamp: FileStamp,
    value: RuntimeValue,
}

struct MmapLenCache {
    path: String,
    stamp: FileStamp,
    len: i64,
}

thread_local! {
    static WRITE_AT_CACHE: RefCell<Option<WriteAtCache>> = const { RefCell::new(None) };
}

fn read_text_cache() -> &'static Mutex<Option<ReadTextCache>> {
    static CACHE: OnceLock<Mutex<Option<ReadTextCache>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(None))
}

fn mmap_len_cache() -> &'static Mutex<Option<MmapLenCache>> {
    static CACHE: OnceLock<Mutex<Option<MmapLenCache>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(None))
}

#[cfg(test)]
fn security_metadata_id(value: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in value.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn runtime_capability_allowed(capability_id: u64) -> bool {
    crate::security_runtime::rt_security_sandbox_capability_allowed(capability_id)
}

fn file_stamp(path: &Path) -> Option<FileStamp> {
    let metadata = std::fs::metadata(path).ok()?;
    Some(FileStamp {
        len: metadata.len(),
        modified: metadata.modified().ok(),
    })
}

#[cfg(unix)]
fn write_all_cached_at(file: &File, data: &[u8], offset: usize, sequential: bool) -> bool {
    let fd = file.as_raw_fd();
    let mut written = 0usize;
    while written < data.len() {
        let ptr = unsafe { data.as_ptr().add(written) } as *const libc::c_void;
        let len = data.len() - written;
        let rc = if sequential {
            unsafe { libc::write(fd, ptr, len) }
        } else {
            unsafe { libc::pwrite(fd, ptr, len, (offset + written) as libc::off_t) }
        };
        if rc <= 0 {
            return false;
        }
        written += rc as usize;
    }
    true
}

#[cfg(not(unix))]
fn write_all_cached_at(file: &mut File, data: &[u8], offset: usize, sequential: bool) -> bool {
    if !sequential && file.seek(SeekFrom::Start(offset as u64)).is_err() {
        return false;
    }
    file.write_all(data).is_ok()
}

fn invalidate_file_caches(path: &str) {
    WRITE_AT_CACHE.with(|cache| {
        let mut guard = cache.borrow_mut();
        if guard.as_ref().map(|cached| cached.path.as_str()) == Some(path) {
            *guard = None;
        }
    });
    invalidate_read_mmap_caches(path);
}

fn invalidate_read_mmap_caches(path: &str) {
    if let Ok(mut guard) = read_text_cache().lock() {
        if guard.as_ref().map(|cached| cached.path.as_str()) == Some(path) {
            *guard = None;
        }
    }
    if let Ok(mut guard) = mmap_len_cache().lock() {
        if guard.as_ref().map(|cached| cached.path.as_str()) == Some(path) {
            *guard = None;
        }
    }
}

fn tagged_text_to_bytes(value: i64) -> Option<&'static [u8]> {
    let text = RuntimeValue::from_raw(value as u64);
    let len = rt_string_len(text);
    if len < 0 {
        return None;
    }
    let data = rt_string_data(text);
    if data.is_null() {
        return None;
    }
    unsafe { Some(std::slice::from_raw_parts(data, len as usize)) }
}

fn tagged_text_to_str(value: i64) -> Option<&'static str> {
    std::str::from_utf8(tagged_text_to_bytes(value)?).ok()
}

unsafe fn path_from_raw_or_tagged(path_ptr: *const u8, path_len: u64) -> Option<&'static str> {
    if path_len == 0 {
        let tagged = path_ptr as i64;
        if RuntimeValue::from_raw(tagged as u64).is_heap() {
            return tagged_text_to_str(tagged);
        }
    }
    if path_ptr.is_null() {
        return None;
    }
    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    std::str::from_utf8(path_bytes).ok()
}

fn string_to_tagged_text(value: &str) -> i64 {
    rt_string_new(value.as_ptr(), value.len() as u64).to_raw() as i64
}

pub(crate) unsafe fn bytes_to_runtime_array(bytes: &[u8]) -> RuntimeValue {
    if bytes.is_empty() {
        return rt_byte_array_new(0);
    }
    let array_handle = rt_byte_array_new(bytes.len() as u64);
    if array_handle.is_nil() {
        return RuntimeValue::NIL;
    }
    let arr = array_handle.as_heap_ptr() as *mut RuntimeArray;
    if arr.is_null() || (*arr).data.is_null() {
        return RuntimeValue::NIL;
    }
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), (*arr).data as *mut u8, bytes.len());
    (*arr).len = bytes.len() as u64;
    array_handle
}

/// Normalize/canonicalize a file path
/// Returns the absolute path with all symbolic links resolved
#[no_mangle]
pub unsafe extern "C" fn rt_file_canonicalize(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    // Avoid std::fs::canonicalize (libc::realpath segfaults in self-hosted binaries).
    // Make absolute and normalize . / .. components instead.
    {
        let p = std::path::Path::new(path_str);
        let abs = if p.is_absolute() {
            p.to_path_buf()
        } else {
            match std::env::current_dir() {
                Ok(cwd) => cwd.join(p),
                Err(_) => return RuntimeValue::NIL,
            }
        };
        let mut out = std::path::PathBuf::new();
        for comp in abs.components() {
            match comp {
                std::path::Component::ParentDir => {
                    out.pop();
                }
                std::path::Component::CurDir => {}
                c => out.push(c),
            }
        }
        let canonical_str = out.to_string_lossy();
        let bytes = canonical_str.as_bytes();
        rt_string_new(bytes.as_ptr(), bytes.len() as u64)
    }
}

/// Read entire file as text
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if !runtime_capability_allowed(READ_FILE_CAPABILITY_ID) {
        return RuntimeValue::NIL;
    }
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    if let Ok(guard) = read_text_cache().lock() {
        if let Some(cached) = guard.as_ref() {
            if cached.path == path_str {
                return cached.value;
            }
        }
    }
    let path = Path::new(path_str);
    let stamp = match file_stamp(path) {
        Some(stamp) => stamp,
        None => return RuntimeValue::NIL,
    };

    match File::open(path) {
        Ok(mut file) => {
            let len = stamp.len;
            let Some(ptr) = alloc_runtime_string(len) else {
                return RuntimeValue::NIL;
            };
            let data_ptr = ptr.add(1) as *mut u8;
            let buf = std::slice::from_raw_parts_mut(data_ptr, len as usize);
            if file.read_exact(buf).is_err() || std::str::from_utf8(buf).is_err() {
                return RuntimeValue::NIL;
            }
            if buf.contains(&b'\r') {
                let normalized: Vec<u8> = buf.iter().copied().filter(|byte| *byte != b'\r').collect();
                let value = rt_string_new_with_len_hash(normalized.as_ptr(), normalized.len() as u64);
                if let Ok(mut guard) = read_text_cache().lock() {
                    *guard = Some(ReadTextCache {
                        path: path_str.to_string(),
                        stamp,
                        value,
                    });
                }
                return value;
            }
            (*ptr).hash = len;
            let value = RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader);
            if let Ok(mut guard) = read_text_cache().lock() {
                *guard = Some(ReadTextCache {
                    path: path_str.to_string(),
                    stamp,
                    value,
                });
            }
            value
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Read entire file as text (RuntimeValue wrapper)
/// Takes a RuntimeValue string, extracts ptr/len, and calls rt_file_read_text.
/// Returns the string directly on success, NIL on failure.
/// (Compiled Simple code expects a plain string, not an Option/Enum wrapper.)
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text_rv(path: RuntimeValue) -> RuntimeValue {
    use crate::value::collections::{rt_string_data, rt_string_len};
    if path.is_nil() || path.0 == 0 {
        return RuntimeValue::NIL;
    }
    let len = rt_string_len(path);
    let ptr = rt_string_data(path);
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    rt_file_read_text(ptr, len as u64)
}

/// Write text to file
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_text(
    path_ptr: *const u8,
    path_len: u64,
    content_ptr: *const u8,
    content_len: u64,
) -> bool {
    if !runtime_capability_allowed(WRITE_FILE_CAPABILITY_ID) {
        return false;
    }
    if path_ptr.is_null() || content_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let content_bytes = std::slice::from_raw_parts(content_ptr, content_len as usize);
    let content_str = match std::str::from_utf8(content_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    invalidate_file_caches(path_str);
    std::fs::write(path_str, content_str).is_ok()
}

/// Synchronize file contents and metadata with durable storage.
#[no_mangle]
pub unsafe extern "C" fn rt_file_fsync(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    match OpenOptions::new().read(true).open(Path::new(path_str)) {
        Ok(file) => file.sync_all().is_ok(),
        Err(_) => false,
    }
}

/// Synchronize the cached write-at handle when it matches `path`.
///
/// Falls back to `rt_file_fsync` when the current thread has no matching
/// write-at cache. This keeps the public path-based API durable while avoiding
/// an open-per-fence cycle on WAL-style sequential append loops.
#[no_mangle]
pub unsafe extern "C" fn rt_file_fsync_cached(path_ptr: *const u8, path_len: u64) -> bool {
    let Some(path_str) = path_from_raw_or_tagged(path_ptr, path_len) else {
        return false;
    };
    let synced_cached = WRITE_AT_CACHE.with(|cache| {
        let guard = cache.borrow();
        match guard.as_ref() {
            Some(cached) if cached.path == path_str => Some(cached.file.sync_all().is_ok()),
            _ => None,
        }
    });
    match synced_cached {
        Some(ok) => ok,
        None => rt_file_fsync(path_ptr, path_len),
    }
}

/// Copy file from src to dest
#[no_mangle]
pub unsafe extern "C" fn rt_file_copy(src_ptr: *const u8, src_len: u64, dest_ptr: *const u8, dest_len: u64) -> bool {
    if src_ptr.is_null() || dest_ptr.is_null() {
        return false;
    }

    let src_bytes = std::slice::from_raw_parts(src_ptr, src_len as usize);
    let src_str = match std::str::from_utf8(src_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let dest_bytes = std::slice::from_raw_parts(dest_ptr, dest_len as usize);
    let dest_str = match std::str::from_utf8(dest_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::copy(src_str, dest_str).is_ok()
}

/// Remove/delete a file
#[no_mangle]
pub unsafe extern "C" fn rt_file_remove(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    invalidate_file_caches(path_str);
    std::fs::remove_file(path_str).is_ok()
}

/// Return file size in bytes, or -1 on failure.
#[no_mangle]
pub unsafe extern "C" fn rt_file_size(path_ptr: *const u8, path_len: u64) -> i64 {
    if path_ptr.is_null() {
        return -1;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match std::fs::metadata(path_str) {
        Ok(metadata) => metadata.len() as i64,
        Err(_) => -1,
    }
}

/// Compute the SHA256 hash of a file and return it as a hex string.
#[no_mangle]
pub unsafe extern "C" fn rt_file_hash_sha256(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    let content = match std::fs::read(path_str) {
        Ok(content) => content,
        Err(_) => return RuntimeValue::NIL,
    };

    let mut hasher = Sha256::new();
    hasher.update(&content);
    let digest = hasher.finalize();
    let hex = format!("{:x}", digest);
    rt_string_new(hex.as_ptr(), hex.len() as u64)
}

/// Best-effort file lock shim for native runtime-only bundles.
///
/// The non-compiler native specs only need this symbol to link; they do not
/// rely on real locking semantics here. Keep the ABI permissive so existing
/// native call sites that pass tagged RuntimeValue strings continue to link.
#[no_mangle]
pub extern "C" fn rt_file_lock(_path: i64) -> i64 {
    1
}

/// Best-effort file unlock shim paired with `rt_file_lock`.
#[no_mangle]
pub extern "C" fn rt_file_unlock(_handle: i64) -> bool {
    true
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_text(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    let path = match path_from_raw_or_tagged(path_ptr, path_len) {
        Some(path) => path,
        None => return RuntimeValue::NIL,
    };
    match std::fs::File::open(Path::new(path)) {
        Ok(file) => match MmapOptions::new().map(&file) {
            Ok(map) => match std::str::from_utf8(&map) {
                Ok(content) => rt_string_new_with_len_hash(content.as_ptr(), content.len() as u64),
                Err(_) => {
                    let content = String::from_utf8_lossy(&map);
                    rt_string_new_with_len_hash(content.as_ptr(), content.len() as u64)
                }
            },
            Err(_) => RuntimeValue::NIL,
        },
        Err(_) => RuntimeValue::NIL,
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_len(path_ptr: *const u8, path_len: u64) -> i64 {
    let path = match path_from_raw_or_tagged(path_ptr, path_len) {
        Some(path) => path,
        None => return -1,
    };
    if let Ok(guard) = mmap_len_cache().lock() {
        if let Some(cached) = guard.as_ref() {
            if cached.path == path {
                return cached.len;
            }
        }
    }
    let path_ref = Path::new(path);
    let stamp = match file_stamp(path_ref) {
        Some(stamp) => stamp,
        None => return -1,
    };
    let file = match std::fs::File::open(path_ref) {
        Ok(file) => file,
        Err(_) => return -1,
    };
    match MmapOptions::new().map(&file) {
        Ok(map) => {
            let len = map.len() as i64;
            if let Ok(mut guard) = mmap_len_cache().lock() {
                *guard = Some(MmapLenCache {
                    path: path.to_string(),
                    stamp,
                    len,
                });
            }
            len
        }
        Err(_) => -1,
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_text_rv(path: RuntimeValue) -> RuntimeValue {
    if path.is_nil() || path.0 == 0 {
        return RuntimeValue::NIL;
    }
    let len = rt_string_len(path);
    let ptr = rt_string_data(path);
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    rt_file_mmap_read_text(ptr, len as u64)
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_bytes(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    let path = match path_from_raw_or_tagged(path_ptr, path_len) {
        Some(path) => path,
        None => return RuntimeValue::NIL,
    };
    let bytes = match std::fs::read(Path::new(path)) {
        Ok(bytes) => bytes,
        Err(_) => return RuntimeValue::NIL,
    };
    bytes_to_runtime_array(&bytes)
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_bytes_rv(path: RuntimeValue) -> RuntimeValue {
    if path.is_nil() || path.0 == 0 {
        return RuntimeValue::NIL;
    }
    let len = rt_string_len(path);
    let ptr = rt_string_data(path);
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    rt_file_mmap_read_bytes(ptr, len as u64)
}

#[no_mangle]
pub extern "C" fn rt_file_read_text_at(path: i64, offset: i64, size: i64) -> i64 {
    let Some(path) = tagged_text_to_str(path) else {
        return RuntimeValue::NIL.to_raw() as i64;
    };
    if size <= 0 {
        return string_to_tagged_text("");
    }
    let Ok(mut file) = std::fs::File::open(Path::new(path)) else {
        return RuntimeValue::NIL.to_raw() as i64;
    };
    let start = offset.max(0) as usize;
    if file.seek(SeekFrom::Start(start as u64)).is_err() {
        return RuntimeValue::NIL.to_raw() as i64;
    }
    let mut buf = vec![0; size as usize];
    match file.read(&mut buf) {
        Ok(read_len) => {
            buf.truncate(read_len);
            string_to_tagged_text(&String::from_utf8_lossy(&buf))
        }
        Err(_) => RuntimeValue::NIL.to_raw() as i64,
    }
}

#[no_mangle]
pub extern "C" fn rt_file_write_text_at(path: i64, offset: i64, data: i64) -> i64 {
    let Some(path) = tagged_text_to_str(path) else {
        return -1;
    };
    let Some(data_bytes) = tagged_text_to_bytes(data) else {
        return -1;
    };
    invalidate_read_mmap_caches(path);
    let start = offset.max(0) as usize;
    WRITE_AT_CACHE.with(|cache| {
        let mut guard = cache.borrow_mut();
        if guard.as_ref().map(|cached| cached.path.as_str()) != Some(path) {
            let file = match OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(false)
                .open(Path::new(path))
            {
                Ok(file) => file,
                Err(_) => return -1,
            };
            *guard = Some(WriteAtCache {
                path: path.to_string(),
                file,
                position: 0,
            });
        }
        let Some(cached) = guard.as_mut() else {
            return -1;
        };
        let sequential = cached.position == start;
        #[cfg(unix)]
        let wrote = write_all_cached_at(&cached.file, data_bytes, start, sequential);
        #[cfg(not(unix))]
        let wrote = write_all_cached_at(&mut cached.file, data_bytes, start, sequential);
        if wrote {
            cached.position = start + data_bytes.len();
            data_bytes.len() as i64
        } else {
            -1
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_file_write_text_at_cached(offset: i64, data: i64) -> i64 {
    let Some(data_bytes) = tagged_text_to_bytes(data) else {
        return -1;
    };
    let start = offset.max(0) as usize;
    WRITE_AT_CACHE.with(|cache| {
        let mut guard = cache.borrow_mut();
        let Some(cached) = guard.as_mut() else {
            return -1;
        };
        let sequential = cached.position == start;
        #[cfg(unix)]
        let wrote = write_all_cached_at(&cached.file, data_bytes, start, sequential);
        #[cfg(not(unix))]
        let wrote = write_all_cached_at(&mut cached.file, data_bytes, start, sequential);
        if wrote {
            cached.position = start + data_bytes.len();
            data_bytes.len() as i64
        } else {
            -1
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_file_write_text_at_cached_repeat(iterations: i64, data: i64) -> i64 {
    if iterations <= 0 {
        return 0;
    }
    let Some(data_bytes) = tagged_text_to_bytes(data) else {
        return -1;
    };
    WRITE_AT_CACHE.with(|cache| {
        let mut guard = cache.borrow_mut();
        let Some(cached) = guard.as_mut() else {
            return -1;
        };
        #[cfg(unix)]
        {
            let count = iterations as usize;
            if count <= 1024 {
                let mut iovecs = Vec::with_capacity(count);
                for _ in 0..count {
                    iovecs.push(libc::iovec {
                        iov_base: data_bytes.as_ptr() as *mut libc::c_void,
                        iov_len: data_bytes.len(),
                    });
                }
                let expected = data_bytes.len().saturating_mul(count);
                let rc = unsafe { libc::writev(cached.file.as_raw_fd(), iovecs.as_ptr(), iovecs.len() as i32) };
                if rc == expected as isize {
                    cached.position += expected;
                    return expected as i64;
                }
                if rc < 0 {
                    return -1;
                }
            }
        }
        let mut total = 0i64;
        for _ in 0..iterations {
            let start = cached.position;
            #[cfg(unix)]
            let wrote = write_all_cached_at(&cached.file, data_bytes, start, true);
            #[cfg(not(unix))]
            let wrote = write_all_cached_at(&mut cached.file, data_bytes, start, true);
            if !wrote {
                return -1;
            }
            cached.position = start + data_bytes.len();
            total += data_bytes.len() as i64;
        }
        total
    })
}

#[no_mangle]
pub extern "C" fn rt_mmap(_path: i64, _size: i64, _offset: i64, _readonly: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_munmap(_addr: i64, _size: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_madvise(_addr: i64, _size: i64, _advice: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_msync(_addr: i64, _size: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_getpid() -> i64 {
    std::process::id() as i64
}

/// Rename/move a file or directory
#[no_mangle]
pub unsafe extern "C" fn rt_file_rename(from_ptr: *const u8, from_len: u64, to_ptr: *const u8, to_len: u64) -> bool {
    if from_ptr.is_null() || to_ptr.is_null() {
        return false;
    }

    let from_bytes = std::slice::from_raw_parts(from_ptr, from_len as usize);
    let from_str = match std::str::from_utf8(from_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let to_bytes = std::slice::from_raw_parts(to_ptr, to_len as usize);
    let to_str = match std::str::from_utf8(to_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::fs::rename(from_str, to_str).is_ok()
}

/// Read file as array of lines
/// Returns an array of strings, one per line
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_lines(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_to_string(path_str) {
        Ok(content) => {
            let lines: Vec<&str> = content.lines().collect();
            let array_handle = rt_array_new(lines.len() as u64);

            for line in lines {
                let bytes = line.as_bytes();
                let str_value = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
                rt_array_push(array_handle, str_value);
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Append text to file (creates file if it doesn't exist)
#[no_mangle]
pub unsafe extern "C" fn rt_file_append_text(
    path_ptr: *const u8,
    path_len: u64,
    content_ptr: *const u8,
    content_len: u64,
) -> bool {
    if path_ptr.is_null() || content_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let content_bytes = std::slice::from_raw_parts(content_ptr, content_len as usize);
    let content_str = match std::str::from_utf8(content_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    match OpenOptions::new().create(true).append(true).open(path_str) {
        Ok(mut file) => file.write_all(content_str.as_bytes()).is_ok(),
        Err(_) => false,
    }
}

/// Read file as raw bytes
/// Returns an array of integers (0-255)
#[no_mangle]
pub unsafe extern "C" fn rt_file_read_bytes(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read(path_str) {
        Ok(bytes) => bytes_to_runtime_array(&bytes),
        Err(_) => RuntimeValue::NIL,
    }
}

/// Create a byte array ([u8]) from a raw memory pointer.
/// Used by LLVM memory buffer emission to avoid temp file I/O.
#[no_mangle]
pub unsafe extern "C" fn rt_bytes_from_raw(ptr: i64, len: i64) -> RuntimeValue {
    if ptr == 0 || len <= 0 {
        return rt_array_new(0);
    }
    let src = ptr as usize as *const u8;
    let slice = std::slice::from_raw_parts(src, len as usize);
    bytes_to_runtime_array(slice)
}

/// Convert a text RuntimeValue to a byte array ([u8]).
#[no_mangle]
pub extern "C" fn rt_text_to_bytes(text: RuntimeValue) -> RuntimeValue {
    let text_len = rt_string_len(text);
    if text_len <= 0 {
        return rt_array_new(0);
    }

    let text_ptr = rt_string_data(text);
    if text_ptr.is_null() {
        return rt_array_new(0);
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(text_ptr, text_len as usize);
        let array_handle = rt_array_new(text_len as u64);
        for &byte in bytes {
            let byte_value = RuntimeValue::from_int(byte as i64);
            rt_array_push(array_handle, byte_value);
        }
        array_handle
    }
}

/// Convert a byte array ([u8]) to a UTF-8 text value.
#[no_mangle]
pub extern "C" fn rt_bytes_to_text(bytes: RuntimeValue) -> RuntimeValue {
    let len = crate::value::collections::rt_array_len(bytes);
    if len < 0 {
        return RuntimeValue::NIL;
    }

    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = crate::value::collections::rt_array_get(bytes, i);
        if !value.is_int() {
            return RuntimeValue::NIL;
        }
        let byte = value.as_int();
        if !(0..=255).contains(&byte) {
            return RuntimeValue::NIL;
        }
        out.push(byte as u8);
    }

    unsafe { rt_string_new(out.as_ptr(), out.len() as u64) }
}

/// Write raw bytes to file
/// Takes an array of integers (0-255)
#[no_mangle]
pub unsafe extern "C" fn rt_file_write_bytes(
    path_ptr: *const u8,
    path_len: u64,
    data_ptr: *const u8,
    data_len: u64,
) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    // If data_ptr is null but len is 0, write empty file
    if data_ptr.is_null() {
        return std::fs::write(path_str, []).is_ok();
    }

    let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
    std::fs::write(path_str, data).is_ok()
}

/// Move file from source to destination
/// Unlike rename, this works across filesystems by copying then deleting
#[no_mangle]
pub unsafe extern "C" fn rt_file_move(src_ptr: *const u8, src_len: u64, dest_ptr: *const u8, dest_len: u64) -> bool {
    if src_ptr.is_null() || dest_ptr.is_null() {
        return false;
    }

    let src_bytes = std::slice::from_raw_parts(src_ptr, src_len as usize);
    let src_str = match std::str::from_utf8(src_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let dest_bytes = std::slice::from_raw_parts(dest_ptr, dest_len as usize);
    let dest_str = match std::str::from_utf8(dest_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    // Try rename first (fast path, same filesystem)
    if std::fs::rename(src_str, dest_str).is_ok() {
        return true;
    }

    // Fallback: copy then delete (works across filesystems)
    if std::fs::copy(src_str, dest_str).is_ok() {
        // Only delete source if copy succeeded
        return std::fs::remove_file(src_str).is_ok();
    }

    false
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};
    use std::fs;
    use tempfile::TempDir;

    // Helper to create string pointer for SFFI
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    // Helper to extract string from RuntimeValue
    unsafe fn extract_string(val: RuntimeValue) -> String {
        if val.is_nil() {
            return String::new();
        }
        let len = rt_string_len(val);
        let ptr = rt_string_data(val);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

    #[test]
    fn test_file_read_write_text() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        unsafe {
            // Write text
            let content = "Hello, World!";
            let (content_ptr, content_len) = str_to_ptr(content);
            assert!(rt_file_write_text(path_ptr, path_len, content_ptr, content_len));

            // Read text
            let result = rt_file_read_text(path_ptr, path_len);
            let read_content = extract_string(result);
            assert_eq!(read_content, content);
        }
    }

    #[test]
    fn sandbox_capability_table_gates_file_text_io() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("sandboxed.txt");
        fs::write(&file_path, "allowed").unwrap();
        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);
        let read_only_sandbox_id = security_metadata_id("read_only_sandbox");
        let write_only_sandbox_id = security_metadata_id("write_only_sandbox");
        let read_only_manifest = "\
sandbox_lowering:
  read_only_sandbox:
    source_backend: simple_vm
    lowered_backend: simple_vm_capability_table
    capability_handles:
      - ReadFile
";
        let write_only_manifest = "\
sandbox_lowering:
  write_only_sandbox:
    source_backend: simple_vm
    lowered_backend: simple_vm_capability_table
    capability_handles:
      - WriteFile
";

        unsafe {
            crate::security_runtime::rt_security_reset_counters();
            crate::security_runtime::rt_security_load_registry_sdn(
                read_only_manifest.as_ptr(),
                read_only_manifest.len() as u64,
            );
            crate::security_runtime::rt_security_load_registry_sdn(
                write_only_manifest.as_ptr(),
                write_only_manifest.len() as u64,
            );

            crate::security_runtime::rt_security_enter_sandbox(read_only_sandbox_id);
            let read_result = rt_file_read_text(path_ptr, path_len);
            assert_eq!(extract_string(read_result), "allowed");
            let (denied_content_ptr, denied_content_len) = str_to_ptr("denied");
            assert!(!rt_file_write_text(
                path_ptr,
                path_len,
                denied_content_ptr,
                denied_content_len
            ));
            crate::security_runtime::rt_security_exit_sandbox(read_only_sandbox_id);

            crate::security_runtime::rt_security_enter_sandbox(write_only_sandbox_id);
            assert_eq!(rt_file_read_text(path_ptr, path_len), RuntimeValue::NIL);
            let (allowed_content_ptr, allowed_content_len) = str_to_ptr("written");
            assert!(rt_file_write_text(
                path_ptr,
                path_len,
                allowed_content_ptr,
                allowed_content_len
            ));
            crate::security_runtime::rt_security_exit_sandbox(write_only_sandbox_id);
        }
    }

    #[test]
    fn test_file_copy() {
        let temp_dir = TempDir::new().unwrap();
        let src_path = temp_dir.path().join("source.txt");
        let dest_path = temp_dir.path().join("dest.txt");

        fs::write(&src_path, "test content").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_copy(src_ptr, src_len, dest_ptr, dest_len));
            assert!(dest_path.exists());

            let content = fs::read_to_string(&dest_path).unwrap();
            assert_eq!(content, "test content");
        }
    }

    #[test]
    fn test_file_fsync_existing_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("sync.txt");
        fs::write(&file_path, "durable").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_file_fsync(path_ptr, path_len));
        }
    }

    #[test]
    fn test_file_fsync_missing_file_fails() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("missing.txt");
        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        unsafe {
            assert!(!rt_file_fsync(path_ptr, path_len));
        }
    }

    #[test]
    fn test_file_fsync_cached_uses_write_at_cache() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("cached_sync.txt");
        let path_str = file_path.to_str().unwrap();
        let path = string_to_tagged_text(path_str);
        let payload = string_to_tagged_text("durable");
        let (path_ptr, path_len) = str_to_ptr(path_str);

        assert_eq!(rt_file_write_text_at(path, 0, payload), 7);
        unsafe {
            assert!(rt_file_fsync_cached(path_ptr, path_len));
        }
        assert_eq!(fs::read_to_string(file_path).unwrap(), "durable");
    }

    #[test]
    fn test_file_remove() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("to_remove.txt");
        fs::write(&file_path, "test").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_file_remove(ptr, len));
            assert!(!file_path.exists());
        }
    }

    #[test]
    fn test_file_rename() {
        let temp_dir = TempDir::new().unwrap();
        let from_path = temp_dir.path().join("old.txt");
        let to_path = temp_dir.path().join("new.txt");

        fs::write(&from_path, "content").unwrap();

        let from_str = from_path.to_str().unwrap();
        let to_str = to_path.to_str().unwrap();

        unsafe {
            let (from_ptr, from_len) = str_to_ptr(from_str);
            let (to_ptr, to_len) = str_to_ptr(to_str);

            assert!(rt_file_rename(from_ptr, from_len, to_ptr, to_len));
            assert!(!from_path.exists());
            assert!(to_path.exists());
        }
    }

    #[test]
    fn test_file_read_lines() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("lines.txt");
        fs::write(&file_path, "line1\nline2\nline3").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_file_read_lines(ptr, len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 3);
        }
    }

    #[test]
    fn test_file_read_lines_empty_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("empty.txt");
        fs::write(&file_path, "").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_file_read_lines(ptr, len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 0);
        }
    }

    #[test]
    fn test_file_append_text() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("append.txt");
        fs::write(&file_path, "Hello").unwrap();

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);
        let (content_ptr, content_len) = str_to_ptr(", World!");

        unsafe {
            assert!(rt_file_append_text(path_ptr, path_len, content_ptr, content_len));

            let content = fs::read_to_string(&file_path).unwrap();
            assert_eq!(content, "Hello, World!");
        }
    }

    #[test]
    fn test_file_append_text_creates_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("new_append.txt");

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);
        let (content_ptr, content_len) = str_to_ptr("New content");

        unsafe {
            assert!(rt_file_append_text(path_ptr, path_len, content_ptr, content_len));
            assert!(file_path.exists());

            let content = fs::read_to_string(&file_path).unwrap();
            assert_eq!(content, "New content");
        }
    }

    #[test]
    fn test_file_write_text_at_runtime_value_path() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("offset.txt");
        let path = string_to_tagged_text(file_path.to_str().unwrap());
        let abc = string_to_tagged_text("abc");
        let def = string_to_tagged_text("def");

        assert_eq!(rt_file_write_text_at(path, 0, abc), 3);
        assert_eq!(rt_file_write_text_at(path, 3, def), 3);
        assert_eq!(fs::read_to_string(file_path).unwrap(), "abcdef");
    }

    #[test]
    fn test_file_write_text_at_cache_invalidates_on_remove() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("offset_remove.txt");
        let path_str = file_path.to_str().unwrap();
        let path = string_to_tagged_text(path_str);
        let old = string_to_tagged_text("old");
        let new = string_to_tagged_text("new");
        let (path_ptr, path_len) = str_to_ptr(path_str);

        assert_eq!(rt_file_write_text_at(path, 0, old), 3);
        unsafe {
            assert!(rt_file_remove(path_ptr, path_len));
        }
        assert_eq!(rt_file_write_text_at(path, 0, new), 3);
        assert_eq!(fs::read_to_string(file_path).unwrap(), "new");
    }

    #[test]
    fn test_file_read_text_at_runtime_value_path() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("read_at.txt");
        fs::write(&file_path, "0123456789").unwrap();
        let path = string_to_tagged_text(file_path.to_str().unwrap());

        let result = RuntimeValue::from_raw(rt_file_read_text_at(path, 3, 4) as u64);
        let text = unsafe { extract_string(result) };
        assert_eq!(text, "3456");
    }

    #[test]
    fn test_file_read_write_bytes() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("binary.bin");

        let path_str = file_path.to_str().unwrap();
        let (path_ptr, path_len) = str_to_ptr(path_str);

        let binary_data: [u8; 5] = [0, 127, 255, 1, 128];

        unsafe {
            // Write bytes
            assert!(rt_file_write_bytes(
                path_ptr,
                path_len,
                binary_data.as_ptr(),
                binary_data.len() as u64
            ));

            // Read bytes back
            let result = rt_file_read_bytes(path_ptr, path_len);
            assert!(!result.is_nil());

            let count = crate::value::collections::rt_array_len(result);
            assert_eq!(count, 5);
        }
    }

    #[test]
    fn test_file_move() {
        let temp_dir = TempDir::new().unwrap();
        let src_path = temp_dir.path().join("src.txt");
        let dest_path = temp_dir.path().join("dest.txt");
        fs::write(&src_path, "move me").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_move(src_ptr, src_len, dest_ptr, dest_len));
            assert!(!src_path.exists());
            assert!(dest_path.exists());

            let content = fs::read_to_string(&dest_path).unwrap();
            assert_eq!(content, "move me");
        }
    }

    #[test]
    fn test_file_move_across_dirs() {
        let temp_dir = TempDir::new().unwrap();
        let subdir = temp_dir.path().join("subdir");
        fs::create_dir(&subdir).unwrap();

        let src_path = temp_dir.path().join("file.txt");
        let dest_path = subdir.join("file.txt");
        fs::write(&src_path, "content").unwrap();

        let src_str = src_path.to_str().unwrap();
        let dest_str = dest_path.to_str().unwrap();

        unsafe {
            let (src_ptr, src_len) = str_to_ptr(src_str);
            let (dest_ptr, dest_len) = str_to_ptr(dest_str);

            assert!(rt_file_move(src_ptr, src_len, dest_ptr, dest_len));
            assert!(!src_path.exists());
            assert!(dest_path.exists());
        }
    }
}
