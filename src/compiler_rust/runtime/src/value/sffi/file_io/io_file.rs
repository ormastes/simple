//! fd-level file I/O backing `std.nogc_sync_mut.io.file` (`FileHandle` / `File`).
//!
//! These are the `rt_io_file_*` symbols declared as `extern fn` in
//! `src/lib/nogc_sync_mut/io/file.spl`. Until 2026-08-05 none of them existed
//! anywhere in the tree: they were listed in `RT_KEEP`
//! (`compiler/src/linker/native_binary/stubs.rs`), which suppressed the
//! undefined-`rt_*` link check and handed each one a fabricated zero-returning
//! stub. The result was silent data loss — `File.write` returned `Ok`, wrote
//! nothing, and `File.exists` reported false, all with exit 0. See
//! `doc/08_tracking/bug/rt_io_file_family_undefined_stubbed_silent_data_loss_2026-08-05.md`.
//!
//! # Why this is a separate family from `rt_file_*`
//!
//! `descriptor.rs` already exposes fd-level `rt_file_open` / `rt_file_get_size`
//! / `rt_file_close`, but its **mode encoding is different**:
//!
//! | value | `rt_file_open` (descriptor.rs) | `rt_io_file_open` (file.spl) |
//! |-------|--------------------------------|------------------------------|
//! | 0     | ReadOnly                       | ReadOnly                     |
//! | 1     | ReadWrite                      | **WriteOnly**                |
//! | 2     | WriteOnly                      | **ReadWrite**                |
//! | 3     | —                              | Append                       |
//!
//! `1` and `2` are swapped. Routing `file.spl` at `rt_file_open` would
//! therefore silently open WriteOnly files ReadWrite and vice versa. The
//! encoding below is the one `file.spl` actually emits (see its `FileMode`
//! match), and must stay in sync with it.
//!
//! `rt_file_open` also never creates or truncates, so `FileMode.WriteOnly`
//! against a fresh path would fail. This family creates on WriteOnly/ReadWrite/
//! Append, matching what `File.write_text` callers expect.
//!
//! # ABI
//!
//! Per the repo's SFFI convention: a `.spl` `text` parameter lowers to a
//! `(*const u8, u64)` pair, a `[u8]` parameter likewise, a `text`/`[u8]`/`T?`
//! return is a `RuntimeValue` (`NIL` for `nil`), and `bool`/`i64` map directly.

use crate::value::collections::rt_string_new;
use crate::value::sffi::file_io::file_ops::bytes_to_runtime_array;
use crate::value::RuntimeValue;

#[cfg(unix)]
use std::os::unix::io::{FromRawFd, IntoRawFd};

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};

/// Run `f` against a `File` borrowed from a raw fd without closing that fd.
///
/// `File::from_raw_fd` takes ownership, so the handle is deliberately leaked
/// with `into_raw_fd` afterwards; dropping it would close a descriptor the
/// Simple-side `FileHandle` still believes it owns.
#[cfg(unix)]
unsafe fn with_fd<T>(fd: i64, default: T, f: impl FnOnce(&mut File) -> T) -> T {
    if fd < 0 {
        return default;
    }
    let mut file = File::from_raw_fd(fd as i32);
    let out = f(&mut file);
    let _ = file.into_raw_fd();
    out
}

#[cfg(not(unix))]
unsafe fn with_fd<T>(_fd: i64, default: T, _f: impl FnOnce(&mut File) -> T) -> T {
    default
}

unsafe fn path_from_raw<'a>(ptr: *const u8, len: u64) -> Option<&'a str> {
    if ptr.is_null() {
        return None;
    }
    std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).ok()
}

/// Open `path` and return a file descriptor, or `-1` on error.
///
/// Mode encoding (must match `FileMode` lowering in `file.spl`):
/// `0` ReadOnly, `1` WriteOnly, `2` ReadWrite, `3` Append.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_open(path_ptr: *const u8, path_len: u64, mode: i64) -> i64 {
    let path = match path_from_raw(path_ptr, path_len) {
        Some(p) => p,
        None => return -1,
    };

    let mut opts = OpenOptions::new();
    match mode {
        0 => {
            opts.read(true);
        }
        1 => {
            opts.write(true).create(true).truncate(true);
        }
        2 => {
            opts.read(true).write(true).create(true);
        }
        3 => {
            opts.append(true).create(true);
        }
        _ => return -1,
    }

    match opts.open(path) {
        #[cfg(unix)]
        Ok(file) => file.into_raw_fd() as i64,
        #[cfg(not(unix))]
        Ok(_) => -1,
        Err(_) => -1,
    }
}

/// Read up to `size` bytes from `fd`. Returns a `[u8]`, empty at EOF.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_read(fd: i64, size: i64) -> RuntimeValue {
    if size < 0 {
        return RuntimeValue::NIL;
    }
    with_fd(fd, RuntimeValue::NIL, |file| {
        let mut buf = vec![0u8; size as usize];
        match file.read(&mut buf) {
            Ok(n) => {
                buf.truncate(n);
                bytes_to_runtime_array(&buf)
            }
            Err(_) => RuntimeValue::NIL,
        }
    })
}

/// Read from the current position to EOF. Returns a `[u8]`.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_read_all(fd: i64) -> RuntimeValue {
    with_fd(fd, RuntimeValue::NIL, |file| {
        let mut buf = Vec::new();
        match file.read_to_end(&mut buf) {
            Ok(_) => bytes_to_runtime_array(&buf),
            Err(_) => RuntimeValue::NIL,
        }
    })
}

/// Read one newline-terminated line. Returns `nil` at EOF.
///
/// Reads a byte at a time so the descriptor is left positioned exactly after
/// the newline — a buffered reader would over-consume and desynchronise any
/// subsequent `seek`/`read` on the same fd.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_read_line(fd: i64) -> RuntimeValue {
    with_fd(fd, RuntimeValue::NIL, |file| {
        let mut line: Vec<u8> = Vec::new();
        let mut byte = [0u8; 1];
        loop {
            match file.read(&mut byte) {
                Ok(0) => break,
                Ok(_) => {
                    line.push(byte[0]);
                    if byte[0] == b'\n' {
                        break;
                    }
                }
                Err(_) => return RuntimeValue::NIL,
            }
        }
        if line.is_empty() {
            return RuntimeValue::NIL;
        }
        rt_string_new(line.as_ptr(), line.len() as u64)
    })
}

/// Write `data` to `fd`. Returns the byte count written, or `-1` on error.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_write(fd: i64, data_ptr: *const u8, data_len: u64) -> i64 {
    if data_ptr.is_null() && data_len > 0 {
        return -1;
    }
    let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
    with_fd(fd, -1i64, |file| match file.write(data) {
        Ok(n) => n as i64,
        Err(_) => -1,
    })
}

/// Write all of `data` to `fd`. Returns false on a short write or error.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_write_all(fd: i64, data_ptr: *const u8, data_len: u64) -> bool {
    if data_ptr.is_null() && data_len > 0 {
        return false;
    }
    let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
    with_fd(fd, false, |file| file.write_all(data).is_ok())
}

/// Seek. `whence`: `0` SEEK_SET, `1` SEEK_CUR, `2` SEEK_END.
/// Returns the new absolute position, or `-1` on error.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_seek(fd: i64, offset: i64, whence: i64) -> i64 {
    let pos = match whence {
        0 => {
            if offset < 0 {
                return -1;
            }
            SeekFrom::Start(offset as u64)
        }
        1 => SeekFrom::Current(offset),
        2 => SeekFrom::End(offset),
        _ => return -1,
    };
    with_fd(fd, -1i64, |file| match file.seek(pos) {
        Ok(p) => p as i64,
        Err(_) => -1,
    })
}

/// Flush userspace buffers and sync data to disk.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_flush(fd: i64) -> bool {
    with_fd(fd, false, |file| file.flush().is_ok() && file.sync_data().is_ok())
}

/// Close `fd`. Unlike the helpers above this genuinely drops the handle.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_close(fd: i64) -> bool {
    #[cfg(unix)]
    {
        if fd < 0 {
            return false;
        }
        let file = File::from_raw_fd(fd as i32);
        // Surface a write-back error rather than losing it in the drop.
        let ok = file.sync_all().is_ok();
        drop(file);
        ok
    }
    #[cfg(not(unix))]
    {
        let _ = fd;
        false
    }
}

/// Toggle the read-only bit on the file behind `fd`.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_set_permissions(fd: i64, readonly: bool) -> bool {
    with_fd(fd, false, |file| match file.metadata() {
        Ok(meta) => {
            let mut perms = meta.permissions();
            perms.set_readonly(readonly);
            file.set_permissions(perms).is_ok()
        }
        Err(_) => false,
    })
}

// ---------------------------------------------------------------------------
// Metadata — returned as scalars, assembled into `FileMetadata` on the Simple
// side. Constructing a Simple struct from Rust would hard-code that struct's
// field layout into the runtime ABI; these four scalars cannot go stale that
// way.
// ---------------------------------------------------------------------------

/// File size in bytes, or `-1` on error.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_meta_size(fd: i64) -> i64 {
    with_fd(fd, -1i64, |file| match file.metadata() {
        Ok(meta) => meta.len() as i64,
        Err(_) => -1,
    })
}

/// Packed metadata flags, or `-1` on error.
/// bit 0 is_file, bit 1 is_dir, bit 2 is_symlink, bit 3 readonly.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_meta_flags(fd: i64) -> i64 {
    with_fd(fd, -1i64, |file| match file.metadata() {
        Ok(meta) => {
            let ft = meta.file_type();
            let mut flags = 0i64;
            if ft.is_file() {
                flags |= 1;
            }
            if ft.is_dir() {
                flags |= 2;
            }
            if ft.is_symlink() {
                flags |= 4;
            }
            if meta.permissions().readonly() {
                flags |= 8;
            }
            flags
        }
        Err(_) => -1,
    })
}

fn secs_since_epoch(t: std::io::Result<std::time::SystemTime>) -> i64 {
    match t {
        Ok(time) => match time.duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => d.as_secs() as i64,
            Err(_) => 0,
        },
        Err(_) => 0,
    }
}

/// Modification time in seconds since the Unix epoch, `0` if unavailable.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_meta_modified(fd: i64) -> i64 {
    with_fd(fd, 0i64, |file| match file.metadata() {
        Ok(meta) => secs_since_epoch(meta.modified()),
        Err(_) => 0,
    })
}

/// Creation time in seconds since the Unix epoch, `0` if unavailable.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_meta_created(fd: i64) -> i64 {
    with_fd(fd, 0i64, |file| match file.metadata() {
        Ok(meta) => secs_since_epoch(meta.created()),
        Err(_) => 0,
    })
}

/// Whether `path` exists.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_exists(path_ptr: *const u8, path_len: u64) -> bool {
    match path_from_raw(path_ptr, path_len) {
        Some(p) => std::path::Path::new(p).exists(),
        None => false,
    }
}

/// Delete `path`.
#[no_mangle]
pub unsafe extern "C" fn rt_io_file_delete(path_ptr: *const u8, path_len: u64) -> bool {
    match path_from_raw(path_ptr, path_len) {
        Some(p) => std::fs::remove_file(p).is_ok(),
        None => false,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use tempfile::TempDir;

    unsafe fn open(path: &str, mode: i64) -> i64 {
        rt_io_file_open(path.as_ptr(), path.len() as u64, mode)
    }

    #[test]
    fn write_then_read_back_round_trips() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("rt.txt");
        let path = path.to_str().unwrap();

        unsafe {
            // WriteOnly must create the file, not fail on a missing path.
            let fd = open(path, 1);
            assert!(fd >= 0, "WriteOnly open failed on a fresh path");
            let data = b"0123456789";
            assert!(rt_io_file_write_all(fd, data.as_ptr(), data.len() as u64));
            assert!(rt_io_file_close(fd));

            assert!(rt_io_file_exists(path.as_ptr(), path.len() as u64));
            assert_eq!(std::fs::read(path).unwrap(), b"0123456789");
        }
    }

    #[test]
    fn seek_reports_absolute_positions() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("seek.txt");
        std::fs::write(&path, b"0123456789").unwrap();
        let path = path.to_str().unwrap();

        unsafe {
            let fd = open(path, 0);
            assert!(fd >= 0);
            assert_eq!(rt_io_file_seek(fd, 3, 0), 3, "SEEK_SET");
            assert_eq!(rt_io_file_seek(fd, 2, 1), 5, "SEEK_CUR from 3");
            assert_eq!(rt_io_file_seek(fd, -1, 2), 9, "SEEK_END - 1");
            assert_eq!(rt_io_file_meta_size(fd), 10);
            rt_io_file_close(fd);
        }
    }

    #[test]
    fn read_after_seek_returns_the_sought_bytes() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("read.txt");
        std::fs::write(&path, b"abcdefghij").unwrap();
        let path = path.to_str().unwrap();

        unsafe {
            let fd = open(path, 0);
            assert_eq!(rt_io_file_seek(fd, 4, 0), 4);
            // Position must advance by exactly the bytes consumed.
            let mut probe = [0u8; 3];
            let n = with_fd(fd, 0usize, |f| f.read(&mut probe).unwrap_or(0));
            assert_eq!(n, 3);
            assert_eq!(&probe, b"efg");
            assert_eq!(rt_io_file_seek(fd, 0, 1), 7);
            rt_io_file_close(fd);
        }
    }

    #[test]
    fn delete_removes_the_file() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("gone.txt");
        std::fs::write(&path, b"x").unwrap();
        let path = path.to_str().unwrap();
        unsafe {
            assert!(rt_io_file_exists(path.as_ptr(), path.len() as u64));
            assert!(rt_io_file_delete(path.as_ptr(), path.len() as u64));
            assert!(!rt_io_file_exists(path.as_ptr(), path.len() as u64));
        }
    }
}
