//! Interpreter-mode implementations of the `rt_io_file_*` family backing
//! `std.nogc_sync_mut.io.file` (`FileHandle` / `File`).
//!
//! These operate on real OS file descriptors, mirroring
//! `src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs` (the native
//! C-ABI implementation linked into compiled binaries) so interpret and
//! native/JIT execution agree. Before this file existed, tree-walk interpret
//! mode failed closed with `unknown extern function: rt_io_file_*` for the
//! whole family: the native symbols exist in the runtime crate, but nothing
//! registered them in the interpreter's static extern-function table, and
//! the dynamic dlsym fallback (`dynamic_sffi.rs`) marshals a single leaked
//! `i64` per `Value::Str` argument, not the `(ptr, len)` pair these
//! natively expect, so it cannot bridge them either. See
//! doc/08_tracking/bug/rt_io_file_family_undefined_stubbed_silent_data_loss_2026-08-05.md
//! and doc/08_tracking/bug/rt_io_file_family_interpreter_fixed_native_still_stubbed_2026-08-05.md.
//!
//! # Documented divergence from native
//!
//! On a genuine I/O error the native side returns a `RuntimeValue::NIL` that
//! a `[u8]`-typed caller detects via `.len() < 0` (a native-only bit-packed
//! sentinel). `Value` here is a plain Rust enum with no such sentinel —
//! calling `.len()` on `Value::Nil` is not the same "-1" trick — so read
//! errors return an empty `Value::array(vec![])` instead, indistinguishable
//! from EOF under interpret mode. This mirrors the EOF-return shape every
//! array-returning function here already uses, and does not affect the
//! exists/write/seek paths, which use `Bool`/`Int` as designed and need no
//! sentinel.

use crate::error::CompileError;
use crate::value::Value;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};

#[cfg(unix)]
use std::os::unix::io::{FromRawFd, IntoRawFd};

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

fn extract_path(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
        _ => Err(CompileError::runtime(format!(
            "rt_io_file: argument {idx} must be a string path"
        ))),
    }
}

#[inline]
fn extract_fd(args: &[Value], idx: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(fd)) if *fd >= 0 => Ok(*fd),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {idx} must be a valid file descriptor"
        ))),
    }
}

#[inline]
fn extract_i64(args: &[Value], idx: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {idx} must be an integer"
        ))),
    }
}

#[inline]
fn extract_bool(args: &[Value], idx: usize, symbol: &str) -> Result<bool, CompileError> {
    match args.get(idx) {
        Some(Value::Bool(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {idx} must be boolean"
        ))),
    }
}

fn byte_of(v: &Value) -> u8 {
    match v {
        Value::Int(n) => *n as u8,
        Value::UInt { value, .. } => *value as u8,
        _ => 0u8,
    }
}

fn extract_bytes(args: &[Value], idx: usize, symbol: &str) -> Result<Vec<u8>, CompileError> {
    args.get(idx)
        .and_then(Value::try_array_bytes)
        .ok_or_else(|| CompileError::runtime(format!("{symbol}: argument {idx} must be bytes")))
}

fn bytes_to_value(bytes: &[u8]) -> Value {
    Value::byte_array(bytes.to_vec())
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

/// Open `path` and return a file descriptor, or `-1` on error.
///
/// Mode encoding (must match `FileMode` lowering in `file.spl` and the
/// native `rt_io_file_open`): `0` ReadOnly, `1` WriteOnly, `2` ReadWrite,
/// `3` Append.
pub fn rt_io_file_open(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let mode = extract_i64(args, 1, "rt_io_file_open")?;
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
        _ => return Err(CompileError::runtime(format!("rt_io_file_open: invalid mode {mode}"))),
    }
    #[cfg(unix)]
    {
        match opts.open(&path) {
            Ok(file) => Ok(Value::Int(file.into_raw_fd() as i64)),
            Err(_) => Ok(Value::Int(-1)),
        }
    }
    #[cfg(not(unix))]
    {
        Ok(Value::Int(-1))
    }
}

/// Read up to `size` bytes from `fd`. Returns a bare `[u8]`, empty at EOF or
/// on error (see module-level divergence note).
pub fn rt_io_file_read(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_read")?;
    let size = extract_i64(args, 1, "rt_io_file_read")?;
    if size < 0 {
        return Err(CompileError::runtime(format!(
            "rt_io_file_read: size must be non-negative, got {size}"
        )));
    }
    let result = unsafe {
        with_fd(fd, Vec::new(), |file| {
            let mut buf = vec![0u8; size as usize];
            match file.read(&mut buf) {
                Ok(n) => {
                    buf.truncate(n);
                    buf
                }
                Err(_) => Vec::new(),
            }
        })
    };
    Ok(bytes_to_value(&result))
}

/// Read from the current position to EOF. Returns a bare `[u8]`.
pub fn rt_io_file_read_all(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_read_all")?;
    let result = unsafe {
        with_fd(fd, Vec::new(), |file| {
            let mut buf = Vec::new();
            let _ = file.read_to_end(&mut buf);
            buf
        })
    };
    Ok(bytes_to_value(&result))
}

/// Read one newline-terminated line. Returns `Value::Nil` at EOF, matching
/// `file.spl`'s `if line == nil:` check on this `text?` extern.
pub fn rt_io_file_read_line(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_read_line")?;
    let result = unsafe {
        with_fd(fd, None, |file| {
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
                    Err(_) => return None,
                }
            }
            if line.is_empty() {
                None
            } else {
                Some(line)
            }
        })
    };
    match result {
        Some(bytes) => Ok(Value::text(String::from_utf8_lossy(&bytes).to_string())),
        None => Ok(Value::Nil),
    }
}

/// Write `data` to `fd`. Returns the byte count written, or `-1` on error.
pub fn rt_io_file_write(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_write")?;
    let data = extract_bytes(args, 1, "rt_io_file_write")?;
    let n = unsafe {
        with_fd(fd, -1i64, |file| match file.write(&data) {
            Ok(n) => n as i64,
            Err(_) => -1,
        })
    };
    Ok(Value::Int(n))
}

/// Write all of `data` to `fd`. Returns false on a short write or error.
pub fn rt_io_file_write_all(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_write_all")?;
    let data = extract_bytes(args, 1, "rt_io_file_write_all")?;
    let ok = unsafe { with_fd(fd, false, |file| file.write_all(&data).is_ok()) };
    Ok(Value::Bool(ok))
}

/// Seek. `whence`: `0` SEEK_SET, `1` SEEK_CUR, `2` SEEK_END. Returns the new
/// absolute position, or `-1` on error.
pub fn rt_io_file_seek(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_seek")?;
    let offset = extract_i64(args, 1, "rt_io_file_seek")?;
    let whence = extract_i64(args, 2, "rt_io_file_seek")?;
    let pos = match whence {
        0 => {
            if offset < 0 {
                return Err(CompileError::runtime(
                    "rt_io_file_seek: negative SEEK_SET offset".to_string(),
                ));
            }
            SeekFrom::Start(offset as u64)
        }
        1 => SeekFrom::Current(offset),
        2 => SeekFrom::End(offset),
        _ => {
            return Err(CompileError::runtime(format!(
                "rt_io_file_seek: invalid whence {whence}"
            )))
        }
    };
    let result = unsafe {
        with_fd(fd, -1i64, |file| match file.seek(pos) {
            Ok(p) => p as i64,
            Err(_) => -1,
        })
    };
    Ok(Value::Int(result))
}

/// Flush userspace buffers and sync data to disk.
pub fn rt_io_file_flush(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_flush")?;
    let ok = unsafe { with_fd(fd, false, |file| file.flush().is_ok() && file.sync_data().is_ok()) };
    Ok(Value::Bool(ok))
}

/// Close `fd`. Unlike the helpers above this genuinely drops the handle.
pub fn rt_io_file_close(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_close")?;
    #[cfg(unix)]
    {
        if fd < 0 {
            return Ok(Value::Bool(false));
        }
        let file = unsafe { File::from_raw_fd(fd as i32) };
        let ok = file.sync_all().is_ok();
        drop(file);
        Ok(Value::Bool(ok))
    }
    #[cfg(not(unix))]
    {
        Ok(Value::Bool(false))
    }
}

/// Toggle the read-only bit on the file behind `fd`.
pub fn rt_io_file_set_permissions(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_set_permissions")?;
    let readonly = extract_bool(args, 1, "rt_io_file_set_permissions")?;
    let ok = unsafe {
        with_fd(fd, false, |file| match file.metadata() {
            Ok(meta) => {
                let mut perms = meta.permissions();
                perms.set_readonly(readonly);
                file.set_permissions(perms).is_ok()
            }
            Err(_) => false,
        })
    };
    Ok(Value::Bool(ok))
}

/// File size in bytes, or `-1` on error.
pub fn rt_io_file_meta_size(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_meta_size")?;
    let size = unsafe {
        with_fd(fd, -1i64, |file| match file.metadata() {
            Ok(meta) => meta.len() as i64,
            Err(_) => -1,
        })
    };
    Ok(Value::Int(size))
}

/// Packed metadata flags, or `-1` on error.
/// bit 0 is_file, bit 1 is_dir, bit 2 is_symlink, bit 3 readonly.
pub fn rt_io_file_meta_flags(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_meta_flags")?;
    let flags = unsafe {
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
    };
    Ok(Value::Int(flags))
}

/// Modification time in seconds since the Unix epoch, `0` if unavailable.
pub fn rt_io_file_meta_modified(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_meta_modified")?;
    let secs = unsafe {
        with_fd(fd, 0i64, |file| match file.metadata() {
            Ok(meta) => secs_since_epoch(meta.modified()),
            Err(_) => 0,
        })
    };
    Ok(Value::Int(secs))
}

/// Creation time in seconds since the Unix epoch, `0` if unavailable.
pub fn rt_io_file_meta_created(args: &[Value]) -> Result<Value, CompileError> {
    let fd = extract_fd(args, 0, "rt_io_file_meta_created")?;
    let secs = unsafe {
        with_fd(fd, 0i64, |file| match file.metadata() {
            Ok(meta) => secs_since_epoch(meta.created()),
            Err(_) => 0,
        })
    };
    Ok(Value::Int(secs))
}

/// Whether `path` exists.
pub fn rt_io_file_exists(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(std::path::Path::new(&path).exists()))
}

/// Delete `path`.
pub fn rt_io_file_delete(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(std::fs::remove_file(&path).is_ok()))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn open(path: &str, mode: i64) -> Value {
        rt_io_file_open(&[Value::text(path.to_string()), Value::Int(mode)]).unwrap()
    }

    fn fd_of(v: &Value) -> i64 {
        match v {
            Value::Int(n) => *n,
            other => panic!("expected fd Int, got {other:?}"),
        }
    }

    #[test]
    fn write_then_read_back_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("interp_rt.txt");
        let path = path.to_str().unwrap();

        let fd = fd_of(&open(path, 1));
        assert!(fd >= 0, "WriteOnly open failed on a fresh path");
        let data = Value::array((0u8..10).map(|b| Value::Int((b'0' + b) as i64)).collect());
        let ok = rt_io_file_write_all(&[Value::Int(fd), data]).unwrap();
        assert_eq!(ok, Value::Bool(true));
        assert_eq!(rt_io_file_close(&[Value::Int(fd)]).unwrap(), Value::Bool(true));

        assert_eq!(
            rt_io_file_exists(&[Value::text(path.to_string())]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(std::fs::read(path).unwrap(), b"0123456789");
    }

    #[test]
    fn seek_and_read_after_seek_report_real_positions_and_bytes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("interp_seek.txt");
        std::fs::write(&path, b"abcdefghij").unwrap();
        let path = path.to_str().unwrap();

        let fd = fd_of(&open(path, 0));
        assert_eq!(
            rt_io_file_seek(&[Value::Int(fd), Value::Int(4), Value::Int(0)]).unwrap(),
            Value::Int(4)
        );
        let chunk = rt_io_file_read(&[Value::Int(fd), Value::Int(3)]).unwrap();
        match chunk {
            Value::Array(arr) => {
                let bytes: Vec<u8> = arr.iter().map(byte_of).collect();
                assert_eq!(bytes, b"efg");
            }
            other => panic!("expected array, got {other:?}"),
        }
        assert_eq!(
            rt_io_file_seek(&[Value::Int(fd), Value::Int(0), Value::Int(1)]).unwrap(),
            Value::Int(7)
        );
        rt_io_file_close(&[Value::Int(fd)]).unwrap();
    }

    #[test]
    fn delete_removes_the_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("interp_gone.txt");
        std::fs::write(&path, b"x").unwrap();
        let path = path.to_str().unwrap().to_string();
        assert_eq!(
            rt_io_file_exists(&[Value::text(path.clone())]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_io_file_delete(&[Value::text(path.clone())]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(rt_io_file_exists(&[Value::text(path)]).unwrap(), Value::Bool(false));
    }

    #[test]
    fn malformed_file_arguments_fail_before_os_io() {
        assert!(rt_io_file_open(&[Value::text("path")]).is_err());
        assert!(rt_io_file_open(&[Value::text("path"), Value::Int(99)]).is_err());
        assert!(rt_io_file_read(&[Value::Nil, Value::Int(1)]).is_err());
        assert!(rt_io_file_read(&[Value::Int(1), Value::Int(-1)]).is_err());
        assert!(rt_io_file_write(&[Value::Int(1), Value::Bool(false)]).is_err());
        assert!(rt_io_file_write_all(&[Value::Int(-1), Value::byte_array(Vec::new())]).is_err());
        assert!(rt_io_file_seek(&[Value::Int(1), Value::Int(0), Value::Int(9)]).is_err());
        assert!(rt_io_file_set_permissions(&[Value::Int(1), Value::Int(0)]).is_err());
        assert!(rt_io_file_meta_size(&[]).is_err());
    }
}
