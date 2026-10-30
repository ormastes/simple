//! Interpreter registrations for the bare POSIX libc externs that hosted
//! standard-library modules call directly:
//!
//! * `src/lib/nogc_sync_mut/io/path_identity_abi.spl`: `malloc`, `free`,
//!   `realpath`, `readlink`
//! * `src/lib/nogc_sync_mut/io/_PathIdentityPosix/errno_abi.spl`: `__error`
//!   (Darwin/FreeBSD) and `__errno_location` (Linux)
//! * `src/lib/nogc_sync_mut/io/retained_file_abi.spl`: `open`, `read`,
//!   `pread`, `write`, `close`, `fsync`, and `statx` on Linux
//!
//! These modules deliberately call libc directly (`path_identity.spl`: "No
//! lexical/runtime canonicalizer fallback"), and the native lane links them
//! against the host libc. The interpreter had a Win32 counterpart
//! (`windows_abi.rs`) but nothing for POSIX, so any interpreted path that
//! reached `path_final_existing` (the parser preprocessor does) failed with
//! `unknown extern function: malloc`. Every call here is the real libc
//! function; nothing is emulated.
//!
//! errno: Simple owners take the errno address first, make the call, then
//! read errno through that address (`readlink`, then
//! `volatile_read_u32(errno_pointer)`). In the interpreter, Rust code runs
//! between those Simple statements and may itself change the thread's real
//! errno. So the errno-address externs return the address of a per-thread
//! cell holding the errno that the last call bridged here left behind. The
//! cell is refreshed immediately after every libc call this module makes and
//! after every dynamic-SFFI call (`dynamic_sffi::call_fptr`, which reaches
//! unbridged libc functions such as `link`), which gives the same "immediate
//! capture" the native lane gets.
//!
//! Hosts: the errno-address name is only claimed on Linux/Android
//! (`__errno_location`) and Darwin/FreeBSD/DragonFly (`__error`). On any
//! other Unix the name is not claimed and falls through to the explicit
//! `unknown extern function` error rather than a silent stub. Windows uses
//! `windows_abi.rs`; this module is not compiled there.

use crate::error::CompileError;
use crate::value::Value;
use std::cell::Cell;

thread_local! {
    static LAST_ERRNO: Cell<i32> = const { Cell::new(0) };
}

#[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd", target_os = "dragonfly"))]
const ERRNO_ADDRESS_NAME: Option<&str> = Some("__error");
#[cfg(any(target_os = "linux", target_os = "android"))]
const ERRNO_ADDRESS_NAME: Option<&str> = Some("__errno_location");
#[cfg(not(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "linux",
    target_os = "android"
)))]
const ERRNO_ADDRESS_NAME: Option<&str> = None;

const COMMON_NAMES: &[&str] = &[
    "malloc", "free", "realpath", "readlink", "open", "read", "pread", "write", "close", "fsync",
];

pub fn is_supported_name(name: &str) -> bool {
    COMMON_NAMES.contains(&name)
        || ERRNO_ADDRESS_NAME == Some(name)
        || (cfg!(target_os = "linux") && name == "statx")
}

fn check_arity(name: &str, args: &[Value], allowed: &[usize]) -> Result<(), CompileError> {
    if allowed.contains(&args.len()) {
        return Ok(());
    }
    let expected = allowed.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(" or ");
    Err(CompileError::semantic(format!(
        "{name} expects {expected} argument(s), got {}",
        args.len()
    )))
}

fn int(args: &[Value], index: usize) -> Result<i64, CompileError> {
    args[index].as_int()
}

fn ptr<T>(value: i64) -> *mut T {
    value as usize as *mut T
}

pub(crate) fn capture_errno() {
    let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
    LAST_ERRNO.with(|cell| cell.set(errno));
}

pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    if ERRNO_ADDRESS_NAME == Some(name) {
        check_arity(name, args, &[0])?;
        return Ok(Value::Int(LAST_ERRNO.with(|cell| cell.as_ptr() as i64)));
    }
    let arity: &[usize] = match name {
        "malloc" | "free" | "close" | "fsync" => &[1],
        "realpath" => &[2],
        "readlink" | "read" | "write" => &[3],
        // libc `open` is variadic; runtime-core declarations omit `mode`.
        "open" => &[2, 3],
        "pread" => &[4],
        "statx" if cfg!(target_os = "linux") => &[5],
        _ => return Err(super::common::unknown_function(name)),
    };
    check_arity(name, args, arity)?;
    // Convert every argument before the libc call so a conversion error can
    // never happen between the call and the errno capture.
    let a: Vec<i64> = (0..args.len()).map(|i| int(args, i)).collect::<Result<_, _>>()?;
    // SAFETY: these are the exact libc entry points the declaring `.spl`
    // modules bind in the native lane; pointer arguments are raw host
    // addresses owned by that Simple code, exactly as in the native lane.
    let result: i64 = unsafe {
        match name {
            "malloc" => libc::malloc(a[0] as usize) as i64,
            "free" => {
                libc::free(ptr(a[0]));
                capture_errno();
                return Ok(Value::Nil);
            }
            "realpath" => libc::realpath(ptr(a[0]), ptr(a[1])) as i64,
            "readlink" => libc::readlink(ptr(a[0]), ptr(a[1]), a[2] as usize) as i64,
            "open" => {
                // The two-argument runtime-core declaration has no mode; with
                // O_CREAT give the conventional 0644 instead of a mode-000 file.
                let mode = if a.len() == 3 {
                    a[2] as libc::c_uint
                } else if a[1] as libc::c_int & libc::O_CREAT != 0 {
                    0o644
                } else {
                    0
                };
                libc::open(ptr(a[0]), a[1] as libc::c_int, mode) as i64
            }
            "read" => libc::read(a[0] as libc::c_int, ptr(a[1]), a[2] as usize) as i64,
            "pread" => libc::pread(a[0] as libc::c_int, ptr(a[1]), a[2] as usize, a[3] as libc::off_t) as i64,
            "write" => libc::write(a[0] as libc::c_int, ptr(a[1]), a[2] as usize) as i64,
            "close" => libc::close(a[0] as libc::c_int) as i64,
            "fsync" => libc::fsync(a[0] as libc::c_int) as i64,
            #[cfg(target_os = "linux")]
            "statx" => libc::statx(
                a[0] as libc::c_int,
                ptr(a[1]),
                a[2] as libc::c_int,
                a[3] as libc::c_uint,
                ptr(a[4]),
            ) as i64,
            _ => return Err(super::common::unknown_function(name)),
        }
    };
    capture_errno();
    Ok(Value::Int(result))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_of(v: Result<Value, CompileError>) -> i64 {
        v.unwrap().as_int().unwrap()
    }

    fn c_text(text: &str) -> i64 {
        let buffer = int_of(dispatch("malloc", &[Value::Int(text.len() as i64 + 1)]));
        assert_ne!(buffer, 0);
        unsafe {
            std::ptr::copy_nonoverlapping(text.as_ptr(), buffer as *mut u8, text.len());
            *((buffer as usize + text.len()) as *mut u8) = 0;
        }
        buffer
    }

    #[test]
    fn claims_exactly_the_declared_posix_names() {
        for name in COMMON_NAMES {
            assert!(is_supported_name(name), "{name}");
        }
        assert!(!is_supported_name("rt_malloc"));
        assert!(!is_supported_name("GetProcessHeap"));
        assert_eq!(is_supported_name("statx"), cfg!(target_os = "linux"));
    }

    #[test]
    fn rejects_wrong_arity_without_calling_libc() {
        assert!(dispatch("malloc", &[]).is_err());
        assert!(dispatch("readlink", &[Value::Int(0)]).is_err());
        assert!(dispatch("open", &[Value::Int(0)]).is_err());
    }

    #[test]
    fn resolves_a_real_path_and_reports_readlink_errno_through_the_cell() {
        let temp = tempfile::tempdir().unwrap();
        let file = temp.path().join("plain");
        std::fs::write(&file, b"x").unwrap();
        let input = c_text(file.to_str().unwrap());
        let resolved = int_of(dispatch("realpath", &[Value::Int(input), Value::Int(0)]));
        assert_ne!(resolved, 0);
        let resolved_text = unsafe { std::ffi::CStr::from_ptr(resolved as *const libc::c_char) };
        assert_eq!(
            std::path::Path::new(resolved_text.to_str().unwrap()),
            file.canonicalize().unwrap()
        );
        dispatch("free", &[Value::Int(resolved)]).unwrap();

        let Some(errno_name) = ERRNO_ADDRESS_NAME else { return };
        // readlink on a non-symlink fails with EINVAL; on a missing leaf, ENOENT.
        let out = c_text("..");
        assert_eq!(int_of(dispatch("readlink", &[Value::Int(input), Value::Int(out), Value::Int(1)])), -1);
        let errno_cell = int_of(dispatch(errno_name, &[]));
        // Rust work between the call and the read must not disturb the cell.
        let _noise = std::fs::metadata("/definitely/not/here");
        assert_eq!(unsafe { *(errno_cell as *const i32) }, libc::EINVAL);
        let missing = c_text(temp.path().join("absent").to_str().unwrap());
        assert_eq!(int_of(dispatch("readlink", &[Value::Int(missing), Value::Int(out), Value::Int(1)])), -1);
        assert_eq!(unsafe { *(errno_cell as *const i32) }, libc::ENOENT);
        for p in [input, out, missing] {
            dispatch("free", &[Value::Int(p)]).unwrap();
        }
    }

    #[test]
    fn two_argument_open_reads_a_file_back() {
        let temp = tempfile::tempdir().unwrap();
        let file = temp.path().join("data");
        std::fs::write(&file, b"hello").unwrap();
        let path = c_text(file.to_str().unwrap());
        let fd = int_of(dispatch("open", &[Value::Int(path), Value::Int(libc::O_RDONLY as i64)]));
        assert!(fd >= 0);
        let buffer = c_text("     ");
        assert_eq!(int_of(dispatch("read", &[Value::Int(fd), Value::Int(buffer), Value::Int(5)])), 5);
        let bytes = unsafe { std::slice::from_raw_parts(buffer as *const u8, 5) };
        assert_eq!(bytes, b"hello");
        assert_eq!(int_of(dispatch("close", &[Value::Int(fd)])), 0);
        for p in [path, buffer] {
            dispatch("free", &[Value::Int(p)]).unwrap();
        }
    }
}
