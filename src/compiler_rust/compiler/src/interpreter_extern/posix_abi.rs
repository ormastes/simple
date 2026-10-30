//! Interpreter registrations for the bare POSIX libc externs that hosted
//! standard-library modules call directly:
//!
//! * `src/lib/nogc_sync_mut/io/path_identity_abi.spl` (non-Windows branch):
//!   `malloc`, `free`, `realpath`, `readlink`
//! * `src/lib/nogc_sync_mut/io/_PathIdentityPosix/errno_abi.spl`: the host's
//!   errno-address owner (see [`ERRNO_ADDRESS_NAME`])
//! * `src/lib/nogc_sync_mut/io/retained_file_abi.spl` (non-Windows branch):
//!   `open`, `read`, `pread`, `write`, `close`, `fsync`, and `statx` on Linux
//!
//! This is the POSIX twin of `windows_abi.rs`: the native link path resolves
//! these names against libc, but the seed interpreter had no implementation
//! for the POSIX branch, so every interpreted path-identity check
//! (`_native_build_entry_closure` -> `path_final_existing` /
//! `path_entry_present`) died with "unknown extern function: malloc". Every
//! call here is the real libc function; nothing is emulated.
//!
//! Interpreter-specific guarantees that the raw libc symbols do not give:
//!
//! * **Ownership registry.** Every pointer handed out by `malloc`, and every
//!   buffer `realpath` allocates (`resolved == 0`), is recorded. `free` only
//!   releases a recorded pointer and refuses a foreign or already-freed
//!   address with an explicit error instead of corrupting the heap. Both
//!   sides use the same libc allocator, so `free(realpath(...))` is exact.
//! * **errno capture.** Simple owners take the errno address, make the call,
//!   then read errno through that address (`volatile_read_u32`). A
//!   tree-walking interpreter runs arbitrary Rust between those statements,
//!   which may itself change the thread's real errno. So every libc call
//!   bridged here (and every dynamic-SFFI call, `dynamic_sffi::call_fptr`,
//!   which reaches unbridged libc functions such as `link`) captures errno
//!   immediately into an interpreter-owned, 4-byte aligned thread-local cell,
//!   and the errno-address extern returns that cell's address.
//! * **Exact arity.** Every name checks its argument count before touching
//!   libc, so a mismatched declaration is an error, not undefined behaviour.
//!
//! Hosts: only the errno spelling of THIS host is claimed: `__error` on
//! Darwin/FreeBSD/DragonFly, `__errno_location` on Linux/Android, `__errno`
//! on NetBSD/OpenBSD. Every other spelling, and all of them on a Unix host
//! not listed, falls through to the explicit `unknown extern function` error
//! rather than a silent stub. Windows is served by `windows_abi.rs`; this
//! module is not compiled there.

use crate::error::CompileError;
use crate::value::Value;
use std::cell::Cell;
use std::collections::BTreeSet;
use std::sync::Mutex;

/// Declared libc externs implemented on every Unix host (`statx` is added on
/// Linux in [`is_supported_name`]).
const COMMON_NAMES: &[&str] = &[
    "malloc", "free", "realpath", "readlink", "open", "read", "pread", "write", "close", "fsync",
];

/// The libc errno-address function of this host, or `None` on a Unix host
/// with no known spelling.
#[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd", target_os = "dragonfly"))]
pub const ERRNO_ADDRESS_NAME: Option<&str> = Some("__error");
#[cfg(any(target_os = "linux", target_os = "android"))]
pub const ERRNO_ADDRESS_NAME: Option<&str> = Some("__errno_location");
#[cfg(any(target_os = "netbsd", target_os = "openbsd"))]
pub const ERRNO_ADDRESS_NAME: Option<&str> = Some("__errno");
#[cfg(not(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "linux",
    target_os = "android",
    target_os = "netbsd",
    target_os = "openbsd"
)))]
pub const ERRNO_ADDRESS_NAME: Option<&str> = None;

/// Every errno-address spelling any host uses; exactly one (or none) is
/// claimed on a given host.
pub const ALL_ERRNO_SPELLINGS: &[&str] = &["__error", "__errno_location", "__errno"];

/// Pointers this module handed out (via `malloc` or an allocating `realpath`)
/// that have not been released yet.
static OWNED: Mutex<BTreeSet<usize>> = Mutex::new(BTreeSet::new());

thread_local! {
    /// Interpreter-owned errno cell; its address is what the errno-address
    /// extern returns. Thread-local statics keep a stable address for the
    /// thread's lifetime, and `Cell<i32>` is 4-byte aligned, which is what
    /// `rt_volatile_read_u32` requires.
    static ERRNO_CELL: Cell<i32> = const { Cell::new(0) };
}

/// True when `name` is one of the POSIX libc externs this module implements.
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

fn owned() -> std::sync::MutexGuard<'static, BTreeSet<usize>> {
    // A poisoned registry would mean a panic mid-update; the set itself is
    // still consistent (single insert/remove per lock), so keep using it.
    OWNED.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Record the thread's current errno in the interpreter-owned cell. Called
/// right after every libc call bridged here and by `dynamic_sffi::call_fptr`.
pub(crate) fn capture_errno() {
    let code = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
    ERRNO_CELL.with(|cell| cell.set(code));
}

fn errno_cell_address() -> i64 {
    ERRNO_CELL.with(|cell| cell.as_ptr() as usize as i64)
}

/// `malloc(size) -> i64`: libc allocation, recorded in the ownership registry.
/// A zero, negative or pointer-width-overflowing size yields 0 (the `.spl`
/// callers treat 0 as `PATH_IDENTITY_ALLOCATION`).
fn malloc_fn(size: i64) -> Value {
    let Ok(size) = usize::try_from(size) else {
        return Value::Int(0);
    };
    if size == 0 {
        return Value::Int(0);
    }
    let ptr = unsafe { libc::malloc(size) };
    if ptr.is_null() {
        return Value::Int(0);
    }
    owned().insert(ptr as usize);
    Value::Int(ptr as usize as i64)
}

/// `free(pointer)`: releases a pointer this module handed out. `0` is a no-op
/// (as in libc); any other unrecorded address is a foreign pointer or a double
/// free and is refused with an explicit error, never passed to the allocator.
fn free_fn(raw: i64) -> Result<Value, CompileError> {
    if raw == 0 {
        return Ok(Value::Nil);
    }
    let Ok(addr) = usize::try_from(raw) else {
        return Err(CompileError::runtime(format!(
            "free: address {raw} is not a pointer this interpreter handed out"
        )));
    };
    if !owned().remove(&addr) {
        return Err(CompileError::runtime(format!(
            "free: address {addr:#x} was not returned by malloc/realpath in this interpreter, or was already freed"
        )));
    }
    unsafe { libc::free(addr as *mut libc::c_void) };
    Ok(Value::Nil)
}

/// `realpath(path, resolved) -> i64`: with `resolved == 0` libc allocates the
/// result, which is recorded so the caller's `free` is accepted. A null or
/// negative `path` yields 0 without calling libc.
fn realpath_fn(path: i64, resolved: i64) -> Value {
    let (Ok(path), Ok(resolved)) = (usize::try_from(path), usize::try_from(resolved)) else {
        ERRNO_CELL.with(|cell| cell.set(libc::EINVAL));
        return Value::Int(0);
    };
    if path == 0 {
        ERRNO_CELL.with(|cell| cell.set(libc::EINVAL));
        return Value::Int(0);
    }
    let result = unsafe { libc::realpath(path as *const libc::c_char, resolved as *mut libc::c_char) };
    capture_errno();
    if result.is_null() {
        return Value::Int(0);
    }
    if resolved == 0 {
        owned().insert(result as usize);
    }
    Value::Int(result as usize as i64)
}

/// `readlink(path, buffer, capacity) -> i64`. A null `path` or `buffer`, or a
/// negative capacity, yields -1 with EINVAL without calling libc.
fn readlink_fn(path: i64, buffer: i64, capacity: i64) -> Value {
    let (Ok(path), Ok(buffer), Ok(capacity)) =
        (usize::try_from(path), usize::try_from(buffer), usize::try_from(capacity))
    else {
        ERRNO_CELL.with(|cell| cell.set(libc::EINVAL));
        return Value::Int(-1);
    };
    if path == 0 || buffer == 0 {
        ERRNO_CELL.with(|cell| cell.set(libc::EINVAL));
        return Value::Int(-1);
    }
    let observed = unsafe { libc::readlink(path as *const libc::c_char, buffer as *mut libc::c_char, capacity) };
    capture_errno();
    Value::Int(observed as i64)
}

fn ptr<T>(value: i64) -> *mut T {
    value as usize as *mut T
}

/// Dispatch a POSIX libc extern by name against pre-evaluated argument values.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    if ERRNO_ADDRESS_NAME == Some(name) {
        check_arity(name, args, &[0])?;
        return Ok(Value::Int(errno_cell_address()));
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
    let a: Vec<i64> = args.iter().map(|v| v.as_int()).collect::<Result<_, _>>()?;
    match name {
        "malloc" => return Ok(malloc_fn(a[0])),
        "free" => return free_fn(a[0]),
        "realpath" => return Ok(realpath_fn(a[0], a[1])),
        "readlink" => return Ok(readlink_fn(a[0], a[1], a[2])),
        _ => {}
    }
    // SAFETY: these are the exact libc entry points the declaring `.spl`
    // modules bind in the native lane; pointer and fd arguments are raw host
    // values owned by that Simple code, exactly as in the native lane.
    let result: i64 = unsafe {
        match name {
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

    /// Only this host's errno spelling is claimed; every other spelling falls
    /// through to the explicit unknown-extern error.
    #[test]
    fn only_the_hosts_errno_owner_is_claimed() {
        let host = ERRNO_ADDRESS_NAME;
        assert!(
            host.is_some()
                || !cfg!(any(
                    target_os = "linux",
                    target_os = "macos",
                    target_os = "freebsd",
                    target_os = "netbsd",
                    target_os = "openbsd"
                )),
            "a mainstream Unix host must claim its errno owner"
        );
        for spelling in ALL_ERRNO_SPELLINGS {
            assert_eq!(is_supported_name(spelling), host == Some(*spelling), "{spelling}");
            if host != Some(*spelling) {
                assert!(dispatch(spelling, &[]).is_err(), "{spelling} must not be served on this host");
            }
        }
        if let Some(owner) = host {
            assert!(dispatch(owner, &[Value::Int(0)]).is_err(), "errno owner takes no arguments");
        }
    }

    #[test]
    fn rejects_wrong_arity_without_calling_libc() {
        assert!(dispatch("malloc", &[]).is_err());
        assert!(dispatch("malloc", &[Value::Int(8), Value::Int(8)]).is_err());
        assert!(dispatch("free", &[]).is_err());
        assert!(dispatch("readlink", &[Value::Int(0)]).is_err());
        assert!(dispatch("open", &[Value::Int(0)]).is_err());
    }

    #[test]
    fn malloc_free_round_trip_and_double_free_refused() {
        let addr = int_of(dispatch("malloc", &[Value::Int(16)]));
        assert_ne!(addr, 0);
        assert!(dispatch("free", &[Value::Int(addr)]).is_ok());
        assert!(dispatch("free", &[Value::Int(addr)]).is_err(), "double free must be refused");
        assert!(dispatch("free", &[Value::Int(0)]).is_ok(), "free(0) is a no-op");
        assert!(dispatch("free", &[Value::Int(0x1000)]).is_err(), "foreign pointer must be refused");
        assert_eq!(dispatch("malloc", &[Value::Int(0)]).unwrap(), Value::Int(0));
        assert_eq!(dispatch("malloc", &[Value::Int(-1)]).unwrap(), Value::Int(0));
    }

    #[test]
    fn null_pointers_fail_closed_without_calling_libc() {
        assert_eq!(dispatch("realpath", &[Value::Int(0), Value::Int(0)]).unwrap(), Value::Int(0));
        let buf = c_text("x");
        assert_eq!(
            dispatch("readlink", &[Value::Int(0), Value::Int(buf), Value::Int(1)]).unwrap(),
            Value::Int(-1)
        );
        if let Some(owner) = ERRNO_ADDRESS_NAME {
            let cell = int_of(dispatch(owner, &[]));
            assert_eq!(unsafe { *(cell as *const i32) }, libc::EINVAL);
        }
        dispatch("free", &[Value::Int(buf)]).unwrap();
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
        // The allocating realpath result is owned, so free accepts it once.
        dispatch("free", &[Value::Int(resolved)]).unwrap();
        assert!(dispatch("free", &[Value::Int(resolved)]).is_err());

        let out = c_text("..");
        let missing = c_text(temp.path().join("absent").to_str().unwrap());
        let Some(errno_name) = ERRNO_ADDRESS_NAME else {
            for p in [input, out, missing] {
                dispatch("free", &[Value::Int(p)]).unwrap();
            }
            return;
        };
        // readlink on a non-symlink fails with EINVAL; on a missing leaf, ENOENT.
        assert_eq!(int_of(dispatch("readlink", &[Value::Int(input), Value::Int(out), Value::Int(1)])), -1);
        let errno_cell = int_of(dispatch(errno_name, &[]));
        assert_eq!(errno_cell % 4, 0);
        // Rust work between the call and the read must not disturb the cell.
        let _noise = std::fs::metadata("/definitely/not/here");
        assert_eq!(unsafe { *(errno_cell as *const i32) }, libc::EINVAL);
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
