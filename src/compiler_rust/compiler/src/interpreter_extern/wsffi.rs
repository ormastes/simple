//! Wrapped SFFI (WFFI) functions for dynamic library loading
//!
//! Provides spl_dlopen, spl_dlsym, spl_dlclose, spl_wffi_call_i64,
//! spl_wffi_call_f64,
//! spl_f64_to_bits, spl_bits_to_f64, spl_str_ptr, and rt_cstring_to_text
//! for the interpreter, enabling dynamic loading of native shared libraries
//! (e.g., libspl_torch.so) at runtime.

use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::sync::Mutex;

/// Global registry of loaded libraries to prevent double-loading
static LOADED_LIBS: std::sync::LazyLock<Mutex<HashMap<String, usize>>> =
    std::sync::LazyLock::new(|| Mutex::new(HashMap::new()));

/// Copy a provider into a sealed Linux memfd and return that descriptor.
pub fn spl_dynlib_snapshot_linux(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "spl_dynlib_snapshot_linux requires 1 argument (path)",
        ));
    }
    let path = match &args[0] {
        Value::Str(path) => path,
        _ => return Err(CompileError::runtime("spl_dynlib_snapshot_linux: path must be a string")),
    };

    #[cfg(target_os = "linux")]
    unsafe {
        let c_path = match CString::new(path.as_str()) {
            Ok(path) => path,
            Err(_) => return Ok(Value::Int(-1)),
        };
        let source = libc::open(
            c_path.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        );
        if source < 0 { return Ok(Value::Int(-1)); }
        let mut source_stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        if libc::fstat(source, source_stat.as_mut_ptr()) != 0 {
            libc::close(source);
            return Ok(Value::Int(-1));
        }
        let source_stat = source_stat.assume_init();
        if source_stat.st_mode & libc::S_IFMT != libc::S_IFREG
            || source_stat.st_size < 0
            || source_stat.st_size as u64 > 1_073_741_824
        {
            libc::close(source);
            return Ok(Value::Int(-1));
        }
        let name = b"simple-sffi-provider\0";
        let snapshot = libc::syscall(
            libc::SYS_memfd_create,
            name.as_ptr() as *const libc::c_char,
            libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
        ) as libc::c_int;
        if snapshot < 0 {
            libc::close(source);
            return Ok(Value::Int(-1));
        }
        let mut buffer = [0u8; 65536];
        let mut total = 0u64;
        loop {
            let got = libc::read(source, buffer.as_mut_ptr().cast(), buffer.len());
            if got == 0 { break; }
            if got < 0 {
                if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted { continue; }
                libc::close(source); libc::close(snapshot);
                return Ok(Value::Int(-1));
            }
            if got as u64 > 1_073_741_824 - total {
                libc::close(source); libc::close(snapshot);
                return Ok(Value::Int(-1));
            }
            total += got as u64;
            let mut offset = 0isize;
            while offset < got {
                let put = libc::write(
                    snapshot,
                    buffer.as_ptr().offset(offset).cast(),
                    (got - offset) as usize,
                );
                if put < 0 && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }
                if put <= 0 {
                    libc::close(source); libc::close(snapshot);
                    return Ok(Value::Int(-1));
                }
                offset += put;
            }
        }
        let seals = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        if total != source_stat.st_size as u64
            || libc::close(source) != 0
            || libc::lseek(snapshot, 0, libc::SEEK_SET) < 0
            || libc::fcntl(snapshot, libc::F_ADD_SEALS, seals) != 0
        {
            libc::close(snapshot);
            return Ok(Value::Int(-1));
        }
        Ok(Value::Int(snapshot as i64))
    }

    #[cfg(not(target_os = "linux"))]
    {
        let _ = path;
        Ok(Value::Int(-1))
    }
}

/// Open a shared library and return its handle as i64.
///
/// Callable from Simple as: `spl_dlopen(path: text) -> i64`
/// Returns 0 on failure.
pub fn spl_dlopen(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_dlopen requires 1 argument (path)"));
    }

    let path = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_dlopen: path must be a string")),
    };

    #[cfg(unix)]
    {
        let c_path = match CString::new(path.as_str()) {
            Ok(c) => c,
            Err(_) => return Ok(Value::Int(0)),
        };

        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };

        if handle.is_null() {
            let err = unsafe { libc::dlerror() };
            if !err.is_null() {
                let err_str = unsafe { CStr::from_ptr(err) }.to_string_lossy();
                tracing::warn!("spl_dlopen failed for '{}': {}", path, err_str);
            }
            Ok(Value::Int(0))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn LoadLibraryA(lpLibFileName: *const u8) -> isize;
        }
        let c_path = match CString::new(path.as_str()) {
            Ok(c) => c,
            Err(_) => return Ok(Value::Int(0)),
        };
        let handle = unsafe { LoadLibraryA(c_path.as_ptr() as *const u8) };
        if handle == 0 {
            tracing::warn!("spl_dlopen failed for '{}'", path);
            Ok(Value::Int(0))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        tracing::warn!("spl_dlopen not supported on this platform");
        Ok(Value::Int(0))
    }
}

/// Look up a symbol in a loaded library by name.
///
/// Callable from Simple as: `spl_dlsym(handle: i64, name: text) -> i64`
/// Returns 0 if the symbol is not found.
pub fn spl_dlsym(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("spl_dlsym requires 2 arguments (handle, name)"));
    }

    let handle_val = match &args[0] {
        Value::Int(h) => *h as usize,
        _ => return Err(CompileError::runtime("spl_dlsym: handle must be an integer")),
    };

    let name = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_dlsym: name must be a string")),
    };

    let c_name = match CString::new(name.as_str()) {
        Ok(c) => c,
        Err(_) => return Ok(Value::Int(0)),
    };

    #[cfg(unix)]
    {
        let handle = handle_val as *mut libc::c_void;
        let sym = unsafe { libc::dlsym(handle, c_name.as_ptr()) };
        Ok(Value::Int(sym as usize as i64))
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn GetProcAddress(hModule: isize, lpProcName: *const u8) -> *mut std::ffi::c_void;
        }
        let sym = unsafe { GetProcAddress(handle_val as isize, c_name.as_ptr() as *const u8) };
        Ok(Value::Int(sym as usize as i64))
    }

    #[cfg(not(any(unix, windows)))]
    {
        Ok(Value::Int(0))
    }
}

/// Close a loaded library.
///
/// Callable from Simple as: `spl_dlclose(handle: i64) -> i64`
/// Returns 0 on success.
pub fn spl_dlclose(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_dlclose requires 1 argument (handle)"));
    }

    let handle_val = match &args[0] {
        Value::Int(h) => *h as usize,
        _ => return Err(CompileError::runtime("spl_dlclose: handle must be an integer")),
    };

    #[cfg(unix)]
    {
        let handle = handle_val as *mut libc::c_void;
        let result = unsafe { libc::dlclose(handle) };
        Ok(Value::Int(result as i64))
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn FreeLibrary(hLibModule: isize) -> i32;
        }
        let result = unsafe { FreeLibrary(handle_val as isize) };
        Ok(Value::Int(if result != 0 { 0 } else { 1 }))
    }

    #[cfg(not(any(unix, windows)))]
    {
        Ok(Value::Int(1))
    }
}

/// Call a function pointer with i64 arguments and return an i64 result.
///
/// Callable from Simple as: `spl_wffi_call_i64(fptr: i64, args: [i64], nargs: i64) -> i64`
///
/// This is the core WFFI dispatch function that enables calling arbitrary
/// C functions loaded via dlsym. Supports 0-8 arguments.
pub fn spl_wffi_call_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "spl_wffi_call_i64 requires 3 arguments (fptr, args, nargs)",
        ));
    }

    let fptr = match &args[0] {
        Value::Int(p) => *p as usize,
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: fptr must be an integer")),
    };

    if fptr == 0 {
        return Err(CompileError::runtime("spl_wffi_call_i64: null function pointer"));
    }

    let call_args: Vec<i64> = match &args[1] {
        Value::Array(arr) => arr
            .iter()
            .map(|v| match v {
                Value::Int(n) => Ok(*n),
                Value::Bool(b) => Ok(if *b { 1i64 } else { 0i64 }),
                _ => Err(CompileError::runtime("spl_wffi_call_i64: args must be integers")),
            })
            .collect::<Result<Vec<_>, _>>()?,
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: args must be an array")),
    };

    let nargs = match &args[2] {
        Value::Int(n) => {
            usize::try_from(*n).map_err(|_| CompileError::runtime("spl_wffi_call_i64: nargs must be non-negative"))?
        }
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: nargs must be an integer")),
    };
    if nargs > 8 {
        return Err(CompileError::runtime("spl_wffi_call_i64: max 8 arguments supported"));
    }
    if nargs > call_args.len() {
        return Err(CompileError::runtime(
            "spl_wffi_call_i64: nargs exceeds supplied argument array",
        ));
    }

    // Safety: we trust the caller has provided a valid function pointer
    // and the correct number of arguments. This is inherently unsafe SFFI.
    let result: i64 = unsafe {
        match nargs {
            0 => {
                let f: extern "C" fn() -> i64 = std::mem::transmute(fptr);
                f()
            }
            1 => {
                let f: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0])
            }
            2 => {
                let f: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1])
            }
            3 => {
                let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2])
            }
            4 => {
                let f: extern "C" fn(i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3])
            }
            5 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4])
            }
            6 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                )
            }
            7 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                )
            }
            8 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                    call_args[7],
                )
            }
            _ => {
                return Err(CompileError::runtime("spl_wffi_call_i64: max 8 arguments supported"));
            }
        }
    };

    Ok(Value::Int(result))
}

/// Checked WFFI transport. Returns `[status, value]`; value is meaningful only
/// for status zero. Bridge failures never masquerade as a foreign zero result.
pub fn spl_wffi_call_i64_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    if !matches!(args[0], Value::Int(p) if p != 0) {
        return Ok(Value::array(vec![Value::Int(2), Value::Int(0)]));
    }
    let supplied = match &args[1] {
        Value::Array(values)
            if values
                .iter()
                .all(|value| matches!(value, Value::Int(_) | Value::Bool(_))) =>
        {
            values.len()
        }
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    let nargs = match args[2] {
        Value::Int(n) => match usize::try_from(n) {
            Ok(n) => n,
            Err(_) => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
        },
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    if nargs > 8 {
        return Ok(Value::array(vec![Value::Int(3), Value::Int(0)]));
    }
    if nargs > supplied {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    let value = spl_wffi_call_i64(args)?;
    Ok(Value::array(vec![Value::Int(0), value]))
}

/// Call a function pointer with f64 arguments and return an f64 result.
///
/// Callable from Simple as: `spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64`
///
/// Supports 0-8 arguments. Integer arguments are accepted and widened to f64
/// for parity with normal Simple numeric conversion.
pub fn spl_wffi_call_f64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "spl_wffi_call_f64 requires 3 arguments (fptr, args, nargs)",
        ));
    }

    let fptr = match &args[0] {
        Value::Int(p) => *p as usize,
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: fptr must be an integer")),
    };

    if fptr == 0 {
        return Err(CompileError::runtime("spl_wffi_call_f64: null function pointer"));
    }

    let call_args: Vec<f64> = match &args[1] {
        Value::Array(arr) => arr.iter().map(Value::as_float).collect::<Result<Vec<_>, _>>()?,
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: args must be an array")),
    };

    let nargs = match &args[2] {
        Value::Int(n) => {
            usize::try_from(*n).map_err(|_| CompileError::runtime("spl_wffi_call_f64: nargs must be non-negative"))?
        }
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: nargs must be an integer")),
    };
    if nargs > 8 {
        return Err(CompileError::runtime("spl_wffi_call_f64: max 8 arguments supported"));
    }
    if nargs > call_args.len() {
        return Err(CompileError::runtime(
            "spl_wffi_call_f64: nargs exceeds supplied argument array",
        ));
    }

    let result: f64 = unsafe {
        match nargs {
            0 => {
                let f: extern "C" fn() -> f64 = std::mem::transmute(fptr);
                f()
            }
            1 => {
                let f: extern "C" fn(f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0])
            }
            2 => {
                let f: extern "C" fn(f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1])
            }
            3 => {
                let f: extern "C" fn(f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2])
            }
            4 => {
                let f: extern "C" fn(f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3])
            }
            5 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4])
            }
            6 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                )
            }
            7 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                )
            }
            8 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                    call_args[7],
                )
            }
            _ => {
                return Err(CompileError::runtime("spl_wffi_call_f64: max 8 arguments supported"));
            }
        }
    };

    Ok(Value::Float(result))
}

pub fn spl_wffi_call_f64_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    if !matches!(args[0], Value::Int(p) if p != 0) {
        return Ok(Value::array(vec![Value::Int(2), Value::Int(0)]));
    }
    let supplied = match &args[1] {
        Value::Array(values)
            if values
                .iter()
                .all(|value| matches!(value, Value::Float(_) | Value::Int(_))) =>
        {
            values.len()
        }
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    let nargs = match args[2] {
        Value::Int(n) => match usize::try_from(n) {
            Ok(n) => n,
            Err(_) => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
        },
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    if nargs > 8 {
        return Ok(Value::array(vec![Value::Int(3), Value::Int(0)]));
    }
    if nargs > supplied {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    match spl_wffi_call_f64(args)? {
        Value::Float(value) => Ok(Value::array(vec![Value::Int(0), Value::Int(value.to_bits() as i64)])),
        _ => Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    }
}

/// Convert f64 to its bit representation as i64.
///
/// Callable from Simple as: `spl_f64_to_bits(f: f64) -> i64`
pub fn spl_f64_to_bits(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_f64_to_bits requires 1 argument"));
    }

    let f = match &args[0] {
        Value::Float(f) => *f,
        Value::Int(n) => *n as f64,
        _ => return Err(CompileError::runtime("spl_f64_to_bits: argument must be a number")),
    };

    Ok(Value::Int(f.to_bits() as i64))
}

/// Convert i64 bit representation back to f64.
///
/// Callable from Simple as: `spl_bits_to_f64(bits: i64) -> f64`
pub fn spl_bits_to_f64(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_bits_to_f64 requires 1 argument"));
    }

    let bits = match &args[0] {
        Value::Int(n) => *n as u64,
        _ => return Err(CompileError::runtime("spl_bits_to_f64: argument must be an integer")),
    };

    Ok(Value::Float(f64::from_bits(bits)))
}

/// Get a pointer to the string data as i64.
///
/// Callable from Simple as: `spl_str_ptr(s: text) -> i64`
///
/// NOTE: The returned pointer is only valid as long as the string lives.
/// For SFFI calls, use it immediately within the same expression.
pub fn spl_str_ptr(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_str_ptr requires 1 argument"));
    }

    let s = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_str_ptr: argument must be a string")),
    };

    // We need to create a null-terminated copy for C compatibility
    let c_str = match CString::new(s.as_str()) {
        Ok(c) => c,
        Err(_) => return Ok(Value::Int(0)),
    };

    // Leak the CString so the pointer stays valid
    let ptr = c_str.into_raw();
    Ok(Value::Int(ptr as usize as i64))
}

/// Convert a C string pointer to a Simple text value.
///
/// Callable from Simple as: `rt_cstring_to_text(ptr: i64) -> text`
pub fn rt_cstring_to_text(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_cstring_to_text requires 1 argument"));
    }

    let ptr = match &args[0] {
        Value::Int(p) => *p as usize as *const std::os::raw::c_char,
        _ => return Err(CompileError::runtime("rt_cstring_to_text: argument must be an integer")),
    };

    if ptr.is_null() {
        return Ok(Value::text(""));
    }

    let c_str = unsafe { CStr::from_ptr(ptr) };
    let s = c_str.to_string_lossy().into_owned();
    Ok(Value::text(s))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    extern "C" fn add_scaled(a: f64, b: f64, scale: f64) -> f64 {
        (a + b) * scale
    }

    #[test]
    fn spl_wffi_call_f64_invokes_function_pointer() {
        let fptr = add_scaled as usize as i64;
        let args = Value::Array(Arc::new(vec![
            Value::Float(1.25),
            Value::Float(2.75),
            Value::Float(0.5),
        ]));

        let result = spl_wffi_call_f64(&[Value::Int(fptr), args, Value::Int(3)]).unwrap();

        match result {
            Value::Float(v) => assert_eq!(v, 2.0),
            other => panic!("expected float result, got {other:?}"),
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn dynlib_snapshot_is_sealed_and_preserves_bytes() {
        use std::os::unix::ffi::OsStrExt;

        let path = std::env::temp_dir().join(format!(
            "simple-sffi-snapshot-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test"),
        ));
        std::fs::write(&path, b"provider-a").unwrap();
        let path_text = std::str::from_utf8(path.as_os_str().as_bytes()).unwrap();
        let result = spl_dynlib_snapshot_linux(&[Value::text(path_text.to_string())]).unwrap();
        let fd = match result {
            Value::Int(fd) if fd >= 0 => fd as libc::c_int,
            other => panic!("expected snapshot descriptor, got {other:?}"),
        };
        std::fs::write(&path, b"provider-b").unwrap();

        let seals = unsafe { libc::fcntl(fd, libc::F_GET_SEALS) };
        let required = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        assert_eq!(seals & required, required);
        let mut bytes = [0u8; 10];
        let got = unsafe { libc::pread(fd, bytes.as_mut_ptr().cast(), bytes.len(), 0) };
        assert_eq!(got, bytes.len() as isize);
        assert_eq!(&bytes, b"provider-a");
        assert_eq!(unsafe { libc::write(fd, b"x".as_ptr().cast(), 1) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));

        unsafe { libc::close(fd) };
        let symlink_path = path.with_extension("symlink");
        std::os::unix::fs::symlink(&path, &symlink_path).unwrap();
        assert_eq!(
            spl_dynlib_snapshot_linux(&[Value::text(symlink_path.to_string_lossy().into_owned())])
                .unwrap(),
            Value::Int(-1),
        );
        assert_eq!(
            spl_dynlib_snapshot_linux(&[Value::text("/dev/null".to_string())]).unwrap(),
            Value::Int(-1),
        );
        std::fs::remove_file(symlink_path).unwrap();
        std::fs::remove_file(path).unwrap();
    }
}
