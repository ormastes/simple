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

/// Open a shared library and return its handle as i64.
///
/// Callable from Simple as: `spl_dlopen(path: text) -> i64`
/// Boundary failures are typed interpreter errors; they never become a handle.
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
            Err(_) => return Err(CompileError::runtime("spl_dlopen: path contains an interior NUL")),
        };

        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };

        if handle.is_null() {
            let err = unsafe { libc::dlerror() };
            if !err.is_null() {
                let err_str = unsafe { CStr::from_ptr(err) }.to_string_lossy();
                tracing::warn!("spl_dlopen failed for '{}': {}", path, err_str);
            }
            Err(CompileError::runtime(format!("spl_dlopen failed for '{path}'")))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryW;
        if path.contains('\0') {
            return Err(CompileError::runtime("spl_dlopen: path contains an interior NUL"));
        }
        let wide: Vec<u16> = path.encode_utf16().chain(std::iter::once(0)).collect();
        let handle = unsafe { LoadLibraryW(wide.as_ptr()) };
        if handle.is_null() {
            tracing::warn!("spl_dlopen failed for '{}'", path);
            Err(CompileError::runtime(format!("spl_dlopen failed for '{path}'")))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        tracing::warn!("spl_dlopen not supported on this platform");
        Err(CompileError::runtime("spl_dlopen is unsupported on this platform"))
    }
}

/// Status/out dynload ABI. Failure initializes the output and returns a
/// non-zero status, preserving a legitimate foreign integer zero elsewhere.
pub fn spl_dlopen_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "spl_dlopen_checked requires 2 arguments (path, out_handle)",
        ));
    }
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => return Err(CompileError::runtime("spl_dlopen_checked: output must be &mut i64")),
    };
    *output.inner_mut() = Value::Int(0);
    match spl_dlopen(&args[..1]) {
        Ok(Value::Int(handle)) if handle != 0 => {
            *output.inner_mut() = Value::Int(handle);
            Ok(Value::Int(0))
        }
        _ => Ok(Value::Int(2)),
    }
}

/// Look up a symbol in a loaded library by name.
///
/// Callable from Simple as: `spl_dlsym(handle: i64, name: text) -> i64`
/// Boundary failures are typed interpreter errors; they never become a symbol.
pub fn spl_dlsym(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("spl_dlsym requires 2 arguments (handle, name)"));
    }

    let handle_val = match &args[0] {
        Value::Int(h) => *h as usize,
        _ => return Err(CompileError::runtime("spl_dlsym: handle must be an integer")),
    };
    if handle_val == 0 {
        return Err(CompileError::runtime("spl_dlsym: null provider handle"));
    }

    let name = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_dlsym: name must be a string")),
    };

    let c_name = match CString::new(name.as_str()) {
        Ok(c) => c,
        Err(_) => return Err(CompileError::runtime("spl_dlsym: name contains an interior NUL")),
    };

    #[cfg(unix)]
    {
        let handle = handle_val as *mut libc::c_void;
        let sym = unsafe { libc::dlsym(handle, c_name.as_ptr()) };
        if sym.is_null() {
            Err(CompileError::runtime(format!("spl_dlsym: unresolved symbol '{name}'")))
        } else {
            Ok(Value::Int(sym as usize as i64))
        }
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn GetProcAddress(hModule: isize, lpProcName: *const u8) -> *mut std::ffi::c_void;
        }
        let sym = unsafe { GetProcAddress(handle_val as isize, c_name.as_ptr() as *const u8) };
        if sym.is_null() {
            Err(CompileError::runtime(format!("spl_dlsym: unresolved symbol '{name}'")))
        } else {
            Ok(Value::Int(sym as usize as i64))
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        Err(CompileError::runtime("spl_dlsym is unsupported on this platform"))
    }
}

/// Status/out symbol-resolution ABI.
pub fn spl_dlsym_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "spl_dlsym_checked requires 3 arguments (handle, name, out_symbol)",
        ));
    }
    let output = match &args[2] {
        Value::BorrowMut(value) => value,
        _ => return Err(CompileError::runtime("spl_dlsym_checked: output must be &mut i64")),
    };
    *output.inner_mut() = Value::Int(0);
    match spl_dlsym(&args[..2]) {
        Ok(Value::Int(symbol)) if symbol != 0 => {
            *output.inner_mut() = Value::Int(symbol);
            Ok(Value::Int(0))
        }
        _ => Ok(Value::Int(3)),
    }
}

/// Checked current-process symbol resolution, separate from null-handle lookup.
pub fn spl_dlsym_process_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "spl_dlsym_process_checked requires 2 arguments (name, out_symbol)",
        ));
    }
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => return Err(CompileError::runtime("spl_dlsym_process_checked: output must be &mut i64")),
    };
    *output.inner_mut() = Value::Int(0);
    let name = match &args[0] {
        Value::Str(value) if !value.is_empty() => value,
        _ => return Ok(Value::Int(1)),
    };
    let c_name = match CString::new(name.as_str()) {
        Ok(value) => value,
        Err(_) => return Ok(Value::Int(1)),
    };

    #[cfg(unix)]
    let symbol = unsafe { libc::dlsym(std::ptr::null_mut(), c_name.as_ptr()) };
    #[cfg(windows)]
    let symbol = unsafe {
        extern "system" {
            fn GetModuleHandleW(name: *const u16) -> isize;
            fn GetProcAddress(module: isize, name: *const u8) -> *mut std::ffi::c_void;
        }
        let process = GetModuleHandleW(std::ptr::null());
        if process == 0 {
            std::ptr::null_mut()
        } else {
            GetProcAddress(process, c_name.as_ptr() as *const u8)
        }
    };
    #[cfg(not(any(unix, windows)))]
    let symbol: *mut std::ffi::c_void = std::ptr::null_mut();

    if symbol.is_null() {
        return Ok(Value::Int(3));
    }
    *output.inner_mut() = Value::Int(symbol as usize as i64);
    Ok(Value::Int(0))
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

/// Allocation-free typed C-boolean call with no arguments.
pub fn spl_wffi_call_bool0_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Ok(Value::Int(1));
    }
    let fptr = match args[0] {
        Value::Int(value) if value != 0 => value as usize,
        _ => return Ok(Value::Int(2)),
    };
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    *output.inner_mut() = Value::Bool(false);
    let function: extern "C" fn() -> bool = unsafe { std::mem::transmute(fptr) };
    *output.inner_mut() = Value::Bool(function());
    Ok(Value::Int(0))
}

/// Allocation-free typed C-boolean call with one i64 argument.
pub fn spl_wffi_call_bool1_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::Int(1));
    }
    let fptr = match args[0] {
        Value::Int(value) if value != 0 => value as usize,
        _ => return Ok(Value::Int(2)),
    };
    let arg0 = match args[1] {
        Value::Int(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    let output = match &args[2] {
        Value::BorrowMut(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    *output.inner_mut() = Value::Bool(false);
    let function: extern "C" fn(i64) -> bool = unsafe { std::mem::transmute(fptr) };
    *output.inner_mut() = Value::Bool(function(arg0));
    Ok(Value::Int(0))
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
                .all(|value| matches!(value, Value::Int(_))) =>
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
            if values.iter().all(|value| matches!(value, Value::Float(_) | Value::Int(_))) =>
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
        Value::Float(value) => Ok(Value::array(vec![
            Value::Int(0),
            Value::Int(value.to_bits() as i64),
        ])),
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

    extern "C" fn return_i64(value: i64) -> i64 {
        value
    }

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

    #[test]
    fn dynload_rejects_interior_nul_instead_of_returning_zero() {
        assert!(spl_dlopen(&[Value::text("invalid\0library")]).is_err());
    }

    #[test]
    fn symbol_lookup_rejects_null_handle_instead_of_returning_zero() {
        assert!(spl_dlsym(&[Value::Int(0), Value::text("missing")]).is_err());
    }

    #[test]
    fn integer_bridge_rejects_boolean_coercion() {
        let values = Value::Array(Arc::new(vec![Value::Bool(true)]));
        assert!(spl_wffi_call_i64(&[
            Value::Int(return_i64 as usize as i64),
            values,
            Value::Int(1),
        ])
        .is_err());
    }
}
