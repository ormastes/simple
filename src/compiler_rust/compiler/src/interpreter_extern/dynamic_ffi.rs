//! Dynamic FFI dispatch for extern functions via runtime library loading.
//!
//! When an `extern fn rt_*()` call is not found in the built-in dispatch table,
//! this module attempts to resolve it dynamically by loading the runtime shared
//! library (`libsimple_runtime.so` / `.dylib` / `.dll`) and calling the function
//! via `dlsym`.
//!
//! ## Value Marshalling
//!
//! The runtime's `RuntimeValue` is `#[repr(transparent)]` over `u64`, so it maps
//! directly to `i64` in C ABI. The interpreter's `Value` enum is marshalled
//! to/from `i64` at the boundary:
//! - `Value::Int(n)` -> `n as i64`
//! - `Value::Float(f)` -> `f64::to_bits(f) as i64` (for raw pass-through)
//! - `Value::Bool(b)` -> `b as i64`
//! - `Value::Nil` -> `0i64`
//! - `Value::Str(s)` -> pointer to leaked CString as i64
//!
//! Return values are interpreted as `i64` and wrapped back as `Value::Int`.

use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;
use std::ffi::CString;
use std::sync::Mutex;

/// Global state for the dynamically loaded runtime library.
struct DynamicRuntime {
    /// Handle from dlopen (0 if not loaded or failed)
    handle: usize,
    /// Whether we already attempted to load (to avoid repeated failures)
    attempted: bool,
    /// Cached symbol lookups: function name -> function pointer address
    symbols: HashMap<String, usize>,
}

static DYNAMIC_RUNTIME: std::sync::LazyLock<Mutex<DynamicRuntime>> =
    std::sync::LazyLock::new(|| {
        Mutex::new(DynamicRuntime {
            handle: 0,
            attempted: false,
            symbols: HashMap::new(),
        })
    });

/// Attempt to find and load the runtime shared library.
///
/// Search order:
/// 1. Same directory as the current executable
/// 2. `../lib/` relative to the current executable
/// 3. System library paths (via dlopen with just the library name)
fn load_runtime_library() -> usize {
    let lib_name = runtime_lib_name();

    // Try paths relative to the current executable
    if let Ok(exe_path) = std::env::current_exe() {
        if let Some(exe_dir) = exe_path.parent() {
            // 1. Same directory as executable
            let same_dir = exe_dir.join(&lib_name);
            if let Some(handle) = try_dlopen(&same_dir.to_string_lossy()) {
                tracing::debug!("Loaded runtime library from: {}", same_dir.display());
                return handle;
            }

            // 2. ../lib/ relative to executable
            let lib_dir = exe_dir.join("../lib").join(&lib_name);
            if let Some(handle) = try_dlopen(&lib_dir.to_string_lossy()) {
                tracing::debug!("Loaded runtime library from: {}", lib_dir.display());
                return handle;
            }

            // 3. ../lib/ without canonicalization (in case symlinks differ)
            if let Some(parent) = exe_dir.parent() {
                let lib_dir2 = parent.join("lib").join(&lib_name);
                if let Some(handle) = try_dlopen(&lib_dir2.to_string_lossy()) {
                    tracing::debug!("Loaded runtime library from: {}", lib_dir2.display());
                    return handle;
                }
            }
        }
    }

    // 4. Also try cargo target directory (for development)
    // Look for target/debug/ or target/release/ relative to current dir
    for profile in &["debug", "release", "bootstrap"] {
        let cargo_path = format!("target/{}/{}", profile, lib_name);
        if let Some(handle) = try_dlopen(&cargo_path) {
            tracing::debug!("Loaded runtime library from cargo target: {}", cargo_path);
            return handle;
        }
    }

    // 5. System library search (just pass the name, let the OS find it)
    if let Some(handle) = try_dlopen(&lib_name) {
        tracing::debug!("Loaded runtime library from system path: {}", lib_name);
        return handle;
    }

    tracing::debug!("Could not find runtime library: {}", lib_name);
    0
}

/// Get the platform-specific library name.
fn runtime_lib_name() -> String {
    #[cfg(target_os = "macos")]
    {
        "libsimple_runtime.dylib".to_string()
    }
    #[cfg(target_os = "windows")]
    {
        "simple_runtime.dll".to_string()
    }
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    {
        "libsimple_runtime.so".to_string()
    }
}

/// Try to dlopen a library path, returning the handle or None.
fn try_dlopen(path: &str) -> Option<usize> {
    #[cfg(unix)]
    {
        let c_path = CString::new(path).ok()?;
        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };
        if handle.is_null() {
            None
        } else {
            Some(handle as usize)
        }
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn LoadLibraryA(lpLibFileName: *const u8) -> isize;
        }
        let c_path = CString::new(path).ok()?;
        let handle = unsafe { LoadLibraryA(c_path.as_ptr() as *const u8) };
        if handle == 0 {
            None
        } else {
            Some(handle as usize)
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        let _ = path;
        None
    }
}

/// Look up a symbol in the loaded runtime library.
fn dlsym_lookup(handle: usize, name: &str) -> Option<usize> {
    #[cfg(unix)]
    {
        let c_name = CString::new(name).ok()?;
        let sym = unsafe { libc::dlsym(handle as *mut libc::c_void, c_name.as_ptr()) };
        if sym.is_null() {
            None
        } else {
            Some(sym as usize)
        }
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn GetProcAddress(hModule: isize, lpProcName: *const u8) -> *mut std::ffi::c_void;
        }
        let c_name = CString::new(name).ok()?;
        let sym = unsafe { GetProcAddress(handle as isize, c_name.as_ptr() as *const u8) };
        if sym.is_null() {
            None
        } else {
            Some(sym as usize)
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        let _ = (handle, name);
        None
    }
}

/// Marshal a `Value` to an `i64` for passing to C functions.
///
/// The runtime functions generally operate on `RuntimeValue` which is a
/// `#[repr(transparent)]` wrapper around `u64`. For the interpreter, we
/// do a best-effort conversion:
/// - Int -> direct i64
/// - Float -> f64 bits as i64 (matches RuntimeValue float encoding)
/// - Bool -> 0 or 1
/// - Nil -> 0
/// - Str -> pointer to null-terminated C string (leaked)
fn value_to_i64(val: &Value) -> i64 {
    match val {
        Value::Int(n) => *n,
        Value::Float(f) => f.to_bits() as i64,
        Value::Bool(b) => if *b { 1 } else { 0 },
        Value::Nil => 0,
        Value::Str(s) => {
            // Create a null-terminated C string and leak it for the FFI call.
            // This is intentionally leaked because the runtime may hold onto
            // the pointer. For short-lived interpreter processes this is acceptable.
            match CString::new(s.as_str()) {
                Ok(c) => c.into_raw() as usize as i64,
                Err(_) => 0,
            }
        }
        // For complex types (Array, Object, etc.), pass 0 as a fallback.
        // These won't work correctly through raw FFI, but the built-in
        // dispatch table should handle them.
        _ => 0,
    }
}

/// Convert an i64 return value back to a Value.
///
/// Since we don't know the return type at this level, we return it as Int.
/// The caller (Simple code) will interpret it appropriately.
fn i64_to_value(v: i64) -> Value {
    Value::Int(v)
}

/// Try to call a function dynamically via the runtime shared library.
///
/// Returns `Some(Ok(Value))` if the function was found and called successfully,
/// `Some(Err(...))` if found but the call failed, or `None` if the function
/// was not found in the runtime library.
pub fn try_call_dynamic(name: &str, evaluated_args: &[Value]) -> Option<Result<Value, CompileError>> {
    let mut rt = match DYNAMIC_RUNTIME.lock() {
        Ok(rt) => rt,
        Err(_) => return None,
    };

    // Lazy-load the runtime library on first call
    if !rt.attempted {
        rt.attempted = true;
        rt.handle = load_runtime_library();
    }

    if rt.handle == 0 {
        return None;
    }

    // Look up the symbol (with caching)
    let fptr = if let Some(&cached) = rt.symbols.get(name) {
        if cached == 0 {
            return None; // Previously looked up and not found
        }
        cached
    } else {
        match dlsym_lookup(rt.handle, name) {
            Some(addr) => {
                rt.symbols.insert(name.to_string(), addr);
                addr
            }
            None => {
                rt.symbols.insert(name.to_string(), 0); // Cache the miss
                return None;
            }
        }
    };

    // Marshal arguments to i64
    let args: Vec<i64> = evaluated_args.iter().map(|v| value_to_i64(v)).collect();
    let nargs = args.len();

    // Call the function pointer with the appropriate number of arguments.
    // Safety: We trust that the function exists in the runtime and that the
    // caller has provided the correct number and types of arguments.
    // All runtime functions use extern "C" ABI with i64-sized args/returns.
    let result: i64 = unsafe {
        match nargs {
            0 => {
                let f: extern "C" fn() -> i64 = std::mem::transmute(fptr);
                f()
            }
            1 => {
                let f: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
                f(args[0])
            }
            2 => {
                let f: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
                f(args[0], args[1])
            }
            3 => {
                let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(args[0], args[1], args[2])
            }
            4 => {
                let f: extern "C" fn(i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(args[0], args[1], args[2], args[3])
            }
            5 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(args[0], args[1], args[2], args[3], args[4])
            }
            6 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 =
                    std::mem::transmute(fptr);
                f(args[0], args[1], args[2], args[3], args[4], args[5])
            }
            7 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64 =
                    std::mem::transmute(fptr);
                f(args[0], args[1], args[2], args[3], args[4], args[5], args[6])
            }
            8 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64) -> i64 =
                    std::mem::transmute(fptr);
                f(
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                    args[7],
                )
            }
            _ => {
                return Some(Err(CompileError::runtime(format!(
                    "dynamic FFI dispatch: function '{}' has {} arguments (max 8 supported)",
                    name, nargs
                ))));
            }
        }
    };

    Some(Ok(i64_to_value(result)))
}
