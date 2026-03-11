//! Dynamic FFI dispatch for extern functions via runtime library loading.
//!
//! When an `extern fn rt_*()` call is not found in the built-in dispatch table,
//! this module attempts to resolve it dynamically by loading the runtime shared
//! library (`libsimple_runtime.so` / `.dylib` / `.dll`) and calling the function
//! via `dlsym`.
//!
//! ## Satellite Libraries
//!
//! Functions with known prefixes (e.g. `rt_ts_*`, `rt_torch_*`) are resolved
//! from satellite shared libraries (`libspl_ts.so`, `libspl_torch.so`, etc.)
//! when they are not found in the main runtime library.  Satellite libraries
//! are loaded lazily on first use.
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

/// Known satellite library prefixes.
///
/// Function names matching `rt_PREFIX_*` where PREFIX is in this list
/// will be resolved from the corresponding satellite library
/// (`libspl_PREFIX.so` / `.dylib` / `.dll`).
const SATELLITE_PREFIXES: &[&str] = &["ts", "torch", "cuda", "vulkan", "vhdl"];

/// State for a lazily-loaded satellite shared library.
struct SatelliteLibrary {
    /// Handle from dlopen (0 if not loaded or failed)
    handle: usize,
    /// Whether we already attempted to load (to avoid repeated failures)
    attempted: bool,
    /// Cached symbol lookups: function name -> function pointer address
    symbols: HashMap<String, usize>,
}

/// Global map of satellite prefix -> library state.
static SATELLITE_LIBRARIES: std::sync::LazyLock<Mutex<HashMap<String, SatelliteLibrary>>> =
    std::sync::LazyLock::new(|| Mutex::new(HashMap::new()));

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

/// Derive the satellite prefix from a function name, if it matches a known prefix.
///
/// The convention is `rt_PREFIX_rest` where PREFIX is checked against
/// `SATELLITE_PREFIXES`.  Returns `None` for functions that belong to the
/// main runtime (e.g. `rt_file_read_text`) or don't start with `rt_`.
fn derive_satellite_prefix(name: &str) -> Option<&'static str> {
    let rest = name.strip_prefix("rt_")?;
    // Extract the second segment (between first and second underscores)
    let prefix_end = rest.find('_')?;
    let prefix = &rest[..prefix_end];
    // Must be at least 2 chars (skip single-char prefixes like `rt_f_*`)
    if prefix.len() < 2 {
        return None;
    }
    SATELLITE_PREFIXES
        .iter()
        .find(|&&p| p == prefix)
        .copied()
}

/// Get the platform-specific satellite library name for a given prefix.
fn satellite_lib_name(prefix: &str) -> String {
    #[cfg(target_os = "macos")]
    {
        format!("libspl_{}.dylib", prefix)
    }
    #[cfg(target_os = "windows")]
    {
        format!("spl_{}.dll", prefix)
    }
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    {
        format!("libspl_{}.so", prefix)
    }
}

/// Attempt to find and load a satellite shared library.
///
/// Uses the same search strategy as `load_runtime_library()` plus an
/// additional `build/` directory search for development convenience.
fn load_satellite_library(prefix: &str) -> usize {
    let lib_name = satellite_lib_name(prefix);

    // Try paths relative to the current executable
    if let Ok(exe_path) = std::env::current_exe() {
        if let Some(exe_dir) = exe_path.parent() {
            // 1. Same directory as executable
            let same_dir = exe_dir.join(&lib_name);
            if let Some(handle) = try_dlopen(&same_dir.to_string_lossy()) {
                tracing::debug!("Loaded satellite library '{}' from: {}", prefix, same_dir.display());
                return handle;
            }

            // 2. ../lib/ relative to executable
            let lib_dir = exe_dir.join("../lib").join(&lib_name);
            if let Some(handle) = try_dlopen(&lib_dir.to_string_lossy()) {
                tracing::debug!("Loaded satellite library '{}' from: {}", prefix, lib_dir.display());
                return handle;
            }

            // 3. ../lib/ without canonicalization
            if let Some(parent) = exe_dir.parent() {
                let lib_dir2 = parent.join("lib").join(&lib_name);
                if let Some(handle) = try_dlopen(&lib_dir2.to_string_lossy()) {
                    tracing::debug!("Loaded satellite library '{}' from: {}", prefix, lib_dir2.display());
                    return handle;
                }
            }
        }
    }

    // 4. Cargo target directories (development)
    for profile in &["debug", "release", "bootstrap"] {
        let cargo_path = format!("target/{}/{}", profile, lib_name);
        if let Some(handle) = try_dlopen(&cargo_path) {
            tracing::debug!("Loaded satellite library '{}' from cargo target: {}", prefix, cargo_path);
            return handle;
        }
    }

    // 5. build/ directory (development — satellite libs may be built here)
    let build_path = format!("build/{}", lib_name);
    if let Some(handle) = try_dlopen(&build_path) {
        tracing::debug!("Loaded satellite library '{}' from build dir: {}", prefix, build_path);
        return handle;
    }

    // 6. System library search
    if let Some(handle) = try_dlopen(&lib_name) {
        tracing::debug!("Loaded satellite library '{}' from system path: {}", prefix, lib_name);
        return handle;
    }

    tracing::debug!("Could not find satellite library '{}': {}", prefix, lib_name);
    0
}

/// Try to call a function from a satellite library, given its prefix.
///
/// Returns `Some(Ok(Value))` if the function was found and called,
/// `Some(Err(...))` on call failure, or `None` if not found.
fn try_call_satellite(
    prefix: &str,
    name: &str,
    evaluated_args: &[Value],
) -> Option<Result<Value, CompileError>> {
    let mut satellites = match SATELLITE_LIBRARIES.lock() {
        Ok(s) => s,
        Err(_) => return None,
    };

    let sat = satellites
        .entry(prefix.to_string())
        .or_insert_with(|| SatelliteLibrary {
            handle: 0,
            attempted: false,
            symbols: HashMap::new(),
        });

    // Lazy-load the satellite library on first access
    if !sat.attempted {
        sat.attempted = true;
        sat.handle = load_satellite_library(prefix);
    }

    if sat.handle == 0 {
        return None;
    }

    // Look up the symbol (with caching)
    let fptr = if let Some(&cached) = sat.symbols.get(name) {
        if cached == 0 {
            return None; // Previously looked up and not found
        }
        cached
    } else {
        match dlsym_lookup(sat.handle, name) {
            Some(addr) => {
                sat.symbols.insert(name.to_string(), addr);
                addr
            }
            None => {
                sat.symbols.insert(name.to_string(), 0);
                return None;
            }
        }
    };

    // Drop the lock before calling the function
    drop(satellites);

    // Marshal arguments and call
    call_fptr(fptr, name, evaluated_args)
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

/// Marshal arguments and call a resolved function pointer.
///
/// This is the shared call path used by both the main runtime dispatch and
/// satellite library dispatch.
fn call_fptr(
    fptr: usize,
    name: &str,
    evaluated_args: &[Value],
) -> Option<Result<Value, CompileError>> {
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

/// Try to call a function dynamically via the runtime shared library.
///
/// Resolution order:
/// 1. Look up in the main runtime library (`libsimple_runtime`)
/// 2. If not found and the name matches a known satellite prefix (`rt_PREFIX_*`),
///    try the corresponding satellite library (`libspl_PREFIX`)
///
/// Returns `Some(Ok(Value))` if the function was found and called successfully,
/// `Some(Err(...))` if found but the call failed, or `None` if the function
/// was not found in any library.
pub fn try_call_dynamic(name: &str, evaluated_args: &[Value]) -> Option<Result<Value, CompileError>> {
    // --- Step 1: Try the main runtime library ---
    let runtime_result = {
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
            None // No runtime library available
        } else {
            // Look up the symbol (with caching)
            if let Some(&cached) = rt.symbols.get(name) {
                if cached == 0 {
                    None // Previously looked up and not found
                } else {
                    Some(cached)
                }
            } else {
                match dlsym_lookup(rt.handle, name) {
                    Some(addr) => {
                        rt.symbols.insert(name.to_string(), addr);
                        Some(addr)
                    }
                    None => {
                        rt.symbols.insert(name.to_string(), 0); // Cache the miss
                        None
                    }
                }
            }
        }
    }; // rt lock dropped here

    if let Some(fptr) = runtime_result {
        return call_fptr(fptr, name, evaluated_args);
    }

    // --- Step 2: Try satellite libraries ---
    if let Some(prefix) = derive_satellite_prefix(name) {
        return try_call_satellite(prefix, name, evaluated_args);
    }

    None
}
