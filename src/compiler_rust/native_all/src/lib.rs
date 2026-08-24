// Combined static library for native Simple binaries.
//
// This crate produces a single `libsimple_native_all.a` that includes
// ALL transitive dependencies from both `simple-compiler` (Cranelift SFFI,
// codegen, parser) and `simple-runtime` (GC, SFFI wrappers, actors).
//
// When linked into a native binary produced by `native-build`, the binary
// gains access to `rt_cranelift_*` functions, enabling self-hosted
// compilation (Stage 3 bootstrap).

// Re-export all crates so their #[no_mangle] extern "C" functions
// are included in the static library.
pub use simple_compiler;
pub use simple_runtime;
#[cfg(feature = "driver-compat")]
pub use simple_driver;

mod mem_snapshot_provider;
pub use mem_snapshot_provider::{
    rt_mem_snapshot_close, rt_mem_snapshot_open, rt_mem_snapshot_record, rt_phase_profile_record,
};

// Row 3 hosted-compositor SFFI bindings. This `extern crate` is the
// load-bearing reference that forces rustc to link the staticlib's
// object files into `libsimple_native_all.a`, exporting the
// `rt_cocoa_*` / `rt_win32_*` / `rt_hosted_select_surface` symbols.
// The crate itself compiles as "stubs only" on all hosts by default;
// real Cocoa / Win32 code is gated behind its `cocoa-real` / `win32-real`
// features.
use spl_hosted_runtime as _;

use std::collections::{BTreeMap, HashMap};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Mutex, OnceLock};

use simple_compiler::optimizations::{format_optimization_guide, NativeOptimizationLevel};
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_runtime::value::{
    rt_array_get, rt_array_len, rt_string_data, rt_string_len, rt_tuple_new, rt_tuple_set, RuntimeValue,
};

#[no_mangle]
pub extern "C" fn rt_jit_cleanup(handle: i64) -> i64 {
    simple_compiler::native_jit_cleanup_handle(handle)
}
// `rt_native_build` and its helpers now live in `simple_compiler::native_build_sffi`.
// They moved there so the SEED binary (which cannot depend on this staticlib crate)
// carries the definition and the JIT can resolve `extern fn rt_native_build`.
// This crate still exports the identical symbol via `pub use simple_compiler;`
// above -- the same mechanism that rolls the `rt_cranelift_*` symbols in.
pub use simple_compiler::native_build_sffi::rt_native_build;
// `simple-runtime` is the sole C-ABI owner; explicitly retain its symbol in
// the combined archive without defining a competing implementation here.
pub use simple_runtime::value::sffi::file_io::file_ops::rt_file_atomic_write;
use simple_compiler::native_build_sffi::{
    extract_rt_string, extract_rt_string_array, native_build_bootstrap_mode, native_build_process_args_usable,
    resolve_native_build_entry,
};

// ============================================================================
// C-ABI stubs for interpreter extern functions missing from the runtime.
//
// These functions are declared as `extern fn` in Simple source but only have
// Rust-mangled implementations in the interpreter dispatch table. The native
// binary needs C-ABI symbols. Functions are implemented using the Rust std
// library directly rather than going through the interpreter.
//
// All functions use the Simple tagged-value ABI: arguments and return values
// are i64 RuntimeValues. Strings are RuntimeValue pointers; integers are
// unboxed i64 values (not tagged).
// ============================================================================

use simple_runtime::value::{rt_string_new, rt_array_new as rt_array_new_impl, rt_array_push as rt_array_push_impl};

/// Convert i64 to RuntimeValue (same bit pattern, repr(transparent) u64)
#[inline(always)]
fn to_rv(val: i64) -> RuntimeValue {
    unsafe { std::mem::transmute::<u64, RuntimeValue>(val as u64) }
}

/// Convert RuntimeValue to i64
#[inline(always)]
fn from_rv(val: RuntimeValue) -> i64 {
    unsafe { std::mem::transmute::<RuntimeValue, u64>(val) as i64 }
}

/// Helper: extract a Rust path string from a RuntimeValue.
fn stub_extract_path(val: i64) -> Option<String> {
    let len = rt_string_len(to_rv(val));
    if len < 0 {
        return None;
    }
    let data = rt_string_data(to_rv(val));
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

/// Helper: create a RuntimeValue string from a Rust string.
fn stub_make_string(s: &str) -> i64 {
    from_rv(rt_string_new(s.as_ptr(), s.len() as u64))
}

#[derive(Clone, Copy)]
enum NativeStoredValue {
    Int(i64),
    Bool(bool),
    Nil,
    Raw(i64),
}

impl NativeStoredValue {
    fn from_abi(value: i64) -> Self {
        let runtime_value = to_rv(value);
        if runtime_value.is_int() {
            Self::Int(runtime_value.as_int())
        } else if runtime_value.is_bool() {
            Self::Bool(runtime_value.as_bool())
        } else if runtime_value.is_nil() {
            Self::Nil
        } else {
            Self::Raw(value)
        }
    }

    fn direct_abi(self) -> i64 {
        match self {
            Self::Int(value) => value,
            Self::Bool(value) => i64::from(value),
            Self::Nil => 0,
            Self::Raw(value) => value,
        }
    }

    fn runtime_value(self) -> RuntimeValue {
        match self {
            Self::Int(value) => RuntimeValue::from_int(value),
            Self::Bool(value) => RuntimeValue::from_bool(value),
            Self::Nil => RuntimeValue::NIL,
            Self::Raw(value) => to_rv(value),
        }
    }
}

type NativeMapRegistry<T> = OnceLock<Mutex<HashMap<i64, T>>>;

static NEXT_HASHMAP_HANDLE: AtomicI64 = AtomicI64::new(1);
static HASHMAP_REGISTRY: NativeMapRegistry<HashMap<String, NativeStoredValue>> = OnceLock::new();
static NEXT_BTREEMAP_HANDLE: AtomicI64 = AtomicI64::new(200_000);
static BTREEMAP_REGISTRY: NativeMapRegistry<BTreeMap<String, NativeStoredValue>> = OnceLock::new();

fn hashmap_registry() -> &'static Mutex<HashMap<i64, HashMap<String, NativeStoredValue>>> {
    HASHMAP_REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

fn btreemap_registry() -> &'static Mutex<HashMap<i64, BTreeMap<String, NativeStoredValue>>> {
    BTREEMAP_REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

fn stub_extract_key(key: i64) -> Option<String> {
    stub_extract_path(key)
}

fn native_array_from_raw_values(values: impl IntoIterator<Item = i64>) -> i64 {
    let array = rt_array_new_impl(0);
    for value in values {
        rt_array_push_impl(array, to_rv(value));
    }
    from_rv(array)
}

fn native_array_from_stored_values(values: impl IntoIterator<Item = NativeStoredValue>) -> i64 {
    let array = rt_array_new_impl(0);
    for value in values {
        rt_array_push_impl(array, value.runtime_value());
    }
    from_rv(array)
}

fn native_entry_pair(key: &str, value: NativeStoredValue) -> RuntimeValue {
    let pair = rt_array_new_impl(2);
    rt_array_push_impl(pair, to_rv(stub_make_string(key)));
    rt_array_push_impl(pair, value.runtime_value());
    pair
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_new() -> i64 {
    let handle = NEXT_HASHMAP_HANDLE.fetch_add(1, Ordering::Relaxed);
    hashmap_registry().lock().unwrap().insert(handle, HashMap::new());
    handle
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_insert(handle: i64, key: i64, value: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    let mut registry = hashmap_registry().lock().unwrap();
    let Some(map) = registry.get_mut(&handle) else {
        return 0;
    };
    let was_new = !map.contains_key(&key);
    map.insert(key, NativeStoredValue::from_abi(value));
    i64::from(was_new)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_get(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.get(&key).copied())
        .map(NativeStoredValue::direct_abi)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_remove(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    hashmap_registry()
        .lock()
        .unwrap()
        .get_mut(&handle)
        .and_then(|map| map.remove(&key))
        .map(NativeStoredValue::direct_abi)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_len(handle: i64) -> i64 {
    hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.len() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_clear(handle: i64) -> i64 {
    if let Some(map) = hashmap_registry().lock().unwrap().get_mut(&handle) {
        map.clear();
        1
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_contains_key(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| i64::from(map.contains_key(&key)))
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_keys(handle: i64) -> i64 {
    let keys: Vec<String> = hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.keys().cloned().collect())
        .unwrap_or_default();
    native_array_from_raw_values(keys.iter().map(|key| stub_make_string(key)))
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_values(handle: i64) -> i64 {
    let values: Vec<NativeStoredValue> = hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.values().copied().collect())
        .unwrap_or_default();
    native_array_from_stored_values(values)
}

#[no_mangle]
pub extern "C" fn __rt_hashmap_entries(handle: i64) -> i64 {
    let entries: Vec<(String, NativeStoredValue)> = hashmap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.iter().map(|(key, value)| (key.clone(), *value)).collect())
        .unwrap_or_default();
    let array = rt_array_new_impl(0);
    for (key, value) in entries {
        rt_array_push_impl(array, native_entry_pair(&key, value));
    }
    from_rv(array)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_new() -> i64 {
    let handle = NEXT_BTREEMAP_HANDLE.fetch_add(1, Ordering::Relaxed);
    btreemap_registry().lock().unwrap().insert(handle, BTreeMap::new());
    handle
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_insert(handle: i64, key: i64, value: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    let mut registry = btreemap_registry().lock().unwrap();
    let Some(map) = registry.get_mut(&handle) else {
        return 0;
    };
    let was_new = !map.contains_key(&key);
    map.insert(key, NativeStoredValue::from_abi(value));
    i64::from(was_new)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_get(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.get(&key).copied())
        .map(NativeStoredValue::direct_abi)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_remove(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    btreemap_registry()
        .lock()
        .unwrap()
        .get_mut(&handle)
        .and_then(|map| map.remove(&key))
        .map(NativeStoredValue::direct_abi)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_len(handle: i64) -> i64 {
    btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.len() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_clear(handle: i64) -> i64 {
    if let Some(map) = btreemap_registry().lock().unwrap().get_mut(&handle) {
        map.clear();
        1
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_contains_key(handle: i64, key: i64) -> i64 {
    let Some(key) = stub_extract_key(key) else {
        return 0;
    };
    btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| i64::from(map.contains_key(&key)))
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_keys(handle: i64) -> i64 {
    let keys: Vec<String> = btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.keys().cloned().collect())
        .unwrap_or_default();
    native_array_from_raw_values(keys.iter().map(|key| stub_make_string(key)))
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_values(handle: i64) -> i64 {
    let values: Vec<NativeStoredValue> = btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.values().copied().collect())
        .unwrap_or_default();
    native_array_from_stored_values(values)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_entries(handle: i64) -> i64 {
    let entries: Vec<(String, NativeStoredValue)> = btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.iter().map(|(key, value)| (key.clone(), *value)).collect())
        .unwrap_or_default();
    let array = rt_array_new_impl(0);
    for (key, value) in entries {
        rt_array_push_impl(array, native_entry_pair(&key, value));
    }
    from_rv(array)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_first_key(handle: i64) -> i64 {
    btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.keys().next().map(|key| stub_make_string(key)))
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn __rt_btreemap_last_key(handle: i64) -> i64 {
    btreemap_registry()
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.keys().next_back().map(|key| stub_make_string(key)))
        .unwrap_or(0)
}

// -- Process/System stubs --
//
// `rt_getpid` and `rt_thread_available_parallelism` are provided by the
// bundled `simple-runtime` (duplicate symbols fail the macOS link), so they are
// not redefined here.

#[no_mangle]
pub extern "C" fn rt_hostname() -> i64 {
    stub_make_string("localhost")
}

#[no_mangle]
pub extern "C" fn rt_system_cpu_count() -> i64 {
    std::thread::available_parallelism()
        .map(|n| n.get() as i64)
        .unwrap_or(1)
}

// spl_thread_cpu_count: the shim formerly here now lives in simple-runtime
// (runtime/src/executor.rs), whose object files are bundled into this same
// staticlib — keeping both defined breaks the Stage-2 bootstrap link with
// `duplicate symbol '_spl_thread_cpu_count'`.

#[no_mangle]
pub extern "C" fn rt_current_time_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

// -- Builtins --
//
// `sys_get_args` and `sys_exit` are provided by the bundled `simple-runtime`
// (duplicate symbols fail the macOS link), so they are not redefined here.

// NOTE: Do NOT export a raw `exit` symbol — it overrides libc's exit()
// and causes infinite recursion with std::process::exit(). The Simple
// `exit()` function is compiled to `app__io__cli_ops__exit` by the LLVM
// backend, and `sys_exit` handles the SFFI path.

#[no_mangle]
pub extern "C" fn sys_malloc(size: i64) -> i64 {
    unsafe {
        let ptr = std::alloc::alloc(std::alloc::Layout::from_size_align(size as usize, 8).unwrap());
        ptr as i64
    }
}

#[no_mangle]
pub extern "C" fn sys_realloc(ptr: i64, size: i64) -> i64 {
    unsafe {
        let new_ptr = std::alloc::realloc(
            ptr as *mut u8,
            std::alloc::Layout::from_size_align(1, 8).unwrap(),
            size as usize,
        );
        new_ptr as i64
    }
}

#[no_mangle]
pub extern "C" fn sys_free(ptr: i64) -> i64 {
    // No-op: we don't track allocations here
    let _ = ptr;
    0
}

// -- I/O builtins (spl_ prefixed to avoid libc/libm symbol collisions) --

#[no_mangle]
pub extern "C" fn spl_print(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        print!("{}", s);
    } else {
        print!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn spl_println(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        println!("{}", s);
    } else {
        println!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn spl_eprint(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        eprint!("{}", s);
    } else {
        eprint!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn spl_eprintln(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        eprintln!("{}", s);
    } else {
        eprintln!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn spl_print_raw(val: i64) -> i64 {
    spl_print(val)
}

#[no_mangle]
pub extern "C" fn spl_eprint_raw(val: i64) -> i64 {
    spl_eprint(val)
}

#[no_mangle]
pub extern "C" fn spl_dbg(val: i64) -> i64 {
    eprintln!("[dbg] {}", val);
    val
}

#[no_mangle]
pub extern "C" fn spl_dprint(val: i64) -> i64 {
    spl_dbg(val)
}

#[no_mangle]
pub extern "C" fn spl_input(_prompt: i64) -> i64 {
    let mut buf = String::new();
    let _ = std::io::stdin().read_line(&mut buf);
    stub_make_string(buf.trim_end())
}

#[no_mangle]
pub extern "C" fn spl_panic(msg: i64) -> i64 {
    if let Some(s) = stub_extract_path(msg) {
        eprintln!("panic: {}", s);
    } else {
        eprintln!("panic: {}", msg);
    }
    std::process::exit(1);
}

// -- Math builtins (spl_ prefixed to avoid libm collisions) --

#[no_mangle]
pub extern "C" fn spl_abs(val: i64) -> i64 {
    val.abs()
}
#[no_mangle]
pub extern "C" fn spl_min(a: i64, b: i64) -> i64 {
    std::cmp::min(a, b)
}
#[no_mangle]
pub extern "C" fn spl_max(a: i64, b: i64) -> i64 {
    std::cmp::max(a, b)
}
#[no_mangle]
pub extern "C" fn spl_pow(base: i64, exp: i64) -> i64 {
    (base as f64).powi(exp as i32) as i64
}
#[no_mangle]
pub extern "C" fn spl_sqrt(val: i64) -> i64 {
    (val as f64).sqrt() as i64
}
#[no_mangle]
pub extern "C" fn spl_ceil(val: i64) -> i64 {
    val
} // integers are already ceil
#[no_mangle]
pub extern "C" fn spl_floor(val: i64) -> i64 {
    val
}
#[no_mangle]
pub extern "C" fn spl_to_int(val: i64) -> i64 {
    val
}

#[no_mangle]
pub extern "C" fn spl_to_string(val: i64) -> i64 {
    // Check if it's a string already
    if rt_string_len(to_rv(val)) >= 0 {
        val
    } else {
        stub_make_string(&val.to_string())
    }
}

// -- Backward-compatible aliases (old bare names → spl_ prefixed) --
// These are kept temporarily for compatibility with older compiled objects.
// Codegen now emits spl_ prefixed names; these can be removed once all
// compiled objects are regenerated.

#[no_mangle]
pub extern "C" fn print(val: i64) -> i64 {
    spl_print(val)
}
#[no_mangle]
pub extern "C" fn println(val: i64) -> i64 {
    spl_println(val)
}
#[no_mangle]
pub extern "C" fn eprint(val: i64) -> i64 {
    spl_eprint(val)
}
#[no_mangle]
pub extern "C" fn eprintln(val: i64) -> i64 {
    spl_eprintln(val)
}
#[no_mangle]
pub extern "C" fn eprint_raw(val: i64) -> i64 {
    spl_eprint_raw(val)
}
#[no_mangle]
pub extern "C" fn dbg(val: i64) -> i64 {
    spl_dbg(val)
}
#[no_mangle]
pub extern "C" fn dprint(val: i64) -> i64 {
    spl_dprint(val)
}
#[no_mangle]
pub extern "C" fn input(prompt: i64) -> i64 {
    spl_input(prompt)
}
#[no_mangle]
pub extern "C" fn panic(msg: i64) -> i64 {
    spl_panic(msg)
}
#[no_mangle]
pub extern "C" fn abs(val: i64) -> i64 {
    spl_abs(val)
}
#[no_mangle]
pub extern "C" fn min(a: i64, b: i64) -> i64 {
    spl_min(a, b)
}
#[no_mangle]
pub extern "C" fn max(a: i64, b: i64) -> i64 {
    spl_max(a, b)
}
#[no_mangle]
pub extern "C" fn pow(base: i64, exp: i64) -> i64 {
    spl_pow(base, exp)
}
#[no_mangle]
pub extern "C" fn sqrt(val: i64) -> i64 {
    spl_sqrt(val)
}
#[no_mangle]
pub extern "C" fn ceil(val: i64) -> i64 {
    spl_ceil(val)
}
#[no_mangle]
pub extern "C" fn floor(val: i64) -> i64 {
    spl_floor(val)
}
#[no_mangle]
pub extern "C" fn to_int(val: i64) -> i64 {
    spl_to_int(val)
}
#[no_mangle]
pub extern "C" fn to_string(val: i64) -> i64 {
    spl_to_string(val)
}

// -- Compiler backend stubs --
//
// `rt_compile_to_llvm_ir`, `rt_compile_to_native`, and
// `rt_compile_to_native_with_opt` are provided by the bundled `simple-runtime`
// (duplicate symbols fail the macOS link), so they are not redefined here.

/// Execute a native binary with arguments and timeout.
///
/// Simple signature: `extern fn rt_execute_native(binary_path: text, args: [text], timeout_ms: i64) -> (text, text, i32)`
fn execute_native_process(
    binary_path: &str,
    cmd_args: &[String],
    timeout: std::time::Duration,
) -> (String, String, i64) {
    use std::io::Read;
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    let mut child = match Command::new(binary_path)
        .args(cmd_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => return (String::new(), format!("Execution error: {}", error), -1),
    };

    // Drain both pipes as soon as the child starts. Waiting for process exit
    // before reading can deadlock when either OS pipe buffer fills.
    let stdout_reader = child.stdout.take().map(|mut stdout| {
        std::thread::spawn(move || {
            let mut captured = String::new();
            let _ = stdout.read_to_string(&mut captured);
            captured
        })
    });
    let stderr_reader = child.stderr.take().map(|mut stderr| {
        std::thread::spawn(move || {
            let mut captured = String::new();
            let _ = stderr.read_to_string(&mut captured);
            captured
        })
    });

    let start = Instant::now();
    let poll_interval = Duration::from_millis(10);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if start.elapsed() >= timeout => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            Ok(None) => std::thread::sleep(poll_interval),
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
        }
    };

    let stdout = stdout_reader.and_then(|reader| reader.join().ok()).unwrap_or_default();
    let stderr = stderr_reader.and_then(|reader| reader.join().ok()).unwrap_or_default();

    match status {
        Some(status) => (stdout, stderr, status.code().unwrap_or(-1) as i64),
        None => (String::new(), "Execution timed out".to_string(), 124),
    }
}

#[no_mangle]
pub extern "C" fn rt_execute_native(path_rv: RuntimeValue, args_rv: RuntimeValue, timeout_ms: i64) -> i64 {
    use std::time::Duration;

    // Helper: build a result tuple (stdout, stderr, exit_code)
    fn make_result(stdout: &str, stderr: &str, code: i64) -> i64 {
        let tup = rt_tuple_new(3);
        let s1 = rt_string_new(stdout.as_ptr(), stdout.len() as u64);
        let s2 = rt_string_new(stderr.as_ptr(), stderr.len() as u64);
        rt_tuple_set(tup, 0, s1);
        rt_tuple_set(tup, 1, s2);
        rt_tuple_set(tup, 2, RuntimeValue::from_int(code));
        from_rv(tup)
    }

    let binary_path = match extract_rt_string(path_rv) {
        Some(s) => s,
        None => return make_result("", "Invalid binary path", -1),
    };

    let cmd_args = extract_rt_string_array(args_rv);

    // Check if binary exists
    if !std::path::Path::new(&binary_path).exists() {
        return make_result("", &format!("Binary not found: {}", binary_path), 127);
    }

    let timeout = if timeout_ms > 0 {
        Duration::from_millis(timeout_ms as u64)
    } else {
        Duration::from_millis(1)
    };

    let (stdout, stderr, exit_code) = execute_native_process(&binary_path, &cmd_args, timeout);
    make_result(&stdout, &stderr, exit_code)
}
#[no_mangle]
pub extern "C" fn rt_cargo_fmt() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn rt_cargo_lint() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn rt_cargo_test_doc() -> i64 {
    0
}

// -- Concurrency stubs --

#[no_mangle]
pub extern "C" fn rt_get_concurrent_backend() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn rt_set_concurrent_backend(_backend: i64) -> i64 {
    0
}

// -- Stdio stubs --
//
// The bundled C runtime (`simple-runtime`, archived into this same
// `libsimple_native_all.a`) already exports the stdio entry points
// (`stdout_write`, `rt_stdout_write`, `rt_stdout_flush`, `stderr_write`,
// `stderr_flush`, `rt_stderr_write`, `rt_stderr_flush`, `stdin_read_char`).
// Redefining them here produced duplicate-symbol link failures on macOS
// (whose `ld` has no `--allow-multiple-definition`). Only `stdout_flush`,
// which the runtime does NOT provide, is defined here.

#[no_mangle]
pub extern "C" fn stdout_flush() -> i64 {
    use std::io::Write;
    let _ = std::io::stdout().flush();
    0
}

// -- Memory stubs --

#[no_mangle]
pub extern "C" fn memory_usage() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn memory_limit() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn default_memory_limit() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn is_memory_limited() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn parse_memory_size(_s: i64) -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn format_bytes(n: i64) -> i64 {
    stub_make_string(&format!("{} B", n))
}

// -- Time stubs --

#[no_mangle]
pub extern "C" fn _current_time_unix() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// -- Native terminal stubs (no-op) --

#[no_mangle]
pub extern "C" fn native_enable_raw_mode() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_disable_raw_mode() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_get_term_size() -> i64 {
    80
} // default 80 cols
#[no_mangle]
pub extern "C" fn native_is_tty() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_stdout() -> i64 {
    1
}
#[no_mangle]
pub extern "C" fn native_stderr() -> i64 {
    2
}
#[no_mangle]
pub extern "C" fn native_stdin() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_term_flush() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_term_poll() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_term_read() -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_term_read_timeout(_ms: i64) -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_term_write(_data: i64) -> i64 {
    0
}

// -- Native FS stubs (delegate to rt_file_* where possible) --

#[no_mangle]
pub extern "C" fn native_fs_exists(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::path::Path::new(&p).exists() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_read_string(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if let Ok(content) = std::fs::read_to_string(&p) {
            stub_make_string(&content)
        } else {
            stub_make_string("")
        }
    } else {
        stub_make_string("")
    }
}
#[no_mangle]
pub extern "C" fn native_fs_write_string(path: i64, content: i64) -> i64 {
    if let (Some(p), Some(c)) = (stub_extract_path(path), stub_extract_path(content)) {
        if std::fs::write(&p, &c).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_read(path: i64) -> i64 {
    native_fs_read_string(path)
}
#[no_mangle]
pub extern "C" fn native_fs_write(path: i64, content: i64) -> i64 {
    native_fs_write_string(path, content)
}
#[no_mangle]
pub extern "C" fn native_fs_append(path: i64, content: i64) -> i64 {
    use std::io::Write;
    if let (Some(p), Some(c)) = (stub_extract_path(path), stub_extract_path(content)) {
        if let Ok(mut f) = std::fs::OpenOptions::new().append(true).create(true).open(&p) {
            if f.write_all(c.as_bytes()).is_ok() {
                return 1;
            }
        }
    }
    0
}
#[no_mangle]
pub extern "C" fn native_fs_copy(src: i64, dst: i64) -> i64 {
    if let (Some(s), Some(d)) = (stub_extract_path(src), stub_extract_path(dst)) {
        if std::fs::copy(&s, &d).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_rename(src: i64, dst: i64) -> i64 {
    if let (Some(s), Some(d)) = (stub_extract_path(src), stub_extract_path(dst)) {
        if std::fs::rename(&s, &d).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_remove_file(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::remove_file(&p).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_remove_dir(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::remove_dir_all(&p).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_create_dir(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::create_dir_all(&p).is_ok() {
            1
        } else {
            0
        }
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn native_fs_metadata(_path: i64) -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn native_fs_read_dir(_path: i64) -> i64 {
    from_rv(rt_array_new_impl(0))
}

// -- Misc stubs (return 0/nil) --

#[no_mangle]
pub extern "C" fn lexer_tokenize(_source: i64) -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn simple_layout_mark(_name: i64) -> i64 {
    0
}
#[no_mangle]
pub extern "C" fn bytes_to_string(data: i64) -> i64 {
    data
}

// -- Remaining stubs: arc_box, rc_box, btreemap/set, hashmap/set, etc.
// These are no-op stubs that return 0. Most are only needed for code paths
// that won't execute during bootstrap.

macro_rules! noop_stubs {
    ($($name:ident),* $(,)?) => {
        $(
            #[no_mangle]
            pub extern "C" fn $name(_a: i64, _b: i64, _c: i64, _d: i64) -> i64 { 0 }
        )*
    };
}

noop_stubs!(
    // Arc/Rc box operations
    arc_box_init,
    arc_box_get_value,
    arc_box_inc_strong,
    arc_box_dec_strong,
    arc_box_inc_weak,
    arc_box_dec_weak,
    arc_box_drop_value,
    arc_box_size,
    arc_box_strong_count,
    arc_box_weak_count,
    rc_box_init,
    rc_box_get_value,
    rc_box_inc_strong,
    rc_box_dec_strong,
    rc_box_inc_weak,
    rc_box_dec_weak,
    rc_box_drop_value,
    rc_box_size,
    rc_box_strong_count,
    rc_box_weak_count,
    // BTreeSet (prefixed with __ in interpreter)
    __rt_btreeset_new,
    __rt_btreeset_insert,
    __rt_btreeset_remove,
    __rt_btreeset_contains,
    __rt_btreeset_len,
    __rt_btreeset_clear,
    __rt_btreeset_first,
    __rt_btreeset_last,
    __rt_btreeset_to_array,
    __rt_btreeset_union,
    __rt_btreeset_intersection,
    __rt_btreeset_difference,
    __rt_btreeset_symmetric_difference,
    __rt_btreeset_is_subset,
    __rt_btreeset_is_superset,
    // HashSet (prefixed with __ in interpreter)
    __rt_hashset_new,
    __rt_hashset_insert,
    __rt_hashset_remove,
    __rt_hashset_contains,
    __rt_hashset_len,
    __rt_hashset_clear,
    __rt_hashset_to_array,
    __rt_hashset_union,
    __rt_hashset_intersection,
    __rt_hashset_difference,
    __rt_hashset_symmetric_difference,
    __rt_hashset_is_subset,
    __rt_hashset_is_superset,
    // Error handling
    rt_error_throw,
    rt_error_message,
    rt_error_free,
    rt_error_division_by_zero,
    rt_error_index_oob,
    rt_error_type_mismatch,
    rt_error_undefined_var,
    rt_error_arg_count,
    rt_error_semantic,
    // Environment (interpreter-internal)
    rt_env_new_handle,
    rt_env_free_handle,
    rt_env_push_scope,
    rt_env_pop_scope,
    rt_env_define_var,
    rt_env_set_var,
    rt_env_get_var,
    rt_env_has_var,
    rt_env_scope_depth,
    rt_env_snapshot,
    rt_env_var_count,
    rt_env_var_names,
    // AST manipulation (interpreter-only)
    rt_ast_registry_clear,
    rt_ast_registry_count,
    rt_ast_expr_tag,
    rt_ast_expr_free,
    rt_ast_expr_int_value,
    rt_ast_expr_float_value,
    rt_ast_expr_bool_value,
    rt_ast_expr_string_value,
    rt_ast_expr_ident_name,
    rt_ast_expr_binary_left,
    rt_ast_expr_binary_right,
    rt_ast_expr_binary_op,
    rt_ast_expr_unary_op,
    rt_ast_expr_unary_operand,
    rt_ast_expr_call_callee,
    rt_ast_expr_call_arg_count,
    rt_ast_expr_call_arg,
    rt_ast_expr_method_receiver,
    rt_ast_expr_method_name,
    rt_ast_expr_method_arg_count,
    rt_ast_expr_method_arg,
    rt_ast_expr_field_receiver,
    rt_ast_expr_field_name,
    rt_ast_expr_array_len,
    rt_ast_expr_array_get,
    rt_ast_arg_name,
    rt_ast_arg_value,
    rt_ast_arg_free,
    rt_ast_node_free,
    // Span/I18N
    rt_span_create,
    rt_span_start,
    rt_span_end,
    rt_span_line,
    rt_span_column,
    rt_span_free,
    rt_i18n_context_new,
    rt_i18n_context_free,
    rt_i18n_context_insert,
    rt_i18n_get_message,
    rt_i18n_severity_name,
    // Mock policy
    __mock_policy_init_all,
    __mock_policy_init_hal_only,
    __mock_policy_init_patterns,
    __mock_policy_check,
    __mock_policy_try_check,
    __mock_policy_disable,
    __mock_policy_get_mode,
    // Vulkan stubs
    rt_vk_available,
    rt_vk_device_create,
    rt_vk_device_free,
    rt_vk_device_sync,
    rt_vk_buffer_alloc,
    rt_vk_buffer_free,
    rt_vk_buffer_upload,
    rt_vk_buffer_download,
    rt_vk_kernel_compile,
    rt_vk_kernel_free,
    rt_vk_kernel_launch,
    rt_vk_kernel_launch_1d
);

// Keep the real one-argument Vulkan ABI in the aggregate archive.
#[cfg(feature = "vulkan")]
#[used]
static RT_VK_DEVICE_CREATE_FOR_WINDOW_PROVIDER: extern "C" fn(u64) -> u64 =
    simple_runtime::value::rt_vk_device_create_for_window;

#[cfg(not(feature = "vulkan"))]
#[no_mangle]
pub extern "C" fn rt_vk_device_create_for_window(_window_handle: u64) -> u64 {
    0
}

// ============================================================================
// Test runner SFFI — allows self-hosted binaries to run tests via the Rust
// test runner from simple-driver. Kept behind `driver-compat` so minimal
// native lanes do not inherit the driver dependency closure.
// ============================================================================

/// Run the full test suite.  Called from Simple code as:
///   extern fn rt_run_tests(args: [text], gc_log: i64, gc_off: i64) -> i64
#[cfg(feature = "driver-compat")]
#[no_mangle]
pub extern "C" fn rt_run_tests(args: RuntimeValue, gc_log: i64, gc_off: i64) -> i64 {
    let args_vec = extract_rt_string_array(args);
    let mut options = simple_driver::cli::test_runner::parse_test_args(&args_vec);
    options.gc_log = gc_log != 0;
    options.gc_off = gc_off != 0;

    if options.watch {
        match simple_driver::cli::test_runner::watch_tests(options) {
            Ok(()) => 0,
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        }
    } else {
        let format = options.format;
        let is_mgmt = options.list_runs || options.cleanup_runs || options.prune_runs.is_some();
        println!("Simple Test Runner v0.9.5");
        println!();
        let result = simple_driver::cli::test_runner::run_tests(options);
        if !is_mgmt {
            simple_driver::cli::test_output::print_summary(&result, format);
        }
        if result.success() {
            0
        } else {
            1
        }
    }
}

// ============================================================================
// CLI `run` SFFI — executes a single .spl source file in-process via the Rust
// seed's interpreter. Replaces the runtime-side stub (gated out by the
// `driver-hooks` feature on simple-runtime) so the self-hosted binary can
// service `simple run <file>` without recursing through a subprocess. Kept
// behind `driver-compat` so the minimal native lane keeps the runtime stub.
// ============================================================================

/// Run a Simple source file in-process.
///
/// Simple-side declaration:
///   extern fn rt_cli_run_file(path: text, args: [text], gc_log: bool, gc_off: bool) -> i64
#[cfg(feature = "driver-compat")]
#[no_mangle]
pub extern "C" fn rt_cli_run_file(path: RuntimeValue, args: RuntimeValue, gc_log: u8, gc_off: u8) -> i64 {
    let path_str = match extract_rt_string(path) {
        Some(s) => s,
        None => {
            eprintln!("error: rt_cli_run_file: invalid path argument");
            return 1;
        }
    };
    let args_vec = extract_rt_string_array(args);
    let path = std::path::Path::new(&path_str);
    simple_driver::cli::basic::run_file_with_args(path, gc_log != 0, gc_off != 0, args_vec) as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_build_entry_infers_single_bare_spl() {
        let entry = resolve_native_build_entry(None, &[PathBuf::from("probe.spl")]).unwrap();
        assert_eq!(entry, Some(PathBuf::from("probe.spl")));
    }

    #[test]
    fn native_build_explicit_entry_wins_over_bare_spl() {
        let entry =
            resolve_native_build_entry(Some(PathBuf::from("main.spl")), &[PathBuf::from("ignored.spl")]).unwrap();
        assert_eq!(entry, Some(PathBuf::from("main.spl")));
    }

    #[test]
    fn native_build_entry_rejects_multiple_bare_spl_inputs() {
        let error = resolve_native_build_entry(None, &[PathBuf::from("a.spl"), PathBuf::from("b.spl")]).unwrap_err();
        assert!(error.contains("use --entry"));
    }

    fn array_values(raw_array: i64) -> Vec<RuntimeValue> {
        let array = to_rv(raw_array);
        let len = rt_array_len(array);
        (0..len).map(|idx| rt_array_get(array, idx)).collect()
    }

    #[test]
    fn native_build_process_args_require_command_marker() {
        assert!(!native_build_process_args_usable(&[]));
        assert!(!native_build_process_args_usable(&["simple".to_string()]));
        assert!(native_build_process_args_usable(&[
            "simple".to_string(),
            "native-build".to_string(),
            "--entry-closure".to_string(),
        ]));
    }

    #[test]
    fn native_build_bootstrap_mode_includes_stage4() {
        assert!(!native_build_bootstrap_mode(false, false));
        assert!(native_build_bootstrap_mode(true, false));
        assert!(native_build_bootstrap_mode(false, true));
    }

    #[cfg(unix)]
    #[test]
    fn execute_native_process_drains_saturated_stdout_and_stderr() {
        let script =
            "i=0; while [ \"$i\" -lt 4096 ]; do printf '0123456789abcdef'; printf 'fedcba9876543210' >&2; i=$((i + 1)); done";
        let args = vec!["-c".to_string(), script.to_string()];

        let (stdout, stderr, exit_code) = execute_native_process("/bin/sh", &args, std::time::Duration::from_secs(5));

        assert_eq!(exit_code, 0);
        assert_eq!(stdout.len(), 65_536);
        assert_eq!(stderr.len(), 65_536);
        assert!(stdout.starts_with("0123456789abcdef"));
        assert!(stderr.starts_with("fedcba9876543210"));
    }

    #[cfg(unix)]
    #[test]
    fn execute_native_process_kills_and_waits_on_timeout() {
        let args = vec!["-c".to_string(), "sleep 2".to_string()];

        let (stdout, stderr, exit_code) =
            execute_native_process("/bin/sh", &args, std::time::Duration::from_millis(20));

        assert_eq!(
            (stdout.as_str(), stderr.as_str(), exit_code),
            ("", "Execution timed out", 124)
        );
    }

    #[test]
    fn native_hashmap_shim_round_trips_scalar_and_collection_values() {
        let handle = __rt_hashmap_new();
        let key = stub_make_string("answer");
        let value = from_rv(RuntimeValue::from_int(42));

        assert_eq!(__rt_hashmap_insert(handle, key, value), 1);
        assert_eq!(__rt_hashmap_get(handle, key), 42);
        assert_eq!(__rt_hashmap_contains_key(handle, key), 1);
        assert_eq!(__rt_hashmap_len(handle), 1);

        let values = array_values(__rt_hashmap_values(handle));
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].as_int(), 42);

        let entries = array_values(__rt_hashmap_entries(handle));
        assert_eq!(entries.len(), 1);
        let pair = array_values(from_rv(entries[0]));
        assert_eq!(extract_rt_string(pair[0]).as_deref(), Some("answer"));
        assert_eq!(pair[1].as_int(), 42);
    }

    #[test]
    fn native_btreemap_shim_keeps_keys_ordered_and_string_values_raw() {
        let handle = __rt_btreemap_new();
        let beta = stub_make_string("beta");
        let alpha = stub_make_string("alpha");
        let text_value = stub_make_string("value");

        assert_eq!(
            __rt_btreemap_insert(handle, beta, from_rv(RuntimeValue::from_int(2))),
            1
        );
        assert_eq!(__rt_btreemap_insert(handle, alpha, text_value), 1);
        assert_eq!(
            extract_rt_string(to_rv(__rt_btreemap_get(handle, alpha))).as_deref(),
            Some("value")
        );
        assert_eq!(
            extract_rt_string(to_rv(__rt_btreemap_first_key(handle))).as_deref(),
            Some("alpha")
        );
        assert_eq!(
            extract_rt_string(to_rv(__rt_btreemap_last_key(handle))).as_deref(),
            Some("beta")
        );

        let keys: Vec<String> = array_values(__rt_btreemap_keys(handle))
            .into_iter()
            .filter_map(extract_rt_string)
            .collect();
        assert_eq!(keys, vec!["alpha".to_string(), "beta".to_string()]);
    }
}
