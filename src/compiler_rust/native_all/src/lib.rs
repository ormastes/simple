// Combined static library for native Simple binaries.
//
// This crate produces a single `libsimple_native_all.a` that includes
// ALL transitive dependencies from both `simple-compiler` (Cranelift FFI,
// codegen, parser) and `simple-runtime` (GC, FFI wrappers, actors).
//
// When linked into a native binary produced by `native-build`, the binary
// gains access to `rt_cranelift_*` functions, enabling self-hosted
// compilation (Stage 3 bootstrap).

// Re-export both crates so their #[no_mangle] extern "C" functions
// are included in the static library.
pub use simple_compiler;
pub use simple_runtime;

use std::path::PathBuf;

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_runtime::value::{
    rt_array_get, rt_array_len, rt_string_data, rt_string_len,
    RuntimeValue,
};

// Helper: extract a Rust String from a Simple runtime string value.
fn extract_rt_string(val: RuntimeValue) -> Option<String> {
    let len = rt_string_len(val);
    if len < 0 {
        return None;
    }
    let data = rt_string_data(val);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

// Helper: extract array of strings from a Simple runtime array value.
fn extract_rt_string_array(arr: RuntimeValue) -> Vec<String> {
    let len = rt_array_len(arr);
    let mut result = Vec::new();
    for i in 0..len {
        let val = rt_array_get(arr, i);
        if let Some(s) = extract_rt_string(val) {
            result.push(s);
        }
    }
    result
}

/// FFI entry point for native-build command.
///
/// Args is a Simple runtime array of strings:
///   ["native-build", "--source", "src/compiler", "--source", "src/app", ...]
///
/// Returns exit code (0 = success).
#[no_mangle]
pub extern "C" fn rt_native_build(args: RuntimeValue) -> i64 {
    let args_vec = extract_rt_string_array(args);

    let mut source_dirs: Vec<PathBuf> = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut entry_file: Option<PathBuf> = None;
    let mut verbose = false;
    let mut strip = false;
    let mut threads: Option<usize> = None;
    let mut timeout: u64 = 60;
    let mut incremental = true;
    let mut clean = false;
    let mut cache_dir: Option<PathBuf> = None;
    let mut no_mangle = false;

    // Parse arguments (skip "native-build" at index 0)
    let mut i = 1;
    while i < args_vec.len() {
        match args_vec[i].as_str() {
            "--help" | "-h" => {
                println!("Simple Native Build - Compile Simple project to native binary");
                println!();
                println!("Usage: simple native-build [options] [source-dirs...]");
                println!();
                println!("Options:");
                println!("  --source <dir>      Source directory to compile (repeatable)");
                println!("  -o <path>           Output binary path (default: bin/simple_stage3)");
                println!("  --entry <file>      Entry file (default: src/app/cli/main.spl)");
                println!("  --verbose, -v       Verbose output");
                println!("  --strip             Strip symbols from output");
                println!("  --threads <n>       Number of compilation threads");
                println!("  --timeout <secs>    Per-file timeout (default: 60)");
                println!("  --no-incremental    Disable incremental compilation");
                println!("  --clean             Force clean rebuild");
                println!("  --cache-dir <dir>   Cache directory");
                println!("  --no-mangle         Disable name mangling");
                return 0;
            }
            "--source" => {
                if i + 1 < args_vec.len() {
                    source_dirs.push(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --source requires a directory path");
                    return 1;
                }
            }
            "-o" | "--output" => {
                if i + 1 < args_vec.len() {
                    output = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: -o requires an output path");
                    return 1;
                }
            }
            "--entry" => {
                if i + 1 < args_vec.len() {
                    entry_file = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --entry requires a file path");
                    return 1;
                }
            }
            "--verbose" | "-v" => {
                verbose = true;
                i += 1;
            }
            "--strip" => {
                strip = true;
                i += 1;
            }
            "--threads" => {
                if i + 1 < args_vec.len() {
                    match args_vec[i + 1].parse() {
                        Ok(n) => threads = Some(n),
                        Err(_) => {
                            eprintln!("error: --threads requires a number");
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --threads requires a number");
                    return 1;
                }
            }
            "--timeout" => {
                if i + 1 < args_vec.len() {
                    match args_vec[i + 1].parse() {
                        Ok(t) => timeout = t,
                        Err(_) => {
                            eprintln!("error: --timeout requires a number");
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --timeout requires a number");
                    return 1;
                }
            }
            "--no-incremental" => {
                incremental = false;
                i += 1;
            }
            "--clean" => {
                clean = true;
                i += 1;
            }
            "--cache-dir" => {
                if i + 1 < args_vec.len() {
                    cache_dir = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --cache-dir requires a directory path");
                    return 1;
                }
            }
            "--no-mangle" => {
                no_mangle = true;
                i += 1;
            }
            other => {
                source_dirs.push(PathBuf::from(other));
                i += 1;
            }
        }
    }

    // Defaults
    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if source_dirs.is_empty() {
        source_dirs.push(project_root.join("src/compiler"));
        source_dirs.push(project_root.join("src/app"));
        source_dirs.push(project_root.join("src/lib"));
    }
    let output = output.unwrap_or_else(|| project_root.join("bin/simple_stage3"));

    let entry_file = entry_file.or_else(|| {
        let default_entry = project_root.join("src/app/cli/main.spl");
        if default_entry.exists() {
            Some(default_entry)
        } else {
            None
        }
    });

    // Ensure output directory exists
    if let Some(parent) = output.parent() {
        if !parent.exists() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                eprintln!("error: cannot create output directory: {}", e);
                return 1;
            }
        }
    }

    if verbose {
        eprintln!("Simple Native Build (self-hosted)");
        eprintln!("  Source dirs: {:?}", source_dirs);
        eprintln!("  Output: {}", output.display());
        eprintln!(
            "  Entry: {}",
            entry_file
                .as_ref()
                .map_or("(none)".to_string(), |p| p.display().to_string())
        );
        eprintln!(
            "  Threads: {}",
            threads.map_or("auto".to_string(), |n| n.to_string())
        );
        eprintln!("  Timeout: {}s", timeout);
        eprintln!("  Incremental: {}", incremental);
        eprintln!("  Mangle: {}", !no_mangle);
    }

    let mut config = NativeBuildConfig::default();
    config.file_timeout = timeout;
    config.verbose = verbose;
    config.strip = strip;
    config.num_threads = threads;
    config.incremental = incremental;
    config.clean = clean;
    config.cache_dir = cache_dir;
    config.no_mangle = no_mangle;

    let mut builder = NativeProjectBuilder::new(project_root, output).config(config);
    if let Some(entry) = entry_file {
        builder = builder.entry_file(entry);
    }
    for dir in source_dirs {
        builder = builder.source_dir(dir);
    }

    match builder.build() {
        Ok(result) => {
            println!(
                "Build complete: {} compiled, {} cached, {} failed",
                result.compiled, result.cached, result.failed
            );
            println!(
                "  Binary: {} ({} KB)",
                result.output.display(),
                result.binary_size / 1024
            );
            println!(
                "  Time: {:.1}s compile + {:.1}s link = {:.1}s total",
                result.compile_time.as_secs_f64(),
                result.link_time.as_secs_f64(),
                (result.compile_time + result.link_time).as_secs_f64()
            );

            if !result.failures.is_empty() && verbose {
                eprintln!("\nFailed files:");
                for (path, msg) in &result.failures {
                    eprintln!("  {}: {}", path.display(), msg);
                }
            }

            if result.failed > 0 {
                eprintln!("\nWarning: {} files failed to compile", result.failed);
            }

            0
        }
        Err(e) => {
            eprintln!("Build failed: {}", e);
            1
        }
    }
}

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

use simple_runtime::value::{
    rt_string_new,
    rt_array_new as rt_array_new_impl, rt_array_push as rt_array_push_impl,
};

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
    if len < 0 { return None; }
    let data = rt_string_data(to_rv(val));
    if data.is_null() { return None; }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

/// Helper: create a RuntimeValue string from a Rust string.
fn stub_make_string(s: &str) -> i64 {
    from_rv(rt_string_new(s.as_ptr(), s.len() as u64))
}

// -- File I/O stubs --

#[no_mangle]
pub extern "C" fn rt_file_size(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        std::fs::metadata(&p).map(|m| m.len() as i64).unwrap_or(0)
    } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_file_delete(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::remove_file(&p).is_ok() { 1 } else { 0 }
    } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_file_lock(_path: i64) -> i64 { 1 } // no-op success

#[no_mangle]
pub extern "C" fn rt_file_unlock(_path: i64) -> i64 { 1 } // no-op success

#[no_mangle]
pub extern "C" fn rt_file_hash_sha256(path: i64) -> i64 {
    // Simple hash using DefaultHasher (same as interpreter implementation)
    if let Some(p) = stub_extract_path(path) {
        if let Ok(content) = std::fs::read(&p) {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut hasher = DefaultHasher::new();
            content.hash(&mut hasher);
            let hash = hasher.finish();
            let hex = format!("{:016x}", hash);
            stub_make_string(&hex)
        } else { stub_make_string("") }
    } else { stub_make_string("") }
}

#[no_mangle]
pub extern "C" fn rt_file_atomic_write(path: i64, content: i64) -> i64 {
    // Fall back to normal write
    if let (Some(p), Some(c)) = (stub_extract_path(path), stub_extract_path(content)) {
        if std::fs::write(&p, &c).is_ok() { 1 } else { 0 }
    } else { 0 }
}

// -- Process/System stubs --

#[no_mangle]
pub extern "C" fn rt_getpid() -> i64 {
    std::process::id() as i64
}

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

#[no_mangle]
pub extern "C" fn rt_process_exists(pid: i64) -> i64 {
    // Check if /proc/<pid> exists on Linux
    let path = format!("/proc/{}", pid);
    if std::path::Path::new(&path).exists() { 1 } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_current_time_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_time_now_monotonic_ms() -> i64 {
    // Use Instant isn't available for extern "C", use SystemTime
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

// -- Builtins --

#[no_mangle]
pub extern "C" fn sys_get_args() -> i64 {
    // Return runtime array of CLI args
    let arr = rt_array_new_impl(16);
    for arg in std::env::args() {
        let s = stub_make_string(&arg);
        rt_array_push_impl(arr, to_rv(s));
    }
    from_rv(arr)
}

#[no_mangle]
pub extern "C" fn sys_exit(code: i64) -> i64 {
    std::process::exit(code as i32);
}

#[no_mangle]
pub extern "C" fn exit(code: i64) -> i64 {
    std::process::exit(code as i32);
}

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

// -- I/O builtins --

#[no_mangle]
pub extern "C" fn print(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        print!("{}", s);
    } else {
        print!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn println(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        println!("{}", s);
    } else {
        println!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn eprint(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        eprint!("{}", s);
    } else {
        eprint!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn eprintln(val: i64) -> i64 {
    if let Some(s) = stub_extract_path(val) {
        eprintln!("{}", s);
    } else {
        eprintln!("{}", val);
    }
    0
}

#[no_mangle]
pub extern "C" fn print_raw(val: i64) -> i64 { print(val) }

#[no_mangle]
pub extern "C" fn eprint_raw(val: i64) -> i64 { eprint(val) }

#[no_mangle]
pub extern "C" fn dbg(val: i64) -> i64 {
    eprintln!("[dbg] {}", val);
    val
}

#[no_mangle]
pub extern "C" fn dprint(val: i64) -> i64 { dbg(val) }

#[no_mangle]
pub extern "C" fn input(_prompt: i64) -> i64 {
    let mut buf = String::new();
    let _ = std::io::stdin().read_line(&mut buf);
    stub_make_string(buf.trim_end())
}

#[no_mangle]
pub extern "C" fn panic(msg: i64) -> i64 {
    if let Some(s) = stub_extract_path(msg) {
        eprintln!("panic: {}", s);
    } else {
        eprintln!("panic: {}", msg);
    }
    std::process::exit(1);
}

// -- Math builtins --

#[no_mangle] pub extern "C" fn abs(val: i64) -> i64 { val.abs() }
#[no_mangle] pub extern "C" fn min(a: i64, b: i64) -> i64 { std::cmp::min(a, b) }
#[no_mangle] pub extern "C" fn max(a: i64, b: i64) -> i64 { std::cmp::max(a, b) }
#[no_mangle] pub extern "C" fn pow(base: i64, exp: i64) -> i64 { (base as f64).powi(exp as i32) as i64 }
#[no_mangle] pub extern "C" fn sqrt(val: i64) -> i64 { (val as f64).sqrt() as i64 }
#[no_mangle] pub extern "C" fn ceil(val: i64) -> i64 { val } // integers are already ceil
#[no_mangle] pub extern "C" fn floor(val: i64) -> i64 { val }
#[no_mangle] pub extern "C" fn to_int(val: i64) -> i64 { val }

#[no_mangle]
pub extern "C" fn to_string(val: i64) -> i64 {
    // Check if it's a string already
    if rt_string_len(to_rv(val)) >= 0 {
        val
    } else {
        stub_make_string(&val.to_string())
    }
}

// -- Compiler backend stubs --

#[no_mangle] pub extern "C" fn rt_compile_to_llvm_ir(_source: i64) -> i64 { stub_make_string("") }
#[no_mangle] pub extern "C" fn rt_compile_to_native(_source: i64, _output: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn rt_execute_native(_path: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn rt_cargo_fmt() -> i64 { 0 }
#[no_mangle] pub extern "C" fn rt_cargo_lint() -> i64 { 0 }
#[no_mangle] pub extern "C" fn rt_cargo_test_doc() -> i64 { 0 }

// -- Concurrency stubs --

#[no_mangle] pub extern "C" fn rt_get_concurrent_backend() -> i64 { 0 }
#[no_mangle] pub extern "C" fn rt_set_concurrent_backend(_backend: i64) -> i64 { 0 }

// -- Stdio stubs --

#[no_mangle] pub extern "C" fn stdout_write(data: i64) -> i64 {
    use std::io::Write;
    if let Some(s) = stub_extract_path(data) {
        let _ = std::io::stdout().write_all(s.as_bytes());
    }
    0
}

#[no_mangle] pub extern "C" fn stdout_flush() -> i64 {
    use std::io::Write;
    let _ = std::io::stdout().flush();
    0
}

#[no_mangle] pub extern "C" fn stderr_write(data: i64) -> i64 {
    use std::io::Write;
    if let Some(s) = stub_extract_path(data) {
        let _ = std::io::stderr().write_all(s.as_bytes());
    }
    0
}

#[no_mangle] pub extern "C" fn stderr_flush() -> i64 {
    use std::io::Write;
    let _ = std::io::stderr().flush();
    0
}

#[no_mangle] pub extern "C" fn stdin_read_char() -> i64 {
    use std::io::Read;
    let mut buf = [0u8; 1];
    let _ = std::io::stdin().read(&mut buf);
    buf[0] as i64
}

// -- Memory stubs --

#[no_mangle] pub extern "C" fn memory_usage() -> i64 { 0 }
#[no_mangle] pub extern "C" fn memory_limit() -> i64 { 0 }
#[no_mangle] pub extern "C" fn default_memory_limit() -> i64 { 0 }
#[no_mangle] pub extern "C" fn is_memory_limited() -> i64 { 0 }
#[no_mangle] pub extern "C" fn parse_memory_size(_s: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn format_bytes(n: i64) -> i64 { stub_make_string(&format!("{} B", n)) }

// -- Time stubs --

#[no_mangle]
pub extern "C" fn _current_time_unix() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// -- Native terminal stubs (no-op) --

#[no_mangle] pub extern "C" fn native_enable_raw_mode() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_disable_raw_mode() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_get_term_size() -> i64 { 80 } // default 80 cols
#[no_mangle] pub extern "C" fn native_is_tty() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_stdout() -> i64 { 1 }
#[no_mangle] pub extern "C" fn native_stderr() -> i64 { 2 }
#[no_mangle] pub extern "C" fn native_stdin() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_term_flush() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_term_poll() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_term_read() -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_term_read_timeout(_ms: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_term_write(_data: i64) -> i64 { 0 }

// -- Native FS stubs (delegate to rt_file_* where possible) --

#[no_mangle] pub extern "C" fn native_fs_exists(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::path::Path::new(&p).exists() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_read_string(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if let Ok(content) = std::fs::read_to_string(&p) {
            stub_make_string(&content)
        } else { stub_make_string("") }
    } else { stub_make_string("") }
}
#[no_mangle] pub extern "C" fn native_fs_write_string(path: i64, content: i64) -> i64 {
    if let (Some(p), Some(c)) = (stub_extract_path(path), stub_extract_path(content)) {
        if std::fs::write(&p, &c).is_ok() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_read(path: i64) -> i64 { native_fs_read_string(path) }
#[no_mangle] pub extern "C" fn native_fs_write(path: i64, content: i64) -> i64 { native_fs_write_string(path, content) }
#[no_mangle] pub extern "C" fn native_fs_append(path: i64, content: i64) -> i64 {
    use std::io::Write;
    if let (Some(p), Some(c)) = (stub_extract_path(path), stub_extract_path(content)) {
        if let Ok(mut f) = std::fs::OpenOptions::new().append(true).create(true).open(&p) {
            if f.write_all(c.as_bytes()).is_ok() { return 1; }
        }
    }
    0
}
#[no_mangle] pub extern "C" fn native_fs_copy(src: i64, dst: i64) -> i64 {
    if let (Some(s), Some(d)) = (stub_extract_path(src), stub_extract_path(dst)) {
        if std::fs::copy(&s, &d).is_ok() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_rename(src: i64, dst: i64) -> i64 {
    if let (Some(s), Some(d)) = (stub_extract_path(src), stub_extract_path(dst)) {
        if std::fs::rename(&s, &d).is_ok() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_remove_file(path: i64) -> i64 { rt_file_delete(path) }
#[no_mangle] pub extern "C" fn native_fs_remove_dir(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::remove_dir_all(&p).is_ok() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_create_dir(path: i64) -> i64 {
    if let Some(p) = stub_extract_path(path) {
        if std::fs::create_dir_all(&p).is_ok() { 1 } else { 0 }
    } else { 0 }
}
#[no_mangle] pub extern "C" fn native_fs_metadata(_path: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn native_fs_read_dir(_path: i64) -> i64 {
    from_rv(rt_array_new_impl(0))
}

// -- Misc stubs (return 0/nil) --

#[no_mangle] pub extern "C" fn lexer_tokenize(_source: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn simple_layout_mark(_name: i64) -> i64 { 0 }
#[no_mangle] pub extern "C" fn bytes_to_string(data: i64) -> i64 { data }

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
    arc_box_init, arc_box_get_value, arc_box_inc_strong, arc_box_dec_strong,
    arc_box_inc_weak, arc_box_dec_weak, arc_box_drop_value, arc_box_size,
    arc_box_strong_count, arc_box_weak_count,
    rc_box_init, rc_box_get_value, rc_box_inc_strong, rc_box_dec_strong,
    rc_box_inc_weak, rc_box_dec_weak, rc_box_drop_value, rc_box_size,
    rc_box_strong_count, rc_box_weak_count,

    // BTreeMap/BTreeSet (prefixed with __ in interpreter)
    __rt_btreemap_new, __rt_btreemap_insert, __rt_btreemap_get,
    __rt_btreemap_remove, __rt_btreemap_len, __rt_btreemap_clear,
    __rt_btreemap_contains_key, __rt_btreemap_keys, __rt_btreemap_values,
    __rt_btreemap_entries, __rt_btreemap_first_key, __rt_btreemap_last_key,
    __rt_btreeset_new, __rt_btreeset_insert, __rt_btreeset_remove,
    __rt_btreeset_contains, __rt_btreeset_len, __rt_btreeset_clear,
    __rt_btreeset_first, __rt_btreeset_last, __rt_btreeset_to_array,
    __rt_btreeset_union, __rt_btreeset_intersection, __rt_btreeset_difference,
    __rt_btreeset_symmetric_difference, __rt_btreeset_is_subset, __rt_btreeset_is_superset,

    // HashMap/HashSet (prefixed with __ in interpreter)
    __rt_hashmap_new, __rt_hashmap_insert, __rt_hashmap_get,
    __rt_hashmap_remove, __rt_hashmap_len, __rt_hashmap_clear,
    __rt_hashmap_contains_key, __rt_hashmap_keys, __rt_hashmap_values,
    __rt_hashmap_entries,
    __rt_hashset_new, __rt_hashset_insert, __rt_hashset_remove,
    __rt_hashset_contains, __rt_hashset_len, __rt_hashset_clear,
    __rt_hashset_to_array, __rt_hashset_union, __rt_hashset_intersection,
    __rt_hashset_difference, __rt_hashset_symmetric_difference,
    __rt_hashset_is_subset, __rt_hashset_is_superset,

    // Error handling
    rt_error_throw, rt_error_message, rt_error_free,
    rt_error_division_by_zero, rt_error_index_oob,
    rt_error_type_mismatch, rt_error_undefined_var,
    rt_error_arg_count, rt_error_semantic,

    // Environment (interpreter-internal)
    rt_env_new_handle, rt_env_free_handle, rt_env_push_scope,
    rt_env_pop_scope, rt_env_define_var, rt_env_set_var,
    rt_env_get_var, rt_env_has_var, rt_env_scope_depth,
    rt_env_snapshot, rt_env_var_count, rt_env_var_names,

    // AST manipulation (interpreter-only)
    rt_ast_registry_clear, rt_ast_registry_count,
    rt_ast_expr_tag, rt_ast_expr_free, rt_ast_expr_int_value,
    rt_ast_expr_float_value, rt_ast_expr_bool_value,
    rt_ast_expr_string_value, rt_ast_expr_ident_name,
    rt_ast_expr_binary_left, rt_ast_expr_binary_right,
    rt_ast_expr_binary_op, rt_ast_expr_unary_op,
    rt_ast_expr_unary_operand, rt_ast_expr_call_callee,
    rt_ast_expr_call_arg_count, rt_ast_expr_call_arg,
    rt_ast_expr_method_receiver, rt_ast_expr_method_name,
    rt_ast_expr_method_arg_count, rt_ast_expr_method_arg,
    rt_ast_expr_field_receiver, rt_ast_expr_field_name,
    rt_ast_expr_array_len, rt_ast_expr_array_get,
    rt_ast_arg_name, rt_ast_arg_value, rt_ast_arg_free,
    rt_ast_node_free,

    // Span/I18N
    rt_span_create, rt_span_start, rt_span_end,
    rt_span_line, rt_span_column, rt_span_free,
    rt_i18n_context_new, rt_i18n_context_free,
    rt_i18n_context_insert, rt_i18n_get_message,
    rt_i18n_severity_name,

    // Mock policy
    __mock_policy_init_all, __mock_policy_init_hal_only,
    __mock_policy_init_patterns, __mock_policy_check,
    __mock_policy_try_check, __mock_policy_disable,
    __mock_policy_get_mode,

    // Vulkan stubs
    rt_vk_available, rt_vk_device_create, rt_vk_device_free,
    rt_vk_device_sync, rt_vk_buffer_alloc, rt_vk_buffer_free,
    rt_vk_buffer_upload, rt_vk_buffer_download,
    rt_vk_kernel_compile, rt_vk_kernel_free,
    rt_vk_kernel_launch, rt_vk_kernel_launch_1d
);
