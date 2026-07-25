//! CLI SFFI functions for Simple programs
//!
//! These functions provide basic CLI functionality that Simple programs can call.
//! They are part of the runtime library so they can be linked into native binaries.

use super::{rt_array_get, rt_array_len, rt_array_new, rt_array_push, rt_string_new, RuntimeValue};
use std::process::{Command, Stdio};

/// CLI version string from VERSION file (set by build.rs), falls back to Cargo.toml
const CLI_VERSION: &str = match option_env!("SIMPLE_VERSION") {
    Some(v) if !v.is_empty() => v,
    _ => env!("CARGO_PKG_VERSION"),
};

/// Get CLI version
#[no_mangle]
pub extern "C" fn rt_cli_version() -> RuntimeValue {
    let version = format!("Simple v{}", CLI_VERSION);
    rt_string_new(version.as_ptr(), version.len() as u64)
}

/// Print help message
#[no_mangle]
pub extern "C" fn rt_cli_print_help() {
    println!("Simple Language CLI");
    println!();
    println!("Usage: simple [OPTIONS] [COMMAND] [FILE]");
    println!();
    println!("Commands:");
    println!("  <file.spl>     Run a Simple source file");
    println!("  -c <code>      Execute code string");
    println!("  repl           Start interactive REPL");
    println!("  test           Run tests");
    println!("  lint           Run linter");
    println!("  fmt            Format code");
    println!("  check          Type check files");
    println!("  compile        Compile to native");
    println!("  watch          Watch file for changes");
    println!();
    println!("Options:");
    println!("  -h, --help     Show this help");
    println!("  -v, --version  Show version");
    println!("  --gc-log       Enable GC logging");
    println!("  --gc-off       Disable GC");
}

/// Print version
#[no_mangle]
pub extern "C" fn rt_cli_print_version() {
    println!("Simple v{}", CLI_VERSION);
}

/// Get command line arguments as a RuntimeValue array.
/// Delegates to rt_get_args() which uses the PROGRAM_ARGS mutex
/// (set at startup via rt_set_args). This is reliable on all platforms
/// including FreeBSD where std::env::args() may not work for native binaries.
#[no_mangle]
pub extern "C" fn rt_cli_get_args() -> RuntimeValue {
    super::rt_get_args()
}

/// Get the command-line argument count through a scalar-only ABI.
#[no_mangle]
pub extern "C" fn rt_cli_arg_count() -> i64 {
    super::args::cli_arg_count()
}

/// Get one command-line argument through a scalar-only ABI.
/// Invalid indices return allocated empty text, never nil.
#[no_mangle]
pub extern "C" fn rt_cli_arg_at(index: i64) -> RuntimeValue {
    let value = super::args::cli_arg_at(index);
    rt_string_new(value.as_ptr(), value.len() as u64)
}

/// Check if a file exists (cli version)
#[no_mangle]
pub extern "C" fn rt_cli_file_exists(path: RuntimeValue) -> u8 {
    if file_exists_impl(path) {
        1
    } else {
        0
    }
}

/// Helper: check if a file exists
fn file_exists_impl(path: RuntimeValue) -> bool {
    let len = super::rt_string_len(path);
    if len <= 0 {
        return false;
    }
    let data = super::rt_string_data(path);
    if data.is_null() {
        return false;
    }
    let path_str = unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        String::from_utf8_lossy(slice).to_string()
    };
    std::path::Path::new(&path_str).exists()
}

/// Check if a file exists (for Simple code - takes RuntimeValue string)
#[no_mangle]
pub extern "C" fn rt_file_exists_str(path: RuntimeValue) -> bool {
    file_exists_impl(path)
}

/// Read file contents as text (for Simple code - takes RuntimeValue string)
#[no_mangle]
pub extern "C" fn rt_read_file_str(path: RuntimeValue) -> RuntimeValue {
    read_file_impl(path)
}

/// Read file contents (CLI version)
#[no_mangle]
pub extern "C" fn rt_cli_read_file(path: RuntimeValue) -> RuntimeValue {
    read_file_impl(path)
}

/// Helper: read file contents
fn read_file_impl(path: RuntimeValue) -> RuntimeValue {
    let len = super::rt_string_len(path);
    if len <= 0 {
        return rt_string_new("".as_ptr(), 0);
    }
    let data = super::rt_string_data(path);
    if data.is_null() {
        return rt_string_new("".as_ptr(), 0);
    }
    let path_str = unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        String::from_utf8_lossy(slice).to_string()
    };
    match std::fs::read_to_string(&path_str) {
        Ok(content) => rt_string_new(content.as_ptr(), content.len() as u64),
        Err(_) => rt_string_new("".as_ptr(), 0),
    }
}

/// Exit with code
#[no_mangle]
pub extern "C" fn rt_cli_exit(code: i64) -> ! {
    std::process::exit(code as i32);
}

#[no_mangle]
pub extern "C" fn rt_cli_dispatch_rust(_cmd: RuntimeValue, _args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_compile_to_native(_source_path: RuntimeValue, _output_path: RuntimeValue) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_compile_to_native_with_opt(
    _source_path: RuntimeValue,
    _output_path: RuntimeValue,
    _opt_level: RuntimeValue,
) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_compile_to_llvm_ir(
    _source_file: RuntimeValue,
    _target_triple: RuntimeValue,
    _bare_metal: u8,
) -> i64 {
    0
}

// Stub implementations for complex CLI functions
// These require the full driver to implement properly

fn not_implemented(name: &str) -> i64 {
    eprintln!("error: {} is not available in standalone mode", name);
    eprintln!("hint: Run using the simple CLI for full functionality");
    1
}

/// Helper: extract string from RuntimeValue
fn extract_string(val: RuntimeValue) -> Option<String> {
    let len = super::rt_string_len(val);
    if len <= 0 {
        return None;
    }
    let data = super::rt_string_data(val);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

/// Helper: extract array of strings from RuntimeValue
fn extract_string_array(arr: RuntimeValue) -> Vec<String> {
    let len = rt_array_len(arr);
    let mut result = Vec::new();
    for i in 0..len {
        let val = rt_array_get(arr, i);
        if let Some(s) = extract_string(val) {
            result.push(s);
        }
    }
    result
}

/// Resolve the current Simple binary (this process) for subprocess calls.
fn simple_binary_path() -> std::path::PathBuf {
    if let Ok(path) = std::env::var("SIMPLE_BOOTSTRAP_DRIVER") {
        if !path.is_empty() {
            return std::path::PathBuf::from(path);
        }
    }

    let bootstrap = std::path::PathBuf::from("src/compiler_rust/target/bootstrap/simple");
    if bootstrap.is_file() {
        return bootstrap;
    }

    let release = std::path::PathBuf::from("src/compiler_rust/target/release/simple");
    if release.is_file() {
        return release;
    }

    let bin = std::path::PathBuf::from("bin/simple");
    if bin.is_file() {
        return bin;
    }

    std::env::current_exe().unwrap_or_else(|_| std::path::PathBuf::from("simple"))
}

const DELEGATE_DEPTH_ENV: &str = "SIMPLE_DELEGATE_DEPTH";
const MAX_DELEGATE_DEPTH: u32 = 3;

fn delegate_depth() -> u32 {
    std::env::var(DELEGATE_DEPTH_ENV)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(0)
}

/// True when `candidate` is this very executable (canonicalized comparison).
fn is_current_exe(candidate: &std::path::Path) -> bool {
    match (
        std::env::current_exe().and_then(|c| c.canonicalize()),
        candidate.canonicalize(),
    ) {
        (Ok(cur), Ok(cand)) => cur == cand,
        _ => false,
    }
}

/// Refuse a delegation that would spawn this same binary or exceed the
/// delegation-depth budget. simple_binary_path() falls back to current_exe(),
/// so a relocated/renamed binary (e.g. a simple.bak backup run where the
/// repo-relative driver candidates don't exist) resolves the delegate to
/// itself and forks without bound — 5814 runaway simple.bak processes
/// OOM-killed the whole user session (2026-06-12). The depth budget also
/// breaks A→B→A cycles that the path comparison can't see.
fn delegate_guard(simple_bin: &std::path::Path, context: &str) -> Option<u32> {
    if is_current_exe(simple_bin) {
        eprintln!(
            "error: refusing to delegate '{}' to this same binary ({}); \
             set SIMPLE_BOOTSTRAP_DRIVER to a real seed driver.",
            context,
            simple_bin.display()
        );
        return None;
    }
    let depth = delegate_depth();
    if depth >= MAX_DELEGATE_DEPTH {
        eprintln!(
            "error: delegation depth {} reached while running '{}' ({}); \
             aborting to avoid a spawn loop.",
            depth,
            context,
            simple_bin.display()
        );
        return None;
    }
    Some(depth + 1)
}

/// Delegate a CLI command to the Rust Simple binary (standalone mode).
fn delegate_to_simple_binary(command: &str, args: RuntimeValue) -> i64 {
    let simple_bin = simple_binary_path();
    let Some(next_depth) = delegate_guard(&simple_bin, command) else {
        return 1;
    };

    let mut cmd = Command::new(&simple_bin);
    cmd.env(DELEGATE_DEPTH_ENV, next_depth.to_string());
    cmd.arg(command);

    // Add arguments from the array (skip first element which is the command itself)
    let args_len = rt_array_len(args);
    for i in 1..args_len {
        let arg_val = rt_array_get(args, i);
        if let Some(arg_str) = extract_string(arg_val) {
            cmd.arg(arg_str);
        }
    }

    // Inherit stdin/stdout/stderr for interactive output
    cmd.stdin(Stdio::inherit());
    cmd.stdout(Stdio::inherit());
    cmd.stderr(Stdio::inherit());

    match cmd.status() {
        Ok(status) => status.code().unwrap_or(1) as i64,
        Err(e) => {
            eprintln!(
                "error: failed to execute simple binary ({}): {}",
                simple_bin.display(),
                e
            );
            1
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_cli_run_code(_code: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_code")
}

#[cfg(not(feature = "driver-hooks"))]
#[no_mangle]
pub extern "C" fn rt_cli_run_file(_path: RuntimeValue, _args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_file")
}

#[cfg(feature = "driver-hooks")]
pub fn rt_cli_run_file(path: RuntimeValue, args: RuntimeValue, gc_log: u8, gc_off: u8) -> i64 {
    type RunFileFn = unsafe extern "C" fn(RuntimeValue, RuntimeValue, u8, u8) -> i64;

    #[cfg(unix)]
    fn lookup_run_file() -> Option<RunFileFn> {
        use std::sync::OnceLock;

        static RUN_FILE: OnceLock<Option<RunFileFn>> = OnceLock::new();
        *RUN_FILE.get_or_init(|| unsafe {
            let lib = libloading::os::unix::Library::this();
            lib.get::<RunFileFn>(b"rt_cli_run_file").ok().map(|symbol| *symbol)
        })
    }

    #[cfg(windows)]
    fn lookup_run_file() -> Option<RunFileFn> {
        use std::sync::OnceLock;

        static RUN_FILE: OnceLock<Option<RunFileFn>> = OnceLock::new();
        *RUN_FILE.get_or_init(|| unsafe {
            let lib = libloading::os::windows::Library::this().ok()?;
            lib.get::<RunFileFn>(b"rt_cli_run_file").ok().map(|symbol| *symbol)
        })
    }

    let Some(run_file) = lookup_run_file() else {
        return not_implemented("rt_cli_run_file");
    };

    // SAFETY: the symbol is resolved from the current process image and is
    // expected to match the shared C ABI used by simple-native-all.
    unsafe { run_file(path, args, gc_log, gc_off) }
}

#[no_mangle]
pub extern "C" fn rt_cli_watch_file(_path: RuntimeValue) -> i64 {
    not_implemented("rt_cli_watch_file")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_repl(_gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_repl")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_tests(args: RuntimeValue, gc_log: u8, gc_off: u8) -> i64 {
    // Extract args array to Vec<String>
    let arg_strings = extract_string_array(args);
    run_tests_with_args(&arg_strings, gc_log, gc_off)
}

/// Stage4 scalar-only test bridge. Read argv from the runtime's owned string
/// storage, never through a container RuntimeValue from another heap. This
/// keeps the runtime archive self-contained while `rt_set_args` and the hosted
/// fallback both populate the same storage.
#[no_mangle]
pub extern "C" fn rt_cli_run_tests_process_args(gc_log: u8, gc_off: u8) -> i64 {
    let count = super::args::cli_arg_count().max(0);
    let process_args: Vec<String> = (0..count).map(super::args::cli_arg_at).collect();
    let arg_strings = test_args_from_process(&process_args);
    run_tests_with_args(&arg_strings, gc_log, gc_off)
}

fn cli_global_option_needs_value(arg: &str) -> bool {
    matches!(
        arg,
        "--backend"
            | "--execution-limit"
            | "--fixed-be"
            | "--interpreter-mode"
            | "--jit-threshold"
            | "--lang"
            | "--log-mode"
            | "--max-recursion-depth"
            | "--progress"
            | "--run-config"
            | "--surface"
            | "--timeout"
    )
}

fn test_args_from_process(process_args: &[String]) -> Vec<String> {
    let mut index = 1;
    while index < process_args.len() {
        let arg = &process_args[index];
        if arg == "test" {
            return process_args[index + 1..]
                .iter()
                .filter(|arg| !matches!(arg.as_str(), "--gc-log" | "--gc-off" | "--gc=off"))
                .cloned()
                .collect();
        }
        index += if cli_global_option_needs_value(arg) { 2 } else { 1 };
    }
    Vec::new()
}

fn run_tests_with_args(arg_strings: &[String], gc_log: u8, gc_off: u8) -> i64 {
    // Delegate to the Rust seed driver (same resolution as lint/check/fmt).
    // Spawning current_exe() here is wrong when this runtime is linked into
    // the self-hosted stage4 CLI: stage4's `test` dispatch calls back into
    // rt_cli_run_tests, so current_exe() would re-enter the same dispatch
    // forever — the SIMPLE_TEST_DEPTH guard then aborts the FIRST legitimate
    // run (stage4 10th-site (a), 2026-06-11).
    let simple_bin = simple_binary_path();
    if is_current_exe(&simple_bin) {
        eprintln!(
            "error: cannot run tests: the test runner would re-spawn this same binary ({}).\n  \
             Provide a Rust seed driver via SIMPLE_BOOTSTRAP_DRIVER or keep \
             src/compiler_rust/target/{{bootstrap,release}}/simple available.",
            simple_bin.display()
        );
        return 1;
    }
    let Some(next_depth) = delegate_guard(&simple_bin, "test") else {
        return 1;
    };

    let mut cmd = Command::new(&simple_bin);
    cmd.env(DELEGATE_DEPTH_ENV, next_depth.to_string());
    cmd.arg("test");

    // Add all arguments
    for arg in arg_strings {
        cmd.arg(arg);
    }

    // Add GC flags
    if gc_log != 0 {
        cmd.arg("--gc-log");
    }
    if gc_off != 0 {
        cmd.arg("--gc-off");
    }

    // Set environment variable to use Rust runner (avoid recursion)
    cmd.env("SIMPLE_TEST_RUNNER_RUST", "1");

    // Execute and return exit code
    match cmd.status() {
        Ok(status) => status.code().unwrap_or(1) as i64,
        Err(e) => {
            eprintln!("Failed to run tests: {}", e);
            1
        }
    }
}

#[cfg(test)]
mod test_process_arg_bridge_tests {
    use super::test_args_from_process;

    #[no_mangle]
    extern "C" fn spl_arg_count() -> i64 {
        0
    }

    #[no_mangle]
    extern "C" fn spl_get_arg(_index: i64) -> *const std::os::raw::c_char {
        std::ptr::null()
    }

    #[test]
    fn slices_only_arguments_after_the_test_command() {
        let process_args = ["simple", "test", "focused_spec.spl", "--gc-log", "--fail-fast"].map(String::from);
        assert_eq!(
            test_args_from_process(&process_args),
            ["focused_spec.spl", "--fail-fast"].map(String::from)
        );
    }

    #[test]
    fn returns_empty_without_a_test_command() {
        let process_args = ["simple", "--version"].map(String::from);
        assert!(test_args_from_process(&process_args).is_empty());
    }

    #[test]
    fn skips_a_global_option_value_named_test() {
        let process_args = ["simple", "--run-config", "test", "test", "focused_spec.spl"].map(String::from);
        assert_eq!(
            test_args_from_process(&process_args),
            ["focused_spec.spl"].map(String::from)
        );
    }
}

#[no_mangle]
pub extern "C" fn rt_cli_run_lint(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("lint", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_fmt(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("fmt", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_fix(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("lint", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_check(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("check", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_verify(args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    delegate_to_simple_binary("verify", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_migrate(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("migrate", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_mcp(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("mcp", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_diff(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("diff", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_context(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("context", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_constr(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("constr", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_query(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("query", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_info(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("info", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_coverage(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("spec-coverage", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_replay(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("replay", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_gen_lean(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("gen-lean", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_feature_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("feature-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_task_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("task-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("spec-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spipe_docgen(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("spipe-docgen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_scan(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("todo-scan", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("todo-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_i18n(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("i18n", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_lex(_args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("lex", _args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_brief(_args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("brief", _args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_sffi_gen(_args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("ffi-gen", _args)
}

#[no_mangle]
pub extern "C" fn rt_context_generate(
    _path: RuntimeValue,
    _target: RuntimeValue,
    _format: RuntimeValue,
) -> RuntimeValue {
    eprintln!("error: rt_context_generate is not available in standalone mode");
    rt_string_new("".as_ptr(), 0)
}

#[no_mangle]
pub extern "C" fn rt_context_stats(_path: RuntimeValue, _target: RuntimeValue) -> RuntimeValue {
    eprintln!("error: rt_context_stats is not available in standalone mode");
    rt_string_new("".as_ptr(), 0)
}

#[no_mangle]
pub extern "C" fn rt_settlement_main() -> i64 {
    crate::loader::startup::settlement_main() as i64
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_compile(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("compile", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_targets() -> i64 {
    // Create empty args array for delegate
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("targets".as_ptr(), 7));
    delegate_to_simple_binary("targets", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_linkers() -> i64 {
    // Create empty args array for delegate
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("linkers".as_ptr(), 7));
    delegate_to_simple_binary("linkers", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_web(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("web", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_diagram(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("diagram", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_init(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("init", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_add(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("add", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_remove(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("remove", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_install() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("install".as_ptr(), 7));
    delegate_to_simple_binary("install", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_update(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("update", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_list() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("list".as_ptr(), 4));
    delegate_to_simple_binary("list", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_tree() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("tree".as_ptr(), 4));
    delegate_to_simple_binary("tree", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_cache(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("cache", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_env(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("env", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_lock(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("lock", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_qualify_ignore(args: RuntimeValue) -> i64 {
    delegate_to_simple_binary("qualify-ignore", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_run(args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    delegate_to_simple_binary("run", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_build(args: RuntimeValue) -> i64 {
    // Load and execute the Simple build system
    // src/app/build/main.spl::main(args)
    use std::process::Command;

    let simple_runtime = std::env::current_exe().unwrap();
    let mut cmd = Command::new(&simple_runtime);
    cmd.arg("src/app/build/main.spl");

    // Add arguments from the array
    let args_len = rt_array_len(args);
    for i in 0..args_len {
        let arg_val = rt_array_get(args, i);
        if let Some(arg_str) = extract_string(arg_val) {
            cmd.arg(arg_str);
        }
    }

    // Inherit stdio for interactive output
    cmd.stdin(Stdio::inherit());
    cmd.stdout(Stdio::inherit());
    cmd.stderr(Stdio::inherit());

    match cmd.status() {
        Ok(status) => status.code().unwrap_or(1) as i64,
        Err(e) => {
            eprintln!("error: failed to execute build system: {}", e);
            1
        }
    }
}

// ============================================================================
// Self-Hosting Compiler SFFI Functions
// ============================================================================

/// Execute a shell command and return exit code.
/// Used for bootstrap compilation.
#[no_mangle]
pub extern "C" fn rt_exec(cmd: RuntimeValue) -> i32 {
    let cmd_str = match extract_string(cmd) {
        Some(s) => s,
        None => return -1,
    };

    match Command::new("sh")
        .arg("-c")
        .arg(&cmd_str)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
    {
        Ok(status) => status.code().unwrap_or(-1),
        Err(_) => -1,
    }
}

/// Execute a shell command and return captured stdout.
#[no_mangle]
pub extern "C" fn rt_exec_output(cmd: RuntimeValue) -> RuntimeValue {
    let cmd_str = match extract_string(cmd) {
        Some(s) => s,
        None => return rt_string_new("".as_ptr(), 0),
    };

    match Command::new("sh").arg("-c").arg(&cmd_str).output() {
        Ok(output) => rt_string_new(output.stdout.as_ptr(), output.stdout.len() as u64),
        Err(_) => rt_string_new("".as_ptr(), 0),
    }
}

/// Compute SHA256 hash of a file.
/// Used for bootstrap verification (v2 == v3).
#[no_mangle]
pub extern "C" fn rt_file_hash(path: RuntimeValue) -> RuntimeValue {
    use std::fs::File;
    use std::io::Read;
    use sha2::{Sha256, Digest};

    let path_str = match extract_string(path) {
        Some(s) => s,
        None => return rt_string_new("".as_ptr(), 0),
    };

    let mut file = match File::open(&path_str) {
        Ok(f) => f,
        Err(_) => return rt_string_new("".as_ptr(), 0),
    };

    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];

    loop {
        match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(n) => hasher.update(&buffer[..n]),
            Err(_) => return rt_string_new("".as_ptr(), 0),
        }
    }

    let result = hasher.finalize();
    let hex = format!("{:x}", result);
    rt_string_new(hex.as_ptr(), hex.len() as u64)
}

/// Write file contents (wrapper for consistency).
#[no_mangle]
pub extern "C" fn rt_write_file(path: RuntimeValue, content: RuntimeValue) -> bool {
    let path_str = match extract_string(path) {
        Some(s) => s,
        None => return false,
    };

    let content_str = match extract_string(content) {
        Some(s) => s,
        None => return false,
    };

    std::fs::write(&path_str, &content_str).is_ok()
}

// =========================================================================
// Fault Detection Configuration SFFI (C ABI for compiled mode)
// =========================================================================

/// Set stack overflow detection enabled/disabled
#[no_mangle]
pub extern "C" fn rt_fault_set_stack_overflow_detection(enabled: u8) {
    simple_common::fault_detection::set_stack_overflow_detection_enabled(enabled != 0);
}

/// Set max recursion depth
#[no_mangle]
pub extern "C" fn rt_fault_set_max_recursion_depth(depth: i64) {
    simple_common::fault_detection::set_max_recursion_depth(depth as u64);
}

/// Set execution timeout in seconds (0 = disable)
#[no_mangle]
pub extern "C" fn rt_fault_set_timeout(secs: i64) {
    // Timeout requires a watchdog thread which is in the compiler crate.
    // In compiled mode, set the env var so the driver can pick it up on next init.
    std::env::set_var("SIMPLE_TIMEOUT_SECONDS", secs.to_string());
}

/// Set execution limit (0 = disable)
#[no_mangle]
pub extern "C" fn rt_fault_set_execution_limit(limit: i64) {
    std::env::set_var("SIMPLE_EXECUTION_LIMIT", limit.to_string());
}

// =========================================================================
// Test Database Integrity Validation SFFI
// =========================================================================

/// Validate test database and return number of violations found
/// Returns -1 on error, >= 0 for violation count
#[no_mangle]
pub extern "C" fn rt_test_db_validate(db_path: RuntimeValue) -> i64 {
    let path_str = match extract_string(db_path) {
        Some(s) => s,
        None => return -1,
    };

    // This requires simple-driver which has the Database implementation
    // For now, delegate to the current simple binary
    let simple_bin = simple_binary_path();
    let Some(next_depth) = delegate_guard(&simple_bin, "test --validate-db") else {
        return -1;
    };
    let mut cmd = Command::new(&simple_bin);
    cmd.env(DELEGATE_DEPTH_ENV, next_depth.to_string());
    cmd.arg("test");
    cmd.arg("--validate-db");
    cmd.arg(&path_str);
    cmd.env("SIMPLE_TEST_DEBUG", "basic");

    match cmd.output() {
        Ok(output) => {
            if output.status.success() {
                // Parse violation count from stdout
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    if line.starts_with("VIOLATIONS:") {
                        if let Some(count_str) = line.split(':').nth(1) {
                            if let Ok(count) = count_str.trim().parse::<i64>() {
                                return count;
                            }
                        }
                    }
                }
                0 // No violations marker found, assume success
            } else {
                -1
            }
        }
        Err(_) => -1,
    }
}

/// Enable debug mode for database validation
#[no_mangle]
pub extern "C" fn rt_test_db_enable_validation(enabled: u8) {
    if enabled != 0 {
        std::env::set_var("SIMPLE_TEST_DEBUG", "basic");
    } else {
        std::env::remove_var("SIMPLE_TEST_DEBUG");
    }
}

/// Check if a test run is stale (running > hours_threshold)
#[no_mangle]
pub extern "C" fn rt_test_run_is_stale(run_id: RuntimeValue, hours_threshold: i64) -> u8 {
    // This would need access to the test database
    // For now, return 0 (not stale) as a safe default
    // Full implementation requires linking against simple-driver
    0
}

/// Cleanup stale test runs in database
/// Returns number of runs cleaned up, or -1 on error
#[no_mangle]
pub extern "C" fn rt_test_db_cleanup_stale_runs(db_path: RuntimeValue) -> i64 {
    let path_str = match extract_string(db_path) {
        Some(s) => s,
        None => return -1,
    };

    let simple_bin = simple_binary_path();
    let Some(next_depth) = delegate_guard(&simple_bin, "test --cleanup-runs") else {
        return -1;
    };
    let mut cmd = Command::new(&simple_bin);
    cmd.env(DELEGATE_DEPTH_ENV, next_depth.to_string());
    cmd.arg("test");
    cmd.arg("--cleanup-runs");
    cmd.arg("--db-path");
    cmd.arg(&path_str);
    cmd.env("SIMPLE_TEST_AUTO_CLEANUP", "1");

    match cmd.status() {
        Ok(status) => {
            if status.success() {
                0 // Success, but we don't have the count without parsing output
            } else {
                -1
            }
        }
        Err(_) => -1,
    }
}
