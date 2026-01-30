//! CLI FFI functions for Simple programs
//!
//! These functions provide basic CLI functionality that Simple programs can call.
//! They are part of the runtime library so they can be linked into native binaries.

use super::{rt_array_get, rt_array_len, rt_array_new, rt_array_push, rt_string_new, RuntimeValue};
use std::process::{Command, Stdio};

/// CLI version string - embedded at compile time
const CLI_VERSION: &str = env!("CARGO_PKG_VERSION");

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

/// Get command line arguments as a RuntimeValue array
#[no_mangle]
pub extern "C" fn rt_cli_get_args() -> RuntimeValue {
    let args: Vec<String> = std::env::args().collect();
    let arr = rt_array_new(args.len() as u64);
    for arg in &args {
        rt_array_push(arr, rt_string_new(arg.as_ptr(), arg.len() as u64));
    }
    arr
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

/// Find the simple_old binary for subprocess calls
/// Looks in: 1) SIMPLE_OLD_PATH env var, 2) same directory as current exe, 3) PATH
fn find_simple_old() -> Option<std::path::PathBuf> {
    // 1. Check environment variable
    if let Ok(path) = std::env::var("SIMPLE_OLD_PATH") {
        let p = std::path::PathBuf::from(&path);
        if p.exists() {
            return Some(p);
        }
    }

    // 2. Check relative to current executable
    if let Ok(exe_path) = std::env::current_exe() {
        if let Some(exe_dir) = exe_path.parent() {
            let simple_old = exe_dir.join("simple_old");
            if simple_old.exists() {
                return Some(simple_old);
            }
        }
    }

    // 3. Check common development paths
    let dev_paths = ["target/debug/simple_old", "target/release/simple_old", "./simple_old"];
    for path in dev_paths {
        let p = std::path::PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }

    // 4. Check PATH using which-style lookup
    if let Ok(output) = Command::new("which").arg("simple_old").output() {
        if output.status.success() {
            let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path_str.is_empty() {
                return Some(std::path::PathBuf::from(path_str));
            }
        }
    }

    None
}

/// Delegate a CLI command to simple_old subprocess
fn delegate_to_simple_old(command: &str, args: RuntimeValue) -> i64 {
    let simple_old = match find_simple_old() {
        Some(path) => path,
        None => {
            eprintln!("error: cannot find simple_old binary");
            eprintln!("hint: Set SIMPLE_OLD_PATH environment variable or ensure simple_old is in PATH");
            return 1;
        }
    };

    let mut cmd = Command::new(&simple_old);
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
            eprintln!("error: failed to execute simple_old: {}", e);
            1
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_cli_run_code(_code: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_code")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_file(_path: RuntimeValue, _args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_file")
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

    // Call the test runner from simple-driver
    // Note: This requires linking against simple-driver
    // For now, we'll exec the binary to avoid circular dependencies
    use std::process::Command;

    let mut cmd = Command::new(std::env::current_exe().unwrap());
    cmd.arg("test");

    // Add all arguments
    for arg in &arg_strings {
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

#[no_mangle]
pub extern "C" fn rt_cli_run_lint(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("lint", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_fmt(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("fmt", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_fix(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("lint", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_check(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("check", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_verify(args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    delegate_to_simple_old("verify", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_migrate(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("migrate", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_mcp(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("mcp", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_diff(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("diff", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_context(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("context", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_constr(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("constr", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_query(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("query", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_info(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("info", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_coverage(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("spec-coverage", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_replay(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("replay", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_gen_lean(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("gen-lean", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_feature_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("feature-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_task_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("task-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("spec-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_sspec_docgen(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("sspec-docgen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_scan(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("todo-scan", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_gen(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("todo-gen", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_i18n(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("i18n", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_lex(_args: RuntimeValue) -> i64 {
    delegate_to_simple_old("lex", _args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_brief(_args: RuntimeValue) -> i64 {
    delegate_to_simple_old("brief", _args)
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
    simple_loader::settlement_main() as i64
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_compile(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("compile", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_targets() -> i64 {
    // Create empty args array for delegate
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("targets".as_ptr(), 7));
    delegate_to_simple_old("targets", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_linkers() -> i64 {
    // Create empty args array for delegate
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("linkers".as_ptr(), 7));
    delegate_to_simple_old("linkers", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_web(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("web", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_diagram(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("diagram", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_init(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("init", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_add(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("add", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_remove(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("remove", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_install() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("install".as_ptr(), 7));
    delegate_to_simple_old("install", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_update(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("update", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_list() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("list".as_ptr(), 4));
    delegate_to_simple_old("list", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_tree() -> i64 {
    let args = rt_array_new(1);
    rt_array_push(args, rt_string_new("tree".as_ptr(), 4));
    delegate_to_simple_old("tree", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_cache(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("cache", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_env(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("env", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_lock(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("lock", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_run_qualify_ignore(args: RuntimeValue) -> i64 {
    delegate_to_simple_old("qualify-ignore", args)
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_run(args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    delegate_to_simple_old("run", args)
}

// ============================================================================
// Self-Hosting Compiler FFI Functions
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
// Fault Detection Configuration FFI (C ABI for compiled mode)
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
// Test Database Integrity Validation FFI
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
    // For now, we'll delegate to simple_old
    let mut cmd = Command::new(std::env::current_exe().unwrap_or_else(|_| "simple_old".into()));
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

    let mut cmd = Command::new(std::env::current_exe().unwrap_or_else(|_| "simple_old".into()));
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
