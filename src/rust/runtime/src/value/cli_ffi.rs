//! CLI FFI functions for Simple programs
//!
//! These functions provide basic CLI functionality that Simple programs can call.
//! They are part of the runtime library so they can be linked into native binaries.

use super::{rt_array_new, rt_array_push, rt_string_new, RuntimeValue};

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

/// Check if a file exists
#[no_mangle]
pub extern "C" fn rt_cli_file_exists(path: RuntimeValue) -> u8 {
    let len = super::rt_string_len(path);
    if len <= 0 {
        return 0;
    }
    let data = super::rt_string_data(path);
    if data.is_null() {
        return 0;
    }
    let path_str = unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        String::from_utf8_lossy(slice).to_string()
    };
    if std::path::Path::new(&path_str).exists() {
        1
    } else {
        0
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

#[no_mangle]
pub extern "C" fn rt_cli_run_code(_code: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_code")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_file(
    _path: RuntimeValue,
    _args: RuntimeValue,
    _gc_log: u8,
    _gc_off: u8,
) -> i64 {
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
pub extern "C" fn rt_cli_run_tests(_args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_tests")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_lint(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_lint")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_fmt(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_fmt")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_check(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_check")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_verify(_args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_run_verify")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_migrate(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_migrate")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_mcp(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_mcp")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_diff(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_diff")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_context(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_context")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_constr(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_constr")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_query(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_query")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_info(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_info")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_coverage(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_spec_coverage")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_replay(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_replay")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_gen_lean(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_gen_lean")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_feature_gen(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_feature_gen")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_task_gen(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_task_gen")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_spec_gen(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_spec_gen")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_sspec_docgen(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_sspec_docgen")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_scan(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_todo_scan")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_todo_gen(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_todo_gen")
}

#[no_mangle]
pub extern "C" fn rt_cli_run_i18n(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_run_i18n")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_compile(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_compile")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_targets() -> i64 {
    not_implemented("rt_cli_handle_targets")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_linkers() -> i64 {
    not_implemented("rt_cli_handle_linkers")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_web(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_web")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_diagram(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_diagram")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_init(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_init")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_add(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_add")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_remove(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_remove")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_install() -> i64 {
    not_implemented("rt_cli_handle_install")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_update(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_update")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_list() -> i64 {
    not_implemented("rt_cli_handle_list")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_tree() -> i64 {
    not_implemented("rt_cli_handle_tree")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_cache(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_cache")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_env(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_env")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_lock(_args: RuntimeValue) -> i64 {
    not_implemented("rt_cli_handle_lock")
}

#[no_mangle]
pub extern "C" fn rt_cli_handle_run(_args: RuntimeValue, _gc_log: u8, _gc_off: u8) -> i64 {
    not_implemented("rt_cli_handle_run")
}
