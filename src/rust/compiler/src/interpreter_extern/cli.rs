//! CLI FFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call into CLI functionality.
//! Basic operations are implemented directly, while complex operations
//! that require the full driver return errors in interpreter mode.

use crate::error::CompileError;
use crate::value::Value;

/// CLI version string
const CLI_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Get CLI version
pub fn rt_cli_version(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Str(format!("Simple v{}", CLI_VERSION)))
}

/// Print help message
pub fn rt_cli_print_help(_args: &[Value]) -> Result<Value, CompileError> {
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
    Ok(Value::Nil)
}

/// Print version
pub fn rt_cli_print_version(_args: &[Value]) -> Result<Value, CompileError> {
    println!("Simple v{}", CLI_VERSION);
    Ok(Value::Nil)
}

/// Get command line arguments
pub fn rt_cli_get_args(_args: &[Value]) -> Result<Value, CompileError> {
    let args: Vec<String> = std::env::args().collect();
    let arr: Vec<Value> = args.into_iter().map(Value::Str).collect();
    Ok(Value::Array(arr))
}

/// Check if file exists
pub fn rt_cli_file_exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Bool(false));
    }
    let path = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Ok(Value::Bool(false)),
    };
    Ok(Value::Bool(std::path::Path::new(&path).exists()))
}

/// Exit with code
pub fn rt_cli_exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = match args.first() {
        Some(Value::Int(i)) => *i as i32,
        _ => 0,
    };
    std::process::exit(code);
}

// Complex operations that require the full driver - not supported in interpreter mode
// These return error codes or print messages

fn interpreter_not_supported(name: &str) -> Result<Value, CompileError> {
    eprintln!("error: {} is not supported in interpreter mode", name);
    eprintln!("hint: Build and run the compiled CLI for full functionality");
    Ok(Value::Int(1))
}

/// Run code string
pub fn rt_cli_run_code(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_code")
}

/// Run a file with arguments
pub fn rt_cli_run_file(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_file")
}

/// Watch a file for changes
pub fn rt_cli_watch_file(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_watch_file")
}

/// Run REPL
pub fn rt_cli_run_repl(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_repl")
}

/// Run tests
pub fn rt_cli_run_tests(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_tests")
}

/// Run linter
pub fn rt_cli_run_lint(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_lint")
}

/// Run formatter
pub fn rt_cli_run_fmt(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_fmt")
}

/// Run check command
pub fn rt_cli_run_check(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_check")
}

/// Run verify command
pub fn rt_cli_run_verify(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_verify")
}

/// Run migrate command
pub fn rt_cli_run_migrate(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_migrate")
}

/// Run MCP command
pub fn rt_cli_run_mcp(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_mcp")
}

/// Run diff command
pub fn rt_cli_run_diff(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_diff")
}

/// Run context command
pub fn rt_cli_run_context(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_context")
}

/// Run constr command (constraint analysis)
pub fn rt_cli_run_constr(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_constr")
}

/// Run query command
pub fn rt_cli_run_query(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_query")
}

/// Run info command
pub fn rt_cli_run_info(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_info")
}

/// Run spec-coverage command
pub fn rt_cli_run_spec_coverage(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_spec_coverage")
}

/// Run replay command
pub fn rt_cli_run_replay(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_replay")
}

/// Run gen-lean command
pub fn rt_cli_run_gen_lean(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_gen_lean")
}

/// Run feature-gen command
pub fn rt_cli_run_feature_gen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_feature_gen")
}

/// Run task-gen command
pub fn rt_cli_run_task_gen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_task_gen")
}

/// Run spec-gen command
pub fn rt_cli_run_spec_gen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_spec_gen")
}

/// Run sspec-docgen command
pub fn rt_cli_run_sspec_docgen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_sspec_docgen")
}

/// Run todo-scan command
pub fn rt_cli_run_todo_scan(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_todo_scan")
}

/// Run todo-gen command
pub fn rt_cli_run_todo_gen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_todo_gen")
}

/// Run i18n command
pub fn rt_cli_run_i18n(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_i18n")
}

/// Generate context pack
pub fn rt_context_generate(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_context_generate")
}

/// Get context statistics
pub fn rt_context_stats(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_context_stats")
}

/// Settlement main entry point
pub fn rt_settlement_main(_args: &[Value]) -> Result<Value, CompileError> {
    // Settlement loading only works in compiled mode (reads from self)
    interpreter_not_supported("rt_settlement_main")
}

/// Handle compile command
pub fn rt_cli_handle_compile(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_compile")
}

/// Handle targets command
pub fn rt_cli_handle_targets(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_targets")
}

/// Handle linkers command
pub fn rt_cli_handle_linkers(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_linkers")
}

/// Handle web command
pub fn rt_cli_handle_web(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_web")
}

/// Handle diagram command
pub fn rt_cli_handle_diagram(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_diagram")
}

/// Handle init command
pub fn rt_cli_handle_init(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_init")
}

/// Handle add command
pub fn rt_cli_handle_add(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_add")
}

/// Handle remove command
pub fn rt_cli_handle_remove(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_remove")
}

/// Handle install command
pub fn rt_cli_handle_install(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_install")
}

/// Handle update command
pub fn rt_cli_handle_update(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_update")
}

/// Handle list command
pub fn rt_cli_handle_list(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_list")
}

/// Handle tree command
pub fn rt_cli_handle_tree(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_tree")
}

/// Handle cache command
pub fn rt_cli_handle_cache(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_cache")
}

/// Handle env command
pub fn rt_cli_handle_env(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_env")
}

/// Handle lock command
pub fn rt_cli_handle_lock(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_lock")
}

/// Handle run command
pub fn rt_cli_handle_run(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_run")
}

// =========================================================================
// Fault Detection Configuration FFI
// =========================================================================

/// Set stack overflow detection enabled/disabled
pub fn rt_fault_set_stack_overflow_detection(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => true,
    };
    crate::interpreter::set_stack_overflow_detection_enabled(enabled);
    Ok(Value::Nil)
}

/// Set max recursion depth
pub fn rt_fault_set_max_recursion_depth(args: &[Value]) -> Result<Value, CompileError> {
    let depth = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        _ => 1000,
    };
    crate::interpreter::set_max_recursion_depth(depth);
    Ok(Value::Nil)
}

/// Set execution timeout (starts watchdog thread)
pub fn rt_fault_set_timeout(args: &[Value]) -> Result<Value, CompileError> {
    let secs = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        _ => 0,
    };
    if secs > 0 {
        crate::watchdog::start_watchdog(secs);
    } else {
        crate::watchdog::stop_watchdog();
    }
    Ok(Value::Nil)
}

/// Set execution limit
pub fn rt_fault_set_execution_limit(args: &[Value]) -> Result<Value, CompileError> {
    let limit = match args.first() {
        Some(Value::Int(n)) => *n as u64,
        _ => 0,
    };
    crate::interpreter::set_execution_limit(limit);
    if limit == 0 {
        crate::interpreter::set_execution_limit_enabled(false);
    } else {
        crate::interpreter::set_execution_limit_enabled(true);
    }
    Ok(Value::Nil)
}
