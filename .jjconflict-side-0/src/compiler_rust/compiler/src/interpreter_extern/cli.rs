//! CLI SFFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call into CLI functionality.
//! Basic operations are implemented directly, while complex operations
//! that require the full driver return errors in interpreter mode.

use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_interpreter_args;
use crate::value::Value;

/// CLI version string
const CLI_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Get CLI version
pub fn rt_cli_version(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(format!("Simple v{}", CLI_VERSION)))
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
    let args = get_interpreter_args();
    let arr: Vec<Value> = args.into_iter().map(Value::text).collect();
    Ok(Value::array(arr))
}

/// Get the command-line argument count through a scalar-only ABI.
pub fn rt_cli_arg_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(get_interpreter_args().len() as i64))
}

/// Get one command-line argument through a scalar-only ABI.
/// Invalid indices return non-nil empty text.
pub fn rt_cli_arg_at(args: &[Value]) -> Result<Value, CompileError> {
    let index = match args.first() {
        Some(Value::Int(index)) => *index,
        _ => -1,
    };
    let value = usize::try_from(index)
        .ok()
        .and_then(|index| get_interpreter_args().get(index).cloned())
        .unwrap_or_default();
    Ok(Value::text(value))
}

/// Check if file exists
pub fn rt_cli_file_exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Bool(false));
    }
    let path = match &args[0] {
        Value::Str(s) => s.as_ref().clone(),
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
pub fn rt_cli_run_tests(args: &[Value]) -> Result<Value, CompileError> {
    // Recursion guard: refuse nested `simple test` invocations.
    // A depth of 1 means a top-level test run is already active; any call to
    // cli_run_tests from within a spec or helper would push it to 2 and is rejected.
    // This prevents runaway process storms (see bug: jit_hotspot_verification_process_storm).
    const MAX_TEST_DEPTH: u32 = 1;
    let current_depth: u32 = std::env::var("SIMPLE_TEST_DEPTH")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    if current_depth >= MAX_TEST_DEPTH {
        eprintln!(
            "ERROR: simple test recursion guard triggered (SIMPLE_TEST_DEPTH={}).\n  \
             Nested `bin/simple test` invocations are not allowed.\n  \
             A spec or script is calling cli_run_tests() from inside a test run.",
            current_depth
        );
        return Ok(Value::Int(1));
    }

    // Extract arguments
    let mut cmd_args = Vec::new();
    if !args.is_empty() {
        if let Value::Array(arr) = &args[0] {
            for val in arr.iter() {
                if let Value::Str(s) = val {
                    cmd_args.push(s.as_ref().clone());
                }
            }
        }
    }

    // Get GC flags
    let gc_log = if args.len() > 1 {
        matches!(&args[1], Value::Bool(true) | Value::Int(1))
    } else {
        false
    };
    let gc_off = if args.len() > 2 {
        matches!(&args[2], Value::Bool(true) | Value::Int(1))
    } else {
        false
    };

    // Execute test runner
    use std::process::Command;
    let mut cmd = Command::new(std::env::current_exe().unwrap_or_else(|_| "simple_old".into()));
    cmd.arg("test");

    for arg in &cmd_args {
        cmd.arg(arg);
    }

    if gc_log {
        cmd.arg("--gc-log");
    }
    if gc_off {
        cmd.arg("--gc-off");
    }

    cmd.env("SIMPLE_TEST_RUNNER_RUST", "1");
    // Propagate incremented depth so nested spawns see a higher value and are refused.
    cmd.env("SIMPLE_TEST_DEPTH", (current_depth + 1).to_string());

    match cmd.status() {
        Ok(status) => Ok(Value::Int(status.code().unwrap_or(1) as i64)),
        Err(e) => {
            eprintln!("Failed to run tests: {}", e);
            Ok(Value::Int(1))
        }
    }
}

/// Native Stage4 owns this scalar bridge. Interpreting the full CLI would
/// otherwise re-enter the current seed process after main has raised depth.
pub fn rt_cli_run_tests_process_args(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_tests_process_args")
}

/// Validate test database
pub fn rt_test_db_validate(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => return Ok(Value::Int(-1)),
    };

    use std::process::Command;
    let mut cmd = Command::new(std::env::current_exe().unwrap_or_else(|_| "simple_old".into()));
    cmd.arg("test");
    cmd.arg("--validate-db");
    cmd.arg(&*path);
    cmd.env("SIMPLE_TEST_DEBUG", "basic");

    match cmd.output() {
        Ok(output) => {
            if output.status.success() {
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    if line.starts_with("VIOLATIONS:") {
                        if let Some(count_str) = line.split(':').nth(1) {
                            if let Ok(count) = count_str.trim().parse::<i64>() {
                                return Ok(Value::Int(count));
                            }
                        }
                    }
                }
                Ok(Value::Int(0))
            } else {
                Ok(Value::Int(-1))
            }
        }
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Enable database validation
pub fn rt_test_db_enable_validation(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        Some(Value::Int(i)) => *i != 0,
        _ => false,
    };

    if enabled {
        std::env::set_var("SIMPLE_TEST_DEBUG", "basic");
    } else {
        std::env::remove_var("SIMPLE_TEST_DEBUG");
    }

    Ok(Value::Nil)
}

/// Check if test run is stale
pub fn rt_test_run_is_stale(_args: &[Value]) -> Result<Value, CompileError> {
    // Requires database access - not available in interpreter mode
    Ok(Value::Bool(false))
}

/// Cleanup stale test runs
pub fn rt_test_db_cleanup_stale_runs(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => return Ok(Value::Int(-1)),
    };

    use std::process::Command;
    let mut cmd = Command::new(std::env::current_exe().unwrap_or_else(|_| "simple_old".into()));
    cmd.arg("test");
    cmd.arg("--cleanup-runs");
    cmd.arg("--db-path");
    cmd.arg(&*path);
    cmd.env("SIMPLE_TEST_AUTO_CLEANUP", "1");

    match cmd.status() {
        Ok(status) => Ok(Value::Int(if status.success() { 0 } else { -1 })),
        Err(_) => Ok(Value::Int(-1)),
    }
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

/// Run spipe-docgen command
pub fn rt_cli_run_spipe_docgen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_spipe_docgen")
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

/// Run SFFI generator command
pub fn rt_cli_run_sffi_gen(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_run_sffi_gen")
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

/// Handle native-build command
pub fn rt_native_build(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_native_build")
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
// Fault Detection Configuration SFFI
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
