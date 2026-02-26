//! Simple Language - Unified CLI
//!
//! Usage like Python:
//!   simple              - Start interactive REPL
//!   simple file.spl     - Run source file
//!   simple file.smf     - Run compiled binary
//!   simple -c "code"    - Run code string
//!   simple compile src.spl [-o out.smf]  - Compile to SMF
//!   simple watch file.spl  - Watch and auto-recompile

use std::path::PathBuf;

use simple_driver::cli::analysis::{run_info, run_query};
use simple_driver::cli::audit::{run_replay, run_spec_coverage};
use simple_driver::cli::basic::{create_runner, run_code, run_file_with_args, watch_file};
use simple_driver::cli::check::{CheckOptions, run_check};
use simple_driver::cli::code_quality::{run_fmt, run_lint};
use simple_driver::cli::gen_lean::run_gen_lean;
use simple_driver::cli::help::{print_help, print_version, version};
use simple_driver::cli::llm_tools::{run_constr, run_context, run_diff, run_mcp};
use simple_driver::cli::migrate::run_migrate;
use simple_driver::cli::repl::run_repl;
use simple_driver::cli::sandbox::{apply_sandbox, parse_sandbox_config};
use simple_driver::cli::test_runner;
use simple_driver::cli::verify::run_verify;
#[cfg(feature = "tui")]
use simple_driver::cli::tui::run_tui_repl;
use simple_driver::cli::doc_gen::{run_feature_gen, run_spec_gen, run_task_gen, run_todo_gen, run_todo_scan};
use simple_driver::cli::sspec_docgen;
use simple_driver::cli::qualify_ignore::{handle_qualify_ignore, parse_qualify_ignore_args};

// Import our new command modules
use simple_driver::cli::commands::*;

// ---------------------------------------------------------------------------
// Table-driven command dispatch
// ---------------------------------------------------------------------------

/// Handler type – covers the different function signatures used by CLI commands.
enum Handler {
    /// `fn(&[String]) -> i32`
    Args(fn(&[String]) -> i32),
    /// `fn() -> i32`  (no args)
    NoArgs(fn() -> i32),
    /// `fn(&[String], bool, bool) -> i32`  (args + gc_log + gc_off)
    ArgsGc(fn(&[String], bool, bool) -> i32),
    /// Custom handler that receives everything and returns exit code
    Custom(fn(&CommandContext) -> i32),
}

/// Everything a command handler might need.
struct CommandContext<'a> {
    args: &'a [String],
    gc_log: bool,
    gc_off: bool,
}

/// One row in the command table.
struct CommandEntry {
    /// CLI name (e.g. "compile", "targets")
    name: &'static str,
    /// Relative path to the Simple app, e.g. "src/app/compile/main.spl"
    app_path: &'static str,
    /// Rust fallback handler
    rust_handler: Handler,
    /// Env var that forces Rust handler (e.g. "SIMPLE_COMPILE_RUST")
    env_override: &'static str,
    /// Flags that require the Rust handler (empty = none)
    needs_rust_flags: &'static [&'static str],
}

/// Execute a command entry: Simple-first with Rust fallback.
fn dispatch_command(entry: &CommandEntry, ctx: &CommandContext) -> i32 {
    // 1. Check env var override → Rust
    if !entry.env_override.is_empty() && std::env::var(entry.env_override).is_ok() {
        return run_rust_handler(&entry.rust_handler, ctx);
    }

    // 2. Check if any args require the Rust handler
    if !entry.needs_rust_flags.is_empty() {
        let needs_rust = ctx.args[1..].iter().any(|a| {
            entry
                .needs_rust_flags
                .iter()
                .any(|f| a.as_str() == *f || a.starts_with(f))
        });
        if needs_rust {
            return run_rust_handler(&entry.rust_handler, ctx);
        }
    }

    // 3. Try Simple app
    if !entry.app_path.is_empty() {
        if let Some(code) = dispatch_to_simple_app(entry.app_path, ctx.args, ctx.gc_log, ctx.gc_off) {
            return code;
        }
    }

    // 4. Fallback → Rust
    run_rust_handler(&entry.rust_handler, ctx)
}

fn run_rust_handler(handler: &Handler, ctx: &CommandContext) -> i32 {
    match handler {
        Handler::Args(f) => f(ctx.args),
        Handler::NoArgs(f) => f(),
        Handler::ArgsGc(f) => f(ctx.args, ctx.gc_log, ctx.gc_off),
        Handler::Custom(f) => f(ctx),
    }
}

// ---------------------------------------------------------------------------
// Rust handler wrappers (adapt existing functions to uniform signatures)
// ---------------------------------------------------------------------------

fn handle_targets_wrapper() -> i32 {
    handle_targets()
}
fn handle_linkers_wrapper() -> i32 {
    handle_linkers()
}
fn handle_install_wrapper() -> i32 {
    handle_install()
}
fn handle_list_wrapper() -> i32 {
    handle_list()
}
fn handle_tree_wrapper() -> i32 {
    handle_tree()
}

fn handle_check_wrapper(ctx: &CommandContext) -> i32 {
    handle_check_impl(ctx.args)
}

fn handle_watch_wrapper(ctx: &CommandContext) -> i32 {
    if ctx.args.len() < 2 {
        eprintln!("error: watch requires a source file");
        eprintln!("Usage: simple watch <file.spl>");
        return 1;
    }
    let path = PathBuf::from(&ctx.args[1]);
    watch_file(&path)
}

fn handle_qualify_ignore_wrapper(ctx: &CommandContext) -> i32 {
    let qi_args = parse_qualify_ignore_args(&ctx.args[1..]);
    match handle_qualify_ignore(qi_args) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn handle_i18n_wrapper(args: &[String]) -> i32 {
    simple_driver::cli::i18n::run_i18n(args)
}

fn handle_run_wrapper(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    handle_run(args, gc_log, gc_off)
}

// ---------------------------------------------------------------------------
// Command table
// ---------------------------------------------------------------------------

const COMMAND_TABLE: &[CommandEntry] = &[
    // Compilation commands
    CommandEntry {
        name: "compile",
        app_path: "src/app/compile/main.spl",
        rust_handler: Handler::Args(handle_compile),
        env_override: "SIMPLE_COMPILE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "targets",
        app_path: "src/app/targets/main.spl",
        rust_handler: Handler::NoArgs(handle_targets_wrapper),
        env_override: "SIMPLE_TARGETS_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "linkers",
        app_path: "src/app/linkers/main.spl",
        rust_handler: Handler::NoArgs(handle_linkers_wrapper),
        env_override: "SIMPLE_LINKERS_RUST",
        needs_rust_flags: &[],
    },
    // Web framework
    CommandEntry {
        name: "web",
        app_path: "src/app/web/main.spl",
        rust_handler: Handler::Args(handle_web),
        env_override: "SIMPLE_WEB_RUST",
        needs_rust_flags: &[],
    },
    // File watching
    CommandEntry {
        name: "watch",
        app_path: "src/app/watch/main.spl",
        rust_handler: Handler::Custom(handle_watch_wrapper),
        env_override: "SIMPLE_WATCH_RUST",
        needs_rust_flags: &[],
    },
    // Testing - always use Rust handler (mature implementation with Rust test integration + DB tracking)
    CommandEntry {
        name: "test",
        app_path: "", // Rust handler is primary (has cargo test integration)
        rust_handler: Handler::ArgsGc(handle_test_rust),
        env_override: "",
        needs_rust_flags: &[],
    },
    // Code quality
    CommandEntry {
        name: "lint",
        app_path: "src/app/lint/main.spl",
        rust_handler: Handler::Args(|a| run_lint(a)),
        env_override: "SIMPLE_LINT_RUST",
        needs_rust_flags: &["--json", "--fix"],
    },
    CommandEntry {
        name: "fix",
        app_path: "src/app/fix/main.spl",
        rust_handler: Handler::Args(|a| run_lint(a)),
        env_override: "SIMPLE_FIX_RUST",
        needs_rust_flags: &["--fix", "--fix-all", "--fix-dry-run", "--fix-interactive"],
    },
    CommandEntry {
        name: "fmt",
        app_path: "src/app/formatter/main.spl",
        rust_handler: Handler::Args(|a| run_fmt(a)),
        env_override: "SIMPLE_FMT_RUST",
        needs_rust_flags: &["--json"],
    },
    CommandEntry {
        name: "check",
        app_path: "src/app/check/main.spl",
        rust_handler: Handler::Custom(handle_check_wrapper),
        env_override: "SIMPLE_CHECK_RUST",
        needs_rust_flags: &[],
    },
    // Localization
    CommandEntry {
        name: "i18n",
        app_path: "src/app/i18n/main.spl",
        rust_handler: Handler::Args(handle_i18n_wrapper),
        env_override: "SIMPLE_I18N_RUST",
        needs_rust_flags: &[],
    },
    // Migration and tooling
    CommandEntry {
        name: "migrate",
        app_path: "src/app/migrate/main.spl",
        rust_handler: Handler::Args(|a| run_migrate(a)),
        env_override: "SIMPLE_MIGRATE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "mcp",
        app_path: "src/app/mcp/main.spl",
        rust_handler: Handler::Args(|a| run_mcp(a)),
        env_override: "SIMPLE_MCP_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "diff",
        app_path: "src/app/diff/main.spl",
        rust_handler: Handler::Args(|a| run_diff(a)),
        env_override: "SIMPLE_DIFF_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "context",
        app_path: "src/app/context/main.spl",
        rust_handler: Handler::Args(|a| run_context(a)),
        env_override: "SIMPLE_CONTEXT_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "constr",
        app_path: "src/app/constr/main.spl",
        rust_handler: Handler::Args(|a| run_constr(a)),
        env_override: "SIMPLE_CONSTR_RUST",
        needs_rust_flags: &[],
    },
    // Analysis
    CommandEntry {
        name: "query",
        app_path: "src/app/query/main.spl",
        rust_handler: Handler::Args(|a| run_query(a)),
        env_override: "SIMPLE_QUERY_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "info",
        app_path: "src/app/info/main.spl",
        rust_handler: Handler::Args(|a| run_info(a)),
        env_override: "SIMPLE_INFO_RUST",
        needs_rust_flags: &[],
    },
    // Auditing
    CommandEntry {
        name: "spec-coverage",
        app_path: "src/app/spec_coverage/main.spl",
        rust_handler: Handler::Args(|a| run_spec_coverage(a)),
        env_override: "SIMPLE_SPEC_COVERAGE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "replay",
        app_path: "src/app/replay/main.spl",
        rust_handler: Handler::Args(|a| run_replay(a)),
        env_override: "SIMPLE_REPLAY_RUST",
        needs_rust_flags: &[],
    },
    // Code generation
    CommandEntry {
        name: "gen-lean",
        app_path: "src/app/gen_lean/main.spl",
        rust_handler: Handler::Args(|a| run_gen_lean(a)),
        env_override: "SIMPLE_GEN_LEAN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "feature-gen",
        app_path: "src/app/feature_gen/main.spl",
        rust_handler: Handler::Args(|a| run_feature_gen(a)),
        env_override: "SIMPLE_FEATURE_GEN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "task-gen",
        app_path: "src/app/task_gen/main.spl",
        rust_handler: Handler::Args(|a| run_task_gen(a)),
        env_override: "SIMPLE_TASK_GEN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "spec-gen",
        app_path: "src/app/spec_gen/main.spl",
        rust_handler: Handler::Args(|a| run_spec_gen(a)),
        env_override: "SIMPLE_SPEC_GEN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "todo-scan",
        app_path: "src/app/todo_scan/main.spl",
        rust_handler: Handler::Args(|a| run_todo_scan(a)),
        env_override: "SIMPLE_TODO_SCAN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "todo-gen",
        app_path: "src/app/todo_gen/main.spl",
        rust_handler: Handler::Args(|a| run_todo_gen(a)),
        env_override: "SIMPLE_TODO_GEN_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "sspec-docgen",
        app_path: "src/app/sspec_docgen/main.spl",
        rust_handler: Handler::Args(|a| run_sspec_docgen_rust(a)),
        env_override: "SIMPLE_SSPEC_DOCGEN_RUST",
        needs_rust_flags: &[],
    },
    // Brief view
    CommandEntry {
        name: "brief",
        app_path: "src/app/brief/main.spl",
        rust_handler: Handler::ArgsGc(handle_brief),
        env_override: "SIMPLE_BRIEF_RUST",
        needs_rust_flags: &[],
    },
    // Dashboard
    CommandEntry {
        name: "dashboard",
        app_path: "src/app/dashboard/main.spl",
        rust_handler: Handler::ArgsGc(handle_dashboard),
        env_override: "SIMPLE_DASHBOARD_RUST",
        needs_rust_flags: &[],
    },
    // Verification
    CommandEntry {
        name: "verify",
        app_path: "src/app/verify/main.spl",
        rust_handler: Handler::ArgsGc(|a, gl, go| run_verify(a, gl, go)),
        env_override: "SIMPLE_VERIFY_RUST",
        needs_rust_flags: &[],
    },
    // Qualified ignore
    CommandEntry {
        name: "qualify-ignore",
        app_path: "src/app/qualify_ignore/main.spl",
        rust_handler: Handler::Custom(handle_qualify_ignore_wrapper),
        env_override: "SIMPLE_QUALIFY_IGNORE_RUST",
        needs_rust_flags: &[],
    },
    // Diagram
    CommandEntry {
        name: "diagram",
        app_path: "src/app/diagram/main.spl",
        rust_handler: Handler::Args(handle_diagram),
        env_override: "SIMPLE_DIAGRAM_RUST",
        needs_rust_flags: &[],
    },
    // Package management
    CommandEntry {
        name: "init",
        app_path: "src/app/init/main.spl",
        rust_handler: Handler::Args(handle_init),
        env_override: "SIMPLE_INIT_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "add",
        app_path: "src/app/add/main.spl",
        rust_handler: Handler::Args(handle_add),
        env_override: "SIMPLE_ADD_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "remove",
        app_path: "src/app/remove/main.spl",
        rust_handler: Handler::Args(handle_remove),
        env_override: "SIMPLE_REMOVE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "install",
        app_path: "src/app/install/main.spl",
        rust_handler: Handler::NoArgs(handle_install_wrapper),
        env_override: "SIMPLE_INSTALL_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "update",
        app_path: "src/app/update/main.spl",
        rust_handler: Handler::Args(handle_update),
        env_override: "SIMPLE_UPDATE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "list",
        app_path: "src/app/list/main.spl",
        rust_handler: Handler::NoArgs(handle_list_wrapper),
        env_override: "SIMPLE_LIST_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "tree",
        app_path: "src/app/tree/main.spl",
        rust_handler: Handler::NoArgs(handle_tree_wrapper),
        env_override: "SIMPLE_TREE_RUST",
        needs_rust_flags: &[],
    },
    CommandEntry {
        name: "cache",
        app_path: "src/app/cache/main.spl",
        rust_handler: Handler::Args(handle_cache),
        env_override: "SIMPLE_CACHE_RUST",
        needs_rust_flags: &[],
    },
    // Environment management
    CommandEntry {
        name: "env",
        app_path: "src/app/env/main.spl",
        rust_handler: Handler::Args(handle_env),
        env_override: "SIMPLE_ENV_RUST",
        needs_rust_flags: &[],
    },
    // Lock file
    CommandEntry {
        name: "lock",
        app_path: "src/app/lock/main.spl",
        rust_handler: Handler::Args(handle_lock),
        env_override: "SIMPLE_LOCK_RUST",
        needs_rust_flags: &[],
    },
    // Coverage (app-only)
    CommandEntry {
        name: "coverage",
        app_path: "src/app/coverage/main.spl",
        rust_handler: Handler::Custom(|_| {
            eprintln!("error: coverage app not found (install Simple or run from project root)");
            1
        }),
        env_override: "",
        needs_rust_flags: &[],
    },
    // Dependency graph (app-only)
    CommandEntry {
        name: "depgraph",
        app_path: "src/app/depgraph/main.spl",
        rust_handler: Handler::Custom(|_| {
            eprintln!("error: depgraph app not found (install Simple or run from project root)");
            1
        }),
        env_override: "",
        needs_rust_flags: &[],
    },
    // LSP (app-only)
    CommandEntry {
        name: "lsp",
        app_path: "src/app/lsp/main.spl",
        rust_handler: Handler::Custom(|_| {
            eprintln!("error: lsp app not found (install Simple or run from project root)");
            1
        }),
        env_override: "",
        needs_rust_flags: &[],
    },
    // DAP (app-only)
    CommandEntry {
        name: "dap",
        app_path: "src/app/dap/main.spl",
        rust_handler: Handler::Custom(|_| {
            eprintln!("error: dap app not found (install Simple or run from project root)");
            1
        }),
        env_override: "",
        needs_rust_flags: &[],
    },
    // Run command
    CommandEntry {
        name: "run",
        app_path: "src/app/run/main.spl",
        rust_handler: Handler::ArgsGc(handle_run_wrapper),
        env_override: "SIMPLE_RUN_RUST",
        needs_rust_flags: &[],
    },
];

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

fn main() {
    // Initialize metrics and startup tracking
    let (metrics_enabled, mut metrics) = init_metrics();

    // Initialize coverage if SIMPLE_COVERAGE env var is set
    simple_compiler::init_coverage_from_env();

    // PHASE 1: Early startup - parse args and start prefetching
    let early_config = early_startup(&mut metrics);

    // Start prefetching input files in background (if enabled)
    let prefetch_handle = start_prefetch(&early_config, &mut metrics);

    // Pre-allocate resources based on app type
    let _resources = allocate_resources(&early_config, &mut metrics);

    // PHASE 2: Normal initialization (happens in parallel with prefetching)
    simple_driver::cli::init::init_runtime(&mut metrics);

    // Reconstruct args from early config for compatibility with existing code
    let args: Vec<String> = early_config
        .remaining_args
        .iter()
        .map(|s| s.to_string_lossy().to_string())
        .collect();

    // Parse global flags
    let global_flags = GlobalFlags::parse(&args);
    global_flags.apply();

    // Parse --lang flag for i18n localization
    parse_lang_flag(&args);

    // Parse and apply sandbox configuration before running code (#916-919)
    let sandbox_start = std::time::Instant::now();
    if let Some(sandbox_config) = parse_sandbox_config(&args) {
        if let Err(e) = apply_sandbox(&sandbox_config) {
            eprintln!("warning: {}", e);
            eprintln!("Continuing without full sandboxing...");
        }
        metrics.record(simple_driver::StartupPhase::SandboxSetup, sandbox_start.elapsed());
    }

    // Filter out internal flags
    let args = filter_internal_flags(&args);

    // No arguments -> REPL (TUI by default if feature enabled)
    if args.is_empty() {
        let runner = create_runner(global_flags.gc_log, global_flags.gc_off);

        #[cfg(feature = "tui")]
        if !global_flags.use_notui {
            // TUI is default when feature is enabled
            std::process::exit(run_tui_repl(version(), runner));
        }

        // Use Normal mode if --notui flag is set or TUI feature is disabled
        std::process::exit(run_repl(version(), runner));
    }

    let first = &args[0];

    // Special cases that don't go through the table
    let exit_code = match first.as_str() {
        "-h" | "--help" => {
            print_help();
            0
        }
        "-v" | "--version" => {
            print_version();
            0
        }
        "-c" => {
            if args.len() < 2 {
                eprintln!("error: -c requires a code argument");
                std::process::exit(1);
            }
            run_code(&args[1], global_flags.gc_log, global_flags.gc_off)
        }

        // Table-driven dispatch for all named commands
        cmd => {
            let ctx = CommandContext {
                args: &args,
                gc_log: global_flags.gc_log,
                gc_off: global_flags.gc_off,
            };

            if let Some(entry) = COMMAND_TABLE.iter().find(|e| e.name == cmd) {
                dispatch_command(entry, &ctx)
            } else {
                // Default: assume it's a file to run
                handle_file_execution(
                    first,
                    &args,
                    global_flags.gc_log,
                    global_flags.gc_off,
                    prefetch_handle,
                    &mut metrics,
                )
            }
        }
    };

    if metrics_enabled {
        exit_with_metrics(exit_code, &metrics);
    } else {
        std::process::exit(exit_code);
    }
}

/// Resolve the path to a Simple app, checking multiple locations:
/// 1. Relative to CWD (development: running from project root)
/// 2. Relative to the executable's directory (installed/native)
/// 3. SIMPLE_HOME environment variable
fn resolve_app_path(relative_path: &str) -> Option<PathBuf> {
    // 1. Relative to CWD
    let cwd_path = PathBuf::from(relative_path);
    if cwd_path.exists() {
        return Some(cwd_path);
    }

    // 2. Relative to executable directory
    if let Ok(exe) = std::env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            // Try alongside the binary (installed layout)
            let exe_relative = exe_dir.join(relative_path);
            if exe_relative.exists() {
                return Some(exe_relative);
            }
            // Try ../../ from target/debug/ (development layout)
            if let Some(project_root) = exe_dir.parent().and_then(|p| p.parent()) {
                let project_relative = project_root.join(relative_path);
                if project_relative.exists() {
                    return Some(project_relative);
                }
            }
        }
    }

    // 3. SIMPLE_HOME env var
    if let Ok(home) = std::env::var("SIMPLE_HOME") {
        let home_path = PathBuf::from(home).join(relative_path);
        if home_path.exists() {
            return Some(home_path);
        }
    }

    None
}

/// Dispatch a command to its Simple app, returning None if app not found
fn dispatch_to_simple_app(app_relative_path: &str, args: &[String], gc_log: bool, gc_off: bool) -> Option<i32> {
    let app_path = resolve_app_path(app_relative_path)?;
    // Match normal file execution: argv[0] is the script path, then user args
    let mut full_args = vec![app_path.to_string_lossy().to_string()];
    full_args.extend(args[1..].iter().cloned());
    Some(run_file_with_args(&app_path, gc_log, gc_off, full_args))
}

/// Original Rust test runner implementation (fallback)
fn handle_test_rust(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    // Parse test options from remaining args
    let test_args: Vec<String> = args[1..].to_vec();
    let mut options = test_runner::parse_test_args(&test_args);
    options.gc_log = gc_log;
    options.gc_off = gc_off;

    // Check if watch mode is enabled
    if options.watch {
        // Watch mode: continuously monitor and re-run tests
        match test_runner::watch_tests(options) {
            Ok(()) => 0,
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        }
    } else {
        // Normal mode: run tests once
        // Only print header for non-JSON output
        if !matches!(options.format, test_runner::OutputFormat::Json) {
            println!("Simple Test Runner v{}", version());
            println!();
        }

        let format = options.format;
        let result = test_runner::run_tests(options);
        test_runner::print_summary(&result, format);

        if result.success() {
            0
        } else {
            1
        }
    }
}

/// Handle check command (impl)
fn handle_check_impl(args: &[String]) -> i32 {
    if args.len() < 2 {
        eprintln!("error: check requires at least one source file");
        eprintln!("Usage: simple check <file.spl> [options]");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --json     Output JSON format for tooling");
        eprintln!("  --verbose  Show additional details");
        eprintln!("  --quiet    Only show errors, no progress");
        eprintln!();
        eprintln!("Examples:");
        eprintln!("  simple check program.spl");
        eprintln!("  simple check src/*.spl");
        eprintln!("  simple check --json program.spl");
        return 1;
    }

    // Parse options
    let json = args.iter().any(|a| a == "--json");
    let verbose = args.iter().any(|a| a == "--verbose" || a == "-v");
    let quiet = args.iter().any(|a| a == "--quiet" || a == "-q");

    let options = CheckOptions { json, verbose, quiet };

    // Collect file paths (skip "check" and flags)
    let files: Vec<PathBuf> = args[1..]
        .iter()
        .filter(|a| !a.starts_with("--") && !a.starts_with("-"))
        .map(PathBuf::from)
        .collect();

    if files.is_empty() {
        eprintln!("error: no files specified");
        return 1;
    }

    run_check(&files, options)
}

/// Handle default case: file execution
fn handle_file_execution(
    first: &str,
    args: &[String],
    gc_log: bool,
    gc_off: bool,
    prefetch_handle: Option<simple_driver::PrefetchHandle>,
    metrics: &mut simple_driver::StartupMetrics,
) -> i32 {
    // PHASE 3: Wait for prefetching to complete before using files
    wait_for_prefetch(prefetch_handle, metrics);

    // Assume it's a file to run
    let path = PathBuf::from(first);
    if path.exists() {
        // Collect remaining arguments to pass to the Simple program
        // Filter out:
        // - GC flags (internal to runtime)
        // - Leading "--" separator (convention for separating runtime args from script args)
        let program_args: Vec<String> = args
            .iter()
            .skip(1) // Skip the file path
            .filter(|a| !a.starts_with("--gc")) // Skip GC flags
            .skip_while(|a| *a == "--") // Skip leading "--" separator
            .cloned()
            .collect();

        // Prepend the file path as argv[0]
        let mut full_args = vec![path.to_string_lossy().to_string()];
        full_args.extend(program_args);

        // Record file execution phase
        let exec_start = std::time::Instant::now();
        let exit_code = run_file_with_args(&path, gc_log, gc_off, full_args);
        metrics.record(simple_driver::StartupPhase::FileExecution, exec_start.elapsed());
        exit_code
    } else {
        eprintln!("error: file not found: {}", path.display());
        eprintln!();
        print_help();
        1
    }
}

/// Original Rust sspec-docgen implementation (fallback)
fn run_sspec_docgen_rust(args: &[String]) -> i32 {
    // Parse arguments
    let mut output_dir = PathBuf::from("doc/spec");
    let mut spec_files: Vec<PathBuf> = Vec::new();

    let mut i = 1; // Skip command name
    while i < args.len() {
        let arg = &args[i];
        if arg == "--output" || arg == "-o" {
            if i + 1 < args.len() {
                output_dir = PathBuf::from(&args[i + 1]);
                i += 2;
                continue;
            }
        } else if arg == "--help" || arg == "-h" {
            println!("SSpec Documentation Generator");
            println!();
            println!("Usage: simple sspec-docgen <spec_file>... [--output <dir>]");
            println!();
            println!("Arguments:");
            println!("  <spec_file>...    One or more sspec files (*_spec.spl)");
            println!();
            println!("Options:");
            println!("  --output <dir>    Output directory (default: doc/spec)");
            println!("  -o <dir>          Short form of --output");
            println!("  --help, -h        Show this help message");
            return 0;
        } else if !arg.starts_with("-") {
            spec_files.push(PathBuf::from(arg));
        }
        i += 1;
    }

    if spec_files.is_empty() {
        eprintln!("error: No spec files provided");
        eprintln!();
        eprintln!("Usage: simple sspec-docgen <spec_file>... [--output <dir>]");
        return 1;
    }

    // Call the sspec_docgen module
    match sspec_docgen::generate_sspec_docs(&spec_files, &output_dir) {
        Ok(stats) => {
            println!(
                "\n✓ Generated {} docs ({} complete, {} stubs)",
                stats.total_specs, stats.specs_with_docs, stats.specs_without_docs
            );
            0
        }
        Err(e) => {
            eprintln!("✗ Failed to generate documentation: {}", e);
            1
        }
    }
}
