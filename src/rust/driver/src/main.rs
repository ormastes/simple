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

fn main() {
    // Initialize metrics and startup tracking
    let (metrics_enabled, mut metrics) = init_metrics();

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

    // Route commands to handlers
    let exit_code = match first.as_str() {
        // Help and version
        "-h" | "--help" => {
            print_help();
            0
        }
        "-v" | "--version" => {
            print_version();
            0
        }

        // Code execution
        "-c" => {
            if args.len() < 2 {
                eprintln!("error: -c requires a code argument");
                std::process::exit(1);
            }
            run_code(&args[1], global_flags.gc_log, global_flags.gc_off)
        }

        // Compilation commands
        "compile" => handle_compile(&args),
        "targets" => handle_targets(),
        "linkers" => handle_linkers(),

        // Web framework
        "web" => handle_web(&args),

        // File watching
        "watch" => {
            if args.len() < 2 {
                eprintln!("error: watch requires a source file");
                eprintln!("Usage: simple watch <file.spl>");
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            watch_file(&path)
        }

        // Testing
        "test" => handle_test(&args, global_flags.gc_log, global_flags.gc_off),

        // Code quality
        "lint" => handle_lint(&args, global_flags.gc_log, global_flags.gc_off),
        "fmt" => handle_fmt(&args, global_flags.gc_log, global_flags.gc_off),
        "check" => handle_check(&args),

        // Localization
        "i18n" => simple_driver::cli::i18n::run_i18n(&args),

        // Migration and tooling
        "migrate" => run_migrate(&args),
        "mcp" => handle_mcp(&args, global_flags.gc_log, global_flags.gc_off),
        "diff" => run_diff(&args),
        "context" => handle_context(&args, global_flags.gc_log, global_flags.gc_off),
        "constr" => run_constr(&args),

        // Analysis
        "query" => run_query(&args),
        "info" => run_info(&args),

        // Auditing
        "spec-coverage" => run_spec_coverage(&args),
        "replay" => run_replay(&args),

        // Code generation
        "gen-lean" => run_gen_lean(&args),
        "feature-gen" => run_feature_gen(&args),
        "task-gen" => run_task_gen(&args),
        "spec-gen" => run_spec_gen(&args),
        "todo-scan" => run_todo_scan(&args),
        "todo-gen" => run_todo_gen(&args),
        "sspec-docgen" => handle_sspec_docgen(&args, global_flags.gc_log, global_flags.gc_off),

        // Brief view - LLM-friendly code overview
        "brief" => handle_brief(&args, global_flags.gc_log, global_flags.gc_off),

        // Dashboard
        "dashboard" => handle_dashboard_dispatch(&args, global_flags.gc_log, global_flags.gc_off),

        // Verification
        "verify" => handle_verify(&args, global_flags.gc_log, global_flags.gc_off),

        // Qualified ignore management
        "qualify-ignore" => {
            let qi_args = parse_qualify_ignore_args(&args[1..]);
            match handle_qualify_ignore(qi_args) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("error: {}", e);
                    1
                }
            }
        }

        // Diagram generation
        "diagram" => handle_diagram(&args),

        // Package management
        "init" => handle_init(&args),
        "add" => handle_add(&args),
        "remove" => handle_remove(&args),
        "install" => handle_install(),
        "update" => handle_update(&args),
        "list" => handle_list(),
        "tree" => handle_tree(),
        "cache" => handle_cache(&args),

        // Environment management
        "env" => handle_env(&args),

        // Lock file management
        "lock" => handle_lock(&args),

        // Coverage
        "coverage" => handle_coverage(&args, global_flags.gc_log, global_flags.gc_off),

        // Dependency graph
        "depgraph" => handle_depgraph(&args, global_flags.gc_log, global_flags.gc_off),

        // LSP server
        "lsp" => handle_lsp(&args, global_flags.gc_log, global_flags.gc_off),

        // DAP server
        "dap" => handle_dap(&args, global_flags.gc_log, global_flags.gc_off),

        // Explicit run command
        "run" => handle_run(&args, global_flags.gc_log, global_flags.gc_off),

        // Default: assume it's a file to run
        _ => handle_file_execution(
            first,
            &args,
            global_flags.gc_log,
            global_flags.gc_off,
            prefetch_handle,
            &mut metrics,
        ),
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
    let mut full_args = vec!["simple_old".to_string(), app_path.to_string_lossy().to_string()];
    full_args.extend(args[1..].iter().cloned());
    Some(run_file_with_args(&app_path, gc_log, gc_off, full_args))
}

/// Handle test command - dispatch to Simple runner or Rust runner
fn handle_test(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    // Recursion guard - child processes use Rust runner directly
    if std::env::var("SIMPLE_TEST_RUNNER_RUST").is_ok() {
        return handle_test_rust(args, gc_log, gc_off);
    }

    // Features requiring Rust runner (advanced features not yet in Simple runner)
    let needs_rust = args[1..].iter().any(|a| {
        a == "--watch" || a == "--parallel" || a == "-p"
            || a.starts_with("--doctest") || a == "--json"
            || a.starts_with("--diagram") || a.starts_with("--seq-")
            || a == "--rust-tests" || a == "--list-runs"
            || a == "--cleanup-runs" || a.starts_with("--prune-runs")
            || a == "--capture-screenshots" || a == "--full-parallel"
            || a == "--rust-ignored"
    });

    if needs_rust {
        return handle_test_rust(args, gc_log, gc_off);
    }

    // Dispatch to Simple runner
    if let Some(app_path) = resolve_app_path("src/app/test_runner_new/main.spl") {
        let mut full_args = vec![
            "simple_old".to_string(),
            app_path.to_string_lossy().to_string(),
        ];
        full_args.extend(args[1..].iter().cloned());
        if gc_log {
            full_args.push("--gc-log".to_string());
        }
        if gc_off {
            full_args.push("--gc=off".to_string());
        }
        return run_file_with_args(&app_path, gc_log, gc_off, full_args);
    }

    handle_test_rust(args, gc_log, gc_off)
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

/// Handle check command
fn handle_check(args: &[String]) -> i32 {
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

/// Handle fmt command - dispatch to Simple formatter or Rust formatter
fn handle_fmt(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_FMT_RUST").is_ok() {
        return run_fmt(args);
    }
    let needs_rust = args[1..].iter().any(|a| a == "--json");
    if needs_rust {
        return run_fmt(args);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/formatter/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_fmt(args)
}

/// Handle lint command - dispatch to Simple linter or Rust linter
fn handle_lint(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_LINT_RUST").is_ok() {
        return run_lint(args);
    }
    let needs_rust = args[1..].iter().any(|a| a == "--json" || a == "--fix");
    if needs_rust {
        return run_lint(args);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/lint/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_lint(args)
}

/// Handle sspec-docgen command - dispatch to Simple app or Rust implementation
fn handle_sspec_docgen(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_SSPEC_DOCGEN_RUST").is_ok() {
        return run_sspec_docgen_rust(args);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/sspec_docgen/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_sspec_docgen_rust(args)
}

/// Handle context command - dispatch to Simple app or Rust implementation
fn handle_context(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_CONTEXT_RUST").is_ok() {
        return run_context(args);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/context/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_context(args)
}

/// Handle mcp command - dispatch to Simple app or Rust implementation
fn handle_mcp(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_MCP_RUST").is_ok() {
        return run_mcp(args);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/mcp/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_mcp(args)
}

/// Handle verify command - dispatch to Simple app or Rust implementation
fn handle_verify(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_VERIFY_RUST").is_ok() {
        return run_verify(args, gc_log, gc_off);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/verify/main.spl", args, gc_log, gc_off) {
        return code;
    }
    run_verify(args, gc_log, gc_off)
}

/// Handle dashboard command - dispatch to Simple app or Rust implementation
fn handle_dashboard_dispatch(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if std::env::var("SIMPLE_DASHBOARD_RUST").is_ok() {
        return handle_dashboard(args, gc_log, gc_off);
    }
    if let Some(code) = dispatch_to_simple_app("src/app/dashboard/main.spl", args, gc_log, gc_off) {
        return code;
    }
    handle_dashboard(args, gc_log, gc_off)
}

/// Handle coverage command - dispatch to Simple app
fn handle_coverage(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if let Some(code) = dispatch_to_simple_app("src/app/coverage/main.spl", args, gc_log, gc_off) {
        return code;
    }
    eprintln!("error: coverage app not found (install Simple or run from project root)");
    1
}

/// Handle depgraph command - dispatch to Simple app
fn handle_depgraph(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if let Some(code) = dispatch_to_simple_app("src/app/depgraph/main.spl", args, gc_log, gc_off) {
        return code;
    }
    eprintln!("error: depgraph app not found (install Simple or run from project root)");
    1
}

/// Handle lsp command - dispatch to Simple app
fn handle_lsp(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if let Some(code) = dispatch_to_simple_app("src/app/lsp/main.spl", args, gc_log, gc_off) {
        return code;
    }
    eprintln!("error: lsp app not found (install Simple or run from project root)");
    1
}

/// Handle dap command - dispatch to Simple app
fn handle_dap(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if let Some(code) = dispatch_to_simple_app("src/app/dap/main.spl", args, gc_log, gc_off) {
        return code;
    }
    eprintln!("error: dap app not found (install Simple or run from project root)");
    1
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
