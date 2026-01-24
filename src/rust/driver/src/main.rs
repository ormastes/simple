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
use simple_driver::cli::llm_tools::{run_context, run_diff, run_mcp};
use simple_driver::cli::migrate::run_migrate;
use simple_driver::cli::repl::run_repl;
use simple_driver::cli::sandbox::{apply_sandbox, parse_sandbox_config};
use simple_driver::cli::test_runner;
use simple_driver::cli::verify::run_verify;
#[cfg(feature = "tui")]
use simple_driver::cli::tui::run_tui_repl;
use simple_driver::cli::doc_gen::{run_feature_gen, run_spec_gen, run_task_gen, run_todo_gen, run_todo_scan};
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
        "lint" => run_lint(&args),
        "fmt" => run_fmt(&args),
        "check" => handle_check(&args),

        // Localization
        "i18n" => simple_driver::cli::i18n::run_i18n(&args),

        // Migration and tooling
        "migrate" => run_migrate(&args),
        "mcp" => run_mcp(&args),
        "diff" => run_diff(&args),
        "context" => run_context(&args),

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

        // Dashboard
        "dashboard" => {
            // TODO: Execute Simple dashboard app
            // For now, print placeholder
            println!("Dashboard command - implementation in progress");
            println!("Usage: simple dashboard [status|collect|help]");
            0
        }

        // Verification
        "verify" => run_verify(&args, global_flags.gc_log, global_flags.gc_off),

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

/// Handle test command with watch support
fn handle_test(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
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
        let program_args: Vec<String> = args
            .iter()
            .skip(1) // Skip the file path
            .filter(|a| !a.starts_with("--gc")) // Skip GC flags
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
