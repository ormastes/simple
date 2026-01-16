//! Simple Language - Unified CLI
//!
//! Usage like Python:
//!   simple              - Start interactive REPL
//!   simple file.spl     - Run source file
//!   simple file.smf     - Run compiled binary
//!   simple -c "code"    - Run code string
//!   simple compile src.spl [-o out.smf]  - Compile to SMF
//!   simple watch file.spl  - Watch and auto-recompile

use std::env;
use std::path::PathBuf;

// Helper to print startup metrics and exit
fn exit_with_metrics(code: i32, metrics: &simple_driver::StartupMetrics) -> ! {
    if simple_driver::metrics_enabled() {
        metrics.print_report();
    }
    std::process::exit(code)
}

use simple_common::target::{Target, TargetArch};
use simple_driver::runner::Runner;
use simple_driver::watcher::watch;
use simple_driver::CompileOptions;
use simple_log;
use simple_pkg::commands::{add, cache_cmd, init, install, list, update};

use simple_driver::cli::analysis::{run_info, run_query};
use simple_driver::cli::audit::{run_replay, run_spec_coverage};
use simple_driver::cli::basic::{create_runner, run_code, run_file, run_file_with_args, watch_file};
use simple_driver::cli::check::{CheckOptions, run_check};
use simple_driver::cli::code_quality::{run_fmt, run_lint};
use simple_driver::cli::compile::{compile_file, list_linkers, list_targets};
use simple_driver::cli::diagram_gen::{parse_diagram_args, print_diagram_help};
use simple_driver::cli::doc_gen::{run_feature_gen, run_spec_gen, run_task_gen};
use simple_driver::cli::gen_lean::run_gen_lean;
use simple_driver::cli::help::{print_help, print_version, version};
use simple_driver::cli::llm_tools::{run_context, run_diff, run_mcp};
use simple_driver::cli::migrate::run_migrate;
use simple_driver::cli::repl::run_repl;
use simple_driver::cli::sandbox::{apply_sandbox, parse_sandbox_config};
use simple_driver::cli::test_runner;
#[cfg(feature = "tui")]
use simple_driver::cli::tui::run_tui_repl;
use simple_driver::cli::web::{web_build, web_features, web_init, web_serve, WebBuildOptions, WebServeOptions};

fn main() {
    // Check for --startup-metrics flag early (#1997)
    let enable_startup_metrics = env::args().any(|a| a == "--startup-metrics");
    if enable_startup_metrics {
        simple_driver::enable_metrics();
    }

    let mut metrics = simple_driver::StartupMetrics::new();
    metrics.start();

    // PHASE 1: Early startup - parse args and start prefetching before runtime init
    let early_start = std::time::Instant::now();
    let early_config = simple_driver::parse_early_args(env::args().skip(1));
    metrics.record(simple_driver::StartupPhase::EarlyArgParse, early_start.elapsed());

    // Start prefetching input files in background (if enabled)
    let prefetch_start = std::time::Instant::now();
    let prefetch_handle = if early_config.enable_prefetch && !early_config.input_files.is_empty() {
        simple_driver::prefetch_files(&early_config.input_files).ok()
    } else {
        None
    };
    if prefetch_handle.is_some() {
        metrics.record(simple_driver::StartupPhase::FilePrefetch, prefetch_start.elapsed());
    }

    // Pre-allocate resources based on app type
    let resource_start = std::time::Instant::now();
    let _resources =
        simple_driver::PreAllocatedResources::allocate(early_config.app_type, &early_config.window_hints).ok();
    metrics.record(
        simple_driver::StartupPhase::ResourceAllocation,
        resource_start.elapsed(),
    );

    // PHASE 2: Normal initialization (happens in parallel with prefetching)
    simple_driver::cli::init::init_runtime(&mut metrics);

    // Reconstruct args from early config for compatibility with existing code
    let args: Vec<String> = early_config
        .remaining_args
        .iter()
        .map(|s| s.to_string_lossy().to_string())
        .collect();

    // Parse global flags
    let gc_log = args.iter().any(|a| a == "--gc-log");
    let gc_off = args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF");
    let use_notui = args.iter().any(|a| a == "--notui");
    let macro_trace = args.iter().any(|a| a == "--macro-trace");
    let debug_mode = args.iter().any(|a| a == "--debug");

    // Enable macro tracing if requested
    if macro_trace {
        simple_compiler::set_macro_trace(true);
    }

    // Enable debug mode if requested (for dprint function)
    if debug_mode {
        simple_compiler::set_debug_mode(true);
    }

    // Parse and apply sandbox configuration before running code (#916-919)
    let sandbox_start = std::time::Instant::now();
    if let Some(sandbox_config) = parse_sandbox_config(&args) {
        if let Err(e) = apply_sandbox(&sandbox_config) {
            eprintln!("warning: {}", e);
            eprintln!("Continuing without full sandboxing...");
        }
        metrics.record(simple_driver::StartupPhase::SandboxSetup, sandbox_start.elapsed());
    }

    // Filter out flags (GC and sandbox flags) and their values
    let mut filtered_args = Vec::new();
    let mut skip_next = false;
    for arg in args.iter() {
        if skip_next {
            skip_next = false;
            continue;
        }

        if arg.starts_with("--gc") {
            continue;
        }

        if arg == "--notui" {
            continue;
        }

        if arg == "--startup-metrics" {
            continue;
        }

        if arg == "--macro-trace" {
            continue;
        }

        if arg == "--debug" {
            continue;
        }

        if arg == "--sandbox" || arg == "--no-network" {
            continue;
        }

        // These flags take a value, so skip the next argument too
        if arg == "--time-limit"
            || arg == "--memory-limit"
            || arg == "--fd-limit"
            || arg == "--thread-limit"
            || arg == "--network-allow"
            || arg == "--network-block"
            || arg == "--read-only"
            || arg == "--read-write"
        {
            skip_next = true;
            continue;
        }

        filtered_args.push(arg.clone());
    }
    let args = filtered_args;

    // No arguments -> REPL (TUI by default if feature enabled)
    if args.is_empty() {
        let runner = create_runner(gc_log, gc_off);

        #[cfg(feature = "tui")]
        if !use_notui {
            // TUI is default when feature is enabled
            std::process::exit(run_tui_repl(version(), runner));
        }

        // Use Normal mode if --notui flag is set or TUI feature is disabled
        std::process::exit(run_repl(version(), runner));
    }

    let first = &args[0];

    // Handle flags
    match first.as_str() {
        "-h" | "--help" => {
            print_help();
            std::process::exit(0);
        }
        "-v" | "--version" => {
            print_version();
            std::process::exit(0);
        }
        "-c" => {
            if args.len() < 2 {
                eprintln!("error: -c requires a code argument");
                std::process::exit(1);
            }
            std::process::exit(run_code(&args[1], gc_log, gc_off));
        }
        "compile" => {
            use simple_compiler::linker::NativeLinker;

            if args.len() < 2 {
                eprintln!("error: compile requires a source file");
                eprintln!("Usage: simple compile <source.spl> [-o <output>] [--native] [--target <arch>] [--linker <name>] [--snapshot]");
                eprintln!();
                eprintln!("Options:");
                eprintln!("  -o <output>         Output file (default: source.smf or source for --native)");
                eprintln!("  --native            Compile to standalone native binary (ELF/PE)");
                eprintln!("  --target <arch>     Target architecture (x86_64, aarch64, etc.)");
                eprintln!("  --linker <name>     Native linker to use (mold, lld, ld)");
                eprintln!("  --layout-optimize   Enable 4KB page layout optimization");
                eprintln!("  --strip             Strip symbols from output");
                eprintln!("  --pie               Create position-independent executable (default)");
                eprintln!("  --no-pie            Disable position-independent executable");
                eprintln!("  --shared            Create shared library (.so/.dll)");
                eprintln!("  --map               Generate linker map file");
                eprintln!("  --snapshot          Create JJ snapshot with build state");
                std::process::exit(1);
            }
            let source = PathBuf::from(&args[1]);
            let output = args
                .iter()
                .position(|a| a == "-o")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from);

            // Parse --native flag
            let native = args.iter().any(|a| a == "--native");

            // Parse --target flag
            let target = args
                .iter()
                .position(|a| a == "--target")
                .and_then(|i| args.get(i + 1))
                .map(|s| {
                    s.parse::<TargetArch>()
                        .map_err(|e| {
                            eprintln!("error: {}", e);
                            std::process::exit(1);
                        })
                        .unwrap()
                })
                .map(|arch| Target::new(arch, simple_common::target::TargetOS::host()));

            // Parse --linker flag
            let linker = args
                .iter()
                .position(|a| a == "--linker")
                .and_then(|i| args.get(i + 1))
                .map(|s| {
                    NativeLinker::from_name(s).unwrap_or_else(|| {
                        eprintln!("error: unknown linker '{}'. Available: mold, lld, ld", s);
                        std::process::exit(1);
                    })
                });

            // Print linker info if specified
            if let Some(l) = linker {
                if !NativeLinker::is_available(l) {
                    eprintln!("warning: linker '{}' not found on system", l.name());
                } else if native {
                    println!("Using linker: {}", l.name());
                }
            }

            // Parse --snapshot flag
            let snapshot = args.iter().any(|a| a == "--snapshot");

            // Parse native binary options
            let layout_optimize = args.iter().any(|a| a == "--layout-optimize");
            let strip = args.iter().any(|a| a == "--strip");
            let pie = !args.iter().any(|a| a == "--no-pie");
            let shared = args.iter().any(|a| a == "--shared");
            let generate_map = args.iter().any(|a| a == "--map");

            // Parse compile options (including emit flags)
            let options = CompileOptions::from_args(&args);

            if native {
                // Compile to standalone native binary
                std::process::exit(simple_driver::cli::compile::compile_file_native(
                    &source,
                    output,
                    target,
                    linker,
                    layout_optimize,
                    strip,
                    pie,
                    shared,
                    generate_map,
                ));
            } else {
                // Compile to SMF (existing behavior)
                std::process::exit(compile_file(&source, output, target, snapshot, options));
            }
        }
        "targets" => {
            std::process::exit(list_targets());
        }
        "linkers" => {
            std::process::exit(list_linkers());
        }
        "web" => {
            if args.len() < 2 {
                eprintln!("Simple Web Framework - Compile .sui files to HTML + WASM");
                eprintln!();
                eprintln!("Usage:");
                eprintln!("  simple web build <file.sui> [options]  - Build web application");
                eprintln!("  simple web serve <file.sui> [options]  - Start development server");
                eprintln!("  simple web init <name>                 - Create new web project");
                eprintln!("  simple web features                    - List supported features");
                eprintln!();
                eprintln!("Build options:");
                eprintln!("  -o, --output <dir>     Output directory (default: public/)");
                eprintln!("  --module <name>        WASM module name (default: app)");
                eprintln!("  --optimize             Optimize WASM binary");
                eprintln!("  --minify               Minify HTML output");
                eprintln!();
                eprintln!("Serve options:");
                eprintln!("  -p, --port <port>      Port number (default: 8000)");
                eprintln!("  --no-watch             Disable file watching");
                eprintln!("  --open                 Open browser automatically");
                eprintln!();
                std::process::exit(1);
            }

            match args[1].as_str() {
                "build" => {
                    if args.len() < 3 {
                        eprintln!("error: web build requires a .sui file");
                        eprintln!("Usage: simple web build <file.sui> [options]");
                        std::process::exit(1);
                    }

                    let source = PathBuf::from(&args[2]);

                    // Parse options
                    let output_dir = args
                        .iter()
                        .position(|a| a == "-o" || a == "--output")
                        .and_then(|i| args.get(i + 1))
                        .map(PathBuf::from)
                        .unwrap_or_else(|| PathBuf::from("public"));

                    let module_name = args
                        .iter()
                        .position(|a| a == "--module")
                        .and_then(|i| args.get(i + 1))
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| "app".to_string());

                    let optimize = args.iter().any(|a| a == "--optimize");
                    let minify_html = args.iter().any(|a| a == "--minify");

                    let options = WebBuildOptions {
                        output_dir,
                        module_name,
                        optimize,
                        minify_html,
                    };

                    std::process::exit(web_build(&source, options));
                }
                "init" => {
                    if args.len() < 3 {
                        eprintln!("error: web init requires a project name");
                        eprintln!("Usage: simple web init <project-name>");
                        std::process::exit(1);
                    }

                    let project_name = &args[2];
                    std::process::exit(web_init(project_name));
                }
                "features" => {
                    std::process::exit(web_features());
                }
                "serve" => {
                    if args.len() < 3 {
                        eprintln!("error: web serve requires a .sui file");
                        eprintln!("Usage: simple web serve <file.sui> [options]");
                        std::process::exit(1);
                    }

                    let source = PathBuf::from(&args[2]);

                    // Parse build options
                    let output_dir = args
                        .iter()
                        .position(|a| a == "-o" || a == "--output")
                        .and_then(|i| args.get(i + 1))
                        .map(PathBuf::from)
                        .unwrap_or_else(|| PathBuf::from("public"));

                    let module_name = args
                        .iter()
                        .position(|a| a == "--module")
                        .and_then(|i| args.get(i + 1))
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| "app".to_string());

                    let build_options = WebBuildOptions {
                        output_dir,
                        module_name,
                        optimize: false, // Dev server: no optimization for speed
                        minify_html: false,
                    };

                    // Parse serve options
                    let port = args
                        .iter()
                        .position(|a| a == "-p" || a == "--port")
                        .and_then(|i| args.get(i + 1))
                        .and_then(|s| s.parse::<u16>().ok())
                        .unwrap_or(8000);

                    let watch = !args.iter().any(|a| a == "--no-watch");
                    let open = args.iter().any(|a| a == "--open");

                    let serve_options = WebServeOptions { port, watch, open };

                    std::process::exit(web_serve(&source, build_options, serve_options));
                }
                _ => {
                    eprintln!("error: unknown web subcommand '{}'", args[1]);
                    eprintln!("Available: build, init, features, serve");
                    std::process::exit(1);
                }
            }
        }
        "watch" => {
            if args.len() < 2 {
                eprintln!("error: watch requires a source file");
                eprintln!("Usage: simple watch <file.spl>");
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            std::process::exit(watch_file(&path));
        }
        "test" => {
            // Parse test options from remaining args
            let test_args: Vec<String> = args[1..].to_vec();
            let mut options = test_runner::parse_test_args(&test_args);
            options.gc_log = gc_log;
            options.gc_off = gc_off;

            // Check if watch mode is enabled
            if options.watch {
                // Watch mode: continuously monitor and re-run tests
                match test_runner::watch_tests(options) {
                    Ok(()) => std::process::exit(0),
                    Err(e) => {
                        eprintln!("error: {}", e);
                        std::process::exit(1);
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

                std::process::exit(if result.success() { 0 } else { 1 });
            }
        }
        "lint" => {
            std::process::exit(run_lint(&args));
        }
        "fmt" => {
            std::process::exit(run_fmt(&args));
        }
        "check" => {
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
                std::process::exit(1);
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
                std::process::exit(1);
            }

            std::process::exit(run_check(&files, options));
        }
        "i18n" => {
            std::process::exit(simple_driver::cli::i18n::run_i18n(&args));
        }
        "migrate" => {
            std::process::exit(run_migrate(&args));
        }
        "mcp" => {
            std::process::exit(run_mcp(&args));
        }
        "diff" => {
            std::process::exit(run_diff(&args));
        }
        "context" => {
            std::process::exit(run_context(&args));
        }
        "query" => {
            std::process::exit(run_query(&args));
        }
        "info" => {
            std::process::exit(run_info(&args));
        }
        "spec-coverage" => {
            std::process::exit(run_spec_coverage(&args));
        }
        "gen-lean" => {
            std::process::exit(run_gen_lean(&args));
        }
        "feature-gen" => {
            std::process::exit(run_feature_gen(&args));
        }
        "task-gen" => {
            std::process::exit(run_task_gen(&args));
        }
        "spec-gen" => {
            std::process::exit(run_spec_gen(&args));
        }
        "replay" => {
            std::process::exit(run_replay(&args));
        }
        "diagram" => {
            // Check for help
            if args.iter().any(|a| a == "-h" || a == "--help") {
                print_diagram_help();
                std::process::exit(0);
            }

            // Parse diagram generation options
            let diagram_args: Vec<String> = args[1..].to_vec();
            let options = parse_diagram_args(&diagram_args);

            // For now, diagram command generates from profile data or loads from file
            // This is a placeholder - actual implementation would hook into test runner
            // or load recorded profile data
            println!("Diagram generation options:");
            println!("  Types: {:?}", options.diagram_types);
            println!("  Output: {}", options.output_dir.display());
            println!("  Name: {}", options.test_name);
            if !options.include_patterns.is_empty() {
                println!("  Include: {:?}", options.include_patterns);
            }
            if !options.exclude_patterns.is_empty() {
                println!("  Exclude: {:?}", options.exclude_patterns);
            }

            // TODO: [driver][P3] Load profile data and generate diagrams
            // For now, just show the help to indicate proper usage
            println!();
            println!("To generate diagrams, use with test command:");
            println!("  simple test --seq-diagram my_test.spl");
            println!();
            println!("Or run profiler directly:");
            println!("  simple diagram --help");

            std::process::exit(0);
        }
        "init" => {
            let name = args.get(1).map(|s| s.as_str());
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            match init::init_project(&dir, name) {
                Ok(()) => {
                    println!(
                        "Created new Simple project{}",
                        name.map(|n| format!(" '{}'", n)).unwrap_or_default()
                    );
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "add" => {
            if args.len() < 2 {
                eprintln!("error: add requires a package name");
                eprintln!("Usage: simple add <pkg> [version] [--path <path>] [--git <url>] [--dev]");
                std::process::exit(1);
            }
            let pkg_name = &args[1];
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

            // Parse options
            let mut options = add::AddOptions::default();
            let mut i = 2;
            while i < args.len() {
                match args[i].as_str() {
                    "--path" => {
                        i += 1;
                        if i < args.len() {
                            options.path = Some(args[i].clone());
                        }
                    }
                    "--git" => {
                        i += 1;
                        if i < args.len() {
                            options.git = Some(args[i].clone());
                        }
                    }
                    "--branch" => {
                        i += 1;
                        if i < args.len() {
                            options.branch = Some(args[i].clone());
                        }
                    }
                    "--tag" => {
                        i += 1;
                        if i < args.len() {
                            options.tag = Some(args[i].clone());
                        }
                    }
                    "--rev" => {
                        i += 1;
                        if i < args.len() {
                            options.rev = Some(args[i].clone());
                        }
                    }
                    "--dev" => {
                        options.dev = true;
                    }
                    arg if !arg.starts_with("-") && options.version.is_none() => {
                        options.version = Some(arg.to_string());
                    }
                    _ => {}
                }
                i += 1;
            }

            match add::add_dependency(&dir, pkg_name, options) {
                Ok(()) => {
                    println!("Added dependency '{}'", pkg_name);
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "remove" => {
            if args.len() < 2 {
                eprintln!("error: remove requires a package name");
                eprintln!("Usage: simple remove <pkg> [--dev]");
                std::process::exit(1);
            }
            let pkg_name = &args[1];
            let dev = args.iter().any(|a| a == "--dev");
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

            match add::remove_dependency(&dir, pkg_name, dev) {
                Ok(true) => {
                    println!("Removed dependency '{}'", pkg_name);
                    std::process::exit(0);
                }
                Ok(false) => {
                    eprintln!("error: dependency '{}' not found", pkg_name);
                    std::process::exit(1);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "install" => {
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            match install::install_dependencies(&dir) {
                Ok(result) => {
                    if result.installed == 0 && result.up_to_date == 0 && result.skipped == 0 {
                        println!("No dependencies to install");
                    } else {
                        if result.installed > 0 {
                            println!("Installed {} package(s)", result.installed);
                        }
                        if result.up_to_date > 0 {
                            println!("{} package(s) up to date", result.up_to_date);
                        }
                        if result.skipped > 0 {
                            println!("{} package(s) skipped (git/registry not yet supported)", result.skipped);
                        }
                    }
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "update" => {
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let pkg_name = args.get(1);

            let result = match pkg_name {
                Some(name) => update::update_package(&dir, name),
                None => update::update_all(&dir),
            };

            match result {
                Ok(r) => {
                    if r.updated.is_empty() {
                        println!("All dependencies up to date");
                    } else {
                        println!("Updated: {}", r.updated.join(", "));
                    }
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "list" => {
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

            match list::list_dependencies(&dir) {
                Ok(packages) => {
                    if packages.is_empty() {
                        println!("No dependencies installed");
                    } else {
                        for pkg in packages {
                            let status = if pkg.is_linked { "" } else { " (not linked)" };
                            println!("{} ({}) [{}]{}", pkg.name, pkg.version, pkg.source_type, status);
                        }
                    }
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "tree" => {
            let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

            match list::dependency_tree(&dir) {
                Ok(tree) => {
                    // Print root
                    println!("{} ({})", tree.name, tree.version);
                    for (i, child) in tree.children.iter().enumerate() {
                        let is_last = i == tree.children.len() - 1;
                        print!("{}", list::format_tree(child, "", is_last));
                    }
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "cache" => {
            let subcommand = args.get(1).map(|s| s.as_str());

            match subcommand {
                Some("clean") => match cache_cmd::cache_clean() {
                    Ok(size) => {
                        println!("Cleaned {} from cache", cache_cmd::format_size(size));
                        std::process::exit(0);
                    }
                    Err(e) => {
                        eprintln!("error: {}", e);
                        std::process::exit(1);
                    }
                },
                Some("list") => match cache_cmd::cache_list() {
                    Ok(packages) => {
                        if packages.is_empty() {
                            println!("Cache is empty");
                        } else {
                            for (name, version) in packages {
                                println!("{} ({})", name, version);
                            }
                        }
                        std::process::exit(0);
                    }
                    Err(e) => {
                        eprintln!("error: {}", e);
                        std::process::exit(1);
                    }
                },
                Some("info") | None => match cache_cmd::cache_info() {
                    Ok(info) => {
                        println!("Cache location: {}", info.location.display());
                        println!("Total size: {}", cache_cmd::format_size(info.size_bytes));
                        println!("Packages: {}", info.package_count);
                        println!("Git repos: {}", info.git_repo_count);
                        std::process::exit(0);
                    }
                    Err(e) => {
                        eprintln!("error: {}", e);
                        std::process::exit(1);
                    }
                },
                Some(cmd) => {
                    eprintln!("error: unknown cache subcommand: {}", cmd);
                    eprintln!("Usage: simple cache [info|list|clean]");
                    std::process::exit(1);
                }
            }
        }
        "run" => {
            // Explicit run command (for compatibility)
            if args.len() < 2 {
                eprintln!("error: run requires a file");
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            std::process::exit(run_file(&path, gc_log, gc_off));
        }
        _ => {
            // PHASE 3: Wait for prefetching to complete before using files
            let prefetch_wait_start = std::time::Instant::now();
            if let Some(handle) = prefetch_handle {
                let _ = handle.wait(); // Ignore errors, prefetch is best-effort
                metrics.record(simple_driver::StartupPhase::PrefetchWait, prefetch_wait_start.elapsed());
            }

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
                exit_with_metrics(exit_code, &metrics);
            } else {
                eprintln!("error: file not found: {}", path.display());
                eprintln!();
                print_help();
                exit_with_metrics(1, &metrics);
            }
        }
    }
}
