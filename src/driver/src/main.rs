//! Simple Language - Unified CLI
//!
//! Usage like Python:
//!   simple              - Start interactive REPL
//!   simple file.spl     - Run source file
//!   simple file.smf     - Run compiled binary
//!   simple -c "code"    - Run code string
//!   simple compile src.spl [-o out.smf]  - Compile to SMF
//!   simple watch file.spl  - Watch and auto-recompile

mod cli;

use std::env;
use std::path::PathBuf;

use simple_common::target::{Target, TargetArch};
use simple_driver::runner::Runner;
use simple_driver::watcher::watch;
use simple_driver::CompileOptions;
use simple_log;
use simple_pkg::commands::{add, cache_cmd, init, install, list, update};

use cli::analysis::{run_info, run_query};
use cli::audit::{run_replay, run_spec_coverage};
use cli::basic::{create_runner, run_code, run_file, run_file_with_args, watch_file};
use cli::code_quality::{run_fmt, run_lint};
use cli::compile::{compile_file, list_linkers, list_targets};
use cli::help::{print_help, print_version, version};
use cli::llm_tools::{run_context, run_diff, run_mcp};
use cli::repl::run_repl;
use cli::sandbox::{apply_sandbox, parse_sandbox_config};
use cli::test_runner;
use cli::web::{web_build, web_features, web_init, web_serve, WebBuildOptions, WebServeOptions};


fn main() {
    simple_log::init();

    // Initialize interpreter handlers for hybrid execution
    simple_compiler::interpreter_ffi::init_interpreter_handlers();

    let args: Vec<String> = env::args().skip(1).collect();

    // Parse global flags
    let gc_log = args.iter().any(|a| a == "--gc-log");
    let gc_off = args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF");

    // Parse and apply sandbox configuration before running code (#916-919)
    if let Some(sandbox_config) = parse_sandbox_config(&args) {
        if let Err(e) = apply_sandbox(&sandbox_config) {
            eprintln!("warning: {}", e);
            eprintln!("Continuing without full sandboxing...");
        }
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

    // No arguments -> REPL
    if args.is_empty() {
        let runner = create_runner(gc_log, gc_off);
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
                eprintln!("Usage: simple compile <source.spl> [-o <output.smf>] [--target <arch>] [--linker <name>] [--snapshot]");
                std::process::exit(1);
            }
            let source = PathBuf::from(&args[1]);
            let output = args
                .iter()
                .position(|a| a == "-o")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from);

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
                } else {
                    eprintln!("Using linker: {}", l.name());
                }
            }

            // Parse --snapshot flag
            let snapshot = args.iter().any(|a| a == "--snapshot");

            // Parse compile options (including emit flags)
            let options = CompileOptions::from_args(&args);

            // TODO: Pass linker to compile_file when pipeline integration is complete
            let _ = linker; // Currently unused but parsed for future integration

            std::process::exit(compile_file(&source, output, target, snapshot, options));
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

                    let serve_options = WebServeOptions {
                        port,
                        watch,
                        open,
                    };

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
        "replay" => {
            std::process::exit(run_replay(&args));
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
                eprintln!(
                    "Usage: simple add <pkg> [version] [--path <path>] [--git <url>] [--dev]"
                );
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
                            println!(
                                "{} package(s) skipped (git/registry not yet supported)",
                                result.skipped
                            );
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
                            println!(
                                "{} ({}) [{}]{}",
                                pkg.name, pkg.version, pkg.source_type, status
                            );
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
            // Assume it's a file to run
            let path = PathBuf::from(first);
            if path.exists() {
                // Collect remaining arguments to pass to the Simple program
                let program_args: Vec<String> = args.iter()
                    .skip(1)  // Skip the file path
                    .filter(|a| !a.starts_with("--gc"))  // Skip GC flags
                    .cloned()
                    .collect();
                // Prepend the file path as argv[0]
                let mut full_args = vec![path.to_string_lossy().to_string()];
                full_args.extend(program_args);
                std::process::exit(run_file_with_args(&path, gc_log, gc_off, full_args));
            } else {
                eprintln!("error: file not found: {}", path.display());
                eprintln!();
                print_help();
                std::process::exit(1);
            }
        }
    }
}
