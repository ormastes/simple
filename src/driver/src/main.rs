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
use simple_log;
use simple_pkg::commands::{add, cache_cmd, init, install, list, update};

use cli::repl::run_repl;

const VERSION: &str = "0.1.0";

fn print_help() {
    eprintln!("Simple Language v{}", VERSION);
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple                      Start interactive REPL");
    eprintln!("  simple <file.spl>           Run source file");
    eprintln!("  simple <file.smf>           Run compiled binary");
    eprintln!("  simple -c \"code\"            Run code string");
    eprintln!("  simple compile <src> [-o <out>] [--target <arch>] [--snapshot]  Compile to SMF");
    eprintln!("  simple watch <file.spl>     Watch and auto-recompile");
    eprintln!("  simple targets              List available target architectures");
    eprintln!();
    eprintln!("Package Management:");
    eprintln!("  simple init [name]          Create a new project");
    eprintln!("  simple add <pkg> [options]  Add a dependency");
    eprintln!("  simple remove <pkg>         Remove a dependency");
    eprintln!("  simple install              Install all dependencies");
    eprintln!("  simple update [pkg]         Update dependencies");
    eprintln!("  simple list                 List installed dependencies");
    eprintln!("  simple tree                 Show dependency tree");
    eprintln!();
    eprintln!("Cache Management:");
    eprintln!("  simple cache info           Show cache information");
    eprintln!("  simple cache list           List cached packages");
    eprintln!("  simple cache clean          Clear the cache");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -h, --help     Show this help");
    eprintln!("  -v, --version  Show version");
    eprintln!("  -c <code>      Run code string");
    eprintln!("  --gc-log       Enable verbose GC logging");
    eprintln!("  --gc=off       Disable garbage collection");
    eprintln!("  --target <arch>  Target architecture for cross-compilation");
    eprintln!("  --snapshot     Create JJ snapshot on successful build/test");
    eprintln!();
    eprintln!("Target Architectures:");
    eprintln!("  x86_64   64-bit x86 (default on most systems)");
    eprintln!("  aarch64  64-bit ARM (Apple Silicon, ARM servers)");
    eprintln!("  i686     32-bit x86");
    eprintln!("  armv7    32-bit ARM");
    eprintln!("  riscv64  64-bit RISC-V");
    eprintln!("  riscv32  32-bit RISC-V");
    eprintln!();
    eprintln!("Add Options:");
    eprintln!("  --path <path>  Add as path dependency");
    eprintln!("  --git <url>    Add as git dependency");
    eprintln!("  --branch <br>  Git branch (with --git)");
    eprintln!("  --dev          Add as dev dependency");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple                      # Start REPL");
    eprintln!("  simple hello.spl            # Run source");
    eprintln!("  simple -c \"main = 42\"       # Run expression");
    eprintln!("  simple compile app.spl      # Compile to app.smf");
    eprintln!("  simple compile app.spl --target aarch64  # Cross-compile");
    eprintln!("  simple compile app.spl --snapshot  # Compile and snapshot");
    eprintln!("  simple watch app.spl        # Watch for changes");
    eprintln!("  simple init myapp           # Create new project");
    eprintln!("  simple add http \"1.0\"       # Add dependency");
    eprintln!("  simple add mylib --path ../mylib  # Add local dep");
}

fn print_version() {
    println!("Simple Language v{}", VERSION);
}

fn create_runner(gc_log: bool, gc_off: bool) -> Runner {
    if gc_off {
        Runner::new_no_gc()
    } else if gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

fn run_file(path: &PathBuf, gc_log: bool, gc_off: bool) -> i32 {
    let runner = create_runner(gc_log, gc_off);
    match runner.run_file(path) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn run_code(code: &str, gc_log: bool, gc_off: bool) -> i32 {
    let runner = create_runner(gc_log, gc_off);

    // Wrap expression in main if not already a full program
    let full_code = if code.contains("main") || code.contains("fn ") || code.contains("let ") {
        code.to_string()
    } else {
        format!("main = {}", code)
    };

    match runner.run_source_in_memory(&full_code) {
        Ok(exit_code) => {
            println!("{}", exit_code);
            exit_code
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn compile_file(
    source: &PathBuf,
    output: Option<PathBuf>,
    target: Option<Target>,
    snapshot: bool,
) -> i32 {
    use simple_driver::jj::{BuildEvent, BuildState, JJConnector};
    use std::time::Instant;

    let runner = Runner::new();
    let out_path = output.unwrap_or_else(|| source.with_extension("smf"));

    let source_content = match std::fs::read_to_string(source) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", source.display(), e);
            return 1;
        }
    };

    // Start timing and create build event
    let start_time = Instant::now();
    let mut build_state = BuildState::new();
    build_state.events.push(BuildEvent::CompilationStarted {
        timestamp: std::time::SystemTime::now(),
        files: vec![source.display().to_string()],
    });

    // Use target-specific compilation if target is specified
    let result = if let Some(target) = target {
        println!("Cross-compiling for target: {}", target);
        runner.compile_to_smf_for_target(&source_content, &out_path, target)
    } else {
        runner.compile_to_smf(&source_content, &out_path)
    };

    let duration_ms = start_time.elapsed().as_millis() as u64;

    match result {
        Ok(()) => {
            println!("Compiled {} -> {}", source.display(), out_path.display());

            // Record successful compilation event
            build_state.events.push(BuildEvent::CompilationSucceeded {
                timestamp: std::time::SystemTime::now(),
                duration_ms,
            });
            build_state = build_state.mark_compilation_success();

            // Create JJ snapshot if requested
            if snapshot {
                let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
                let jj = JJConnector::new(&cwd);

                // Try to get current commit ID to verify we're in a JJ repo
                match jj.current_commit_id() {
                    Ok(commit_id) => {
                        build_state = build_state.with_commit(commit_id.clone());

                        // Store the build state
                        if let Err(e) = jj.store_state(build_state.clone()) {
                            eprintln!("warning: failed to store build state: {}", e);
                        }

                        // Describe the change with build state
                        if let Err(e) = jj.describe_with_state(&build_state) {
                            eprintln!("warning: failed to describe change: {}", e);
                        } else {
                            println!(
                                "📸 Updated JJ change description with build state (commit: {})",
                                &commit_id[..std::cmp::min(12, commit_id.len())]
                            );
                        }
                    }
                    Err(_) => {
                        eprintln!("warning: --snapshot requires a JJ repository (run 'jj git init' or 'jj init')");
                    }
                }
            }

            0
        }
        Err(e) => {
            eprintln!("error: {}", e);

            // Record failed compilation event
            build_state.events.push(BuildEvent::CompilationFailed {
                timestamp: std::time::SystemTime::now(),
                duration_ms,
                error: e.to_string(),
            });

            if snapshot {
                // Save failure state for diagnostics
                let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
                let jj = JJConnector::new(&cwd);
                let _ = jj.store_state(build_state);
            }

            1
        }
    }
}

fn list_targets() -> i32 {
    println!("Available target architectures:");
    println!();
    println!("Host architecture: {} (default)", TargetArch::host());
    println!();
    println!("64-bit targets:");
    println!("  x86_64   - AMD/Intel 64-bit");
    println!("  aarch64  - ARM 64-bit (Apple Silicon, ARM servers)");
    println!("  riscv64  - RISC-V 64-bit");
    println!();
    println!("32-bit targets:");
    println!("  i686     - Intel/AMD 32-bit");
    println!("  armv7    - ARM 32-bit");
    println!("  riscv32  - RISC-V 32-bit");
    println!();
    println!("Usage: simple compile <source.spl> --target <arch>");
    0
}

fn watch_file(path: &PathBuf) -> i32 {
    println!("Watching {} for changes...", path.display());
    println!("Press Ctrl-C to stop.");

    match watch(path, true) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn main() {
    simple_log::init();

    let args: Vec<String> = env::args().skip(1).collect();

    // Parse global flags
    let gc_log = args.iter().any(|a| a == "--gc-log");
    let gc_off = args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF");

    // Filter out flags
    let args: Vec<String> = args
        .into_iter()
        .filter(|a| !a.starts_with("--gc"))
        .collect();

    // No arguments -> REPL
    if args.is_empty() {
        let runner = create_runner(gc_log, gc_off);
        std::process::exit(run_repl(VERSION, runner));
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
            if args.len() < 2 {
                eprintln!("error: compile requires a source file");
                eprintln!("Usage: simple compile <source.spl> [-o <output.smf>] [--target <arch>] [--snapshot]");
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

            // Parse --snapshot flag
            let snapshot = args.iter().any(|a| a == "--snapshot");

            std::process::exit(compile_file(&source, output, target, snapshot));
        }
        "targets" => {
            std::process::exit(list_targets());
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
                std::process::exit(run_file(&path, gc_log, gc_off));
            } else {
                eprintln!("error: file not found: {}", path.display());
                eprintln!();
                print_help();
                std::process::exit(1);
            }
        }
    }
}
