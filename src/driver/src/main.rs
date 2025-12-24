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

use cli::repl::run_repl;
use cli::test_runner;

const VERSION: &str = "0.1.0";

fn print_help() {
    eprintln!("Simple Language v{}", VERSION);
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple                      Start interactive REPL");
    eprintln!("  simple <file.spl>           Run source file");
    eprintln!("  simple <file.smf>           Run compiled binary");
    eprintln!("  simple -c \"code\"            Run code string");
    eprintln!("  simple compile <src> [-o <out>] [options]  Compile source file");
    eprintln!("  simple watch <file.spl>     Watch and auto-recompile");
    eprintln!("  simple targets              List available target architectures");
    eprintln!("  simple linkers              List available native linkers");
    eprintln!();
    eprintln!("Testing:");
    eprintln!("  simple test [path]          Run tests (default: test/)");
    eprintln!("  simple test --unit          Run unit tests only");
    eprintln!("  simple test --integration   Run integration tests only");
    eprintln!("  simple test --system        Run system tests only");
    eprintln!("  simple test --tag <name>    Filter by tag");
    eprintln!("  simple test --fail-fast     Stop on first failure");
    eprintln!("  simple test --seed <N>      Deterministic shuffle");
    eprintln!("  simple test --format <fmt>  Output format: text, json, doc");
    eprintln!("  simple test --json          Shorthand for --format json");
    eprintln!("  simple test --doc           Shorthand for --format doc");
    eprintln!("  simple test --watch         Watch and auto-rerun on changes");
    eprintln!();
    eprintln!("Code Quality:");
    eprintln!("  simple lint [path]          Run linter on file or directory");
    eprintln!("  simple lint --json          Output lint results as JSON");
    eprintln!("  simple lint --fix           Apply auto-fixes");
    eprintln!("  simple fmt [path]           Format file or directory");
    eprintln!("  simple fmt --check          Check formatting without changes");
    eprintln!();
    eprintln!("LLM-Friendly Tools:");
    eprintln!("  simple mcp <file.spl>       Generate minimal code preview (90% token reduction)");
    eprintln!("  simple mcp <file.spl> --expand <symbol>  Expand specific symbol");
    eprintln!("  simple mcp <file.spl> --search <query>   Search for symbols");
    eprintln!("  simple mcp <file.spl> --show-coverage    Show coverage overlays");
    eprintln!("  simple diff <old.spl> <new.spl> --semantic  Semantic diff (compare AST/HIR)");
    eprintln!("  simple diff <old.spl> <new.spl> --json     Output diff as JSON");
    eprintln!("  simple context <file.spl> [target]  Extract minimal context pack");
    eprintln!("  simple context <file.spl> --minimal     Only direct dependencies");
    eprintln!("  simple context <file.spl> --json        Output as JSON");
    eprintln!("  simple context <file.spl> --markdown    Output as Markdown");
    eprintln!();
    eprintln!("Build & Audit (#911-915):");
    eprintln!("  simple query --generated           Find all LLM-generated code");
    eprintln!("  simple query --generated --unverified    Find unverified generated code");
    eprintln!("  simple query --generated-by=<tool>       Find code by specific tool");
    eprintln!("  simple info <function> --provenance      Show provenance metadata");
    eprintln!("  simple spec-coverage                     Show specification coverage");
    eprintln!("  simple spec-coverage --by-category       Coverage by category");
    eprintln!("  simple spec-coverage --missing           Show missing features");
    eprintln!("  simple spec-coverage --report=html       Generate HTML report");
    eprintln!("  simple replay <log.json>                 Display build log");
    eprintln!("  simple replay --compare <log1> <log2>    Compare two builds");
    eprintln!("  simple replay --extract-errors <log>     Extract diagnostics");
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
    eprintln!("  --linker <name>  Native linker: mold, lld, ld (auto-detected if not set)");
    eprintln!("  --snapshot     Create JJ snapshot on successful build/test");
    eprintln!();
    eprintln!("Sandboxed Execution (#916-919):");
    eprintln!("  --sandbox               Enable sandboxing with default limits");
    eprintln!("  --time-limit <secs>     Set CPU time limit (seconds)");
    eprintln!("  --memory-limit <bytes>  Set memory limit (bytes, accepts K/M/G suffix)");
    eprintln!("  --fd-limit <count>      Set file descriptor limit");
    eprintln!("  --thread-limit <count>  Set thread limit");
    eprintln!("  --no-network            Block all network access");
    eprintln!("  --network-allow <domains>  Allow specific domains (comma-separated)");
    eprintln!("  --network-block <domains>  Block specific domains (comma-separated)");
    eprintln!("  --read-only <paths>     Restrict filesystem to read-only paths (comma-separated)");
    eprintln!("  --read-write <paths>    Restrict filesystem to specific read-write paths (comma-separated)");
    eprintln!();
    eprintln!("Build Optimization (#824):");
    eprintln!("  --parallel     Enable parallel compilation (uses all CPU cores)");
    eprintln!("  --parallel=N   Use N threads for parallel compilation");
    eprintln!("  --profile      Show compilation profiling information");
    eprintln!("  --mmap         Force memory-mapped file reading");
    eprintln!("  --no-mmap      Disable memory-mapped file reading");
    eprintln!();
    eprintln!("IR Export (LLM-friendly #885-887):");
    eprintln!("  --emit-ast     Export AST to stdout");
    eprintln!("  --emit-ast=<file>  Export AST to file");
    eprintln!("  --emit-hir     Export HIR to stdout");
    eprintln!("  --emit-hir=<file>  Export HIR to file");
    eprintln!("  --emit-mir     Export MIR to stdout");
    eprintln!("  --emit-mir=<file>  Export MIR to file");
    eprintln!();
    eprintln!("Deterministic Builds (#911) & Replay Logs (#912):");
    eprintln!("  --deterministic              Enable deterministic build mode");
    eprintln!("  --build-timestamp=<ISO8601>  Override build timestamp (e.g., 2025-01-15T10:00:00Z)");
    eprintln!("  --log=<file.json>            Save build log for replay and debugging");
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
    eprintln!();
    eprintln!("Sandbox Examples:");
    eprintln!("  simple script.spl --sandbox                    # Run with default sandbox");
    eprintln!("  simple script.spl --time-limit 30              # 30 second CPU limit");
    eprintln!("  simple script.spl --memory-limit 100M          # 100 MB memory limit");
    eprintln!("  simple script.spl --no-network                 # Block all network");
    eprintln!("  simple script.spl --network-allow github.com   # Allow only GitHub");
    eprintln!("  simple script.spl --read-only /tmp,/usr/lib    # Read-only filesystem");
    eprintln!("  simple script.spl --sandbox --time-limit 60 --memory-limit 256M  # Combined");
}

fn print_version() {
    println!("Simple Language v{}", VERSION);
}

/// Parse memory size from string (supports K, M, G suffixes)
fn parse_memory_size(s: &str) -> Result<u64, String> {
    let s = s.trim();
    let (num_str, multiplier) = if s.ends_with('G') || s.ends_with('g') {
        (&s[..s.len() - 1], 1024 * 1024 * 1024)
    } else if s.ends_with('M') || s.ends_with('m') {
        (&s[..s.len() - 1], 1024 * 1024)
    } else if s.ends_with('K') || s.ends_with('k') {
        (&s[..s.len() - 1], 1024)
    } else {
        (s, 1)
    };

    num_str
        .parse::<u64>()
        .map(|n| n * multiplier)
        .map_err(|e| format!("invalid memory size '{}': {}", s, e))
}

/// Parse sandbox configuration from command-line arguments
fn parse_sandbox_config(args: &[String]) -> Option<simple_runtime::SandboxConfig> {
    use simple_runtime::SandboxConfig;
    use std::time::Duration;

    // Check if sandboxing is enabled at all
    let has_sandbox_flag = args.iter().any(|a| {
        a == "--sandbox"
            || a.starts_with("--time-limit")
            || a.starts_with("--memory-limit")
            || a.starts_with("--fd-limit")
            || a.starts_with("--thread-limit")
            || a == "--no-network"
            || a.starts_with("--network-allow")
            || a.starts_with("--network-block")
            || a.starts_with("--read-only")
            || a.starts_with("--read-write")
    });

    if !has_sandbox_flag {
        return None;
    }

    let mut config = SandboxConfig::new();

    // Parse resource limits
    for i in 0..args.len() {
        let arg = &args[i];

        if arg == "--time-limit" && i + 1 < args.len() {
            if let Ok(secs) = args[i + 1].parse::<u64>() {
                config = config.with_cpu_time(Duration::from_secs(secs));
            }
        } else if arg == "--memory-limit" && i + 1 < args.len() {
            if let Ok(bytes) = parse_memory_size(&args[i + 1]) {
                config = config.with_memory(bytes);
            }
        } else if arg == "--fd-limit" && i + 1 < args.len() {
            if let Ok(count) = args[i + 1].parse::<u64>() {
                config = config.with_file_descriptors(count);
            }
        } else if arg == "--thread-limit" && i + 1 < args.len() {
            if let Ok(count) = args[i + 1].parse::<u64>() {
                config = config.with_threads(count);
            }
        } else if arg == "--no-network" {
            config = config.with_no_network();
        } else if arg == "--network-allow" && i + 1 < args.len() {
            let domains: Vec<String> = args[i + 1].split(',').map(|s| s.trim().to_string()).collect();
            config = config.with_network_allowlist(domains);
        } else if arg == "--network-block" && i + 1 < args.len() {
            let domains: Vec<String> = args[i + 1].split(',').map(|s| s.trim().to_string()).collect();
            config = config.with_network_blocklist(domains);
        } else if arg == "--read-only" && i + 1 < args.len() {
            let paths: Vec<std::path::PathBuf> = args[i + 1]
                .split(',')
                .map(|s| std::path::PathBuf::from(s.trim()))
                .collect();
            config = config.with_read_paths(paths);
        } else if arg == "--read-write" && i + 1 < args.len() {
            let read_write: Vec<&str> = args[i + 1].split(',').collect();
            let paths: Vec<std::path::PathBuf> = read_write
                .iter()
                .map(|s| std::path::PathBuf::from(s.trim()))
                .collect();
            // For --read-write, set both read and write paths to the same set
            config = config.with_restricted_paths(paths.clone(), paths);
        }
    }

    Some(config)
}

/// Apply sandbox configuration to the current process
fn apply_sandbox(config: &simple_runtime::SandboxConfig) -> Result<(), String> {
    simple_runtime::apply_sandbox(config)
        .map_err(|e| format!("Failed to apply sandbox: {}", e))
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
    options: CompileOptions,
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
        runner.compile_to_smf_with_options(&source_content, &out_path, &options)
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

fn list_linkers() -> i32 {
    use simple_compiler::linker::NativeLinker;

    println!("Available native linkers:");
    println!();

    // Check each linker's availability
    let linkers = [
        (NativeLinker::Mold, "mold", "Modern, fastest linker (Linux only, ~4x faster than lld)"),
        (NativeLinker::Lld, "lld", "LLVM's linker (cross-platform, fast)"),
        (NativeLinker::Ld, "ld", "GNU ld (traditional fallback)"),
    ];

    for (linker, name, description) in &linkers {
        let available = NativeLinker::is_available(*linker);
        let status = if available { "✓" } else { "✗" };
        let version = if available {
            linker.version().unwrap_or_default()
        } else {
            String::new()
        };

        println!("  {} {:<6} - {}", status, name, description);
        if available && !version.is_empty() {
            println!("           {}", version);
        }
    }

    println!();

    // Show detected linker
    match NativeLinker::detect() {
        Some(linker) => {
            println!("Auto-detected: {} (will be used by default)", linker.name());
        }
        None => {
            println!("No native linker found!");
        }
    }

    println!();
    println!("Override with: simple compile <src> --linker <name>");
    println!("Or set: SIMPLE_LINKER=mold|lld|ld");
    0
}

fn run_lint(args: &[String]) -> i32 {
    use simple_compiler::{LintChecker, LintConfig};
    use simple_parser::Parser;
    use std::fs;

    // Parse arguments
    let path = args.get(1).map(|s| PathBuf::from(s)).unwrap_or_else(|| PathBuf::from("."));
    let json_output = args.iter().any(|a| a == "--json");
    let _fix = args.iter().any(|a| a == "--fix"); // TODO: Implement auto-fix

    // Check if path is directory
    if path.is_dir() {
        return lint_directory(&path, json_output);
    }

    // Lint single file
    lint_file(&path, json_output)
}

fn lint_directory(dir: &PathBuf, json_output: bool) -> i32 {
    use walkdir::WalkDir;
    use simple_common::diagnostic::Diagnostics;

    let mut all_errors = false;
    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut all_diags = Diagnostics::new();

    for entry in WalkDir::new(dir)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
    {
        let path = entry.path();
        let result = lint_file_internal(path, false);
        
        if let Some((has_err, err_count, warn_count, diags)) = result {
            if has_err {
                all_errors = true;
            }
            total_errors += err_count;
            total_warnings += warn_count;
            
            if json_output {
                for diag in diags {
                    all_diags.push(diag);
                }
            }
        }
    }

    if json_output {
        match all_diags.to_json() {
            Ok(json) => println!("{}", json),
            Err(e) => {
                eprintln!("error: failed to serialize diagnostics: {}", e);
                return 1;
            }
        }
    } else {
        println!();
        println!("Total: {} error(s), {} warning(s) across {} file(s)", 
            total_errors, total_warnings, 
            WalkDir::new(dir).into_iter().filter(|e| 
                e.as_ref().ok().and_then(|e| 
                    e.path().extension().and_then(|s| s.to_str())
                ) == Some("spl")
            ).count()
        );
    }

    if all_errors { 1 } else { 0 }
}

fn lint_file(path: &PathBuf, json_output: bool) -> i32 {
    use simple_common::diagnostic::Diagnostics;

    if let Some((has_errors, _, _, diags)) = lint_file_internal(path, json_output) {
        if json_output {
            // Single file JSON output
            let mut all_diags = Diagnostics::new();
            for diag in diags {
                all_diags.push(diag);
            }
            match all_diags.to_json() {
                Ok(json) => println!("{}", json),
                Err(e) => {
                    eprintln!("error: failed to serialize diagnostics: {}", e);
                    return 1;
                }
            }
        }
        if has_errors { 1 } else { 0 }
    } else {
        1
    }
}

fn lint_file_internal(path: &std::path::Path, json_output: bool) -> Option<(bool, usize, usize, Vec<simple_common::diagnostic::Diagnostic>)> {
    use simple_compiler::{LintChecker, LintConfig};
    use simple_parser::Parser;
    use std::fs;

    // Read file
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            if !json_output {
                eprintln!("error: cannot read {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Parse file
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            if !json_output {
                eprintln!("error: parse failed in {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Create lint checker
    let config = LintConfig::default();
    let mut checker = LintChecker::new();
    
    // Run lint checks
    checker.check_module(&module.items);
    let diagnostics = checker.diagnostics();

    
    let error_count = diagnostics.iter().filter(|d| d.is_error()).count();
    let warning_count = diagnostics.len() - error_count;
    let has_errors = error_count > 0;

    // Convert to common diagnostics
    let common_diags: Vec<simple_common::diagnostic::Diagnostic> = diagnostics
        .iter()
        .map(|d| d.to_diagnostic(Some(path.display().to_string())))
        .collect();

    if json_output {
        // Return diagnostics for aggregation
    } else {
        // Human-readable output
        if diagnostics.is_empty() {
            println!("{}: OK", path.display());
        } else {
            for diagnostic in diagnostics {
                // Format: file:line:col: level: message
                let span = &diagnostic.span;
                let level_str = if diagnostic.is_error() { "error" } else { "warning" };
                println!(
                    "{}:{}:{}: {}: {} [{}]",
                    path.display(),
                    span.line,
                    span.column,
                    level_str,
                    diagnostic.message,
                    diagnostic.lint.as_str()
                );
                if let Some(suggestion) = &diagnostic.suggestion {
                    println!("  help: {}", suggestion);
                }
            }
        }
    }

    Some((has_errors, error_count, warning_count, common_diags))
}

fn run_fmt(args: &[String]) -> i32 {
    use std::fs;

    // Parse arguments
    let path = args.get(1).map(|s| PathBuf::from(s)).unwrap_or_else(|| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // TODO: Implement actual formatting logic
    // For now, this is a placeholder that validates the file can be parsed
    use simple_parser::Parser;
    let mut parser = Parser::new(&source);
    match parser.parse() {
        Ok(_) => {
            if check_only {
                println!("{}: formatted correctly", path.display());
                0
            } else {
                println!("{}: would format (formatter not yet implemented)", path.display());
                0
            }
        }
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            1
        }
    }
}

fn run_context(args: &[String]) -> i32 {
    use simple_compiler::api_surface::ApiSurface;
    use simple_compiler::context_pack::ContextPack;
    use simple_parser::Parser;
    use std::fs;

    // Parse arguments
    if args.len() < 2 {
        eprintln!("error: context requires a source file");
        eprintln!("Usage: simple context <file.spl> [target] [--minimal] [--json] [--markdown]");
        return 1;
    }

    let path = PathBuf::from(&args[1]);
    let target = args.get(2).filter(|s| !s.starts_with("--")).map(|s| s.as_str());
    let minimal = args.iter().any(|a| a == "--minimal");
    let json_output = args.iter().any(|a| a == "--json");
    let markdown_output = args.iter().any(|a| a == "--markdown");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Parse
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            return 1;
        }
    };

    // Build API surface from module
    let api_surface = ApiSurface::from_nodes(&path.display().to_string(), &module.items);

    // Extract context pack
    let target_name = target.unwrap_or("main");
    let pack = if minimal {
        ContextPack::from_target_minimal(target_name, &module.items, &api_surface)
    } else {
        ContextPack::from_target(target_name, &module.items, &api_surface)
    };

    // Output in requested format
    if json_output {
        match pack.to_json() {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate JSON: {}", e);
                1
            }
        }
    } else if markdown_output {
        println!("{}", pack.to_markdown());
        0
    } else {
        // Default: plain text
        println!("{}", pack.to_text());

        // Show stats
        let full_count = api_surface.functions.len()
            + api_surface.structs.len()
            + api_surface.classes.len()
            + api_surface.enums.len()
            + api_surface.traits.len();
        if full_count > 0 {
            let savings = pack.token_savings(full_count);
            eprintln!();
            eprintln!("Context reduction: {:.1}%", savings);
            eprintln!("Symbols: {} / {} (extracted / total)", pack.symbol_count, full_count);
        }
        0
    }
}

fn run_diff(args: &[String]) -> i32 {
    use simple_compiler::semantic_diff::{SemanticDiffer};
    use simple_parser::Parser;
    use std::fs;

    // Parse arguments
    if args.len() < 3 {
        eprintln!("error: diff requires two source files");
        eprintln!("Usage: simple diff <old.spl> <new.spl> [--semantic] [--json]");
        return 1;
    }

    let old_path = PathBuf::from(&args[1]);
    let new_path = PathBuf::from(&args[2]);
    let semantic = args.iter().any(|a| a == "--semantic");
    let json_output = args.iter().any(|a| a == "--json");

    // Read old file
    let old_source = match fs::read_to_string(&old_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", old_path.display(), e);
            return 1;
        }
    };

    // Read new file
    let new_source = match fs::read_to_string(&new_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", new_path.display(), e);
            return 1;
        }
    };

    // Parse old file
    let mut old_parser = Parser::new(&old_source);
    let old_module = match old_parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse failed in {}: {}", old_path.display(), e);
            return 1;
        }
    };

    // Parse new file
    let mut new_parser = Parser::new(&new_source);
    let new_module = match new_parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse failed in {}: {}", new_path.display(), e);
            return 1;
        }
    };

    if semantic {
        // Semantic diff (AST-based)
        let differ = SemanticDiffer::new(format!(
            "{} -> {}",
            old_path.display(),
            new_path.display()
        ));
        let diff = differ.diff_modules(&old_module, &new_module);

        if json_output {
            match SemanticDiffer::format_json(&diff) {
                Ok(json) => {
                    println!("{}", json);
                    0
                }
                Err(e) => {
                    eprintln!("error: failed to format JSON: {}", e);
                    1
                }
            }
        } else {
            println!("{}", SemanticDiffer::format_text(&diff));
            0
        }
    } else {
        // TODO: Implement text-based diff
        eprintln!("error: text-based diff not implemented yet. Use --semantic flag.");
        eprintln!("Usage: simple diff <old.spl> <new.spl> --semantic");
        1
    }
}

fn run_mcp(args: &[String]) -> i32 {
    use simple_compiler::mcp::{ExpandWhat, McpGenerator, McpTools};
    use simple_parser::Parser;
    use std::fs;

    // Parse arguments
    if args.len() < 2 {
        eprintln!("error: mcp requires a source file");
        eprintln!("Usage: simple mcp <file.spl> [--expand <symbol>] [--search <query>] [--show-coverage]");
        return 1;
    }

    let path = PathBuf::from(&args[1]);
    let expand_symbol = args
        .iter()
        .position(|a| a == "--expand")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str());
    let search_query = args
        .iter()
        .position(|a| a == "--search")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str());
    let show_coverage = args.iter().any(|a| a == "--show-coverage");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Parse
    let mut parser = Parser::new(&source);
    let nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            return 1;
        }
    };

    // Generate MCP output
    if let Some(query) = search_query {
        // Search mode
        let tools = McpTools::new();
        let results = tools.search(&nodes.items, query, true);
        if results.is_empty() {
            eprintln!("No symbols found matching '{}'", query);
            return 1;
        } else {
            println!("Found {} symbol(s):", results.len());
            for result in results {
                println!("  {}", result);
            }
            return 0;
        }
    } else if let Some(symbol) = expand_symbol {
        // Expand mode
        let tools = McpTools::new();
        match tools.expand_at(&nodes.items, symbol, ExpandWhat::All) {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate MCP: {}", e);
                1
            }
        }
    } else {
        // Default collapsed mode
        let mut generator = McpGenerator::new();
        if show_coverage {
            generator = generator.show_coverage(true);
        }
        let output = generator.generate(&nodes.items);
        match serde_json::to_string_pretty(&output) {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate MCP: {}", e);
                1
            }
        }
    }
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

fn run_query(args: &[String]) -> i32 {
    use simple_parser::{Node, Parser};
    use std::fs;

    // Parse arguments
    let show_generated = args.iter().any(|a| a == "--generated");
    let show_unverified = args.iter().any(|a| a == "--unverified");
    let generated_by_tool = args
        .iter()
        .find(|a| a.starts_with("--generated-by="))
        .and_then(|a| a.strip_prefix("--generated-by="));

    if !show_generated && generated_by_tool.is_none() {
        eprintln!("error: query requires --generated or --generated-by=<tool>");
        eprintln!("Usage:");
        eprintln!("  simple query --generated");
        eprintln!("  simple query --generated --unverified");
        eprintln!("  simple query --generated-by=<tool>");
        return 1;
    }

    // Get the path to search (default to current directory)
    // Skip the first argument (command name "query") and flags
    let search_path = args
        .iter()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    // Collect all .spl files
    let mut spl_files = Vec::new();
    if search_path.is_file() {
        spl_files.push(search_path.clone());
    } else if search_path.is_dir() {
        // Walk directory recursively
        if let Ok(entries) = fs::read_dir(&search_path) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_file() && path.extension().map_or(false, |e| e == "spl") {
                    spl_files.push(path);
                }
                // TODO: Add recursive directory walking
            }
        }
    }

    if spl_files.is_empty() {
        eprintln!("error: no .spl files found in {}", search_path.display());
        return 1;
    }

    // Search for generated functions
    let mut found_any = false;
    for file_path in spl_files {
        let source = match fs::read_to_string(&file_path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let mut parser = Parser::new(&source);
        let module = match parser.parse() {
            Ok(m) => m,
            Err(_) => continue,
        };

        // Search for generated functions
        for item in &module.items {
            if let Node::Function(func) = item {
                if !func.is_generated() {
                    continue;
                }

                let metadata = func.generated_by_metadata();

                // Apply filters
                if let Some(tool_filter) = generated_by_tool {
                    // Check if tool matches
                    let matches_tool = metadata.map_or(false, |args| {
                        args.iter().any(|arg| {
                            if arg.name.as_deref() != Some("tool") {
                                return false;
                            }
                            match &arg.value {
                                simple_parser::Expr::String(s) => s == tool_filter,
                                simple_parser::Expr::FString(parts) => {
                                    // Handle FString with single Literal part
                                    if parts.len() == 1 {
                                        if let simple_parser::FStringPart::Literal(s) = &parts[0] {
                                            return s == tool_filter;
                                        }
                                    }
                                    false
                                }
                                _ => false,
                            }
                        })
                    });
                    if !matches_tool {
                        continue;
                    }
                }

                if show_unverified {
                    // Check if verified flag is false or missing
                    let is_verified = metadata.map_or(false, |args| {
                        args.iter().any(|arg| {
                            arg.name.as_deref() == Some("verified")
                                && matches!(&arg.value, simple_parser::Expr::Bool(true))
                        })
                    });
                    if is_verified {
                        continue;
                    }
                }

                // Print result
                found_any = true;
                println!("{}:{}", file_path.display(), func.name);
            }
        }
    }

    if !found_any {
        println!("No generated functions found.");
    }

    0
}

fn run_spec_coverage(args: &[String]) -> i32 {
    use simple_compiler::{SpecCoverageReport, find_spec_file};

    // Find the spec file
    let spec_path = match find_spec_file() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("error: {}", e);
            eprintln!("Make sure specs/language.yaml exists in the project root");
            return 1;
        }
    };

    // Load the spec coverage report
    let report = match SpecCoverageReport::load(&spec_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    // Parse options
    let by_category = args.iter().any(|a| a == "--by-category");
    let show_missing = args.iter().any(|a| a == "--missing");
    let html_report = args.iter()
        .find(|a| a.starts_with("--report="))
        .and_then(|a| a.strip_prefix("--report="));

    // Generate requested output
    if let Some("html") = html_report {
        println!("{}", report.generate_html());
        0
    } else if by_category {
        report.display_by_category();
        0
    } else if show_missing {
        report.display_missing();
        0
    } else {
        report.display_summary();
        0
    }
}

fn run_replay(args: &[String]) -> i32 {
    use simple_compiler::BuildLog;
    use std::path::PathBuf;

    // Parse options
    let compare_mode = args.iter().any(|a| a == "--compare");
    let extract_errors = args.iter().any(|a| a == "--extract-errors");

    if compare_mode {
        // Compare two build logs
        if args.len() < 3 {
            eprintln!("error: --compare requires two log files");
            eprintln!("Usage: simple replay --compare build1.json build2.json");
            return 1;
        }

        let log1_path = PathBuf::from(&args[1]);
        let log2_path = PathBuf::from(&args[2]);

        let log1 = match BuildLog::load(&log1_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error loading {}: {}", log1_path.display(), e);
                return 1;
            }
        };

        let log2 = match BuildLog::load(&log2_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error loading {}: {}", log2_path.display(), e);
                return 1;
            }
        };

        let comparison = log1.compare(&log2);

        println!("Build Comparison:");
        println!("  Session 1: {}", comparison.session1);
        println!("  Session 2: {}", comparison.session2);
        println!();

        if comparison.result_changed {
            println!("  ⚠ Build result changed!");
            println!();
        }

        println!("  Duration difference: {:+} ms", comparison.duration_difference_ms);
        println!();

        if !comparison.phase_differences.is_empty() {
            println!("  Phase differences:");
            for diff in &comparison.phase_differences {
                println!("    {}: {:+} ms{}",
                    diff.phase_name,
                    diff.duration_diff_ms,
                    if diff.result_changed { " (result changed)" } else { "" }
                );
            }
        } else {
            println!("  No significant phase differences (< 5ms)");
        }

        return 0;
    }

    if extract_errors {
        // Extract errors from build log
        if args.len() < 2 {
            eprintln!("error: --extract-errors requires a log file");
            eprintln!("Usage: simple replay --extract-errors build.json");
            return 1;
        }

        let log_path = PathBuf::from(&args[1]);
        let log = match BuildLog::load(&log_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error: {}", e);
                return 1;
            }
        };

        println!("Diagnostics from {}:", log_path.display());
        println!();

        for diag in &log.diagnostics {
            let level_str = match diag.level {
                simple_compiler::DiagnosticLevel::Error => "error",
                simple_compiler::DiagnosticLevel::Warning => "warning",
                simple_compiler::DiagnosticLevel::Info => "info",
            };

            if let (Some(file), Some(line), Some(column)) = (&diag.file, diag.line, diag.column) {
                println!("{}:{}:{}: {}: {}", file, line, column, level_str, diag.message);
            } else {
                println!("{}: {}", level_str, diag.message);
            }
        }

        return if log.error_count() > 0 { 1 } else { 0 };
    }

    // Default: display build log
    if args.len() < 2 {
        eprintln!("error: replay requires a log file");
        eprintln!("Usage: simple replay build.json");
        eprintln!("       simple replay --compare build1.json build2.json");
        eprintln!("       simple replay --extract-errors build.json");
        return 1;
    }

    let log_path = PathBuf::from(&args[1]);
    let log = match BuildLog::load(&log_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    // Display build log summary
    println!("Build Log: {}", log_path.display());
    println!();
    println!("Session ID: {}", log.session_id);
    println!("Timestamp: {}", log.timestamp);
    println!("Compiler: {}", log.compiler_version);
    println!("Command: {}", log.command);
    println!("Working Dir: {}", log.environment.working_dir);
    println!();

    println!("Input Files:");
    for file in &log.inputs.source_files {
        println!("  - {}", file);
    }
    println!();

    if !log.inputs.dependencies.is_empty() {
        println!("Dependencies:");
        for (name, version) in &log.inputs.dependencies {
            println!("  - {} = {}", name, version);
        }
        println!();
    }

    println!("Compilation Phases:");
    for phase in &log.phases {
        let result_str = match phase.result {
            simple_compiler::PhaseResult::Success => "✓",
            simple_compiler::PhaseResult::Failed => "✗",
            simple_compiler::PhaseResult::Skipped => "⊘",
        };
        println!("  {} {}: {} ms{}",
            result_str,
            phase.name,
            phase.duration_ms,
            phase.error.as_ref().map(|e| format!(" ({})", e)).unwrap_or_default()
        );
    }
    println!();

    println!("Total Duration: {} ms", log.total_duration_ms());
    println!();

    if let Some(output) = &log.output {
        println!("Output:");
        println!("  Binary: {}", output.binary);
        println!("  Size: {} bytes", output.size_bytes);
        println!("  Hash: {}", output.hash);
        println!();
    }

    let result_str = match log.result {
        simple_compiler::BuildResult::Success => "SUCCESS",
        simple_compiler::BuildResult::Failed => "FAILED",
        simple_compiler::BuildResult::Cancelled => "CANCELLED",
    };
    println!("Build Result: {}", result_str);

    if !log.diagnostics.is_empty() {
        println!();
        println!("Diagnostics: {} errors, {} warnings", log.error_count(), log.warning_count());
    }

    if log.error_count() > 0 { 1 } else { 0 }
}

fn run_info(args: &[String]) -> i32 {
    use simple_parser::{Node, Parser};
    use std::fs;

    // Parse arguments
    let show_provenance = args.iter().any(|a| a == "--provenance");

    if !show_provenance {
        eprintln!("error: info command currently only supports --provenance");
        eprintln!("Usage: simple info <function> --provenance [file]");
        return 1;
    }

    if args.len() < 2 {
        eprintln!("error: info requires a function name");
        eprintln!("Usage: simple info <function> --provenance [file]");
        return 1;
    }

    let function_name = &args[1];

    // Get the file to search (default to all .spl files in current directory)
    // Skip command name "info", function name, and flags
    let search_path = args
        .iter()
        .skip(3)
        .find(|a| !a.starts_with("--"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    // Collect all .spl files
    let mut spl_files = Vec::new();
    if search_path.is_file() {
        spl_files.push(search_path.clone());
    } else if search_path.is_dir() {
        // Walk directory recursively
        if let Ok(entries) = fs::read_dir(&search_path) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_file() && path.extension().map_or(false, |e| e == "spl") {
                    spl_files.push(path);
                }
            }
        }
    }

    if spl_files.is_empty() {
        eprintln!("error: no .spl files found in {}", search_path.display());
        return 1;
    }

    // Search for the function
    for file_path in spl_files {
        let source = match fs::read_to_string(&file_path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let mut parser = Parser::new(&source);
        let module = match parser.parse() {
            Ok(m) => m,
            Err(_) => continue,
        };

        // Search for the function
        for item in &module.items {
            if let Node::Function(func) = item {
                if func.name == *function_name {
                    // Found the function - display provenance
                    println!("Function: {}", func.name);
                    println!("Location: {}", file_path.display());

                    if func.is_generated() {
                        println!("Provenance:");

                        if let Some(metadata) = func.generated_by_metadata() {
                            // Extract and display metadata fields
                            for arg in metadata {
                                if let Some(name) = &arg.name {
                                    let value = match &arg.value {
                                        simple_parser::Expr::String(s) => s.clone(),
                                        simple_parser::Expr::Bool(b) => b.to_string(),
                                        simple_parser::Expr::Integer(i) => i.to_string(),
                                        simple_parser::Expr::FString(parts) => {
                                            // Handle FString with single Literal part
                                            if parts.len() == 1 {
                                                if let simple_parser::FStringPart::Literal(s) = &parts[0] {
                                                    s.clone()
                                                } else {
                                                    format!("{:?}", parts)
                                                }
                                            } else {
                                                format!("{:?}", parts)
                                            }
                                        }
                                        _ => format!("{:?}", arg.value),
                                    };
                                    println!("  {}: {}", name, value);
                                }
                            }
                        } else {
                            println!("  (no metadata)");
                        }
                    } else {
                        println!("Provenance: Not generated (no @generated_by decorator)");
                    }

                    return 0;
                }
            }
        }
    }

    eprintln!("error: function '{}' not found", function_name);
    1
}

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
                    println!("Simple Test Runner v{}", VERSION);
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
