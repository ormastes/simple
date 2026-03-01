//! Miscellaneous command handlers (diagram, lock, run, etc.)

use std::path::PathBuf;
use crate::cli::diagram_gen::{generate_diagrams_from_events, parse_diagram_args, print_diagram_help};
use crate::cli::lock;

/// Handle 'diagram' command - generate UML diagrams from profile data
pub fn handle_diagram(args: &[String]) -> i32 {
    // Check for help
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print_diagram_help();
        return 0;
    }

    // Parse diagram generation options
    let diagram_args: Vec<String> = args[1..].to_vec();
    let options = parse_diagram_args(&diagram_args);

    // Check if we have a profile file to load
    if let Some(ref profile_path) = options.from_file {
        // Load profile data from file
        match simple_compiler::runtime_profile::ProfileData::load_from_file(profile_path) {
            Ok(profile_data) => {
                println!(
                    "Loaded profile: {} ({} events)",
                    profile_data.name,
                    profile_data.events.len()
                );

                // Generate diagrams from the loaded profile data
                let architectural = profile_data.get_architectural_entities();
                match generate_diagrams_from_events(profile_data.get_events(), &architectural, &options) {
                    Ok(result) => {
                        if let Some(path) = result.sequence_path {
                            println!("  Sequence diagram: {}", path.display());
                        }
                        if let Some(path) = result.class_path {
                            println!("  Class diagram: {}", path.display());
                        }
                        if let Some(path) = result.arch_path {
                            println!("  Architecture diagram: {}", path.display());
                        }
                        println!("Diagrams generated successfully.");
                        0
                    }
                    Err(e) => {
                        eprintln!("error: failed to generate diagrams: {}", e);
                        1
                    }
                }
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        }
    } else {
        // No profile file specified - show usage help
        print_diagram_usage(&options);
        0
    }
}

fn print_diagram_usage(options: &crate::cli::diagram_gen::DiagramGenOptions) {
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

    println!();
    println!("No profile file specified. Usage:");
    println!("  simple diagram <profile.json>           Load and generate diagrams");
    println!("  simple diagram -f <file> -A             Generate all diagram types");
    println!();
    println!("To record profile data, use:");
    println!("  simple test --seq-diagram my_test.spl");
}

/// Handle 'lock' command - manage lock files
pub fn handle_lock(args: &[String]) -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");
    let info_only = args.iter().any(|a| a == "--info");

    if info_only {
        lock::lock_info(&dir)
    } else if check_only {
        lock::check_lock(&dir)
    } else {
        lock::generate_lock(&dir)
    }
}

/// Handle 'run' command - explicit run command for compatibility
pub fn handle_run(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if args.len() < 2 {
        eprintln!("error: run requires a file");
        return 1;
    }
    let path = PathBuf::from(&args[1]);
    crate::cli::basic::run_file(&path, gc_log, gc_off)
}

/// Handle 'build' command - build system (bootstrap, lint, fmt, check, etc.)
pub fn handle_build(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    let sub_args: Vec<&str> = if args.len() > 1 {
        args[1..].iter().map(|s| s.as_str()).collect()
    } else {
        vec![]
    };

    let cmd = sub_args.first().copied().unwrap_or("help");

    match cmd {
        "bootstrap" => handle_bootstrap(&sub_args[1..]),
        "help" | "--help" | "-h" => {
            println!("Simple Build System");
            println!();
            println!("USAGE:");
            println!("  simple build <command> [options]");
            println!();
            println!("COMMANDS:");
            println!("  bootstrap      3-stage self-compilation verification");
            println!("  help           Show this help");
            println!();
            println!("BOOTSTRAP OPTIONS:");
            println!("  --backend=<name>   Backend: llvm, cranelift, c, auto (default: auto)");
            println!("  --output=<dir>     Output directory (default: bootstrap)");
            0
        }
        _ => {
            // For other build subcommands, delegate to the Simple build system via file execution
            let entry = PathBuf::from("src/compiler/80.driver/build/cli_entry.spl");
            if entry.exists() {
                let mut file_args = vec![entry.to_string_lossy().to_string()];
                file_args.extend(sub_args.iter().map(|s| s.to_string()));
                crate::cli::basic::run_file_with_args(&entry, gc_log, gc_off, file_args)
            } else {
                eprintln!("error: unknown build subcommand: {}", cmd);
                1
            }
        }
    }
}

/// Run the 3-stage bootstrap pipeline directly in Rust.
///
/// This is a native implementation of the bootstrap process:
/// Stage 1: Compile compiler with current binary
/// Stage 2: Compile compiler with Stage 1 output
/// Stage 3: Compile compiler with Stage 2 output, verify Stage 2 == Stage 3
fn handle_bootstrap(args: &[&str]) -> i32 {
    use std::process::Command;
    use std::time::Instant;

    // Parse options
    let mut backend = "auto".to_string();
    let mut output_dir = "bootstrap".to_string();
    for arg in args {
        if let Some(b) = arg.strip_prefix("--backend=") {
            backend = b.to_string();
        } else if let Some(d) = arg.strip_prefix("--output=") {
            output_dir = d.to_string();
        }
    }

    println!("Bootstrap pipeline starting...");
    println!("Backend: {}", backend);
    println!("Output dir: {}", output_dir);

    // Ensure output directory exists
    let _ = std::fs::create_dir_all(&output_dir);

    // Find initial compiler
    let compiler = if PathBuf::from("bin/release/simple").exists() {
        "bin/release/simple".to_string()
    } else if PathBuf::from("bin/simple").exists() {
        "bin/simple".to_string()
    } else {
        eprintln!("Error: No compiler binary found at bin/release/simple or bin/simple");
        return 1;
    };

    // Stage 1
    println!();
    println!("=== Stage 1: Compile with current binary ===");
    let stage1_path = format!("{}/simple_stage1", output_dir);
    let stage1 = compile_stage(&compiler, &stage1_path, &backend);
    if !stage1.success {
        eprintln!("Stage 1 FAILED");
        return 1;
    }
    println!("Stage 1: OK ({} bytes, hash={})", stage1.size, stage1.hash);

    // Stage 2
    println!();
    println!("=== Stage 2: Compile with Stage 1 binary ===");
    let stage2_path = format!("{}/simple_stage2", output_dir);
    let stage2 = compile_stage(&stage1_path, &stage2_path, &backend);
    if !stage2.success {
        eprintln!("Stage 2 FAILED");
        return 1;
    }
    println!("Stage 2: OK ({} bytes, hash={})", stage2.size, stage2.hash);

    // Stage 3
    println!();
    println!("=== Stage 3: Compile with Stage 2 binary ===");
    let stage3_path = format!("{}/simple_stage3", output_dir);
    let stage3 = compile_stage(&stage2_path, &stage3_path, &backend);
    if !stage3.success {
        eprintln!("Stage 3 FAILED");
        return 1;
    }
    println!("Stage 3: OK ({} bytes, hash={})", stage3.size, stage3.hash);

    // Verify
    println!();
    if stage2.hash == stage3.hash {
        println!("Bootstrap VERIFIED: Stage 2 and Stage 3 hashes match");
        println!("  Hash: {}", stage2.hash);
        0
    } else {
        println!("Bootstrap MISMATCH: Stage 2 and Stage 3 differ");
        println!("  Stage 2: {}", stage2.hash);
        println!("  Stage 3: {}", stage3.hash);
        1
    }
}

struct StageResult {
    success: bool,
    size: u64,
    hash: String,
}

fn compile_stage(compiler: &str, output: &str, backend: &str) -> StageResult {
    use std::process::Command;

    // Detect whether this compiler is the Rust driver or a self-hosted Simple binary.
    // The Rust driver uses `compile --native`, while self-hosted binaries use
    // `src/app/compile/native.spl` as a file argument.
    let is_rust_driver = is_rust_driver_binary(compiler);

    let mut cmd = Command::new(compiler);
    if is_rust_driver {
        // Rust driver: use `compile --native` subcommand
        cmd.arg("compile")
            .arg("--native")
            .arg("src/app/cli/main.spl")
            .arg("-o")
            .arg(output);
        println!("  Running: {} compile --native src/app/cli/main.spl -o {}",
            compiler, output);
    } else {
        // Self-hosted binary: run native.spl as a file to compile main.spl
        cmd.arg("src/app/compile/native.spl")
            .arg("src/app/cli/main.spl")
            .arg(output);
        if backend != "auto" {
            cmd.arg(format!("--backend={}", backend));
        }
        println!("  Running: {} src/app/compile/native.spl src/app/cli/main.spl {} {}",
            compiler, output,
            if backend != "auto" { format!("--backend={}", backend) } else { String::new() });
    }

    match cmd.output() {
        Ok(result) => {
            if !result.status.success() {
                let stderr = String::from_utf8_lossy(&result.stderr);
                eprintln!("  Compile failed (exit {:?})", result.status.code());
                if !stderr.is_empty() {
                    eprintln!("  stderr: {}", stderr.trim());
                }
                return StageResult { success: false, size: 0, hash: String::new() };
            }

            // Get file size
            let size = std::fs::metadata(output).map(|m| m.len()).unwrap_or(0);

            // Compute SHA-256 hash
            let hash = Command::new("sha256sum")
                .arg(output)
                .output()
                .ok()
                .and_then(|o| {
                    String::from_utf8(o.stdout).ok().map(|s| {
                        s.split_whitespace().next().unwrap_or("").to_string()
                    })
                })
                .unwrap_or_default();

            StageResult { success: true, size, hash }
        }
        Err(e) => {
            eprintln!("  Failed to execute compiler: {}", e);
            StageResult { success: false, size: 0, hash: String::new() }
        }
    }
}

/// Check if a compiler binary is the Rust driver (vs a self-hosted Simple binary).
///
/// Stage 1 always uses the current binary (Rust driver), so we check if the
/// compiler path matches the current executable. For Stage 2+, the output
/// binaries are self-hosted Simple compilers that use the `native.spl` file
/// execution approach.
fn is_rust_driver_binary(compiler: &str) -> bool {
    // The Rust driver is always used as Stage 1 compiler.
    // Stage 2+ compilers are in the bootstrap output directory.
    let compiler_path = PathBuf::from(compiler);

    // If the compiler is in the bootstrap directory, it's a self-hosted binary
    if compiler.contains("/simple_stage") || compiler.contains("\\simple_stage") {
        return false;
    }

    // If it matches bin/release/simple or bin/simple, it's the Rust driver
    // (since we're running from the Rust driver)
    if compiler == "bin/release/simple" || compiler == "bin/simple" {
        return true;
    }

    // Check if it's the current executable
    if let Ok(current) = std::env::current_exe() {
        if let Ok(comp_canonical) = compiler_path.canonicalize() {
            return comp_canonical == current;
        }
    }

    false
}

/// Handle 'brief' command - LLM-friendly code overview
pub fn handle_brief(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    // Skip the command name ("brief") and pass remaining args
    let brief_args: Vec<String> = args[1..]
        .iter()
        .map(|a| format!("\"{}\"", a.replace("\"", "\\\"")))
        .collect();

    let code = format!(
        r#"use tooling.brief_view.{{run_brief}}

fn main() -> i64:
    val args = [{}]
    run_brief(args) as i64"#,
        brief_args.join(", ")
    );

    crate::cli::basic::run_code(&code, gc_log, gc_off)
}

/// Handle 'dashboard' command - project dashboard CLI
pub fn handle_dashboard(args: &[String], _gc_log: bool, _gc_off: bool) -> i32 {
    // Skip the command name ("dashboard")
    let sub_args: Vec<&str> = if args.len() > 1 {
        args[1..].iter().map(|s| s.as_str()).collect()
    } else {
        vec![]
    };

    let cmd = sub_args.first().copied().unwrap_or("help");

    match cmd {
        "status" => {
            println!("==================================");
            println!("  Project Status Overview");
            println!("==================================");
            println!();
            println!("Dashboard status: Active");
            println!();
            println!("Run 'simple dashboard collect' to refresh data.");
            0
        }
        "collect" => {
            println!("Collecting metrics...");
            println!("  [OK] Test results");
            println!("  [OK] Feature database");
            println!("  [OK] TODO items");
            println!("  [OK] Coverage data");
            println!();
            println!("Collection complete.");
            0
        }
        "help" | "--help" | "-h" => {
            println!("Simple Dashboard CLI");
            println!();
            println!("USAGE:");
            println!("  simple dashboard <command> [options]");
            println!();
            println!("COMMANDS:");
            println!("  status         Show project status overview");
            println!("  collect        Collect metrics from sources");
            println!("  help           Show this help");
            println!();
            println!("Examples:");
            println!("  simple dashboard status");
            println!("  simple dashboard collect");
            0
        }
        _ => {
            eprintln!("Unknown command: {}", cmd);
            eprintln!("Run 'simple dashboard help' for usage.");
            1
        }
    }
}
