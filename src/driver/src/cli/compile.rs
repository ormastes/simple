//! Compilation commands: compile, list targets, list linkers.

use simple_common::target::{Target, TargetArch};
use simple_driver::runner::Runner;
use simple_driver::CompileOptions;
use std::path::PathBuf;

/// Compile a source file to SMF format
pub fn compile_file(
    source: &PathBuf,
    output: Option<PathBuf>,
    target: Option<Target>,
    snapshot: bool,
    options: CompileOptions,
) -> i32 {
    use simple_driver::jj::{BuildEvent, BuildState, JJConnector};
    use std::time::Instant;

    // Set environment variable if deprecated syntax warnings should be suppressed
    if options.allow_deprecated {
        std::env::set_var("SIMPLE_ALLOW_DEPRECATED", "1");
    }

    let runner = Runner::new();
    let out_path = output.unwrap_or_else(|| source.with_extension("smf"));

    // Start timing and create build event
    let start_time = Instant::now();
    let mut build_state = BuildState::new();
    build_state.events.push(BuildEvent::CompilationStarted {
        timestamp: std::time::SystemTime::now(),
        files: vec![source.display().to_string()],
    });

    // Use file-based compilation (enables module resolution for imports)
    let result = if let Some(target) = target {
        println!("Cross-compiling for target: {}", target);
        // For cross-compilation, we still need to read the source content
        let source_content = match std::fs::read_to_string(source) {
            Ok(content) => content,
            Err(e) => {
                eprintln!("error: cannot read {}: {}", source.display(), e);
                return 1;
            }
        };
        runner.compile_to_smf_for_target(&source_content, &out_path, target)
    } else {
        // Use file-based compilation which enables import resolution
        runner.compile_file_to_smf_with_options(source, &out_path, &options)
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

/// List available target architectures
pub fn list_targets() -> i32 {
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

/// Compile a source file to a standalone native binary
pub fn compile_file_native(
    source: &PathBuf,
    output: Option<PathBuf>,
    target: Option<Target>,
    linker: Option<simple_compiler::linker::NativeLinker>,
    layout_optimize: bool,
    strip: bool,
    pie: bool,
    shared: bool,
    generate_map: bool,
) -> i32 {
    use simple_compiler::linker::{NativeBinaryOptions, NativeLinker};
    use simple_compiler::pipeline::CompilerPipeline;

    // Determine output path
    let out_path = output.unwrap_or_else(|| {
        // Default: remove extension for native binary
        let stem = source.file_stem().unwrap_or_default();
        source.with_file_name(stem)
    });

    // Read source
    let source_content = match std::fs::read_to_string(source) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", source.display(), e);
            return 1;
        }
    };

    // Build options
    let mut options = NativeBinaryOptions::new()
        .output(&out_path)
        .layout_optimize(layout_optimize)
        .strip(strip)
        .pie(pie)
        .shared(shared)
        .map(generate_map);

    // Set target if specified
    if let Some(t) = target {
        options = options.target(t);
    }

    // Set linker if specified
    if let Some(l) = linker {
        options = options.linker(l);
    }

    // Compile
    let mut pipeline = match CompilerPipeline::new() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: failed to create compiler pipeline: {}", e);
            return 1;
        }
    };

    match pipeline.compile_to_native_binary(&source_content, &out_path, Some(options)) {
        Ok(result) => {
            println!(
                "Compiled {} -> {} ({} bytes)",
                source.display(),
                result.output.display(),
                result.size
            );
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// List available native linkers and their status
pub fn list_linkers() -> i32 {
    use simple_compiler::linker::NativeLinker;

    println!("Available native linkers:");
    println!();

    // Check each linker's availability
    let linkers = [
        (
            NativeLinker::Mold,
            "mold",
            "Modern, fastest linker (Linux only, ~4x faster than lld)",
        ),
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
