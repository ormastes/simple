//! CLI handler for `simple native-build`: compile a Simple project to a native binary.
//!
//! Usage:
//!   simple native-build [options]
//!
//! Options:
//!   --source <dir>      Source directory (can be repeated; default: src/compiler, src/app, src/lib)
//!   -o <path>           Output binary path (default: bin/simple_native)
//!   --entry <file>      Entry file whose main() becomes the program entry point
//!                        (default: src/app/cli/main.spl if it exists)
//!   --verbose           Verbose output
//!   --strip             Strip symbols from output
//!   --threads <n>       Number of compilation threads (default: all CPUs for
//!                        cranelift, clamped to 4 for llvm -- see LLVM_DEFAULT_MAX_THREADS
//!                        in pipeline/native_project/mod.rs)
//!   --low-memory        Force single-worker compilation regardless of backend/--threads
//!   --timeout <secs>    Per-file compilation timeout (default: 60)
//!   --no-incremental    Disable incremental compilation
//!   --clean             Force clean rebuild (delete cache)
//!   --cache-dir <dir>   Cache directory for incremental builds
//!   --no-mangle         Disable name mangling (enabled by default for symbol collision avoidance)
//!   --backend <name>    Compilation backend (cranelift, llvm)
//!   --cpu <name>        CPU profile: default, native, x86-64-v1..v4
//!   --runtime-bundle <mode> Runtime lane to link (auto, simple-core, core-c-bootstrap)
//!   --mode <name>       Pure-Simple build mode name accepted for bootstrap compatibility:
//!                        dynload or one-binary (seed still emits native bootstrap artifacts)
//!   --emit-archive      Emit a static archive from Simple objects instead of linking an executable
//!   --entry-closure     Compile only modules reachable from --entry
//!   --help              Show help

use std::path::PathBuf;

use simple_compiler::optimizations::{format_optimization_guide, NativeOptimizationLevel};
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_compiler::is_native_codegen_backend_available;
use simple_common::target::{NativeCodegenBackend, TargetCpu};

fn is_valid_runtime_bundle(value: &str) -> bool {
    matches!(
        value,
        "auto"
            | "simple-core"
            | "simple_core"
            | "core-c-bootstrap"
            | "core_c_bootstrap"
            | "runtime"
            | "core"
            | "core-c"
            | "core_c"
            | "host-gpu"
            | "host_gpu"
            | "gpu"
    )
}

fn is_removed_runtime_bundle(value: &str) -> bool {
    matches!(
        value,
        "hosted" | "rust-hosted" | "rust_hosted" | "hosted-runtime" | "rust-runtime" | "all"
    )
}

fn is_allowed_runtime_bundle(value: &str, bootstrap: bool) -> bool {
    is_valid_runtime_bundle(value) || (bootstrap && value == "rust-hosted")
}

fn normalize_backend(value: &str) -> Result<String, String> {
    let normalized = match value.trim().to_ascii_lowercase().as_str() {
        "llvm-lib" | "llvmlib" => "llvm".to_string(),
        other => other.to_string(),
    };
    let backend = normalized
        .parse::<NativeCodegenBackend>()
        .map_err(|_| format!("invalid --backend value '{}'. Expected one of: llvm, cranelift", value))?;
    if !is_native_codegen_backend_available(backend) {
        return Err(format!(
            "native backend '{}' is not available in this build; rebuild the Rust driver with --features llvm or use --backend cranelift",
            backend
        ));
    }
    Ok(backend.to_string())
}

pub fn handle_native_build(args: &[String]) -> i32 {
    let mut source_dirs: Vec<PathBuf> = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut entry_file: Option<PathBuf> = None;
    let mut verbose = false;
    let mut strip = false;
    let mut threads: Option<usize> = None;
    let mut low_memory = false;
    // Large legitimate files need >60s; raised to avoid spurious bootstrap aborts.
    let mut timeout: u64 = 300;
    let mut incremental = true;
    let mut clean = false;
    let mut cache_dir: Option<PathBuf> = None;
    let mut no_mangle = false;
    let mut backend = String::new();
    let mut cpu: Option<TargetCpu> = None;
    let mut runtime_path: Option<PathBuf> = None;
    let mut runtime_bundle = String::from("auto");
    let mut entry_closure = false;
    let mut entry_closure_explicit = false;
    let mut emit_archive = false;
    let mut target_triple: Option<String> = None;
    let mut linker_script: Option<PathBuf> = None;
    let mut opt_level = NativeOptimizationLevel::default_for_native_executable();
    let mut build_mode = String::from("dynload");
    // M4 (LLVM mem-infra lane): `--sanitize` and `--mem-infra=asan` are two
    // spellings of the same request; both fold into one bool. See
    // `NativeBuildConfig::sanitize` and `doc/05_design/compiler/backend/m4_llvm_mem_infra_design.md`.
    let mut sanitize = false;
    // M4: `--memprof` and `--mem-infra=memprof` are two spellings of the same
    // request, mirroring `sanitize` above. See `NativeBuildConfig::memprof`.
    let mut memprof = false;

    // Parse arguments
    let mut i = 1; // Skip "native-build"
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_help();
                return 0;
            }
            "--list-optimizations" => {
                println!("{}", format_optimization_guide());
                return 0;
            }
            "--source" => {
                if i + 1 < args.len() {
                    source_dirs.push(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --source requires a directory path");
                    return 1;
                }
            }
            "-o" | "--output" => {
                if i + 1 < args.len() {
                    output = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: -o requires an output path");
                    return 1;
                }
            }
            "--entry" => {
                if i + 1 < args.len() {
                    entry_file = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --entry requires a file path");
                    return 1;
                }
            }
            "--verbose" | "-v" => {
                verbose = true;
                i += 1;
            }
            "--strip" => {
                strip = true;
                i += 1;
            }
            "--threads" => {
                if i + 1 < args.len() {
                    match args[i + 1].parse() {
                        Ok(n) => threads = Some(n),
                        Err(_) => {
                            eprintln!("error: --threads requires a number");
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --threads requires a number");
                    return 1;
                }
            }
            "--low-memory" => {
                // Forces single-worker compilation regardless of backend or
                // host core count. Previously this flag was UNRECOGNIZED here
                // and silently fell through to the `other => source_dirs.push(..)`
                // catch-all below -- i.e. it was pushed as a (nonexistent)
                // source directory and did nothing whatsoever to bound
                // memory. Every caller that passed `--low-memory` believing
                // it throttled parallelism (e.g.
                // scripts/bootstrap/bootstrap-from-scratch.sh) was getting a
                // no-op. See NativeBuildConfig::low_memory / init_rayon_pool
                // in pipeline/native_project/mod.rs for the actual effect.
                low_memory = true;
                i += 1;
            }
            "--timeout" => {
                if i + 1 < args.len() {
                    match args[i + 1].parse() {
                        Ok(t) => timeout = t,
                        Err(_) => {
                            eprintln!("error: --timeout requires a number");
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --timeout requires a number");
                    return 1;
                }
            }
            "--no-incremental" => {
                incremental = false;
                i += 1;
            }
            "--clean" => {
                clean = true;
                i += 1;
            }
            "--cache-dir" => {
                if i + 1 < args.len() {
                    cache_dir = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --cache-dir requires a directory path");
                    return 1;
                }
            }
            // Declare this lane's private cache scope. Entries produced under one
            // scope are unreachable from another, so concurrent bootstrap lanes
            // sharing a --cache-dir cannot poison each other.
            // doc/05_design/compiler/incremental_build/per_lane_private_caches.md
            "--cache-scope" => {
                if i + 1 < args.len() {
                    std::env::set_var("SIMPLE_CACHE_SCOPE", &args[i + 1]);
                    i += 2;
                } else {
                    eprintln!("error: --cache-scope requires a scope name");
                    return 1;
                }
            }
            "--no-mangle" => {
                no_mangle = true;
                i += 1;
            }
            "--backend" => {
                if i + 1 < args.len() {
                    backend = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("error: --backend requires a value (cranelift or llvm)");
                    return 1;
                }
            }
            other if other.starts_with("--backend=") => {
                backend = other.strip_prefix("--backend=").unwrap_or("").to_string();
                i += 1;
            }
            "--sanitize" => {
                sanitize = true;
                i += 1;
            }
            "--memprof" => {
                memprof = true;
                i += 1;
            }
            other if other.starts_with("--mem-infra=") => {
                let requested = other.strip_prefix("--mem-infra=").unwrap_or("");
                // Deliberately NOT expanding "auto" here: that expansion is
                // backend-conditional (`mem_infra_auto_rows` in
                // `src/lib/common/mem_infra/config.spl`) and CLI args parse
                // in one left-to-right pass, so `--mem-infra=auto` could
                // precede `--backend=`. Only the explicit "asan"/"memprof"
                // rows are safe to act on order-independently.
                if requested.split(',').any(|row| row == "asan") {
                    sanitize = true;
                }
                if requested.split(',').any(|row| row == "memprof") {
                    memprof = true;
                }
                i += 1;
            }
            "--cpu" => {
                if i + 1 < args.len() {
                    match args[i + 1].parse::<TargetCpu>() {
                        Ok(value) => cpu = Some(value),
                        Err(err) => {
                            eprintln!("error: invalid --cpu value '{}': {}", args[i + 1], err);
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --cpu requires a value (default, native, x86-64-v1..v4)");
                    return 1;
                }
            }
            other if other.starts_with("--cpu=") => {
                let value = other.strip_prefix("--cpu=").unwrap_or("");
                match value.parse::<TargetCpu>() {
                    Ok(parsed) => cpu = Some(parsed),
                    Err(err) => {
                        eprintln!("error: invalid --cpu value '{}': {}", value, err);
                        return 1;
                    }
                }
                i += 1;
            }
            "--runtime-path" => {
                if i + 1 < args.len() {
                    runtime_path = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --runtime-path requires a directory path");
                    return 1;
                }
            }
            other if other.starts_with("--runtime-path=") => {
                runtime_path = Some(PathBuf::from(other.strip_prefix("--runtime-path=").unwrap_or("")));
                i += 1;
            }
            "--runtime-bundle" => {
                if i + 1 < args.len() {
                    runtime_bundle = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!(
                        "error: --runtime-bundle requires a value (auto, simple-core, core-c-bootstrap, host-gpu)"
                    );
                    return 1;
                }
            }
            other if other.starts_with("--runtime-bundle=") => {
                runtime_bundle = other.strip_prefix("--runtime-bundle=").unwrap_or("auto").to_string();
                i += 1;
            }
            "--mode" | "--build-mode" => {
                if i + 1 < args.len() {
                    build_mode = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("error: --mode requires dynload or one-binary");
                    return 1;
                }
            }
            other if other.starts_with("--mode=") => {
                let value = other.strip_prefix("--mode=").unwrap_or("");
                build_mode = if value.is_empty() {
                    "dynload".to_string()
                } else {
                    value.to_string()
                };
                i += 1;
            }
            other if other.starts_with("--build-mode=") => {
                let value = other.strip_prefix("--build-mode=").unwrap_or("");
                build_mode = if value.is_empty() {
                    "dynload".to_string()
                } else {
                    value.to_string()
                };
                i += 1;
            }
            "--entry-closure" => {
                entry_closure = true;
                entry_closure_explicit = true;
                i += 1;
            }
            "--no-entry-closure" => {
                entry_closure = false;
                entry_closure_explicit = true;
                i += 1;
            }
            "--emit-archive" => {
                emit_archive = true;
                i += 1;
            }
            "--target" => {
                if i + 1 < args.len() {
                    target_triple = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --target requires a target triple (e.g. riscv32-unknown-none)");
                    return 1;
                }
            }
            other if other.starts_with("--target=") => {
                target_triple = Some(other.strip_prefix("--target=").unwrap_or("").to_string());
                i += 1;
            }
            "--linker-script" => {
                if i + 1 < args.len() {
                    linker_script = Some(PathBuf::from(&args[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --linker-script requires a file path");
                    return 1;
                }
            }
            other if other.starts_with("--linker-script=") => {
                linker_script = Some(PathBuf::from(other.strip_prefix("--linker-script=").unwrap_or("")));
                i += 1;
            }
            "--opt-level" => {
                if i + 1 < args.len() {
                    match NativeOptimizationLevel::parse(&args[i + 1]) {
                        Ok(level) => opt_level = level,
                        Err(err) => {
                            eprintln!("error: {}", err);
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --opt-level requires a value");
                    return 1;
                }
            }
            other if other.starts_with("--opt-level=") => {
                match NativeOptimizationLevel::parse(other.strip_prefix("--opt-level=").unwrap_or("")) {
                    Ok(level) => opt_level = level,
                    Err(err) => {
                        eprintln!("error: {}", err);
                        return 1;
                    }
                }
                i += 1;
            }
            other => {
                // Treat as source directory
                source_dirs.push(PathBuf::from(other));
                i += 1;
            }
        }
    }

    if build_mode != "dynload" && build_mode != "one-binary" {
        eprintln!("error: invalid --mode '{}'. Expected dynload or one-binary", build_mode);
        return 1;
    }

    let bootstrap = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
    if !is_allowed_runtime_bundle(&runtime_bundle, bootstrap) {
        if is_removed_runtime_bundle(&runtime_bundle) {
            eprintln!(
                "error: runtime bundle '{}' was removed; use simple-core or core-c-bootstrap",
                runtime_bundle
            );
            return 1;
        }
        eprintln!(
            "error: invalid --runtime-bundle value '{}'. Expected one of: auto, simple-core, core-c-bootstrap, host-gpu, runtime",
            runtime_bundle
        );
        return 1;
    }

    // Defaults
    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if source_dirs.is_empty() {
        source_dirs.push(project_root.join("src/compiler"));
        source_dirs.push(project_root.join("src/app"));
        source_dirs.push(project_root.join("src/lib"));
    }
    let output = output.unwrap_or_else(|| project_root.join("bin/simple_native"));

    // Auto-default entry file: if not specified and src/app/cli/main.spl exists, use it
    let entry_file = entry_file.or_else(|| {
        let default_entry = project_root.join("src/app/cli/main.spl");
        if default_entry.exists() {
            Some(default_entry)
        } else {
            None
        }
    });

    // When --entry is provided, default to entry-closure discovery so only
    // reachable modules are compiled. This avoids pulling in wrong-arch code
    // (e.g. RISC-V baremetal asm on x86_64) from broad --source dirs like src/lib.
    // Callers can still pass --no-entry-closure to force full-scan if needed.
    if entry_file.is_some() && !entry_closure && !entry_closure_explicit {
        entry_closure = true;
    }

    // Ensure output directory exists
    if let Some(parent) = output.parent() {
        if !parent.exists() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                eprintln!("error: cannot create output directory: {}", e);
                return 1;
            }
        }
    }

    if verbose {
        eprintln!("Simple Native Build");
        eprintln!("  Source dirs: {:?}", source_dirs);
        eprintln!("  Output: {}", output.display());
        eprintln!(
            "  Entry: {}",
            entry_file
                .as_ref()
                .map_or("(none)".to_string(), |p| p.display().to_string())
        );
        eprintln!("  Threads: {}", threads.map_or("auto".to_string(), |n| n.to_string()));
        eprintln!("  Low memory: {}", low_memory);
        eprintln!("  Timeout: {}s", timeout);
        eprintln!("  Incremental: {}", incremental);
        eprintln!("  Mangle: {}", !no_mangle);
        if !backend.is_empty() {
            eprintln!("  Backend: {}", backend);
        }
        if let Some(ref selected_cpu) = cpu {
            eprintln!("  CPU: {}", selected_cpu);
        }
        if let Some(ref rp) = runtime_path {
            eprintln!("  Runtime path: {}", rp.display());
        }
        eprintln!("  Runtime bundle: {}", runtime_bundle);
        eprintln!("  Entry closure: {}", entry_closure);
        eprintln!("  Emit archive: {}", emit_archive);
        eprintln!("  Opt level: {}", opt_level.as_str());
    }

    // Set runtime path override before building
    if let Some(ref rp) = runtime_path {
        simple_compiler::pipeline::native_project::set_runtime_path_override(rp.clone());
        // Also set env vars in-process as fallback
        unsafe {
            std::env::set_var("SIMPLE_RUNTIME_PATH", rp);
        }
    }

    // Set target override before building (used by compile_file_to_object)
    // Parse target triple if provided
    let target = if let Some(ref triple) = target_triple {
        match simple_common::target::Target::parse(triple) {
            Ok(t) => Some(t),
            Err(e) => {
                eprintln!("error: invalid target triple '{}': {}", triple, e);
                return 1;
            }
        }
    } else {
        None
    };

    let mut config = NativeBuildConfig {
        file_timeout: timeout,
        verbose,
        strip,
        num_threads: threads,
        incremental,
        clean,
        cache_dir,
        no_mangle,
        runtime_path,
        runtime_bundle,
        entry_closure,
        target,
        linker_script,
        opt_level,
        emit_archive,
        // SIMPLE_NATIVE_INCREMENTAL=1 no longer gates cache-key correctness (the
        // hardened per-module key is unconditional whenever the object cache is
        // live, see native_project/mod.rs:836-841); it only enables the
        // `[native-incremental] N reused / M rebuilt` receipt line. Also note this
        // Rust handler is reached only via SIMPLE_NATIVE_BUILD_RUST=1 or a
        // cross-target executable build (see dispatch_command in driver/src/main.rs)
        // -- plain `bin/simple native-build` runs the pure-Simple driver instead
        // (src/compiler/80.driver/driver_aot_native_output.spl), whose receipt is
        // `[NATIVE] cache hit: <module>` and which this flag does not affect at all.
        incremental_hardening: std::env::var("SIMPLE_NATIVE_INCREMENTAL").as_deref() == Ok("1"),
        sanitize,
        memprof,
        low_memory,
        ..Default::default()
    };
    // cranelift has no rv32 codegen backend; default rv32 targets to LLVM when the
    // user did not pass an explicit --backend (explicit --backend still wins above).
    if backend.is_empty() && config.target.as_ref().map(|t| t.arch) == Some(simple_common::target::TargetArch::Riscv32)
    {
        backend = "llvm".to_string();
    }
    if !backend.is_empty() {
        let normalized = match normalize_backend(&backend) {
            Ok(value) => value,
            Err(err) => {
                eprintln!("error: {}", err);
                return 1;
            }
        };
        config.backend = normalized.clone();
        // Set env var so compile_file_to_object can select backend.
        std::env::set_var("SIMPLE_BACKEND", &normalized);
    }
    if let Some(selected_cpu) = cpu {
        std::env::set_var("SIMPLE_NATIVE_CPU", selected_cpu.as_str());
    }
    if config.sanitize {
        // M4: asan is LLVM-only per the capability matrix
        // (`src/lib/common/mem_infra/config.spl` — `MemInfraRow(name: "asan",
        // ..., cranelift: false, llvm: true)`). A cranelift/default request
        // is a silent no-op unless we say so: no fallback exists (unlike
        // `strict`, which degrades to `harden` on cranelift), so error loudly
        // rather than pretend coverage that doesn't exist.
        if config.backend != "llvm" {
            eprintln!(
                "error: --sanitize/--mem-infra=asan requires --backend=llvm (got '{}') — asan has no cranelift fallback",
                config.backend
            );
            return 1;
        }
        std::env::set_var("SIMPLE_MEM_ASAN", "1");
    }
    if config.memprof {
        // M4: memprof is LLVM-only per the capability matrix
        // (`src/lib/common/mem_infra/config.spl` — `MemInfraRow(name:
        // "memprof", ..., cranelift: false, llvm: true)`). Same loud-error
        // policy as `sanitize` above: no fallback exists, so a
        // cranelift/default request errors rather than silently no-op'ing.
        if config.backend != "llvm" {
            eprintln!(
                "error: --memprof/--mem-infra=memprof requires --backend=llvm (got '{}') — memprof has no cranelift fallback",
                config.backend
            );
            return 1;
        }
        std::env::set_var("SIMPLE_MEM_MEMPROF", "1");
    }

    // Set target override for compile_file_to_object (thread-safe global)
    if let Some(ref t) = config.target {
        simple_compiler::pipeline::native_project::set_target_override(*t);
    }

    let mut builder = NativeProjectBuilder::new(project_root, output).config(config);
    if let Some(entry) = entry_file {
        builder = builder.entry_file(entry);
    }
    for dir in source_dirs {
        builder = builder.source_dir(dir);
    }

    let build_start = std::time::SystemTime::now();
    match builder.build() {
        Ok(result) => {
            println!(
                "Build complete: {} compiled, {} cached, {} failed",
                result.compiled, result.cached, result.failed
            );
            println!(
                "  {}: {} ({} KB)",
                if result.output.extension().and_then(|ext| ext.to_str()) == Some("a") {
                    "Archive"
                } else {
                    "Binary"
                },
                result.output.display(),
                result.binary_size / 1024
            );
            println!(
                "  Time: {:.1}s compile + {:.1}s link = {:.1}s total",
                result.compile_time.as_secs_f64(),
                result.link_time.as_secs_f64(),
                (result.compile_time + result.link_time).as_secs_f64()
            );

            if !result.failures.is_empty() && verbose {
                eprintln!("\nFailed files:");
                for (path, msg) in &result.failures {
                    eprintln!("  {}: {}", path.display(), msg);
                }
            }

            // Fail closed. Three independent conditions, every one of which
            // used to be reported as SUCCESS by the unconditional `0` below:
            //   1. one or more files failed to compile;
            //   2. the declared artifact is missing, empty, or carries no code;
            //   3. a link step ran but the artifact on disk is stale.
            if result.failed > 0 {
                eprintln!(
                    "\nerror: {} file(s) failed to compile -- build did NOT succeed",
                    result.failed
                );
                return 1;
            }
            let freshness_floor = if result.link_time > std::time::Duration::ZERO {
                Some(build_start)
            } else {
                None
            };
            if let ArtifactVerdict::Reject(why) =
                verify_emitted_artifact(&result.output, freshness_floor)
            {
                eprintln!("\nerror: native-build reported success but {}", why);
                return 1;
            }

            0
        }
        Err(e) => {
            eprintln!("Build failed: {}", e);
            1
        }
    }
}

/// Verdict from the emitted-artifact gate.
///
/// `native-build` used to return 0 on any `Ok(result)` from the builder, so a
/// link that produced a function-less ELF (294 `FILE` symbols, 0 `FUNC`) was
/// still reported as `Build complete`. A false green is worse than a failure:
/// it destroys the evidence that something went wrong. See
/// `doc/08_tracking/bug/native_build_reports_success_for_functionless_artifact_2026-08-10.md`.
///
/// This gate NEVER fabricates anything to make a check pass -- it only reads
/// what was actually emitted and refuses to call an empty artifact a success.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ArtifactVerdict {
    /// Artifact exists and carries real content.
    Ok,
    /// Artifact is missing, empty, or contains no code.
    Reject(String),
}

fn rd_u16(b: &[u8], off: usize) -> Option<u16> {
    Some(u16::from_le_bytes(b.get(off..off + 2)?.try_into().ok()?))
}
fn rd_u32(b: &[u8], off: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(off..off + 4)?.try_into().ok()?))
}
fn rd_u64(b: &[u8], off: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(off..off + 8)?.try_into().ok()?))
}

/// Counts (defined FUNC symbols, total .text bytes) in an ELF64 LE image.
/// Returns `None` when the image is not an ELF64 LE we can parse.
fn elf64_code_census(buf: &[u8]) -> Option<(usize, u64, bool)> {
    if buf.len() < 64 || &buf[0..4] != b"\x7fELF" {
        return None;
    }
    // EI_CLASS == ELFCLASS64, EI_DATA == ELFDATA2LSB
    if buf[4] != 2 || buf[5] != 1 {
        return None;
    }
    let e_shoff = rd_u64(buf, 0x28)? as usize;
    let e_shentsize = rd_u16(buf, 0x3a)? as usize;
    let e_shnum = rd_u16(buf, 0x3c)? as usize;
    let e_shstrndx = rd_u16(buf, 0x3e)? as usize;
    if e_shoff == 0 || e_shnum == 0 || e_shentsize < 64 || e_shstrndx >= e_shnum {
        return None;
    }
    let sh = |i: usize| -> Option<(u32, u32, u64, u64, u64)> {
        let o = e_shoff.checked_add(i.checked_mul(e_shentsize)?)?;
        Some((
            rd_u32(buf, o)?,          // sh_name
            rd_u32(buf, o + 4)?,      // sh_type
            rd_u64(buf, o + 0x18)?,   // sh_offset
            rd_u64(buf, o + 0x20)?,   // sh_size
            rd_u64(buf, o + 0x38)?,   // sh_entsize
        ))
    };
    let (_, _, shstr_off, shstr_size, _) = sh(e_shstrndx)?;
    let shstr = buf.get(shstr_off as usize..(shstr_off + shstr_size) as usize)?;
    let name_at = |n: u32| -> &str {
        let s = n as usize;
        match shstr.get(s..) {
            Some(rest) => {
                let end = rest.iter().position(|&c| c == 0).unwrap_or(rest.len());
                std::str::from_utf8(&rest[..end]).unwrap_or("")
            }
            None => "",
        }
    };

    let mut text_bytes: u64 = 0;
    let mut func_syms: usize = 0;
    let mut saw_symtab = false;
    for i in 0..e_shnum {
        let (nm, sh_type, off, size, entsize) = match sh(i) {
            Some(v) => v,
            None => continue,
        };
        let name = name_at(nm);
        // SHT_PROGBITS(1) with SHF_EXECINSTR is code; keep it simple and look
        // at the canonical text sections the linker emits.
        if name == ".text" || name.starts_with(".text.") {
            text_bytes = text_bytes.saturating_add(size);
        }
        // SHT_SYMTAB == 2, SHT_DYNSYM == 11
        if sh_type == 2 || sh_type == 11 {
            if sh_type == 2 {
                saw_symtab = true;
            }
            if entsize < 24 {
                continue;
            }
            let count = (size / entsize) as usize;
            for k in 0..count {
                let so = off as usize + k * entsize as usize;
                let st_info = match buf.get(so + 4) {
                    Some(v) => *v,
                    None => break,
                };
                let st_shndx = match rd_u16(buf, so + 6) {
                    Some(v) => v,
                    None => break,
                };
                // STT_FUNC == 2, defined means st_shndx != SHN_UNDEF(0)
                if (st_info & 0xf) == 2 && st_shndx != 0 {
                    func_syms += 1;
                }
            }
        }
    }
    Some((func_syms, text_bytes, saw_symtab))
}

/// Fail-closed check that a declared build artifact actually exists and is
/// non-trivial. Never mutates or creates the artifact.
/// `not_older_than`: when `Some(t)`, the artifact must have been written at
/// or after `t`. Callers pass the build start time ONLY when a link step
/// actually ran -- a link that ran must have rewritten its output, so an older
/// mtime means the file on disk is a STALE artifact left by a previous run and
/// an existence check on it is a false green. Cached, no-link builds pass
/// `None` so they cannot be failed for not rewriting a file they never touched.
pub(crate) fn verify_emitted_artifact(
    path: &std::path::Path,
    not_older_than: Option<std::time::SystemTime>,
) -> ArtifactVerdict {
    let meta = match std::fs::metadata(path) {
        Ok(m) => m,
        Err(e) => {
            return ArtifactVerdict::Reject(format!(
                "declared output '{}' does not exist ({})",
                path.display(),
                e
            ))
        }
    };
    if meta.len() == 0 {
        return ArtifactVerdict::Reject(format!("declared output '{}' is empty", path.display()));
    }
    if let Some(floor) = not_older_than {
        match meta.modified() {
            Ok(mtime) => {
                // 2s slack for coarse filesystem timestamp granularity.
                let floor = floor
                    .checked_sub(std::time::Duration::from_secs(2))
                    .unwrap_or(floor);
                if mtime < floor {
                    return ArtifactVerdict::Reject(format!(
                        "declared output '{}' is STALE -- a link step ran but the file on disk predates this build",
                        path.display()
                    ));
                }
            }
            Err(e) => {
                return ArtifactVerdict::Reject(format!(
                    "declared output '{}' has no readable mtime, cannot prove it is fresh ({})",
                    path.display(),
                    e
                ))
            }
        }
    }
    let buf = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            return ArtifactVerdict::Reject(format!(
                "declared output '{}' is unreadable ({})",
                path.display(),
                e
            ))
        }
    };
    match elf64_code_census(&buf) {
        // Not an ELF64 LE image (archive, wasm, mach-o, ELF32): the only claim
        // we can make is non-emptiness, already established above.
        None => ArtifactVerdict::Ok,
        Some((funcs, text_bytes, saw_symtab)) => {
            if funcs > 0 {
                return ArtifactVerdict::Ok;
            }
            if !saw_symtab {
                // Stripped image: fall back to "there is executable content".
                if text_bytes > 0 {
                    return ArtifactVerdict::Ok;
                }
                return ArtifactVerdict::Reject(format!(
                    "declared output '{}' is a stripped ELF with an empty .text -- no code was emitted",
                    path.display()
                ));
            }
            ArtifactVerdict::Reject(format!(
                "declared output '{}' has a symbol table with zero defined FUNC symbols (.text = {} bytes) -- no function was emitted",
                path.display(),
                text_bytes
            ))
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{
        is_allowed_runtime_bundle, normalize_backend, verify_emitted_artifact, ArtifactVerdict,
    };

    /// Regression pins for
    /// `doc/08_tracking/bug/native_build_reports_success_for_functionless_artifact_2026-08-10.md`.
    /// Fixtures are real ELF images -- no stub or empty object is ever
    /// fabricated to make a check pass.
    fn fixture_dir() -> std::path::PathBuf {
        let d = std::env::temp_dir().join(format!("nb_gate_{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    #[test]
    fn rejects_missing_and_empty_artifacts() {
        let d = fixture_dir();
        let missing = d.join("no_such_file.out");
        let _ = std::fs::remove_file(&missing);
        assert!(matches!(
            verify_emitted_artifact(&missing, None),
            ArtifactVerdict::Reject(_)
        ));

        let empty = d.join("empty.out");
        std::fs::write(&empty, b"").unwrap();
        assert!(matches!(
            verify_emitted_artifact(&empty, None),
            ArtifactVerdict::Reject(_)
        ));
        let _ = std::fs::remove_file(&empty);
    }

    #[test]
    fn accepts_real_binary_and_rejects_functionless_elf() {
        let d = fixture_dir();
        // Positive control: the test binary itself is a real ELF with
        // functions, so no toolchain invocation is needed for this half.
        let me = std::env::current_exe().unwrap();
        assert_eq!(verify_emitted_artifact(&me, None), ArtifactVerdict::Ok);

        // Negative control: an ELF64 with a symtab and zero defined FUNC
        // symbols -- the shape the incident produced.
        let asm = d.join("nofunc.s");
        std::fs::write(&asm, ".section .data\n.globl datum\ndatum: .quad 42\n").unwrap();
        let obj = d.join("nofunc.o");
        let cc = std::process::Command::new("cc")
            .arg("-c")
            .arg(&asm)
            .arg("-o")
            .arg(&obj)
            .status();
        if !matches!(cc, Ok(st) if st.success()) {
            eprintln!("SKIP: no working `cc` to build the 0-FUNC fixture");
            return;
        }
        let out = d.join("nofunc.out");
        let ld = std::process::Command::new("ld")
            .arg(&obj)
            .arg("-o")
            .arg(&out)
            .status();
        if !matches!(ld, Ok(st) if st.success()) {
            eprintln!("SKIP: no working `ld` to link the 0-FUNC fixture");
            return;
        }
        match verify_emitted_artifact(&out, None) {
            ArtifactVerdict::Reject(why) => {
                assert!(why.contains("FUNC"), "unexpected reason: {}", why)
            }
            ArtifactVerdict::Ok => panic!("0-FUNC ELF was accepted -- the false green is back"),
        }
    }

    #[test]
    fn rejects_stale_artifact_left_by_a_previous_run() {
        let d = fixture_dir();
        // A valid binary from a PREVIOUS run: it exists, is non-empty, and has
        // functions, so an existence check passes it. Only the freshness floor
        // catches that this build did not produce it.
        let stale = d.join("stale.out");
        std::fs::copy(std::env::current_exe().unwrap(), &stale).unwrap();
        let floor = std::time::SystemTime::now() + std::time::Duration::from_secs(3600);
        match verify_emitted_artifact(&stale, Some(floor)) {
            ArtifactVerdict::Reject(why) => {
                assert!(why.contains("STALE"), "unexpected reason: {}", why)
            }
            ArtifactVerdict::Ok => panic!("a stale artifact was accepted as a fresh build product"),
        }
        // Same file, no freshness claim (cached build, no link ran) -> accepted.
        assert_eq!(verify_emitted_artifact(&stale, None), ArtifactVerdict::Ok);
        let _ = std::fs::remove_file(&stale);
    }


    #[test]
    fn permits_rust_hosted_only_for_bootstrap() {
        assert!(is_allowed_runtime_bundle("rust-hosted", true));
        assert!(!is_allowed_runtime_bundle("rust-hosted", false));
        assert!(is_allowed_runtime_bundle("simple-core", false));
    }

    #[test]
    fn normalizes_llvm_aliases() {
        let expected = if cfg!(feature = "llvm") {
            Ok("llvm".to_string())
        } else {
            Err("not available in this build")
        };
        match (normalize_backend("llvm-lib"), expected) {
            (Ok(actual), Ok(expected)) => assert_eq!(actual, expected),
            (Err(actual), Err(expected)) => assert!(actual.contains(expected)),
            (actual, expected) => panic!("unexpected result: {:?}, expected {:?}", actual, expected),
        }
    }

    #[test]
    fn accepts_cranelift_backend() {
        assert_eq!(normalize_backend("cranelift").unwrap(), "cranelift");
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn accepts_llvm_when_feature_enabled() {
        assert_eq!(normalize_backend("llvm").unwrap(), "llvm");
    }

    #[cfg(not(feature = "llvm"))]
    #[test]
    fn rejects_llvm_when_feature_disabled() {
        let err = normalize_backend("llvm").unwrap_err();
        assert!(err.contains("not available in this build"));
        assert!(err.contains("--features llvm"));
    }

    #[test]
    fn rejects_unknown_backend() {
        let err = normalize_backend("c").unwrap_err();
        assert!(err.contains("invalid --backend value"));
    }
}

fn print_help() {
    println!("Simple Native Build - Compile Simple project to native binary");
    println!();
    println!("Usage: simple native-build [options] [source-dirs...]");
    println!();
    println!("Options:");
    println!("  --source <dir>      Source directory to compile (repeatable)");
    println!("  -o <path>           Output binary path (default: bin/simple_native)");
    println!("  --entry <file>      Entry file whose main() becomes the program entry point");
    println!("                       (default: src/app/cli/main.spl if it exists)");
    println!("  --verbose, -v       Verbose output");
    println!("  --strip             Strip symbols from output");
    println!("  --threads <n>       Number of compilation threads (default: all CPUs; llvm backend defaults to at most 4 -- each worker owns a full LLVM Context/optimizer, so unclamped parallelism balloons memory)");
    println!("  --low-memory        Force single-worker compilation (overrides --threads); use when even the llvm default (4 workers) is too much for the host");
    println!("  --timeout <secs>    Per-file timeout in seconds (default: 60)");
    println!("  --no-incremental    Disable incremental compilation");
    println!("  --clean             Force clean rebuild (delete cache)");
    println!("  --cache-dir <dir>   Cache directory for incremental builds");
    println!("  --cache-scope <name> Private cache lane (env: SIMPLE_CACHE_SCOPE, default: default)");
    println!("  --no-mangle         Disable name mangling (enabled by default)");
    println!("  --backend <name>    Codegen backend: llvm (default when available) or cranelift");
    println!("  --opt-level=<level> Optimization level: none, basic, standard, aggressive");
    println!("  --list-optimizations Print implemented optimization groups and levels");
    println!("  --runtime-bundle <mode> Runtime lane to link (auto, simple-core, core-c-bootstrap)");
    println!("  --mode <name>       Pure-Simple build mode: dynload (default) or one-binary");
    println!("  --emit-archive     Emit a static archive from Simple objects instead of linking an executable");
    println!("  --entry-closure     Compile only modules reachable from --entry");
    println!("  --help, -h          Show this help");
    println!();
    println!("Examples:");
    println!("  simple native-build");
    println!("  simple native-build --source src/compiler --source src/app -o bin/simple_native");
    println!("  simple native-build --entry src/app/cli/main.spl --verbose");
    println!("  simple native-build --verbose --threads 4");
    println!("  simple native-build --clean --verbose");
    println!("  simple native-build --no-incremental");
}
