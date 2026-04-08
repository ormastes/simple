//! CLI handler for `simple native-build`: compile a Simple project to a native binary.
//!
//! Usage:
//!   simple native-build [options]
//!
//! Options:
//!   --source <dir>      Source directory (can be repeated; default: src/compiler, src/app, src/lib)
//!   -o <path>           Output binary path (default: bin/release/simple_native)
//!   --entry <file>      Entry file whose main() becomes the program entry point
//!                        (default: src/app/cli/main.spl if it exists)
//!   --verbose           Verbose output
//!   --strip             Strip symbols from output
//!   --threads <n>       Number of compilation threads
//!   --timeout <secs>    Per-file compilation timeout (default: 60)
//!   --no-incremental    Disable incremental compilation
//!   --clean             Force clean rebuild (delete cache)
//!   --cache-dir <dir>   Cache directory for incremental builds
//!   --no-mangle         Disable name mangling (enabled by default for symbol collision avoidance)
//!   --backend <name>    Compilation backend (cranelift, llvm)
//!   --runtime-bundle <mode> Runtime libs to link (auto, runtime, all)
//!   --entry-closure     Compile only modules reachable from --entry
//!   --help              Show help

use std::path::PathBuf;

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};

pub fn handle_native_build(args: &[String]) -> i32 {
    let mut source_dirs: Vec<PathBuf> = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut entry_file: Option<PathBuf> = None;
    let mut verbose = false;
    let mut strip = false;
    let mut threads: Option<usize> = None;
    let mut timeout: u64 = 60;
    let mut incremental = true;
    let mut clean = false;
    let mut cache_dir: Option<PathBuf> = None;
    let mut no_mangle = false;
    let mut backend = String::new();
    let mut runtime_path: Option<PathBuf> = None;
    let mut runtime_bundle = String::from("auto");
    let mut entry_closure = false;
    let mut target_triple: Option<String> = None;
    let mut linker_script: Option<PathBuf> = None;

    // Parse arguments
    let mut i = 1; // Skip "native-build"
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_help();
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
                    eprintln!("error: --runtime-bundle requires a value (auto, runtime, all)");
                    return 1;
                }
            }
            other if other.starts_with("--runtime-bundle=") => {
                runtime_bundle = other.strip_prefix("--runtime-bundle=").unwrap_or("auto").to_string();
                i += 1;
            }
            "--entry-closure" => {
                entry_closure = true;
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
            other => {
                // Treat as source directory
                source_dirs.push(PathBuf::from(other));
                i += 1;
            }
        }
    }

    // Defaults
    let project_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if source_dirs.is_empty() {
        source_dirs.push(project_root.join("src/compiler"));
        source_dirs.push(project_root.join("src/app"));
        source_dirs.push(project_root.join("src/lib"));
    }
    let output = output.unwrap_or_else(|| project_root.join("bin/release/simple_native"));

    // Auto-default entry file: if not specified and src/app/cli/main.spl exists, use it
    let entry_file = entry_file.or_else(|| {
        let default_entry = project_root.join("src/app/cli/main.spl");
        if default_entry.exists() {
            Some(default_entry)
        } else {
            None
        }
    });

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
        eprintln!("  Timeout: {}s", timeout);
        eprintln!("  Incremental: {}", incremental);
        eprintln!("  Mangle: {}", !no_mangle);
        if !backend.is_empty() {
            eprintln!("  Backend: {}", backend);
        }
        if let Some(ref rp) = runtime_path {
            eprintln!("  Runtime path: {}", rp.display());
        }
        eprintln!("  Runtime bundle: {}", runtime_bundle);
        eprintln!("  Entry closure: {}", entry_closure);
    }

    // Set runtime path override before building
    if let Some(ref rp) = runtime_path {
        simple_compiler::pipeline::native_project::set_runtime_path_override(rp.clone());
        // Also set env vars in-process as fallback
        unsafe {
            std::env::set_var("SIMPLE_RUNTIME_PATH", rp);
        }
        let native_all = rp.join("libsimple_native_all.a");
        if native_all.exists() {
            unsafe {
                std::env::set_var("SIMPLE_NATIVE_ALL_PATH", &native_all);
            }
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
        ..Default::default()
    };
    if !backend.is_empty() {
        // Normalize backend aliases
        let normalized = match backend.as_str() {
            "llvm-lib" | "llvmlib" => "llvm".to_string(),
            other => other.to_string(),
        };
        config.backend = normalized.clone();
        // Set env var so compile_file_to_object can select backend
        if normalized != "cranelift" {
            std::env::set_var("SIMPLE_BACKEND", &normalized);
        }
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

    match builder.build() {
        Ok(result) => {
            println!(
                "Build complete: {} compiled, {} cached, {} failed",
                result.compiled, result.cached, result.failed
            );
            println!(
                "  Binary: {} ({} KB)",
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

            if result.failed > 0 {
                eprintln!("\nWarning: {} files failed to compile", result.failed);
            }

            0
        }
        Err(e) => {
            eprintln!("Build failed: {}", e);
            1
        }
    }
}

fn print_help() {
    println!("Simple Native Build - Compile Simple project to native binary");
    println!();
    println!("Usage: simple native-build [options] [source-dirs...]");
    println!();
    println!("Options:");
    println!("  --source <dir>      Source directory to compile (repeatable)");
    println!("  -o <path>           Output binary path (default: bin/release/simple_native)");
    println!("  --entry <file>      Entry file whose main() becomes the program entry point");
    println!("                       (default: src/app/cli/main.spl if it exists)");
    println!("  --verbose, -v       Verbose output");
    println!("  --strip             Strip symbols from output");
    println!("  --threads <n>       Number of compilation threads (default: all CPUs)");
    println!("  --timeout <secs>    Per-file timeout in seconds (default: 60)");
    println!("  --no-incremental    Disable incremental compilation");
    println!("  --clean             Force clean rebuild (delete cache)");
    println!("  --cache-dir <dir>   Cache directory for incremental builds");
    println!("  --no-mangle         Disable name mangling (enabled by default)");
    println!("  --backend <name>    Codegen backend: llvm (default when available) or cranelift");
    println!("  --runtime-bundle <mode> Runtime libs to link (auto, runtime, all)");
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
