//! CLI handler for `simple native-build`: compile a Simple project to a native binary.
//!
//! Usage:
//!   simple native-build [options]
//!
//! Options:
//!   --source <dir>      Source directory (can be repeated; default: src/compiler)
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
        eprintln!("  Entry: {}", entry_file.as_ref().map_or("(none)".to_string(), |p| p.display().to_string()));
        eprintln!("  Threads: {}", threads.map_or("auto".to_string(), |n| n.to_string()));
        eprintln!("  Timeout: {}s", timeout);
        eprintln!("  Incremental: {}", incremental);
        eprintln!("  Mangle: {}", !no_mangle);
    }

    let mut config = NativeBuildConfig::default();
    config.file_timeout = timeout;
    config.verbose = verbose;
    config.strip = strip;
    config.num_threads = threads;
    config.incremental = incremental;
    config.clean = clean;
    config.cache_dir = cache_dir;
    config.no_mangle = no_mangle;

    let mut builder = NativeProjectBuilder::new(project_root, output)
        .config(config);
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
                eprintln!(
                    "\nWarning: {} files failed to compile",
                    result.failed
                );
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
