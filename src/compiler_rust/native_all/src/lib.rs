// Combined static library for native Simple binaries.
//
// This crate produces a single `libsimple_native_all.a` that includes
// ALL transitive dependencies from both `simple-compiler` (Cranelift FFI,
// codegen, parser) and `simple-runtime` (GC, FFI wrappers, actors).
//
// When linked into a native binary produced by `native-build`, the binary
// gains access to `rt_cranelift_*` functions, enabling self-hosted
// compilation (Stage 3 bootstrap).

// Re-export both crates so their #[no_mangle] extern "C" functions
// are included in the static library.
pub use simple_compiler;
pub use simple_runtime;

use std::path::PathBuf;

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_runtime::value::{
    rt_array_get, rt_array_len, rt_string_data, rt_string_len,
    RuntimeValue,
};

// Helper: extract a Rust String from a Simple runtime string value.
fn extract_rt_string(val: RuntimeValue) -> Option<String> {
    let len = rt_string_len(val);
    if len < 0 {
        return None;
    }
    let data = rt_string_data(val);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

// Helper: extract array of strings from a Simple runtime array value.
fn extract_rt_string_array(arr: RuntimeValue) -> Vec<String> {
    let len = rt_array_len(arr);
    let mut result = Vec::new();
    for i in 0..len {
        let val = rt_array_get(arr, i);
        if let Some(s) = extract_rt_string(val) {
            result.push(s);
        }
    }
    result
}

/// FFI entry point for native-build command.
///
/// Args is a Simple runtime array of strings:
///   ["native-build", "--source", "src/compiler", "--source", "src/app", ...]
///
/// Returns exit code (0 = success).
#[no_mangle]
pub extern "C" fn rt_native_build(args: RuntimeValue) -> i64 {
    let args_vec = extract_rt_string_array(args);

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

    // Parse arguments (skip "native-build" at index 0)
    let mut i = 1;
    while i < args_vec.len() {
        match args_vec[i].as_str() {
            "--help" | "-h" => {
                println!("Simple Native Build - Compile Simple project to native binary");
                println!();
                println!("Usage: simple native-build [options] [source-dirs...]");
                println!();
                println!("Options:");
                println!("  --source <dir>      Source directory to compile (repeatable)");
                println!("  -o <path>           Output binary path (default: bin/simple_stage3)");
                println!("  --entry <file>      Entry file (default: src/app/cli/main.spl)");
                println!("  --verbose, -v       Verbose output");
                println!("  --strip             Strip symbols from output");
                println!("  --threads <n>       Number of compilation threads");
                println!("  --timeout <secs>    Per-file timeout (default: 60)");
                println!("  --no-incremental    Disable incremental compilation");
                println!("  --clean             Force clean rebuild");
                println!("  --cache-dir <dir>   Cache directory");
                println!("  --no-mangle         Disable name mangling");
                return 0;
            }
            "--source" => {
                if i + 1 < args_vec.len() {
                    source_dirs.push(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --source requires a directory path");
                    return 1;
                }
            }
            "-o" | "--output" => {
                if i + 1 < args_vec.len() {
                    output = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: -o requires an output path");
                    return 1;
                }
            }
            "--entry" => {
                if i + 1 < args_vec.len() {
                    entry_file = Some(PathBuf::from(&args_vec[i + 1]));
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
                if i + 1 < args_vec.len() {
                    match args_vec[i + 1].parse() {
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
                if i + 1 < args_vec.len() {
                    match args_vec[i + 1].parse() {
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
                if i + 1 < args_vec.len() {
                    cache_dir = Some(PathBuf::from(&args_vec[i + 1]));
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
    let output = output.unwrap_or_else(|| project_root.join("bin/simple_stage3"));

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
        eprintln!("Simple Native Build (self-hosted)");
        eprintln!("  Source dirs: {:?}", source_dirs);
        eprintln!("  Output: {}", output.display());
        eprintln!(
            "  Entry: {}",
            entry_file
                .as_ref()
                .map_or("(none)".to_string(), |p| p.display().to_string())
        );
        eprintln!(
            "  Threads: {}",
            threads.map_or("auto".to_string(), |n| n.to_string())
        );
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
