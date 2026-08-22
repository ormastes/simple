//! `rt_native_build`: the SFFI entry point for the `native-build` command.
//!
//! # Why this lives in `simple-compiler` and not in `native_all`
//!
//! It used to live in `native_all/src/lib.rs`. `native_all` is a
//! `crate-type = ["staticlib"]` crate, so nothing can depend on it — in
//! particular the seed binary (`--bin simple`) cannot. The consequence was
//! that `rt_native_build` was absent from the seed's own image
//! (`nm | grep -c rt_native_build` == 0), so when the seed JIT-compiled
//! `src/app/cli/bootstrap_main.spl` — which declares
//! `extern fn rt_native_build` on line 2 — cranelift declared a
//! `Linkage::Import` that neither the static runtime-symbol registry nor
//! `dlsym(RTLD_DEFAULT)` could resolve. `first_unresolved_import` then dropped
//! the ENTIRE stage1 module to the interpreter:
//!
//! ```text
//! [jit-fallback] unresolved external symbol 'rt_native_build':
//!  whole module dropped to the interpreter
//! ```
//!
//! Its interpreter registration (`interpreter_extern/mod.rs` ->
//! `cli::rt_native_build`) points at `interpreter_not_supported`, so the
//! interpreter lane could not stand in for it either.
//!
//! This module RELOCATES the one existing definition; it does not add a second
//! one and it is emphatically not a stub. Every dependency the body has
//! (`simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder}`,
//! `simple_compiler::optimizations`, `simple_runtime::value`) already lives in
//! or below this crate, so no layering edge is added or reversed. `native_all`
//! keeps exporting the identical symbol, because it already carries
//! `pub use simple_compiler;` — exactly the mechanism by which the
//! `rt_cranelift_*` symbols defined in this crate are rolled into
//! `libsimple_native_all.a` today. The set of symbols in that archive is
//! therefore unchanged; the seed binary gains one it should always have had.
//!
//! See `doc/08_tracking/bug/jit_unresolved_rt_native_build_and_runtime_file_rename_2026-08-22.md`.

use std::path::{Path, PathBuf};

use crate::optimizations::{format_optimization_guide, NativeOptimizationLevel};
use crate::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_runtime::value::{rt_array_get, rt_array_len, rt_string_data, rt_string_len, RuntimeValue};


pub fn native_build_rust_trace_enabled() -> bool {
    matches!(
        std::env::var("SIMPLE_NATIVE_BUILD_RUST_TRACE").as_deref(),
        Ok("1") | Ok("true") | Ok("yes") | Ok("on")
    )
}

pub fn native_build_process_args_usable(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "native-build")
}

pub fn is_valid_runtime_bundle(value: &str) -> bool {
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

pub fn is_removed_runtime_bundle(value: &str) -> bool {
    matches!(
        value,
        "hosted" | "rust-hosted" | "rust_hosted" | "hosted-runtime" | "rust-runtime" | "all"
    )
}

pub fn is_allowed_runtime_bundle(value: &str, bootstrap: bool) -> bool {
    is_valid_runtime_bundle(value) || (bootstrap && value == "rust-hosted")
}

pub fn native_build_bootstrap_mode(bootstrap: bool, stage4: bool) -> bool {
    bootstrap || stage4
}

// Helper: extract a Rust String from a Simple runtime string value.
pub fn extract_rt_string(val: RuntimeValue) -> Option<String> {
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
pub fn extract_rt_string_array(arr: RuntimeValue) -> Vec<String> {
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

pub fn resolve_native_build_entry(
    explicit: Option<PathBuf>,
    bare_spl: &[PathBuf],
) -> Result<Option<PathBuf>, &'static str> {
    if explicit.is_some() {
        return Ok(explicit);
    }
    match bare_spl {
        [] => Ok(None),
        [entry] => Ok(Some(entry.clone())),
        _ => Err("multiple bare .spl inputs are ambiguous; use --entry <file>"),
    }
}

/// SFFI entry point for native-build command.
///
/// Args is a Simple runtime array of strings:
///   ["native-build", "--source", "src/compiler", "--source", "src/app", ...]
///
/// Returns exit code (0 = success).
#[no_mangle]
pub extern "C" fn rt_native_build(args: RuntimeValue) -> i64 {
    let args_vec = if std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1") {
        // ponytail: bootstrap binaries currently mix the C array ABI with the
        // Rust RuntimeValue ABI. Prefer process argv when the native runtime
        // initialized it; otherwise preserve the Simple array passed by
        // bootstrap_main instead of silently compiling the default project.
        let process_args: Vec<String> = std::env::args().collect();
        if native_build_process_args_usable(&process_args) {
            process_args
        } else {
            extract_rt_string_array(args)
        }
    } else {
        extract_rt_string_array(args)
    };
    if native_build_rust_trace_enabled() {
        eprintln!("[native-rust-trace] raw args={:?}", args_vec);
    }

    let mut source_dirs: Vec<PathBuf> = Vec::new();
    let mut bare_spl: Vec<PathBuf> = Vec::new();
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
    let mut backend = if cfg!(feature = "llvm") { "llvm" } else { "cranelift" }.to_string();
    let mut runtime_path: Option<PathBuf> = None;
    let mut runtime_bundle = "auto".to_string();
    let mut entry_closure = false;
    let mut emit_archive = false;
    let mut target_triple: Option<String> = None;
    let mut target_cpu: Option<String> = None;
    let mut linker_script: Option<PathBuf> = None;
    let mut log_mode = "on".to_string();
    let mut opt_level = NativeOptimizationLevel::default_for_native_executable();

    // Parse arguments — skip binary name and "native-build" command prefix.
    // The args may come as ["native-build", ...] or ["path/to/simple", "native-build", ...].
    let mut i = 0;
    // Skip past the binary name and/or "native-build" command word
    while i < args_vec.len() {
        if args_vec[i] == "native-build" {
            i += 1; // skip "native-build" itself
            break;
        }
        i += 1; // skip binary name or other preamble
    }
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
                println!("  --cache-scope <name> Private cache lane (env: SIMPLE_CACHE_SCOPE)");
                println!("  --no-mangle         Disable name mangling");
                println!("  --backend <name>    Codegen backend: llvm (default when available) or cranelift");
                println!("  --opt-level=<level> Optimization level: none, basic, standard, aggressive");
                println!("  --list-optimizations Print implemented optimization groups and levels");
                println!(
                    "  --runtime-bundle <mode> Runtime lane to link: auto (default), simple-core, or core-c-bootstrap"
                );
                println!("  --runtime-path <dir> Directory containing libsimple_runtime.a");
                println!("  --entry-closure     Compile only modules reachable from --entry");
                println!(
                    "  --emit-archive      Emit a static archive from Simple objects instead of linking an executable"
                );
                println!("  --target <triple>   Cross-compilation target (e.g. x86_64-unknown-none)");
                println!("  --cpu <policy>      CPU policy: default, native, or x86-64-v1..v4");
                println!("  --linker-script <f> Linker script for freestanding/OS targets");
                println!("  --log <on|off>      Compile normal SimpleOS logging in or out");
                return 0;
            }
            "--list-optimizations" => {
                println!("{}", format_optimization_guide());
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
            // See doc/05_design/compiler/incremental_build/per_lane_private_caches.md
            "--cache-scope" => {
                if i + 1 < args_vec.len() {
                    std::env::set_var("SIMPLE_CACHE_SCOPE", &args_vec[i + 1]);
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
                if i + 1 < args_vec.len() {
                    backend = args_vec[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("error: --backend requires a value (cranelift or llvm)");
                    return 1;
                }
            }
            "--runtime-bundle" => {
                if i + 1 < args_vec.len() {
                    runtime_bundle = args_vec[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("error: --runtime-bundle requires a value (auto, simple-core, core-c-bootstrap)");
                    return 1;
                }
            }
            "--runtime-path" => {
                if i + 1 < args_vec.len() {
                    runtime_path = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --runtime-path requires a directory path");
                    return 1;
                }
            }
            "--entry-closure" => {
                entry_closure = true;
                i += 1;
            }
            "--mode" => {
                if i + 1 < args_vec.len() {
                    i += 2;
                } else {
                    eprintln!("error: --mode requires a value");
                    return 1;
                }
            }
            "--emit-archive" => {
                emit_archive = true;
                i += 1;
            }
            "--target" => {
                if i + 1 < args_vec.len() {
                    target_triple = Some(args_vec[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --target requires a target triple (e.g. x86_64-unknown-none)");
                    return 1;
                }
            }
            "--cpu" => {
                if i + 1 < args_vec.len() {
                    target_cpu = Some(args_vec[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --cpu requires a CPU policy");
                    return 1;
                }
            }
            "--linker-script" => {
                if i + 1 < args_vec.len() {
                    linker_script = Some(PathBuf::from(&args_vec[i + 1]));
                    i += 2;
                } else {
                    eprintln!("error: --linker-script requires a file path");
                    return 1;
                }
            }
            "--opt-level" => {
                if i + 1 < args_vec.len() {
                    match NativeOptimizationLevel::parse(&args_vec[i + 1]) {
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
            "--log" => {
                if i + 1 < args_vec.len() {
                    if args_vec[i + 1].starts_with('-') {
                        eprintln!("error: --log requires a value (on or off)");
                        return 1;
                    }
                    match args_vec[i + 1].as_str() {
                        "on" | "off" => log_mode = args_vec[i + 1].clone(),
                        other => {
                            eprintln!("error: --log requires 'on' or 'off' (got '{}')", other);
                            return 1;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("error: --log requires a value (on or off)");
                    return 1;
                }
            }
            other => {
                // Handle --key=value forms for flags that take values
                if let Some(val) = other.strip_prefix("--backend=") {
                    backend = val.to_string();
                } else if let Some(val) = other.strip_prefix("--entry=") {
                    entry_file = Some(PathBuf::from(val));
                } else if let Some(val) = other.strip_prefix("--output=") {
                    output = Some(PathBuf::from(val));
                } else if let Some(val) = other.strip_prefix("--threads=") {
                    match val.parse() {
                        Ok(n) => threads = Some(n),
                        Err(_) => {
                            eprintln!("error: --threads requires a number");
                            return 1;
                        }
                    }
                } else if let Some(val) = other.strip_prefix("--timeout=") {
                    match val.parse() {
                        Ok(t) => timeout = t,
                        Err(_) => {
                            eprintln!("error: --timeout requires a number");
                            return 1;
                        }
                    }
                } else if let Some(val) = other.strip_prefix("--cache-dir=") {
                    cache_dir = Some(PathBuf::from(val));
                } else if let Some(val) = other.strip_prefix("--runtime-path=") {
                    runtime_path = Some(PathBuf::from(val));
                } else if let Some(val) = other.strip_prefix("--target=") {
                    target_triple = Some(val.to_string());
                } else if let Some(val) = other.strip_prefix("--cpu=") {
                    target_cpu = Some(val.to_string());
                } else if let Some(val) = other.strip_prefix("--linker-script=") {
                    linker_script = Some(PathBuf::from(val));
                } else if let Some(val) = other.strip_prefix("--opt-level=") {
                    match NativeOptimizationLevel::parse(val) {
                        Ok(level) => opt_level = level,
                        Err(err) => {
                            eprintln!("error: {}", err);
                            return 1;
                        }
                    }
                } else if let Some(val) = other.strip_prefix("--log=") {
                    match val {
                        "on" | "off" => log_mode = val.to_string(),
                        _ => {
                            eprintln!("error: --log requires 'on' or 'off' (got '{}')", val);
                            return 1;
                        }
                    }
                } else if other.starts_with("--mode=") {
                } else if other.starts_with("--log") {
                    eprintln!(
                        "error: unknown log option '{}'; expected --log or --log=<on|off>",
                        other
                    );
                    return 1;
                } else if let Some(val) = other.strip_prefix("--runtime-bundle=") {
                    runtime_bundle = val.to_string();
                } else if other.starts_with("--") {
                    eprintln!("warning: unknown option '{}', ignoring", other);
                } else if other.ends_with(".spl") {
                    bare_spl.push(PathBuf::from(other));
                } else {
                    source_dirs.push(PathBuf::from(other));
                }
                i += 1;
            }
        }
    }

    let bootstrap = native_build_bootstrap_mode(
        std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1"),
        std::env::var("SIMPLE_BOOTSTRAP_STAGE4").as_deref() == Ok("1"),
    );
    let entry_file = match resolve_native_build_entry(entry_file, &bare_spl) {
        Ok(entry) => entry,
        Err(message) => {
            eprintln!("error: {message}");
            return 1;
        }
    };
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
        eprintln!("  Threads: {}", threads.map_or("auto".to_string(), |n| n.to_string()));
        eprintln!("  Timeout: {}s", timeout);
        eprintln!("  Incremental: {}", incremental);
        eprintln!("  Mangle: {}", !no_mangle);
        eprintln!("  Backend: {}", backend);
        if let Some(ref rp) = runtime_path {
            eprintln!("  Runtime path: {}", rp.display());
        }
        eprintln!("  Entry closure: {}", entry_closure);
        eprintln!("  Emit archive: {}", emit_archive);
        if let Some(ref t) = target_triple {
            eprintln!("  Target: {}", t);
        }
        if let Some(ref ls) = linker_script {
            eprintln!("  Linker script: {}", ls.display());
        }
        eprintln!("  Log mode: {}", log_mode);
        eprintln!("  Opt level: {}", opt_level.as_str());
    }

    // Set runtime path override before building (works in C-compiled binaries)
    if let Some(ref rp) = runtime_path {
        crate::pipeline::native_project::set_runtime_path_override(rp.clone());
        // Also set env var in-process as fallback (for code that checks env vars directly)
        unsafe {
            std::env::set_var("SIMPLE_RUNTIME_PATH", rp);
        }
    }

    let mut config = NativeBuildConfig {
        file_timeout: timeout,
        verbose,
        strip,
        num_threads: threads,
        incremental,
        clean,
        cache_dir,
        no_mangle,
        backend: backend.clone(),
        runtime_path,
        runtime_bundle,
        entry_closure,
        emit_archive,
        linker_script,
        opt_level,
        ..Default::default()
    };

    // Parse and set target override
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
    if let Some(ref t) = target {
        crate::pipeline::native_project::set_target_override(*t);
    }
    config.target = target;
    if let Some(ref cpu) = target_cpu {
        std::env::set_var("SIMPLE_NATIVE_CPU", cpu);
    }

    // Normalize backend aliases
    if backend == "llvm-lib" {
        backend = "llvm".to_string();
    }

    config.backend = backend.clone();

    // Also set env var so compile_file_to_object can read it
    if backend != "cranelift" {
        std::env::set_var("SIMPLE_BACKEND", &backend);
    }
    std::env::set_var("SIMPLE_OS_LOG_MODE", &log_mode);

    if native_build_rust_trace_enabled() {
        eprintln!("[native-rust-trace] parsed native-build args:");
        eprintln!("  project_root={}", project_root.display());
        eprintln!("  output={}", output.display());
        eprintln!(
            "  entry_file={}",
            entry_file
                .as_ref()
                .map_or("<none>".to_string(), |p| p.display().to_string())
        );
        eprintln!(
            "  source_dirs={}",
            source_dirs
                .iter()
                .map(|p| p.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        eprintln!("  entry_closure={}", entry_closure);
        eprintln!("  backend={}", backend);
        eprintln!(
            "  cache_dir={}",
            config
                .cache_dir
                .as_ref()
                .map_or("<default>".to_string(), |p| p.display().to_string())
        );
        eprintln!("  clean={} incremental={} threads={:?}", clean, incremental, threads);
        eprintln!(
            "  env SIMPLE_NATIVE_BUILD_ENTRY={}",
            std::env::var("SIMPLE_NATIVE_BUILD_ENTRY").unwrap_or_else(|_| "<unset>".to_string())
        );
        eprintln!(
            "  env SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE={}",
            std::env::var("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE").unwrap_or_else(|_| "<unset>".to_string())
        );
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
