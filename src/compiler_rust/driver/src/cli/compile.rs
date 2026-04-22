//! Compilation commands: compile, list targets, list linkers.

use crate::cli::examples_safety::{is_timeout_error, timeout_error_message, ExamplesWatchdogGuard};
use crate::{Interpreter, RunConfig};
use crate::runner::Runner;
use crate::CompileOptions;
use simple_common::smf::{SectionType, SmfHeader, SmfSection, SECTION_FLAG_READ};
use simple_common::target::{Target, TargetArch};
use std::fs;
use std::mem;
use std::path::{Path, PathBuf};

/// Compile a source file to SMF format
pub fn compile_file(
    source: &Path,
    output: Option<PathBuf>,
    target: Option<Target>,
    snapshot: bool,
    options: CompileOptions,
) -> i32 {
    let source = source.to_path_buf();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        compile_file_impl(&source, output, target, snapshot, options)
    }));

    match result {
        Ok(code) => code,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: compiler crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            101
        }
    }
}

/// Generate VHDL from Simple source.
///
/// Builder-oriented sources that print complete VHDL are still supported for
/// compatibility. Ordinary Simple functions fall back to the compiler pipeline's
/// conservative MIR-to-VHDL subset.
pub fn compile_file_to_vhdl(source: &Path, output: Option<PathBuf>) -> i32 {
    let out_path = output.unwrap_or_else(|| source.with_extension("vhd"));
    let interpreter = Interpreter::new();
    let config = RunConfig {
        capture_output: true,
        ..RunConfig::default()
    };

    if let Ok(result) = interpreter.run_file(source, config) {
        if result.exit_code == 0 && looks_like_vhdl(&result.stdout) {
            return write_vhdl_output(&out_path, &result.stdout);
        }
    }

    let mut pipeline = match simple_compiler::pipeline::CompilerPipeline::new() {
        Ok(pipeline) => pipeline,
        Err(err) => {
            eprintln!("error: failed to initialize VHDL compiler pipeline: {err:?}");
            return 1;
        }
    };

    match pipeline.compile_file_to_vhdl(source, &out_path) {
        Ok(()) => {
            println!("Output: {}", out_path.display());
            0
        }
        Err(err) => {
            eprintln!("error: VHDL compilation failed: {err}");
            1
        }
    }
}

fn looks_like_vhdl(text: &str) -> bool {
    let vhdl = text.trim_start();
    vhdl.starts_with("library ")
        || vhdl.starts_with("use ")
        || vhdl.starts_with("package ")
        || vhdl.starts_with("entity ")
}

fn write_vhdl_output(out_path: &Path, vhdl: &str) -> i32 {
    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            if let Err(err) = fs::create_dir_all(parent) {
                eprintln!("error: failed to create output directory {}: {err}", parent.display());
                return 1;
            }
        }
    }

    if let Err(err) = fs::write(out_path, vhdl) {
        eprintln!("error: failed to write VHDL output {}: {err}", out_path.display());
        return 1;
    }

    println!("Output: {}", out_path.display());
    0
}

/// Compile a driver source to an SMF and wrap it in a loadable Library SMF archive.
pub fn compile_dynamic_driver_library(
    source: &Path,
    output: Option<PathBuf>,
    target: Option<Target>,
    _snapshot: bool,
    options: CompileOptions,
) -> i32 {
    let out_path = output.unwrap_or_else(|| source.with_extension("lsm"));
    let tmp = match tempfile::Builder::new()
        .prefix("simple-driver-dynamic-")
        .suffix(".smf")
        .tempfile()
    {
        Ok(tmp) => tmp,
        Err(err) => {
            eprintln!("error: failed to create temporary SMF: {}", err);
            return 1;
        }
    };

    if options.allow_deprecated {
        std::env::set_var("SIMPLE_ALLOW_DEPRECATED", "1");
    }

    let runner = Runner::new();
    let compile_result = if let Some(target) = target {
        runner
            .compile_file_to_smf_for_target(source, tmp.path(), target)
            .map_err(|error| annotate_target_compile_error(target, error))
    } else {
        runner.compile_file_to_smf_with_options(source, tmp.path(), &options)
    };
    if let Err(err) = compile_result {
        eprintln!("error: {}", err);
        return 1;
    }

    let mut smf = match fs::read(tmp.path()) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: failed to read temporary SMF {}: {}", tmp.path().display(), err);
            return 1;
        }
    };

    match driver_manifest_from_source(source) {
        Ok(Some(manifest)) => {
            if !contains_drv_manifest(&smf) {
                match add_drv_manifest_section(&smf, &manifest) {
                    Ok(updated) => smf = updated,
                    Err(err) => {
                        eprintln!("error: failed to add .drv_manifest section: {}", err);
                        return 1;
                    }
                }
            }
        }
        Ok(None) => {}
        Err(err) => {
            eprintln!("error: failed to read driver manifest metadata: {}", err);
            return 1;
        }
    }

    let module_name = dynamic_driver_module_name(source);
    if let Err(err) = write_lsmf_archive(&out_path, &module_name, &smf) {
        eprintln!("error: failed to write dynamic driver library: {}", err);
        return 1;
    }

    println!("Compiled {} -> {}", source.display(), out_path.display());
    0
}

fn compile_file_impl(
    source: &Path,
    output: Option<PathBuf>,
    target: Option<Target>,
    snapshot: bool,
    options: CompileOptions,
) -> i32 {
    use crate::jj::{BuildEvent, BuildState, JJConnector};
    use std::time::Instant;

    // Set environment variable if deprecated syntax warnings should be suppressed
    if options.allow_deprecated {
        std::env::set_var("SIMPLE_ALLOW_DEPRECATED", "1");
    }

    let watchdog = ExamplesWatchdogGuard::for_path(source);
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
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if let Some(target) = target {
            println!("Cross-compiling for target: {}", target);
            runner
                .compile_file_to_smf_for_target(source, &out_path, target)
                .map_err(|error| annotate_target_compile_error(target, error))
        } else {
            // Use file-based compilation which enables import resolution
            runner.compile_file_to_smf_with_options(source, &out_path, &options)
        }
    }));

    let duration_ms = start_time.elapsed().as_millis() as u64;

    let result = match result {
        Ok(result) => result,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: compiler crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            return 101;
        }
    };

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
            if watchdog.is_active() && is_timeout_error(&e) {
                eprintln!("error: {}", timeout_error_message(source, watchdog.timeout_secs()));
            } else {
                eprintln!("error: {}", e);
            }

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

fn annotate_target_compile_error(target: Target, error: String) -> String {
    if target.arch.is_wasm() && error.contains("32-bit targets require the LLVM backend") {
        format!(
            "{error}\nHint: rebuild `simple-driver` with `--features wasm` (or at minimum `--features llvm`) for WebAssembly targets."
        )
    } else {
        error
    }
}

const LSMF_HEADER_SIZE: usize = 128;
const LSMF_INDEX_ENTRY_SIZE: usize = 128;
const FNV1A_OFFSET: u64 = 0xcbf29ce484222325;
const FNV1A_PRIME: u64 = 0x100000001b3;

fn write_lsmf_archive(output: &Path, module_name: &str, smf: &[u8]) -> std::io::Result<()> {
    let smf_offset = (LSMF_HEADER_SIZE + LSMF_INDEX_ENTRY_SIZE) as u64;
    let smf_size = smf.len() as u64;
    let smf_hash = fnv1a_hash(smf);

    let mut index = Vec::with_capacity(LSMF_INDEX_ENTRY_SIZE);
    let mut name = [0u8; 64];
    let name_bytes = module_name.as_bytes();
    let copy_len = name_bytes.len().min(63);
    name[..copy_len].copy_from_slice(&name_bytes[..copy_len]);
    index.extend_from_slice(&name);
    push_u64(&mut index, smf_offset);
    push_u64(&mut index, smf_size);
    push_u64(&mut index, 0);
    push_u64(&mut index, 0);
    push_u64(&mut index, smf_hash);
    push_u64(&mut index, 0);
    index.resize(LSMF_INDEX_ENTRY_SIZE, 0);

    let mut content_for_hash = Vec::with_capacity(index.len() + smf.len());
    content_for_hash.extend_from_slice(&index);
    content_for_hash.extend_from_slice(smf);

    let mut header = Vec::with_capacity(LSMF_HEADER_SIZE);
    header.extend_from_slice(b"LSMF");
    header.push(1);
    header.push(0);
    header.extend_from_slice(&[0, 0]);
    push_u32(&mut header, 1);
    push_u64(&mut header, LSMF_HEADER_SIZE as u64);
    push_u64(&mut header, LSMF_INDEX_ENTRY_SIZE as u64);
    push_u64(&mut header, smf_offset);
    push_u64(&mut header, fnv1a_hash(&content_for_hash));
    push_u64(&mut header, fnv1a_hash(&index));
    header.resize(LSMF_HEADER_SIZE, 0);

    let mut archive = Vec::with_capacity(header.len() + index.len() + smf.len());
    archive.extend_from_slice(&header);
    archive.extend_from_slice(&index);
    archive.extend_from_slice(smf);
    fs::write(output, archive)
}

fn fnv1a_hash(data: &[u8]) -> u64 {
    let mut hash = FNV1A_OFFSET;
    for byte in data {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV1A_PRIME);
    }
    hash
}

fn push_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn dynamic_driver_module_name(source: &Path) -> String {
    source
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty())
        .unwrap_or("driver")
        .to_string()
}

fn contains_drv_manifest(smf: &[u8]) -> bool {
    smf.windows(b".drv_manifest".len()).any(|w| w == b".drv_manifest") || smf.windows(4).any(|w| w == b"SVRD")
}

fn driver_manifest_from_source(source: &Path) -> Result<Option<Vec<u8>>, std::io::Error> {
    let text = fs::read_to_string(source)?;
    let Some(attr_start) = text.find("@driver(") else {
        return Ok(None);
    };
    let attr_body_start = attr_start + "@driver(".len();
    let Some(attr_end_rel) = text[attr_body_start..].find(')') else {
        return Ok(None);
    };
    let attr = &text[attr_body_start..attr_body_start + attr_end_rel];
    let name = next_function_name(&text[attr_body_start + attr_end_rel..])
        .or_else(|| source.file_stem().and_then(|s| s.to_str()).map(|s| s.to_string()))
        .unwrap_or_else(|| "driver".to_string());

    let class = parse_named_integer(attr, "class").unwrap_or(0) as u8;
    let vendor = parse_named_integer(attr, "vendor").unwrap_or(0) as u32;
    let version = parse_named_string(attr, "version").unwrap_or_else(|| "0".to_string());
    let devices = parse_device_list(attr);

    let mut out = Vec::new();
    push_u32(&mut out, 0x4452_5653);
    out.push(0);
    out.push(class);
    out.extend_from_slice(&1u16.to_le_bytes());
    push_u32(&mut out, vendor);
    push_u32(&mut out, devices.len() as u32);
    push_fixed_ascii(&mut out, &version, 16);
    push_fixed_ascii(&mut out, &name, 32);
    for device in devices {
        push_u32(&mut out, 0);
        push_u32(&mut out, device as u32);
    }
    Ok(Some(out))
}

fn next_function_name(text: &str) -> Option<String> {
    let fn_pos = text.find("fn ")? + 3;
    let rest = &text[fn_pos..];
    let end = rest
        .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .unwrap_or(rest.len());
    (end > 0).then(|| rest[..end].to_string())
}

fn parse_named_integer(attr: &str, key: &str) -> Option<u64> {
    let marker = format!("{key}");
    let key_pos = attr.find(&marker)?;
    let after_key = &attr[key_pos + marker.len()..];
    let eq_pos = after_key.find('=')?;
    let value = after_key[eq_pos + 1..].trim_start();
    let end = value
        .find(|ch: char| !(ch.is_ascii_hexdigit() || ch == 'x' || ch == 'X'))
        .unwrap_or(value.len());
    parse_int_literal(&value[..end])
}

fn parse_named_string(attr: &str, key: &str) -> Option<String> {
    let marker = format!("{key}");
    let key_pos = attr.find(&marker)?;
    let after_key = &attr[key_pos + marker.len()..];
    let eq_pos = after_key.find('=')?;
    let value = after_key[eq_pos + 1..].trim_start();
    let value = value.strip_prefix('"')?;
    let end = value.find('"')?;
    Some(value[..end].to_string())
}

fn parse_device_list(attr: &str) -> Vec<u64> {
    let Some(key_pos) = attr.find("device") else {
        return Vec::new();
    };
    let after_key = &attr[key_pos + "device".len()..];
    let Some(eq_pos) = after_key.find('=') else {
        return Vec::new();
    };
    let value = after_key[eq_pos + 1..].trim_start();
    if let Some(list) = value.strip_prefix('[') {
        let end = list.find(']').unwrap_or(list.len());
        return list[..end]
            .split(',')
            .filter_map(|part| parse_int_literal(part.trim()))
            .collect();
    }
    parse_int_literal(value).into_iter().collect()
}

fn parse_int_literal(value: &str) -> Option<u64> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return None;
    }
    if let Some(hex) = trimmed.strip_prefix("0x").or_else(|| trimmed.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).ok()
    } else {
        trimmed.parse::<u64>().ok()
    }
}

fn push_fixed_ascii(out: &mut Vec<u8>, value: &str, width: usize) {
    let bytes = value.as_bytes();
    let copy_len = bytes.len().min(width);
    out.extend_from_slice(&bytes[..copy_len]);
    out.resize(out.len() + (width - copy_len), 0);
}

fn add_drv_manifest_section(smf: &[u8], manifest: &[u8]) -> Result<Vec<u8>, String> {
    if smf.len() < mem::size_of::<SmfHeader>() || &smf[..4] != b"SMF\0" {
        return Err("unsupported SMF header layout".to_string());
    }

    let header_size = mem::size_of::<SmfHeader>();
    let section_size = mem::size_of::<SmfSection>();
    let mut header = unsafe { std::ptr::read_unaligned(smf.as_ptr() as *const SmfHeader) };
    let section_table = header.section_table_offset as usize;
    let section_count = header.section_count as usize;
    let old_table_size = section_count
        .checked_mul(section_size)
        .ok_or_else(|| "SMF section table size overflow".to_string())?;
    let old_table_end = section_table + old_table_size;
    if section_table < header_size || old_table_end > smf.len() {
        return Err("invalid SMF section table bounds".to_string());
    }

    header.section_count = header
        .section_count
        .checked_add(1)
        .ok_or_else(|| "SMF section count overflow".to_string())?;
    header.symbol_table_offset = header
        .symbol_table_offset
        .checked_add(section_size as u64)
        .ok_or_else(|| "SMF symbol table offset overflow".to_string())?;

    let mut sections = Vec::with_capacity(section_count + 1);
    for idx in 0..section_count {
        let offset = section_table + idx * section_size;
        let mut section = unsafe { std::ptr::read_unaligned(smf[offset..].as_ptr() as *const SmfSection) };
        if section.offset >= old_table_end as u64 {
            section.offset += section_size as u64;
        }
        sections.push(section);
    }

    let mut name = [0u8; 16];
    name[..13].copy_from_slice(b".drv_manifest");
    sections.push(SmfSection {
        section_type: SectionType::DrvManifest,
        flags: SECTION_FLAG_READ,
        offset: smf.len() as u64 + section_size as u64,
        size: manifest.len() as u64,
        virtual_size: manifest.len() as u64,
        alignment: 8,
        name,
    });

    let mut out = Vec::with_capacity(smf.len() + section_size + manifest.len());
    push_struct(&mut out, &header);
    if section_table > header_size {
        out.extend_from_slice(&smf[header_size..section_table]);
    }
    for section in &sections {
        push_struct(&mut out, section);
    }
    out.extend_from_slice(&smf[old_table_end..]);
    out.extend_from_slice(manifest);
    Ok(out)
}

fn push_struct<T>(out: &mut Vec<u8>, value: &T) {
    let bytes = unsafe { std::slice::from_raw_parts(value as *const T as *const u8, mem::size_of::<T>()) };
    out.extend_from_slice(bytes);
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
    println!("WebAssembly targets:");
    println!("  wasm32-unknown-unknown  - Standalone/browser WASM module");
    println!("  wasm32-wasi             - WASI-compatible WASM module");
    println!();
    println!("Usage: simple compile <source.spl> --target <target>");
    0
}

/// Compile a source file to a standalone native binary
#[allow(clippy::too_many_arguments)]
pub fn compile_file_native(
    source: &Path,
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

    let watchdog = ExamplesWatchdogGuard::for_path(source);

    // Determine output path
    let out_path = output.unwrap_or_else(|| {
        // Default: remove extension for native binary
        let stem = source.file_stem().unwrap_or_default();
        source.with_file_name(stem)
    });

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

    // Use compile_file_to_native_binary which properly resolves imports
    match pipeline.compile_file_to_native_binary(source, &out_path, Some(options)) {
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
            let message = e.to_string();
            if watchdog.is_active() && is_timeout_error(&message) {
                eprintln!("error: {}", timeout_error_message(source, watchdog.timeout_secs()));
            } else {
                eprintln!("error: {}", message);
            }
            1
        }
    }
}

/// Compile a source file to PTX (NVIDIA GPU assembly) output
pub fn compile_file_to_ptx(source: &Path, output: Option<PathBuf>) -> i32 {
    use simple_compiler::pipeline::CompilerPipeline;

    let watchdog = ExamplesWatchdogGuard::for_path(source);
    let out_path = output.unwrap_or_else(|| source.with_extension("ptx"));

    let mut pipeline = match CompilerPipeline::new() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: failed to create compiler pipeline: {}", e);
            return 1;
        }
    };

    match pipeline.compile_file_to_ptx(source, &out_path) {
        Ok(()) => {
            println!("Compiled {} -> {}", source.display(), out_path.display());
            0
        }
        Err(e) => {
            let message = e.to_string();
            if watchdog.is_active() && is_timeout_error(&message) {
                eprintln!("error: {}", timeout_error_message(source, watchdog.timeout_secs()));
            } else {
                eprintln!("error: {}", message);
            }
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
