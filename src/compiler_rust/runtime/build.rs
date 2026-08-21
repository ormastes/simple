use std::env;
use std::fs;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

#[path = "src/runtime_export_scan.rs"]
mod runtime_export_scan;

fn main() {
    println!("cargo:rerun-if-changed=../common/src/runtime_symbols.rs");
    println!("cargo:rerun-if-changed=src/runtime_export_scan.rs");
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=../../runtime/runtime_memory.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_process_owned.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_memory_guard.h");
    println!("cargo:rerun-if-changed=../../runtime/runtime_time.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_timestamp.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_pool.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_framebuffer.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_image.c");
    println!("cargo:rerun-if-changed=../../runtime/startup/common/runtime_log_hosted.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_socket_nonblock.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_directx_core.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_rocm.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_hosted_signal.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_hosted_fs.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_font.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_value.h");
    println!("cargo:rerun-if-changed=../../runtime/runtime_db.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_memtrack.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_simd_dispatch.c");
    println!("cargo:rerun-if-changed=../../runtime/hosted_win32.c");
    println!("cargo:rerun-if-changed=../../runtime/hosted_cocoa.c");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DRIVER_HOOKS");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_NATIVE_ALL_PROVIDER");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_RUNTIME_SYMBOL_TABLE");

    compile_c_runtime_sources();

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let source = manifest_dir.join("../common/src/runtime_symbols.rs");
    let content = fs::read_to_string(&source).expect("read runtime_symbols.rs");
    let runtime_src = manifest_dir.join("src");
    let runtime_c_dir = manifest_dir.join("../../runtime");
    let runtime_symbol_table = env::var_os("CARGO_FEATURE_RUNTIME_SYMBOL_TABLE").is_some();
    let runtime_regex = env::var_os("CARGO_FEATURE_RUNTIME_REGEX").is_some();

    // Symbols provided by simple-native-all when driver-hooks is active.
    let driver_hooks = env::var_os("CARGO_FEATURE_DRIVER_HOOKS").is_some();
    const DRIVER_HOOK_SYMBOLS: &[&str] = &["rt_cli_run_file"];

    let mut seen = HashSet::new();
    let mut symbols = Vec::new();
    let mut in_list = false;

    for line in content.lines() {
        if line.contains("pub const RUNTIME_SYMBOL_NAMES") {
            in_list = true;
            continue;
        }
        if !in_list {
            continue;
        }
        if line.contains("];") {
            break;
        }
        if let Some(start) = line.find('"') {
            let rest = &line[start + 1..];
            if let Some(end) = rest.find('"') {
                let symbol = rest[..end].to_string();
                if seen.insert(symbol.clone()) {
                    symbols.push(symbol);
                }
            }
        }
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let mut generated = String::new();
    generated.push_str("use simple_runtime_abi::RuntimeSymbolEntry;\n\n");

    if !runtime_symbol_table {
        generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[];\n");
        fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
        return;
    }

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let defined_symbols = collect_defined_runtime_symbols(&runtime_src, &runtime_c_dir, runtime_regex, &target_os);

    generated.push_str("#[allow(clashing_extern_declarations)]\n");
    generated.push_str("mod exported_symbols {\n");
    generated.push_str("    #[allow(clashing_extern_declarations)]\n");
    generated.push_str("    unsafe extern \"C\" {\n");
    for symbol in &symbols {
        if defined_symbols.contains(symbol) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                continue;
            }
            let alias = runtime_symbol_alias(symbol);
            generated.push_str(&format!("        #[link_name = \"{symbol}\"]\n"));
            generated.push_str("        ");
            generated.push_str(&runtime_symbol_declaration(symbol, &alias));
            generated.push('\n');
        }
    }
    generated.push_str("    }\n");
    generated.push_str("}\n\n");
    generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[\n");
    for symbol in &symbols {
        if defined_symbols.contains(symbol) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                continue;
            }
            let alias = runtime_symbol_alias(symbol);
            generated.push_str(&format!(
                "    RuntimeSymbolEntry::new(\"{symbol}\", exported_symbols::{alias} as *const u8),\n"
            ));
        }
    }
    generated.push_str("];\n");

    fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
}

/// Emit the canonical callable ABI for symbols that are also declared by the
/// Rust runtime. A mismatched declaration is undefined behavior if it is ever
/// called and triggers `clashing_extern_declarations` even when used only as a
/// linker anchor. Symbols not yet migrated retain the legacy address-anchor
/// form and are tracked by the SFFI contract inventory.
fn runtime_symbol_declaration(symbol: &str, alias: &str) -> String {
    let signature = match symbol {
        "rt_alloc" => "(size: i64) -> *mut u8",
        "rt_free" => "(ptr: *mut u8)",
        "rt_ptr_read_i64" => "(addr: i64, offset: i64) -> i64",
        "rt_ptr_read_u8" => "(addr: i64, offset: i64) -> i64",
        "rt_ptr_read_i32" => "(addr: i64, offset: i64) -> i32",
        "rt_ptr_write_u8" => "(addr: i64, offset: i64, value: i64)",
        "rt_ptr_write_i32" => "(addr: i64, offset: i64, value: i32)",
        "rt_ptr_write_i64" => "(addr: i64, offset: i64, value: i64)",
        "rt_ptr_write_bytes_raw" => "(addr: i64, offset: i64, src: *const u8, len: i64) -> i64",
        "rt_memset" => "(dst: *mut u8, val: i8, n: i64) -> *mut u8",
        "rt_memcpy" => "(dst: *mut u8, src: *const u8, n: i64) -> *mut u8",
        "rt_time_now_nanos" | "rt_time_now_micros" | "rt_time_now_unix_micros" => "() -> i64",
        _ => "()",
    };
    format!("pub fn {alias}{signature};")
}

fn compile_c_runtime_sources() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let runtime_c_dir = manifest_dir.join("../../runtime");
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let native_all_provider = env::var_os("CARGO_FEATURE_NATIVE_ALL_PROVIDER").is_some();
    let mut c_sources = vec![
        "runtime_memory.c",
        "runtime_time.c",
        "runtime_timestamp.c",
        "runtime_db.c",
        "runtime_pool.c",
        "runtime_framebuffer.c",
        "runtime_directx_core.c",
        "runtime_rocm.c",
        "runtime_hosted_signal.c",
        "runtime_hosted_fs.c",
        "runtime_font.c",
        "runtime_memtrack.c",
        "runtime_simd_dispatch.c",
        // rt_opengl_* / rt_oneapi_* (interpreter_extern_registration_lanes.md,
        // lane R2): both families were entirely absent from this list, so the
        // interpreter/seed binary had no path to the real (stub) C
        // definitions -- the same "source-list-absent" shape the rt_sdl2_*
        // lane found, just against this list instead of the
        // native-product-build list at runtime_compiler.spl (which already
        // carries "runtime_native"). The two families live in
        // runtime_native.c alongside ~470 other symbols, several of which
        // (rt_host_gpu_lane_*, rt_host_gpu_queue_*) already have real
        // definitions in this crate's own host_gpu_lane.rs and duplicate-
        // symbol at link time if the whole translation unit is pulled in.
        // runtime_native_gpu_stub.c carries a verbatim, comment-linked copy
        // of only the two families' bodies so this crate can link them
        // without dragging in the rest of runtime_native.c.
        "runtime_native_gpu_stub.c",
        // rt_audio_* (31 names, doc/08_tracking/bug/interpreter_extern_unreachable_names.md
        // bucket (a)): runtime_audio.c was absent from this list entirely, so
        // the interpreter/seed binary had no path to the real (miniaudio-
        // backed) C implementation -- the same "source-list-absent" shape as
        // rt_opengl_*/rt_oneapi_* above. Unlike runtime_native.c, the whole
        // file is safe to compile in directly: it defines only rt_audio_*
        // (checked against this crate's own symbols, including
        // host_gpu_lane.rs, before landing -- no name collision). One
        // function, rt_audio_play_pcm_f32, calls spl_array_get/spl_as_float,
        // which live in runtime.c -- not compiled by this crate (Rust
        // reimplements that layer). SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY below
        // swaps that one function for a trivial stub so the rest of the file
        // still links; the interpreter refuses that name at the Rust
        // dispatch layer (interpreter_extern/audio.rs) and never calls
        // through, so the stub is unreachable from there. The native product
        // build (runtime_compiler.spl) does not define this macro and keeps
        // the real implementation.
        "runtime_audio.c",
        // Remaining bucket (a) "source-list-absent" names after the
        // rt_audio_* lane above (doc/08_tracking/bug/interpreter_extern_unreachable_names.md):
        // rt_image_* (6 names, stb_image-backed, no dependency on anything
        // this crate doesn't compile -- confirmed no other C source here
        // defines STB_IMAGE_IMPLEMENTATION before landing), the hosted
        // log-lib fallback (5 names -- this is the deliberate hosted
        // counterpart to the baremetal src/runtime/startup/baremetal/runtime_log.c,
        // which is NOT compiled here and never has been, so there is no
        // duplicate-symbol risk. The baremetal counterpart is cross-compiled
        // into the SimpleOS sysroot's libsimple_runtime_native.a instead, by
        // src/os/port/llvm/sysroot.shs, scripts/os/simpleos-sysroot-aarch64.shs
        // and scripts/os/simpleos-sysroot-riscv64.shs. The two definitions are
        // mutually exclusive by ARCHIVE: this host archive never gets the
        // baremetal object and the freestanding sysroot archives never get the
        // hosted one, so neither lane needs -z muldefs. Do NOT add
        // startup/baremetal/runtime_log.c to this list), and the standalone
        // rt_socket_set_nonblocking
        // extraction (see that file's header comment for why the whole
        // async_linux_epoll.c it was extracted from is not linked here).
        // runtime_framebuffer.c (rt_fb_*, 2 names) already appears above in
        // this same list -- only its interpreter dispatch entry was missing.
        "runtime_image.c",
        "startup/common/runtime_log_hosted.c",
        "runtime_socket_nonblock.c",
        // Pre-existing gap (unrelated to lane F1): counterpart_abi_runtime.c
        // ships rt_counterpart_*/rt_packed_span_v1_* symbols that
        // interpreter_extern/counterpart.rs declares `extern "C"`, but this
        // list never included the source file, so every seed build on this
        // tree fails to LINK (not compile) with undefined-symbol errors.
        "counterpart_abi_runtime.c",
        // Same pre-existing gap: rt_packed_span_v1_* symbols counterpart.rs
        // also declares extern "C" live in runtime_packed_span.c, also never
        // registered here.
        "runtime_packed_span.c",
        // rt_process_run_owned_bounded_value + rt_process_owned_* (Vulkan
        // Engine2D native-JIT blocker, doc/08_tracking/bug/
        // vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md
        // follow-up): the names are in the runtime_symbols.rs manifest and
        // declared by JIT codegen, but this list never included the source
        // file, so the JIT hit "unresolved external symbol
        // 'rt_process_run_owned_bounded_value'" and dropped whole modules to
        // the interpreter. Its only cross-file C dependency, rt_free_deep
        // (runtime_native.c, not compiled here), is swapped for the Rust
        // rt_string_free via SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE below --
        // exact-equivalent since every value it deep-frees is a string.
        // Re-added after the tree-wipe restore ae55a746719 dropped it again.
        "runtime_process_owned.c",
    ];
    if target_os != "windows" && !native_all_provider {
        c_sources.push("hosted_win32.c");
    }

    let mut build = cc::Build::new();
    build.opt_level(2).warnings(false).cargo_metadata(false);
    build.define("SIMPLE_RUNTIME_OPENCL_ONLY", None);
    // See the runtime_audio.c comment above: this crate doesn't compile
    // runtime.c, so spl_array_get/spl_as_float are unavailable here.
    build.define("SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY", None);
    // See the runtime_process_owned.c comment above: rt_free_deep lives in
    // runtime_native.c, which this crate does not compile.
    build.define("SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE", None);
    if env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default() != "msvc" {
        build.flag_if_supported("-std=gnu11");
    } else {
        // MSVC's default C mode predates C11 <stdatomic.h> support (used by
        // runtime_simd_dispatch.c). `-std=gnu11` above is a GCC/Clang-only
        // flag `cl.exe` doesn't recognize, so `flag_if_supported` silently
        // dropped it here, leaving MSVC on a C mode without atomics and
        // failing with "C atomics require C11 or later" (cl.exe's own
        // vcruntime_c11_stdatomic.h #error). `/std:c11` is cl.exe's
        // equivalent, supported unconditionally on the VS 2022 17.x toolsets
        // this repo targets (verified against MSVC 14.44.35207) — but on
        // THIS toolset `/std:c11` alone still left <stdatomic.h> refusing
        // with "C atomic support is not enabled" (a second, more specific
        // #error a level deeper than the first): MSVC 14.44 still gates the
        // real C11 atomics implementation behind the separate
        // `/experimental:c11atomics` switch even when `/std:c11` is set.
        build.flag_if_supported("/std:c11");
        build.flag_if_supported("/experimental:c11atomics");
    }
    for source in &c_sources {
        let src_path = runtime_c_dir.join(source);
        if src_path.exists() {
            build.file(src_path);
        }
    }
    build.compile("runtime_sffi_c");

    // hosted_cocoa.c is Objective-C behind a .c extension (real NSWindow path
    // on __APPLE__). Compile it separately with the ObjC language flag so the
    // staticlib carries real rt_cocoa_* providers on macOS; AppKit/Foundation
    // are already in the platform framework link set.
    if env::var("CARGO_CFG_TARGET_OS").unwrap_or_default() == "macos" {
        let cocoa = runtime_c_dir.join("hosted_cocoa.c");
        if cocoa.exists() {
            let mut objc = cc::Build::new();
            objc.opt_level(2).warnings(false).cargo_metadata(false);
            objc.flag("-xobjective-c").file(cocoa);
            objc.compile("runtime_sffi_objc");
            println!("cargo:rustc-link-lib=static=runtime_sffi_objc");
        }
    }

    let out_dir = env::var("OUT_DIR").expect("OUT_DIR");
    println!("cargo:rustc-link-search=native={out_dir}");
    if env::var_os("CARGO_FEATURE_RUNTIME_SYMBOL_TABLE").is_some() {
        // A runtime-symbol-table cdylib promises that every registered C
        // provider is dynamically available. Normal selective archive
        // extraction drops providers that are referenced only through the
        // generated table, leaving hosted executables to abort in dyld before
        // backend selection. Whole-archive is intentionally limited to this
        // complete-provider feature; minimal runtime builds stay unchanged.
        println!("cargo:rustc-link-lib=static:+whole-archive=runtime_sffi_c");
    } else {
        println!("cargo:rustc-link-lib=static=runtime_sffi_c");
    }

    if target_os != "windows" {
        println!("cargo:rustc-link-lib=dylib=m");
    } else {
        // hosted_win32.c real mode: CreateWindowExW + CreateDIBSection + BitBlt.
        println!("cargo:rustc-link-lib=dylib=user32");
        println!("cargo:rustc-link-lib=dylib=gdi32");
    }
    // openpty / forkpty live in libutil on Linux and most BSDs.
    // On macOS they are part of libc itself; on Windows the functions don't exist.
    if matches!(target_os.as_str(), "linux" | "freebsd" | "netbsd" | "openbsd") {
        println!("cargo:rustc-link-lib=dylib=util");
    }
}

fn collect_defined_runtime_symbols(
    root: &Path,
    c_root: &Path,
    runtime_regex: bool,
    target_os: &str,
) -> HashSet<String> {
    let mut exported = HashSet::new();
    let mut stack = vec![root.to_path_buf()];

    while let Some(path) = stack.pop() {
        let Ok(entries) = fs::read_dir(&path) else {
            continue;
        };
        for entry in entries.flatten() {
            let entry_path = entry.path();
            if entry.file_type().map(|kind| kind.is_dir()).unwrap_or(false) {
                stack.push(entry_path);
                continue;
            }
            if entry_path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
                continue;
            }
            if !runtime_regex && entry_path.file_name().and_then(|name| name.to_str()) == Some("regex.rs") {
                continue;
            }
            if let Ok(file) = fs::read_to_string(&entry_path) {
                collect_rust_file_exports(&file, &mut exported);
            }
        }
    }

    let native_all_provider = env::var_os("CARGO_FEATURE_NATIVE_ALL_PROVIDER").is_some();
    collect_c_runtime_exports(c_root, target_os, native_all_provider, &mut exported);
    exported
}

fn collect_c_runtime_exports(root: &Path, target_os: &str, native_all_provider: bool, exported: &mut HashSet<String>) {
    const LINKED_C_SOURCES: &[&str] = &[
        "runtime_memory.c",
        "runtime_time.c",
        "runtime_timestamp.c",
        "runtime_db.c",
        "runtime_pool.c",
        "runtime_framebuffer.c",
        "runtime_directx_core.c",
        "runtime_rocm.c",
        "runtime_hosted_signal.c",
        "runtime_hosted_fs.c",
        "runtime_font.c",
        "runtime_memtrack.c",
        "runtime_simd_dispatch.c",
        "hosted_win32.c",
    ];
    for source in LINKED_C_SOURCES {
        if *source == "hosted_win32.c" && (target_os == "windows" || native_all_provider) {
            continue;
        }
        let path = root.join(source);
        let Ok(file) = fs::read_to_string(path) else {
            continue;
        };
        if *source == "runtime_simd_dispatch.c" {
            let dispatch_exports = runtime_export_scan::c_function_definitions(&file);
            exported.extend(
                dispatch_exports
                    .into_iter()
                    .filter(|symbol| symbol.starts_with("rt_opencl_")),
            );
        } else {
            exported.extend(runtime_export_scan::c_function_definitions(&file));
        }
    }
}

fn collect_rust_file_exports(file: &str, exported: &mut HashSet<String>) {
    let lines: Vec<&str> = file.lines().collect();
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(symbol) = export_name_symbol(trimmed) {
            exported.insert(symbol.to_string());
        }
        if !trimmed.contains("fn ") {
            continue;
        }
        let start = idx.saturating_sub(4);
        if lines[start..idx].iter().any(|prev| prev.trim() == "#[no_mangle]") {
            if let Some(symbol) = rust_function_name(trimmed) {
                exported.insert(symbol.to_string());
            }
        }
    }
}

fn export_name_symbol(line: &str) -> Option<&str> {
    let prefix = "#[export_name = \"";
    let suffix = "\"]";
    line.strip_prefix(prefix)?.strip_suffix(suffix)
}

fn rust_function_name(line: &str) -> Option<&str> {
    let fn_pos = line.find("fn ")?;
    let after_fn = &line[fn_pos + 3..];
    let end = after_fn.find('(')?;
    Some(after_fn[..end].trim())
}

fn runtime_symbol_alias(symbol: &str) -> String {
    format!("__simple_runtime_symbol_{}", symbol.replace('.', "_dot_"))
}
