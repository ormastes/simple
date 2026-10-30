//! Extern-table drift guard for the seed interpreter.
//!
//! Class of defect this closes (for every host at once): an `extern fn rt_*`
//! declared in `.spl`, backed by the runtime (present in
//! `simple_common::RUNTIME_SYMBOL_NAMES`), with a live call site, but with no
//! entry in the interpreter's `EXTERN_DISPATCH`, so interpreted code dies with
//! "unknown extern function: rt_...". Instances fixed one at a time before
//! this test existed: rt_tuple_len (#5340), rt_thread_spawn_isolated2 (#5387),
//! rt_mmap, rt_par_atomic_*, rt_io_file_close_value (#4688), and now
//! rt_tuple_new / rt_tuple_set.
//!
//! Universe checked:
//!   declared(.spl under src/lib, src/app, src/compiler)
//!   ∩ called(.spl; the name followed by `(` on a line that is not an
//!             `extern fn` declaration and not a `#` comment)
//!   ∩ RUNTIME_SYMBOL_NAMES
//! Every member must be in EXTERN_DISPATCH, served by one of the prefix
//! dispatchers in `call_extern_function_with_values`, or named below with a
//! reason. The allowlist is explicit and frozen: adding a new caller for an
//! unregistered runtime symbol fails this test until the symbol is either
//! registered or deliberately listed.
//!
//! Symbols defined only by the C runtime (src/runtime/*.c) are outside
//! RUNTIME_SYMBOL_NAMES and therefore outside the universe above; the ones
//! with live `.spl` callers that the interpreter must serve are pinned
//! separately in `PINNED_C_ONLY_SYMBOLS`.

use super::EXTERN_DISPATCH;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// Wildcard namespaces handled outside the table (mirror of the
/// `name.starts_with(..)` arms in `call_extern_function_with_values`).
const PREFIX_DISPATCHERS: &[&str] = &[
    "rt_winit_",
    "rt_rapier2d_",
    "rt_sdl2_",
    "rt_glfw_",
    "rt_sdl3_",
    "rt_audio_",
    "rt_fb_",
    "rt_image_",
    "rt_simpleos_log_",
    "rt_log_target_",
    "rt_opengl_",
    "rt_oneapi_",
    "rt_host_gpu_lane_",
    "rt_host_gpu_queue_",
    "rt_driver_",
    "rt_vulkan_",
];

/// Exact names handled outside the table by a dedicated `dispatch` arm in
/// `call_extern_function_with_values` (not a wildcard namespace).
const EXACT_NAME_DISPATCHERS: &[&str] = &[
    // socket_nonblock::dispatch: scalar syscall shims for pure-Simple rt_socket_set_nonblocking
    "rt_socket_nonblock_prepare",
    "rt_socket_nonblock_commit",
    "rt_socket_nonblock_mask",
];

/// Lane-intentional gaps: families that by design have no interpreter
/// implementation (accelerator/device lanes that only exist natively, or a
/// fallback another test pins). Prefix match.
const ALLOWED_LANE_FAMILIES: &[(&str, &str)] = &[
    ("rt_actor_", "pinned out of the table by `actor_hosted_symbols_keep_dynamic_fallback` (dynamic SFFI fallback by design)"),
    ("rt_cuda_", "CUDA device lane: native-only, no host implementation in the interpreter"),
    ("rt_metal_", "Metal device lane: native-only (Darwin), no interpreter implementation"),
    ("rt_opencl_", "OpenCL device lane: native-only, no interpreter implementation"),
    ("rt_directx_", "DirectX device lane: native-only (Windows), no interpreter implementation"),
    ("rt_engine2d_rocm_", "ROCm engine2d upload/download: native-only"),
    ("rt_engine2d_simd_", "engine2d SIMD span kernels: native/JIT-only"),
    ("rt_gpu_provider_", "GPU provider plugin ABI: loaded as a native satellite, not by the interpreter"),
    ("rt_torch_torchtensor_", "torch tensor reductions: torch feature lane (interp bridges rt_torch_* only when built with torch)"),
    ("rt_dyn_torch_", "dynamic torch tensor construction: torch feature lane"),
];

/// Known, frozen gaps: runtime symbols with live `.spl` callers that the
/// interpreter does not register today. Each is a real "unknown extern
/// function" on the interpreter lane if its caller is reached. They are listed
/// so that NEW drift fails this test while these are worked off; registering
/// one (after reading its runtime ABI) requires removing it here. Exact match.
const ALLOWED_KNOWN_GAPS: &[(&str, &str)] = &[
    ("rt_enum_new", "generic `rt_enum_new<T>(id, discriminant, payload) -> T`; the interpreter would need an id->enum map plus a raw-word->Value bridge. Blocks interpreted enum_wire_restore_nil one call after rt_tuple_new/rt_tuple_set"),
    ("rt_atexit_check", "interp registers rt_atexit_install but not the check probe"),
    ("rt_atomic_bool_fetch_and", "atomic.rs registers the AtomicBool core set and compare_exchange, not fetch_and/not/or"),
    ("rt_atomic_bool_fetch_not", "see rt_atomic_bool_fetch_and"),
    ("rt_atomic_bool_fetch_or", "see rt_atomic_bool_fetch_and"),
    ("rt_bdd_clear_state", "BDD runner externs; the interpreter runs the pure-Simple spec runner instead"),
    ("rt_bdd_expect_truthy", "see rt_bdd_clear_state"),
    ("rt_bdd_format_results", "see rt_bdd_clear_state"),
    ("rt_cli_run_brief", "cli.rs registers many rt_cli_run_* subcommand bridges, but not brief/fix/lex"),
    ("rt_cli_run_fix", "see rt_cli_run_brief"),
    ("rt_cli_run_lex", "see rt_cli_run_brief"),
    ("rt_coverage_path_probe", "coverage.rs registers the condition/decision probes but not the path probe"),
    ("rt_current_task_id", "async task identity; the interpreter has no runtime task table"),
    ("rt_debug_add_breakpoint", "JIT debugger hook family (rt_debug_*); the interpreter has its own debugger"),
    ("rt_debug_continue", "see rt_debug_add_breakpoint"),
    ("rt_debug_current_file", "see rt_debug_add_breakpoint"),
    ("rt_debug_current_line", "see rt_debug_add_breakpoint"),
    ("rt_debug_is_active", "see rt_debug_add_breakpoint"),
    ("rt_debug_locals", "see rt_debug_add_breakpoint"),
    ("rt_debug_pause", "see rt_debug_add_breakpoint"),
    ("rt_debug_remove_all_breakpoints", "see rt_debug_add_breakpoint"),
    ("rt_debug_remove_breakpoint", "see rt_debug_add_breakpoint"),
    ("rt_debug_set_active", "see rt_debug_add_breakpoint"),
    ("rt_debug_set_step_mode", "see rt_debug_add_breakpoint"),
    ("rt_debug_stack_depth", "see rt_debug_add_breakpoint"),
    ("rt_debug_stack_trace", "see rt_debug_add_breakpoint"),
    ("rt_dh_curve25519_free", "X25519 handle family; no X25519 registration in the interpreter"),
    ("rt_dh_curve25519_keypair", "see rt_dh_curve25519_free"),
    ("rt_dh_curve25519_public_key", "see rt_dh_curve25519_free"),
    ("rt_dh_curve25519_shared_secret", "see rt_dh_curve25519_free"),
    ("rt_ed25519_sign_seed", "crypto.rs registers rt_ed25519_sign/_checked and verify/_checked, not the seed form"),
    ("rt_file_view_close_v1", "file view v1 family (C owner runtime_file_view.c); no interpreter twin yet"),
    ("rt_file_view_device_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_inode_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_map_copy_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_mapping_supported_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_open_beneath_no_follow_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_pread_exact_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_prefetch_v1", "see rt_file_view_close_v1"),
    ("rt_file_view_size_v1", "see rt_file_view_close_v1"),
    ("rt_log_clear_scope_levels", "rt_log_* scoped logging family; only rt_simpleos_log_/rt_log_target_ are prefix-dispatched"),
    ("rt_log_emit", "see rt_log_clear_scope_levels"),
    ("rt_log_get_global_level", "see rt_log_clear_scope_levels"),
    ("rt_log_get_scope_level", "see rt_log_clear_scope_levels"),
    ("rt_log_is_enabled", "see rt_log_clear_scope_levels"),
    ("rt_log_set_global_level", "see rt_log_clear_scope_levels"),
    ("rt_log_set_scope_level", "see rt_log_clear_scope_levels"),
    ("rt_madvise", "page advice; memory.rs registers mmap/munmap/mprotect/page_size but not madvise"),
    ("rt_math_hypot", "math.rs lacks hypot"),
    ("rt_path_parent", "path helper; interp exposes rt_path_* subset without parent"),
    ("rt_print_value", "MIR-lowering print builtins; the interpreter implements print/println natively and registers rt_print and rt_print_err only"),
    ("rt_println", "see rt_print_value"),
    ("rt_println_value", "see rt_print_value"),
    ("rt_process_run_with_limits", "rlimit-bounded run (Rust unix-only, audit item 9); interp registers run/run_timeout/run_bounded"),
    ("rt_process_spawn", "raw spawn; the interpreter registers spawn_async/spawn_piped/spawn_guarded but not spawn/spawn_inherit (audit item 5)"),
    ("rt_process_spawn_inherit", "see rt_process_spawn"),
    ("rt_read_stdin_line", "alias of rt_stdin_read_line not registered (interp registers rt_stdin_read_line)"),
    ("rt_realloc", "memory.rs registers rt_alloc/rt_free without realloc"),
    ("rt_stdout_write", "raw stdout write; interp routes output through io/ print handlers"),
    ("rt_string_char_at", "rt_string_* text helpers; the interpreter serves these as language-level text methods, the direct externs are unregistered"),
    ("rt_string_char_code_at", "see rt_string_char_at"),
    ("rt_string_contains", "see rt_string_char_at"),
    ("rt_string_replace", "see rt_string_char_at"),
    ("rt_string_starts_with", "see rt_string_char_at"),
    ("rt_string_trim", "see rt_string_char_at"),
    ("rt_tls13_x25519_public_key", "see rt_dh_curve25519_free"),
    ("rt_tls13_x25519_shared_secret", "see rt_dh_curve25519_free"),
    ("rt_tls_get_cipher_suite", "TLS session queries and the whole rt_tls_server_* side; net_tls_client.rs registers the client connect/read/write/close family only"),
    ("rt_tls_get_negotiated_alpn", "see rt_tls_get_cipher_suite"),
    ("rt_tls_is_handshake_complete", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_accept", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_close_connection", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_create", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_read_checked", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_shutdown", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_write", "see rt_tls_get_cipher_suite"),
    ("rt_tls_server_write_bytes", "see rt_tls_get_cipher_suite"),
    ("rt_write_fill_u32s_to_raw_checksum", "raw u32 fill checksum; JIT/native-only"),
    ("rt_ws_mask_bytes", "WebSocket masking kernel; JIT/native-only"),
];

/// Symbols defined only by the C runtime (outside RUNTIME_SYMBOL_NAMES and
/// the JIT RuntimeFuncSpec table) that have live `.spl` callers the
/// interpreter must serve itself.
const PINNED_C_ONLY_SYMBOLS: &[(&str, &str)] = &[
    ("rt_list_dir_recursive", "runtime_core_io_exports.c only; caller 80.driver/project.spl"),
    ("rt_fs_read_text", "runtime_native.c only; caller sffi/fs.spl fs_read_text"),
];

/// Sentinels that must appear in the scanned universe, so a wrong repo-root
/// path or a broken scanner cannot produce a vacuous pass.
const UNIVERSE_SENTINELS: &[&str] = &["rt_tuple_len", "rt_tuple_new", "rt_tuple_set", "rt_array_len"];

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <repo>/src/compiler_rust/compiler
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let root = manifest
        .ancestors()
        .nth(3)
        .expect("compiler crate must live three levels under the repo root")
        .to_path_buf();
    assert!(
        root.join("src/lib").is_dir() && root.join("src/compiler").is_dir(),
        "repo root not found from CARGO_MANIFEST_DIR: {}",
        root.display()
    );
    root
}

fn collect_spl_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        if file_type.is_dir() {
            collect_spl_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "spl") {
            out.push(path);
        }
    }
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Every `rt_<ident>` immediately followed by `(` in `line`.
fn rt_calls_in_line(line: &str, out: &mut BTreeSet<String>) {
    let bytes = line.as_bytes();
    let mut i = 0;
    while let Some(off) = line[i..].find("rt_") {
        let start = i + off;
        if start > 0 && is_ident_byte(bytes[start - 1]) {
            i = start + 3;
            continue;
        }
        let mut end = start;
        while end < bytes.len() && is_ident_byte(bytes[end]) {
            end += 1;
        }
        if end < bytes.len() && bytes[end] == b'(' {
            out.insert(line[start..end].to_string());
        }
        i = end.max(start + 3);
    }
}

/// (declared, called): `extern fn rt_*` names and `rt_*(` call sites.
fn scan_spl(root: &Path) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut files = Vec::new();
    for sub in ["src/lib", "src/app", "src/compiler"] {
        collect_spl_files(&root.join(sub), &mut files);
    }
    assert!(files.len() > 100, "expected a populated .spl tree, found {} files", files.len());

    let mut declared = BTreeSet::new();
    let mut called = BTreeSet::new();
    for file in files {
        let Ok(text) = fs::read_to_string(&file) else {
            continue;
        };
        for line in text.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with('#') {
                continue;
            }
            if let Some(idx) = line.find("extern fn ") {
                let rest = &line[idx + "extern fn ".len()..];
                let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                if name.starts_with("rt_") {
                    declared.insert(name);
                }
                continue;
            }
            rt_calls_in_line(line, &mut called);
        }
    }
    (declared, called)
}

fn served_by_prefix_dispatcher(name: &str) -> bool {
    PREFIX_DISPATCHERS.iter().any(|prefix| name.starts_with(prefix)) || EXACT_NAME_DISPATCHERS.contains(&name)
}

fn allowlisted(name: &str) -> bool {
    ALLOWED_LANE_FAMILIES.iter().any(|(prefix, _)| name.starts_with(prefix))
        || ALLOWED_KNOWN_GAPS.iter().any(|(gap, _)| *gap == name)
}

#[test]
fn extern_dispatch_covers_declared_runtime_symbols_with_live_callers() {
    let root = repo_root();
    let (declared, called) = scan_spl(&root);
    let runtime: BTreeSet<&str> = simple_common::RUNTIME_SYMBOL_NAMES.iter().copied().collect();

    let universe: BTreeSet<&str> = declared
        .iter()
        .filter(|name| called.contains(*name))
        .filter(|name| runtime.contains(name.as_str()))
        .map(String::as_str)
        .collect();

    for sentinel in UNIVERSE_SENTINELS {
        assert!(universe.contains(sentinel), "scanner lost sentinel {sentinel}; universe has {} names", universe.len());
    }

    let missing: Vec<&str> = universe
        .iter()
        .copied()
        .filter(|name| !EXTERN_DISPATCH.contains_key(name))
        .filter(|name| !served_by_prefix_dispatcher(name))
        .filter(|name| !allowlisted(name))
        .collect();

    assert!(
        missing.is_empty(),
        "{} runtime extern(s) declared in .spl with live callers are missing from the interpreter's \
         EXTERN_DISPATCH (register them in interpreter_extern/mod.rs, or add an explicit entry to \
         ALLOWED_KNOWN_GAPS / ALLOWED_LANE_FAMILIES with the reason):\n  {}",
        missing.len(),
        missing.join("\n  ")
    );

    // The pinned C-only symbols are outside the universe by construction;
    // guard them explicitly so the gap class is closed for them too.
    for (name, why) in PINNED_C_ONLY_SYMBOLS {
        assert!(declared.contains(*name) && called.contains(*name), "{name} lost its .spl declaration/caller ({why})");
        assert!(EXTERN_DISPATCH.contains_key(name), "{name} missing from EXTERN_DISPATCH ({why})");
    }

    // Keep the exact-match allowlist honest: an entry that is no longer a
    // runtime symbol, or that gained a registration, must be removed.
    for (name, _) in ALLOWED_KNOWN_GAPS {
        assert!(runtime.contains(name), "allowlist entry {name} is not in RUNTIME_SYMBOL_NAMES any more; remove it");
        assert!(
            !EXTERN_DISPATCH.contains_key(name),
            "allowlist entry {name} is now registered in EXTERN_DISPATCH; remove it from ALLOWED_KNOWN_GAPS"
        );
    }
}

/// The two tuple externs this guard was written alongside, pinned by name so
/// a stale-WC sync that drops the registration lines is caught even if the
/// `.spl` callers move.
#[test]
fn dispatch_registers_tuple_construction_family() {
    for name in ["rt_tuple_new", "rt_tuple_set", "rt_tuple_get", "rt_tuple_len"] {
        assert!(EXTERN_DISPATCH.contains_key(name), "{name} not registered");
    }
}

/// POSIX libc externs declared by path_identity_abi.spl / errno_abi.spl are
/// served by `posix_abi` (twin of `windows_abi`); they are outside the rt_
/// universe above, so pin them here. The errno owner is pinned by the HOST's
/// spelling only (`__error` on Darwin/FreeBSD, `__errno_location` on Linux,
/// `__errno` on NetBSD/OpenBSD); every other spelling must stay an explicit
/// unknown extern, never a silent stub.
#[cfg(unix)]
#[test]
fn posix_abi_serves_path_identity_externs() {
    for name in ["malloc", "free", "realpath", "readlink", "open", "read", "pread", "write", "close", "fsync"] {
        assert!(super::posix_abi::is_supported_name(name), "{name} not served by posix_abi");
    }
    let expected_host_owner = if cfg!(any(target_os = "macos", target_os = "freebsd")) {
        Some("__error")
    } else if cfg!(target_os = "linux") {
        Some("__errno_location")
    } else if cfg!(any(target_os = "netbsd", target_os = "openbsd")) {
        Some("__errno")
    } else {
        super::posix_abi::ERRNO_ADDRESS_NAME
    };
    assert_eq!(super::posix_abi::ERRNO_ADDRESS_NAME, expected_host_owner);
    for spelling in super::posix_abi::ALL_ERRNO_SPELLINGS {
        assert_eq!(
            super::posix_abi::is_supported_name(spelling),
            expected_host_owner == Some(*spelling),
            "{spelling}"
        );
    }
}
