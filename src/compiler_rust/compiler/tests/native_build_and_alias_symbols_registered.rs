//! Reproduce + regression gate for
//! `doc/08_tracking/bug/jit_unresolved_rt_native_build_and_runtime_file_rename_2026-08-22.md`.
//!
//! Same defect class as
//! `jit_unresolved_rt_process_read_stdout_checked_2026-08-22.md`: one
//! unresolvable `Linkage::Import` makes `first_unresolved_import` drop the
//! WHOLE stage1 module to the interpreter.
//!
//! Two distinct causes, two distinct fixes, both pinned here:
//!
//! 1. `rt_native_build` — a real definition existed, but only in the
//!    `crate-type = ["staticlib"]` `native_all` crate, which nothing (least of
//!    all the seed binary) can depend on. Relocated into `simple-compiler`
//!    (`native_build_sffi`) and registered by ADDRESS through
//!    `codegen::jit::compiler_owned_symbol_resolves`. Not a stub.
//!
//! 2. `runtime_file_rename` — not a runtime symbol at all: the local alias of
//!    `use std.io_runtime.{file_rename as runtime_file_rename}`. Fixed in HIR
//!    alias resolution, so it has no entry here; its gate is the compile-side
//!    check below.
//!
//! The third test is the SWEEP: every name in `RUNTIME_SYMBOL_NAMES` must be
//! resolvable exactly the way the JIT resolves it. Any regression of this whole
//! defect class fails here rather than one symbol at a time.

use simple_native_loader::{RuntimeSymbolProvider, static_provider, RUNTIME_SYMBOL_NAMES};

fn registered() -> std::sync::Arc<dyn RuntimeSymbolProvider> {
    simple_runtime::register_static_runtime_symbols();
    static_provider()
}

#[test]
fn rt_native_build_is_resolvable_by_the_jit() {
    assert!(
        simple_compiler::codegen::jit::compiler_owned_symbol_resolves("rt_native_build"),
        "`rt_native_build` is declared `extern` by src/app/cli/bootstrap_main.spl:2 but is \
         not resolvable in the seed image; the JIT will report it as an `unresolved external \
         symbol` and de-JIT the whole stage1 module"
    );
}

/// Non-vacuity for the table above: it must discriminate, not answer yes to
/// everything, and must not be empty.
#[test]
fn compiler_owned_table_is_live() {
    assert!(
        !simple_compiler::codegen::jit::COMPILER_OWNED_RUNTIME_SYMBOLS.is_empty(),
        "compiler-owned symbol table is empty; the assertion above proves nothing"
    );
    for name in simple_compiler::codegen::jit::COMPILER_OWNED_RUNTIME_SYMBOLS {
        assert!(
            simple_compiler::codegen::jit::compiler_owned_symbol_resolves(name),
            "{name} is listed in COMPILER_OWNED_RUNTIME_SYMBOLS but has no address"
        );
    }
    assert!(
        !simple_compiler::codegen::jit::compiler_owned_symbol_resolves(
            "rt_definitely_not_a_compiler_owned_symbol"
        ),
        "compiler-owned table answers yes for a nonexistent symbol; it cannot discriminate"
    );
}

/// Pre-existing population of `RUNTIME_SYMBOL_NAMES` entries with no definition
/// reachable from the seed, measured 2026-08-22 (83 names).
///
/// This is the same population `scripts/check/check-no-unresolved-runtime-symbols.shs`
/// reports and is honestly RED; it is far too large to fix in one change, so it
/// is FROZEN here rather than made fatal at once — the same ratchet shape as
/// `scripts/check/unbacked_extern_baseline.txt`. A NEW unresolvable name fails,
/// and so does a baselined name that has since become resolvable (a stale
/// baseline is how a ratchet silently stops ratcheting).
const UNRESOLVED_BASELINE: &[&str] = &[
    "__simple_runtime_gemm_add",
    "__simple_runtime_matrix_f64_cols",
    "__simple_runtime_matrix_f64_free",
    "__simple_runtime_matrix_f64_get",
    "__simple_runtime_matrix_f64_new",
    "__simple_runtime_matrix_f64_rows",
    "native_tcp_set_read_timeout",
    "native_tcp_set_write_timeout",
    "native_udp_set_read_timeout",
    "native_udp_set_write_timeout",
    "rt_call_ptr_0",
    "rt_call_ptr_1",
    "rt_call_ptr_2",
    "rt_call_ptr_3",
    "rt_char_from_code",
    "rt_cuda_event_create",
    "rt_cuda_event_destroy",
    "rt_cuda_event_elapsed_ns",
    "rt_cuda_event_record",
    "rt_cuda_event_synchronize",
    "rt_dict_insert",
    "rt_ed25519_sign_seed",
    "rt_engine2d_simd_copy_u32",
    "rt_engine2d_simd_fill_u32",
    "rt_hostname",
    "rt_native_profile_count",
    "rt_native_profile_event",
    "rt_pbkdf2_hmac_sha1",
    "rt_pbkdf2_hmac_sha256",
    "rt_pbkdf2_hmac_sha384",
    "rt_pbkdf2_hmac_sha512",
    "rt_process_owned_cancel",
    "rt_process_owned_cancel_value",
    "rt_process_owned_terminate",
    "rt_process_run_owned_bounded_value",
    "rt_simd_copy_row_u32",
    "rt_simd_fill_row_u32",
    "rt_simple_sandbox_section_end",
    "rt_simple_sandbox_section_start",
    "rt_simpleos_file_open_bytes",
    "rt_simpleos_file_read_bytes",
    "rt_simpleos_file_rename_bytes",
    "rt_simpleos_file_write_bytes",
    "rt_simpleos_socket_bind_bytes",
    "rt_simpleos_socket_connect_bytes",
    "rt_simpleos_socket_recv_bytes",
    "rt_simpleos_socket_send_bytes",
    "rt_system_cpu_count",
    "rt_tls13_ed25519_sign",
    "rt_tls13_hkdf_expand_into",
    "rt_tls13_hkdf_expand_label",
    "rt_tls13_hkdf_expand_label_client_app",
    "rt_tls13_hkdf_expand_label_client_hs",
    "rt_tls13_hkdf_expand_label_derived",
    "rt_tls13_hkdf_expand_label_finished",
    "rt_tls13_hkdf_expand_label_into",
    "rt_tls13_hkdf_expand_label_iv",
    "rt_tls13_hkdf_expand_label_key",
    "rt_tls13_hkdf_expand_label_server_app",
    "rt_tls13_hkdf_expand_label_server_hs",
    "rt_tls13_hkdf_extract",
    "rt_tls13_hkdf_extract_into",
    "rt_tls13_x25519_public_key",
    "rt_tls13_x25519_shared_secret",
    "rt_torch_torchtensor_det_checked",
    "rt_torch_torchtensor_max_checked",
    "rt_torch_torchtensor_mean_checked",
    "rt_torch_torchtensor_min_checked",
    "rt_torch_torchtensor_norm_checked",
    "rt_torch_torchtensor_std_checked",
    "rt_torch_torchtensor_sum_checked",
    "rt_torch_torchtensor_var_checked",
    "rt_vulkan_query_elapsed_ns",
    "rt_vulkan_timestamp_period_fnum",
    "rt_vulkan_timestamp_supported",
    "rt_webgpu_compute_draw",
    "rt_webgpu_create_surface",
    "rt_webgpu_destroy_surface",
    "rt_webgpu_init",
    "rt_webgpu_is_available",
    "rt_webgpu_present",
    "rt_webgpu_shutdown",
    "rt_webgpu_upload_pixels",
];

/// Sweep + ratchet over the whole of `RUNTIME_SYMBOL_NAMES`.
///
/// A listed-but-undefined name is precisely the shape that took stage1 down
/// twice (`rt_process_read_stdout_checked`, then `rt_native_build`). Reported
/// as a full list, never one at a time.
#[test]
fn listed_runtime_symbols_do_not_regress() {
    let provider = registered();
    let resolves = |name: &str| {
        provider.get_symbol(name).is_some()
            || simple_compiler::codegen::jit::compiler_owned_symbol_resolves(name)
    };

    // Non-vacuity: the resolution mechanism must be live and must discriminate,
    // otherwise "nothing new is missing" would be meaningless.
    assert!(
        !RUNTIME_SYMBOL_NAMES.is_empty(),
        "RUNTIME_SYMBOL_NAMES is empty; this sweep checks nothing"
    );
    assert!(resolves("rt_array_new"), "symbol registry is inert; this sweep proves nothing");
    assert!(
        !resolves("rt_definitely_not_a_runtime_symbol"),
        "registry answers Some for a nonexistent symbol; it cannot discriminate"
    );

    let baseline: std::collections::HashSet<&str> = UNRESOLVED_BASELINE.iter().copied().collect();
    let missing: std::collections::HashSet<&str> = RUNTIME_SYMBOL_NAMES
        .iter()
        .copied()
        .filter(|name| !resolves(name))
        .collect();

    let mut newly: Vec<&str> = missing.difference(&baseline).copied().collect();
    newly.sort_unstable();
    let mut stale: Vec<&str> = baseline.difference(&missing).copied().collect();
    stale.sort_unstable();

    assert!(
        newly.is_empty(),
        "{} NEW name(s) in RUNTIME_SYMBOL_NAMES have no definition reachable from the seed \
         (each one de-JITs any module that calls it): {:?}",
        newly.len(),
        newly
    );
    assert!(
        stale.is_empty(),
        "{} baselined name(s) are now resolvable; remove them from UNRESOLVED_BASELINE so the \
         ratchet keeps ratcheting: {:?}",
        stale.len(),
        stale
    );
}
