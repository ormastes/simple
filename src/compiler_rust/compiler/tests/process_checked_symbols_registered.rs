//! Reproduce + regression gate for
//! `doc/08_tracking/bug/jit_unresolved_rt_process_read_stdout_checked_2026-08-22.md`.
//!
//! `rt_process_read_stdout_checked` (and its whole C-only `rt_process_*_piped`
//! family) is listed in `RUNTIME_SYMBOL_NAMES`, declared as an `extern` in
//! `src/lib/nogc_sync_mut/io/process_ops.spl`, dispatched by
//! `interpreter_extern/system.rs`, and DEFINED in `src/runtime/runtime_process.c`
//! — but `src/compiler_rust/runtime/build.rs` never listed that C file, so the
//! symbol was absent from `RUNTIME_SYMBOL_ENTRIES`. The JIT's
//! `first_unresolved_import` guard therefore tripped on it and dropped the whole
//! stage1 module to the interpreter (~100-1000x slowdown).
//!
//! Pre-fix this test fails with `not registered`; post-fix every name resolves.
//! It deliberately checks the whole family, not just the one name the JIT
//! happened to report first — the others were equally unresolvable and would
//! have surfaced one at a time.

use simple_native_loader::{RuntimeSymbolProvider, static_provider};

/// C-only (`src/runtime/runtime_process.c`) runtime symbols that are listed in
/// `RUNTIME_SYMBOL_NAMES` and so must be resolvable by the JIT.
const C_ONLY_PROCESS_SYMBOLS: &[&str] = &[
    "rt_process_read_stdout_checked",
    "rt_process_is_alive_checked",
];

fn registered() -> std::sync::Arc<dyn RuntimeSymbolProvider> {
    simple_runtime::register_static_runtime_symbols();
    static_provider()
}

#[test]
fn checked_process_symbols_are_registered_for_jit() {
    let provider = registered();
    let missing: Vec<&str> = C_ONLY_PROCESS_SYMBOLS
        .iter()
        .copied()
        .filter(|name| provider.get_symbol(name).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "runtime symbols listed in RUNTIME_SYMBOL_NAMES but not registered \
         (the JIT will report them as `unresolved external symbol` and de-JIT \
         the whole module): {missing:?}"
    );
}

/// Non-vacuity: the lookup mechanism itself must be live, so an empty/inert
/// registry cannot make the assertion above pass by accident.
#[test]
fn registry_is_live() {
    let provider = registered();
    assert!(
        provider.get_symbol("rt_array_new").is_some(),
        "static runtime symbol registry is inert; the family check above proves nothing"
    );
    assert!(
        provider.get_symbol("rt_definitely_not_a_runtime_symbol").is_none(),
        "registry answers Some for a nonexistent symbol; it cannot discriminate"
    );
}
