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
//! The original third test (a sweep freezing the unresolvable
//! `RUNTIME_SYMBOL_NAMES` population as an x86_64-measured baseline) was not
//! restored with this file on 2026-09-28: the population has drifted by 52 new
//! names / 6 stale ones since 2026-08-22 and is host-arch dependent. That
//! population is tracked by `scripts/check/check-no-unresolved-runtime-symbols.shs`.

use simple_native_loader::{static_provider, RuntimeSymbolProvider};

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
        !simple_compiler::codegen::jit::compiler_owned_symbol_resolves("rt_definitely_not_a_compiler_owned_symbol"),
        "compiler-owned table answers yes for a nonexistent symbol; it cannot discriminate"
    );
}
