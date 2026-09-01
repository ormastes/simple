//! M4 (LLVM mem-infra lane) standalone verification probe.
//!
//! Builds one LLVM function containing a deliberate out-of-bounds stack
//! write (`LlvmBackend::build_m4_asan_probe_function`, see
//! `codegen/llvm/backend_core.rs`) and runs it through the REAL
//! `LlvmBackend::emit_object` path — the exact production code this lane
//! changed (`optimize_module_ir`'s asan module-pass injection and
//! `apply_function_optimization_attrs`'s `sanitize_address` attribute,
//! both gated on `SIMPLE_MEM_ASAN=1`).
//!
//! This is a `cargo run --example`, not a `#[test]`, because
//! `llvm_asan_enabled()` caches `SIMPLE_MEM_ASAN` in a process-wide
//! `OnceLock` (the same zero-overhead-when-off pattern as
//! `SIMPLE_MEM_GUARD_RATE` in `interpreter_extern/mem_guard.rs`) — running
//! the on/off comparison inside one `cargo test` binary would race on
//! whichever test's `LlvmBackend` use initializes the cache first. Each
//! invocation below is its own process, so the cache always starts clean.
//!
//! Usage:
//!   cargo run --example m4_asan_probe --features llvm                     # off
//!   SIMPLE_MEM_ASAN=1 cargo run --example m4_asan_probe --features llvm   # on
//!
//! Prints `ASAN_SYMBOLS=<n>` and `INSTRUMENTED=yes|no`. Pass a path as the
//! first CLI arg to also write the emitted object file there (used by the
//! M4 lane report to link and RUN the "on" object under a real process and
//! observe the runtime ASan trap).

use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::codegen::llvm::LlvmBackend;
use simple_compiler::mir::MirModule;
use simple_compiler::optimizations::NativeOptimizationLevel;

fn main() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    // `NativeOptimizationLevel::None` deliberately, not the `Standard`
    // default: at O1+ the standard pipeline legitimately proves this
    // function's whole body has no externally observable effect (nothing
    // calls it, the alloca never escapes) and collapses it to `ret poison`
    // *before* asan gets a chance to instrument anything — independently
    // confirmed with `opt -passes="default<O1>,asan"` and
    // `"default<O2>,asan"`, both of which strip the body while still
    // emitting decoy `__asan_report*` declarations from the module-level
    // ctor boilerplate (a false positive if you only grep symbol counts).
    // This is the same well-known ASan-vs-optimizer interaction that is why
    // upstream clang recommends `-O0`/`-O1` for sanitizer builds, not a bug
    // in this lane's wiring — see the M4 lane report.
    let backend = LlvmBackend::new_with_opt_level(target, NativeOptimizationLevel::None).expect("create LlvmBackend");
    backend
        .build_m4_asan_probe_function("oob_store")
        .expect("build M4 asan probe function");

    let object = backend.emit_object(&MirModule::default()).expect("emit_object");

    let hits = count_occurrences(&object, b"__asan_report");
    let instrumented = hits > 0;
    println!("ASAN_SYMBOLS={hits}");
    println!("INSTRUMENTED={}", if instrumented { "yes" } else { "no" });

    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(&path, &object).expect("write object file");
        println!("OBJECT_PATH={path}");
    }
}

fn count_occurrences(haystack: &[u8], needle: &[u8]) -> usize {
    if needle.is_empty() || haystack.len() < needle.len() {
        return 0;
    }
    haystack.windows(needle.len()).filter(|w| *w == needle).count()
}
