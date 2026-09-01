//! M4 (LLVM mem-infra lane) standalone verification probe — memprof half.
//!
//! Builds one LLVM function containing a genuine heap allocation/access
//! pattern (`LlvmBackend::build_m4_memprof_probe_function`, see
//! `codegen/llvm/backend_core.rs`) and runs it through the REAL
//! `LlvmBackend::emit_object` path — the exact production code this lane
//! changed (`optimize_module_ir`'s `function(memprof),module(memprof-module)`
//! pass-pipeline injection, gated on `SIMPLE_MEM_MEMPROF=1`).
//!
//! This is a `cargo run --example`, not a `#[test]`, for the same reason
//! `m4_asan_probe.rs` documents: `llvm_memprof_enabled()` caches
//! `SIMPLE_MEM_MEMPROF` in a process-wide `OnceLock`, so the on/off
//! comparison must run as two separate processes.
//!
//! Usage:
//!   cargo run --example m4_memprof_probe --features llvm                       # off
//!   SIMPLE_MEM_MEMPROF=1 cargo run --example m4_memprof_probe --features llvm  # on
//!
//! Prints `MEMPROF_SYMBOLS=<n>` and `INSTRUMENTED=yes|no`. Pass a path as the
//! first CLI arg to also write the emitted object file there (used by the M4
//! lane report to link it against the real memprof runtime via `clang
//! -fmemory-profile` and observe a genuine `memprof.profraw` written on run).

use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::codegen::llvm::LlvmBackend;
use simple_compiler::mir::MirModule;
use simple_compiler::optimizations::NativeOptimizationLevel;

fn main() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    // `NativeOptimizationLevel::None`, matching `m4_asan_probe.rs`: no
    // optimizer runs at all, so there is no phase-ordering question of
    // whether memprof's instrumentation survives DCE (empirically it does
    // survive optimization too — see the M4 lane report — but None keeps
    // this probe's signal unambiguous).
    let backend = LlvmBackend::new_with_opt_level(target, NativeOptimizationLevel::None).expect("create LlvmBackend");
    backend
        .build_m4_memprof_probe_function("heap_touch")
        .expect("build M4 memprof probe function");

    let object = backend.emit_object(&MirModule::default()).expect("emit_object");

    let hits = count_occurrences(&object, b"__memprof");
    let instrumented = hits > 0;
    println!("MEMPROF_SYMBOLS={hits}");
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
