pub mod backend_trait;
pub mod buffer_pool;
pub mod bytecode;
pub mod closure_boxed_entry;
pub mod common_backend;
mod cranelift;
pub mod cranelift_emitter;
#[allow(clippy::missing_safety_doc)] // reason: safety contract documented in the calling module-level doc comment
pub mod cranelift_sffi;
pub mod dispatch;
pub mod emitter_trait;
pub mod execution_manager;
pub mod instr;
pub mod inline_asm;
pub mod instr_gpu;
#[cfg(not(doctest))]
pub mod local_execution;
#[cfg(all(not(doctest), feature = "llvm"))]
pub mod llvm_jit;
pub mod mir_interpreter;
mod mir_inline;
#[cfg(not(doctest))]
pub mod jit;
pub mod lean;
pub mod llvm;
pub mod parallel;
pub mod runtime_sffi;
pub mod shared;
pub mod types_util;
pub mod vtable_c8_debug;
pub mod vulkan;
pub mod wasm_bindgen_gen;

#[cfg(all(test, feature = "llvm-tests"))]
mod llvm_tests;

#[cfg(test)]
#[cfg(not(doctest))]
#[path = "codegen_instr_tests/mod.rs"]
mod codegen_instr_tests;

#[cfg(test)]
#[cfg(not(doctest))]
#[path = "codegen_shared_tests/mod.rs"]
mod codegen_shared_tests;

#[cfg(all(test, not(doctest), target_arch = "x86_64"))]
#[path = "local_execution_tests.rs"]
mod local_execution_tests;

pub use backend_trait::{BackendKind, NativeBackend};
pub use buffer_pool::{
    acquire_thread_buffer, clear_thread_buffer_pool, init_thread_buffer_pool, init_thread_buffer_pool_with_config,
    release_thread_buffer, thread_buffer_pool_stats, BufferPool, BufferPoolConfig, BufferPoolStats, LocalBufferPool,
    PooledBuffer,
};
pub use closure_boxed_entry::{boxed_entry_name, BOXED_ENTRY_SUFFIX};
pub use common_backend::{BackendError, BackendResult, BackendSettings, CodegenBackend};
pub use cranelift_sffi::clear_cranelift_registries;
pub use cranelift::*;
pub use execution_manager::{CodeInfo, ExecutionManager, ExecutionResult};
#[cfg(not(doctest))]
pub use jit::*;
#[cfg(not(doctest))]
pub use local_execution::{JitBackend, LocalExecutionManager};
pub use parallel::{
    compile_modules_parallel, compile_modules_parallel_with_config, BatchCodegen, CodegenStats, CompiledModule,
    CompiledModuleCache, ParallelCodegen, ParallelCodegenConfig,
};

/// Whether the JIT closure ABI can carry a value of this type across a
/// closure call boundary.
///
/// Every crossing is now TAGGED (see codegen/closure_boxed_entry.rs): the boxed
/// entry unboxes each argument to the type the body was compiled with and boxes
/// the result back. `BOOL` is nevertheless still excluded, and the reason is
/// worth stating because it is NOT an ABI reason: the boxed entry does carry a
/// bool correctly (full-width `rt_value_bool` 0/1, never a bare `i8`), but
/// declaring the OUTLINED BODY's Cranelift return type as `i8` still SIGSEGVs
/// `print(f(32))` for `\\x: x > 1` — measured again on this convention. The
/// defect is in the surrounding sub-register value handling, not at the
/// boundary, so it is refused here and left named rather than papered over.
/// Item 4 of the remaining list in
/// doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md.
///
/// `TypeId::ANY` remains excluded, and that exclusion is the whole point: at an
/// untyped boundary neither side knows whether the word is a tagged integer, a
/// heap-boxed float or a raw handle, so no encoding is correct for all of them.
/// `TypeId::VOID` is excluded as a call-boundary VALUE type for the same
/// reason — a void lambda answers tagged NIL, which is a value, not a type.
pub fn jit_closure_abi_supports(ty: crate::hir::TypeId) -> bool {
    use cranelift_codegen::ir::types;
    if ty == crate::hir::TypeId::ANY || ty == crate::hir::TypeId::VOID {
        return false;
    }
    if ty == crate::hir::TypeId::BOOL {
        return false;
    }
    matches!(types_util::type_id_to_cranelift(ty), types::I64 | types::F64)
}
