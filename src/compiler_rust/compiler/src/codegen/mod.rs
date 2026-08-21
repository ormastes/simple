pub mod backend_trait;
pub mod buffer_pool;
pub mod bytecode;
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
mod jit;
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
/// The boundary is a raw Cranelift signature with no boxing, so a type is only
/// carryable when its machine representation is a full register the rest of
/// codegen already treats uniformly: a 64-bit integer/pointer or an f64.
/// `TypeId::BOOL` lowers to `i8` and a lambda returning one crashed (measured:
/// SIGSEGV on `print(f(32))` for `\\x: x > 1`), because the parent's value
/// handling assumes register width. `TypeId::ANY` is excluded on purpose: an
/// untyped boundary has no correct encoding, which is the defect this whole
/// change exists to remove.
pub fn jit_closure_abi_supports(ty: crate::hir::TypeId) -> bool {
    use cranelift_codegen::ir::types;
    if ty == crate::hir::TypeId::ANY || ty == crate::hir::TypeId::VOID {
        return false;
    }
    matches!(types_util::type_id_to_cranelift(ty), types::I64 | types::F64)
}
