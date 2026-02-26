pub mod backend_trait;
pub mod buffer_pool;
pub mod bytecode;
pub mod common_backend;
mod cranelift;
pub mod cranelift_emitter;
pub mod cranelift_ffi;
pub mod dispatch;
pub mod emitter_trait;
pub mod execution_manager;
pub mod instr;
pub mod instr_gpu;
#[cfg(not(doctest))]
pub mod local_execution;
#[cfg(all(not(doctest), feature = "llvm"))]
pub mod llvm_jit;
pub mod mir_interpreter;
#[cfg(not(doctest))]
mod jit;
pub mod lean;
pub mod llvm;
pub mod parallel;
pub mod runtime_ffi;
pub mod shared;
pub mod types_util;
pub mod vulkan;
pub mod wasm_bindgen_gen;

#[cfg(all(test, feature = "llvm-tests"))]
mod llvm_tests;

#[cfg(test)]
#[cfg(not(doctest))]
#[path = "codegen_instr_tests.rs"]
mod codegen_instr_tests;

#[cfg(test)]
#[cfg(not(doctest))]
#[path = "codegen_shared_tests.rs"]
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
