pub mod backend_trait;
pub mod buffer_pool;
pub mod common_backend;
mod cranelift;
pub mod instr;
pub mod instr_gpu;
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

pub use backend_trait::{BackendKind, NativeBackend};
pub use buffer_pool::{
    acquire_thread_buffer, clear_thread_buffer_pool, init_thread_buffer_pool, init_thread_buffer_pool_with_config,
    release_thread_buffer, thread_buffer_pool_stats, BufferPool, BufferPoolConfig, BufferPoolStats, LocalBufferPool,
    PooledBuffer,
};
pub use common_backend::{BackendError, BackendResult, BackendSettings, CodegenBackend};
pub use cranelift::*;
#[cfg(not(doctest))]
pub use jit::*;
pub use parallel::{
    compile_modules_parallel, compile_modules_parallel_with_config, BatchCodegen, CodegenStats, CompiledModule,
    CompiledModuleCache, ParallelCodegen, ParallelCodegenConfig,
};
