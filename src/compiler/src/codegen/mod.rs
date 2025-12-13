pub mod backend_trait;
pub mod common_backend;
mod cranelift;
pub mod instr;
mod jit;
pub mod llvm;
pub mod runtime_ffi;
pub mod shared;
pub mod types_util;

#[cfg(test)]
mod llvm_tests;

pub use backend_trait::{BackendKind, NativeBackend};
pub use common_backend::{BackendError, BackendResult, BackendSettings, CodegenBackend};
pub use cranelift::*;
pub use jit::*;
