/// LLVM backend for 32-bit and 64-bit target support
///
/// This backend complements Cranelift by providing:
/// - 32-bit architecture support (i686, armv7, riscv32)
/// - Alternative 64-bit backend option
/// - Shared MIR transforms and runtime FFI specs
///
/// Requires the `llvm` feature flag and LLVM 18 toolchain to be enabled.
// Module structure
mod backend_core;
mod functions;
mod gpu_instructions;
mod instructions;
mod types;
mod wasm_imports;

#[cfg(feature = "llvm-gpu")]
pub mod gpu;

// Re-export public types
pub use backend_core::LlvmBackend;
pub use types::{BinOp, LlvmType};
pub use wasm_imports::declare_wasi_imports;

#[cfg(feature = "llvm-gpu")]
pub use gpu::{GpuComputeCapability, LlvmGpuBackend};

// Test helper methods for LLVM backend.
#[cfg(feature = "llvm-tests")]
include!("../llvm_test_utils.rs");

// WASM compilation tests
#[cfg(test)]
mod wasm_tests;
