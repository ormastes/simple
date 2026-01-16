//! Vulkan GPU backend for Simple language
//!
//! This module implements a cross-platform GPU backend using Vulkan/SPIR-V.
//! It provides both compute and graphics capabilities as an alternative to CUDA.
//!
//! # Architecture
//!
//! ```text
//! Simple GPU Kernel (#[gpu] fn)
//!     ↓
//! MIR (GPU instructions: GpuGlobalId, GpuBarrier, etc.)
//!     ↓
//! SPIR-V Bytecode (via rspirv)
//!     ↓
//! Vulkan Runtime (device, buffers, pipelines)
//!     ↓
//! GPU Execution
//! ```
//!
//! # Components
//!
//! - `backend`: VulkanBackend implementing NativeBackend trait
//! - `spirv_builder`: SPIR-V module construction from MIR
//! - `types`: Type mapping (Simple → SPIR-V)
//! - `instr_compute`: Compute instruction lowering
//! - `instr_graphics`: Graphics instruction lowering (vertex/fragment shaders)
//!
//! # Usage
//!
//! Enable with cargo feature:
//! ```toml
//! [dependencies]
//! simple-compiler = { features = ["vulkan"] }
//! ```

#[cfg(feature = "vulkan")]
mod backend;
#[cfg(feature = "vulkan")]
mod instr_compute;
#[cfg(feature = "vulkan")]
mod spirv_builder;
#[cfg(feature = "vulkan")]
mod spirv_instructions;
#[cfg(feature = "vulkan")]
mod types;

#[cfg(all(feature = "vulkan", feature = "vulkan-graphics"))]
mod instr_graphics;

#[cfg(feature = "vulkan")]
pub use backend::VulkanBackend;
#[cfg(feature = "vulkan")]
pub use spirv_builder::SpirvModule;
#[cfg(feature = "vulkan")]
pub use types::TypeMapper;
