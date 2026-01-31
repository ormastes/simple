//! Vulkan/SPIR-V implementation of the `CodegenEmitter` trait (GPU subset).
//!
//! This module provides a Vulkan-based emitter that wraps the existing
//! `VulkanBackend` and SPIR-V builder. Only GPU-relevant instructions
//! are implemented; CPU-only operations return errors.
//!
//! Currently a stub — the full implementation will refactor existing
//! `vulkan/spirv_instructions.rs` into trait method implementations.

// TODO: Implement once Vulkan backend instruction lowering is refactored.
//
// Implementation steps:
// 1. Create VulkanEmitter struct wrapping SpirvModule + SpirvBuilder
// 2. Implement GPU-relevant CodegenEmitter methods
// 3. Return errors for CPU-only operations (closures, actors, etc.)
