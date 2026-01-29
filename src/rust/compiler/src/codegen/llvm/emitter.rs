//! LLVM implementation of the `CodegenEmitter` trait.
//!
//! This module provides an LLVM-based emitter that wraps the existing
//! `LlvmBackend` and delegates to functions in `llvm/instructions.rs`
//! and `llvm/functions/`.
//!
//! Currently a stub — the full implementation will refactor existing
//! `llvm/instructions.rs` into trait method implementations.

// TODO: Implement once LLVM backend instruction lowering is refactored
// into trait-compatible form. The existing code in instructions.rs
// uses a different calling convention (LlvmBackend methods vs free functions).
//
// Implementation steps:
// 1. Extract instruction lowering from LlvmBackend methods into free functions
// 2. Create LlvmEmitter struct wrapping inkwell Builder + Module
// 3. Implement CodegenEmitter for LlvmEmitter
