//! Factory functions for constructing `CompileError` values.
//!
//! Split into two sub-files by functional area:
//! - `resolve`: module resolution, argument/type, macros, type/name lookup,
//!              trait impl, effect/capability, type mismatch, binding, FFI, pipeline
//! - `codegen_ops`: codegen/LLVM, assignment, tensor, unit conversion, parser,
//!                  result/option, math eval, conversion, dependency, block, interpreter

mod resolve;
mod codegen_ops;

/// Re-export all factory functions under `error::factory::*`.
pub mod factory {
    pub use super::resolve::*;
    pub use super::codegen_ops::*;
}
