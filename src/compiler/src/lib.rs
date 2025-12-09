//! Simple language compiler.
//!
//! This crate provides the main compilation pipeline for the Simple language,
//! including interpretation, type checking, and code generation.

pub mod hir;
pub mod mir;
pub mod codegen;
pub mod linker;
pub mod error;
pub mod value;
pub mod effects;
pub mod pipeline;
pub mod interpreter;

// Re-export main types
pub use error::CompileError;
pub use value::{
    BorrowMutValue, BorrowValue, Env, FutureValue, GeneratorState, GeneratorValue,
    ManualHandleValue, ManualSharedValue, ManualUniqueValue, ManualWeakValue, Value,
    // NewTypes for formal verification
    ClassName, EnumTypeName, VariantName,
    // Magic class name constants for formal verification
    BUILTIN_RANGE, BUILTIN_ARRAY,
};
pub use pipeline::CompilerPipeline;
pub use interpreter::evaluate_module;
