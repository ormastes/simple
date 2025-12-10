//! Simple language compiler.
//!
//! This crate provides the main compilation pipeline for the Simple language,
//! including interpretation, type checking, and code generation.

pub mod codegen;
pub mod compilability;
pub mod effects;
pub mod error;
pub mod hir;
pub mod interpreter;
pub mod interpreter_ffi;
pub mod linker;
pub mod mir;
pub mod pipeline;
pub mod value;
pub mod value_bridge;

// Re-export main types
pub use error::CompileError;
pub use interpreter::evaluate_module;
pub use pipeline::CompilerPipeline;
pub use value::{
    BorrowMutValue,
    BorrowValue,
    ChannelValue,
    // NewTypes for formal verification
    ClassName,
    EnumTypeName,
    Env,
    FutureValue,
    GeneratorState,
    GeneratorValue,
    ManualHandleValue,
    ManualSharedValue,
    ManualUniqueValue,
    ManualWeakValue,
    ThreadPoolValue,
    Value,
    VariantName,
    BUILTIN_ARRAY,
    // Magic class name constants for formal verification
    BUILTIN_RANGE,
};
