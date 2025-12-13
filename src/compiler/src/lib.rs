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
pub mod lint;
pub mod mir;
pub mod module_resolver;
pub mod monomorphize;
pub mod pipeline;
pub mod project;
pub mod value;
pub mod value_bridge;

#[cfg(test)]
mod test_helpers;

// Re-export main types
pub use error::{codes as error_codes, typo, CompileError, ErrorContext};
pub use interpreter::evaluate_module;
pub use lint::{LintChecker, LintConfig, LintDiagnostic, LintLevel, LintName};
pub use module_resolver::{DirectoryManifest, ModuleResolver, ResolvedModule};
pub use monomorphize::{
    monomorphize_module, CallSiteAnalyzer, ConcreteType, MonomorphizationTable, Monomorphizer,
    PointerKind, SpecializationKey, TypeBindings,
};
pub use pipeline::CompilerPipeline;
pub use project::ProjectContext;
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
