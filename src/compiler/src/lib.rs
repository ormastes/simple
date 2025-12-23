//! Simple language compiler.
//!
//! This crate provides the main compilation pipeline for the Simple language,
//! including interpretation, type checking, and code generation.

pub mod codegen;
pub mod compilability;
pub mod coverage;
pub mod effects;
pub mod effects_cache;
pub mod aop_config;
pub mod di;
pub mod elf_utils;
pub mod error;
pub mod hir;
pub mod import_loader;
pub mod incremental;
pub mod interpreter;
pub mod interpreter_ffi;
pub mod linker;
pub mod lint;
pub mod mir;
pub mod module_resolver;
pub mod monomorphize;
pub mod parallel;
pub mod pipeline;
pub mod pipeline_parallel;
pub mod project;
pub mod smf_builder;
pub mod value;
pub mod value_bridge;

#[cfg(test)]
mod test_helpers;

// Re-export main types
pub use coverage::{
    get_coverage_output_path, get_global_coverage, init_coverage, is_coverage_enabled,
    save_global_coverage, Condition, CoverageCollector, CoverageReport, CoverageStats,
    CoverageSummary, Decision, ExecutionPath, FunctionCoverage, ModuleCoverage, SourceLoc,
};
pub use error::{codes as error_codes, typo, CompileError, ErrorContext};
pub use interpreter::evaluate_module;
pub use lint::{LintChecker, LintConfig, LintDiagnostic, LintLevel, LintName};
pub use module_resolver::{DirectoryManifest, ModuleResolver, ResolvedModule};
pub use monomorphize::{
    monomorphize_module, CallSiteAnalyzer, ConcreteType, MonomorphizationTable, Monomorphizer,
    PointerKind, SpecializationKey, TypeBindings,
};
pub use mir::ContractMode;
pub use parallel::{
    load_module_parallel, parse_all_parallel, parse_files_parallel, ParallelConfig,
    ParallelParseCache, ParsedFile,
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
