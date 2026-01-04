//! Simple language compiler.
//!
//! This crate provides the main compilation pipeline for the Simple language,
//! including interpretation, type checking, and code generation.

#![allow(internal_features)]
#![cfg_attr(not(target_env = "msvc"), feature(linkage))]

pub mod codegen;
pub mod compilability;
pub mod coverage;
pub mod effects;
pub mod layout_recorder;
pub mod effects_cache;
pub mod aop_config;
pub mod api_surface;
pub mod arch_rules;
pub mod build_log;
pub mod build_mode;
pub mod context_pack;
pub mod di;
pub mod mcp;
pub mod ir_export;
pub mod semantic_diff;
pub mod mock;
pub mod pattern_analysis;
pub mod predicate;
pub mod predicate_parser;
pub mod weaving;
pub mod elf_utils;
pub mod error;
pub mod error_explanations;
pub mod hir;
pub mod hydration_manifest;
pub mod import_loader;
pub mod incremental;
pub mod interpreter;
pub mod interpreter_contract;
pub mod interpreter_ffi;
pub mod interpreter_unit;
pub mod linker;
pub mod lint;
pub mod macro_contracts;
pub mod spec_coverage;
pub mod macro_validation;
pub mod mir;
pub mod module_resolver;
pub mod monomorphize;
pub mod parallel;
pub mod pipeline;
pub mod pipeline_parallel;
pub mod project;
pub mod smf_builder;
pub mod trait_coherence;
pub mod value;
pub mod value_bridge;
pub mod verification_checker;
pub mod web_compiler;
pub mod runtime_profile;

#[cfg(test)]
pub mod test_helpers;

// Re-export main types
pub use coverage::{
    get_coverage_output_path, get_global_coverage, init_coverage, is_coverage_enabled,
    save_global_coverage, Condition, CoverageCollector, CoverageReport, CoverageStats,
    CoverageSummary, Decision, ExecutionPath, FunctionCoverage, ModuleCoverage, SourceLoc,
};
pub use error::{codes as error_codes, typo, CompileError, ErrorContext};
pub use interpreter::{evaluate_module, set_interpreter_args, get_interpreter_args, set_macro_trace};
pub use lint::{LintChecker, LintConfig, LintDiagnostic, LintLevel, LintName};
pub use module_resolver::{DirectoryManifest, ModuleResolver, ResolvedModule};
pub use monomorphize::{
    monomorphize_module, CallSiteAnalyzer, ConcreteType, MonomorphizationTable, Monomorphizer,
    PointerKind, SpecializationKey, TypeBindings,
};
pub use build_log::{
    BuildComparison, BuildDiagnostic, BuildEnvironment, BuildInputs, BuildLog, BuildLogger,
    BuildOutput, BuildPhase, BuildResult, DiagnosticLevel, PhaseDifference, PhaseResult,
};
pub use build_mode::{BuildMode, DeterministicConfig};
pub use mir::ContractMode;
pub use parallel::{
    load_module_parallel, parse_all_parallel, parse_files_parallel, ParallelConfig,
    ParallelParseCache, ParsedFile,
};
pub use pipeline::CompilerPipeline;
pub use pipeline::{extract_startup_config, StartupAppType, StartupConfig, StartupWindowHints};
pub use project::ProjectContext;
pub use layout_recorder::{
    start_recording, stop_recording, is_recording, record_function_call,
    record_function_return, record_layout_marker, export_layout_sdn,
    export_layout_config, clear_recording, merge_with_config,
};
pub use trait_coherence::{CoherenceChecker, CoherenceError};
pub use di::{
    create_di_match_context, parse_di_config, DependencyGraph, DiBindingRule, DiConfig,
    DiContainer, DiMode, DiProfile, DiResolveError, DiScope,
};
pub use ir_export::{export_ast, export_hir, export_mir, ExportResult};
pub use mcp::{ExpandWhat, McpGenerator, McpMetadata, McpMode, McpOutput, McpTools};
pub use semantic_diff::{
    ChangeKind, ImpactLevel, SemanticChange, SemanticDiff, SemanticDiffer, DiffSummary,
};
pub use spec_coverage::{SpecCoverageReport, find_spec_file};
pub use web_compiler::{WebCompiler, SuiCompilationResult};
pub use runtime_profile::{
    collect_global_metrics, generate_global_feedback, global_profiler, record_call,
    start_profiling, stop_profiling, FunctionStats, LayoutFeedback, ProfileConfig,
    RuntimeMetrics, RuntimeProfiler,
};
pub use verification_checker::{
    can_call, has_unsafe_effect, is_pure_effects, VerificationChecker, VerificationRule,
    VerificationViolation,
};
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
