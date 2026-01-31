//! Simple language compiler.
//!
//! This crate provides the main compilation pipeline for the Simple language,
//! including interpretation, type checking, and code generation.

#![allow(internal_features)]
#![cfg_attr(not(target_env = "msvc"), feature(linkage))]

pub mod aop_config;
pub mod api_surface;
pub mod arch_rules;
pub mod build_log;
pub mod blocks;
pub mod build_mode;
pub mod codegen;
pub mod compilability;
pub mod compilation_context;
pub mod concurrent_providers;
pub mod context_pack;
pub mod coverage;
pub mod di;
pub mod effects;
pub mod effects_cache;
pub mod elf_utils;
pub mod error;
pub mod ffi_bridge;
pub mod error_explanations;
pub mod formatter;
pub mod pretty_printer;
pub mod hir;
pub mod hydration_manifest;
pub mod i18n;
pub mod i18n_diagnostics;
pub mod import_loader;
pub mod incremental;
pub mod interpreter;
pub mod interpreter_contract;
pub mod interpreter_ffi;
pub mod interpreter_unit;
pub mod ir_export;
pub mod layout_recorder;
pub mod linker;
pub mod lint;
pub mod lsp_mcp;
pub mod r#macro;
pub mod macro_contracts;
pub mod macro_validation;
pub mod mcp;
pub mod method_registry;
pub mod mir;
pub mod mock;
pub mod module_resolver;
pub mod monomorphize;
pub mod parallel;
pub mod pattern_analysis;
pub mod pipeline;
pub mod pipeline_parallel;
pub mod predicate;
pub mod predicate_parser;
pub mod project;
pub mod runtime_bridge;
pub mod runtime_profile;
pub mod semantic_diff;
pub mod semantics;
pub mod smf_builder;
pub mod smf_writer;
pub mod spec_coverage;
pub mod symbol_analyzer;
pub mod text_diff;
pub mod trait_coherence;
pub mod type_check;
pub mod type_inference_config;
pub mod value;
pub mod value_bridge;
pub mod verification_checker;
pub mod weaving;
pub mod watchdog;
pub mod web_compiler;

#[cfg(test)]
pub mod test_helpers;

// Re-export main types
pub use build_log::{
    BuildComparison, BuildDiagnostic, BuildEnvironment, BuildInputs, BuildLog, BuildLogger, BuildOutput, BuildPhase,
    BuildResult, DiagnosticLevel, PhaseDifference, PhaseResult,
};
pub use build_mode::{BuildMode, DeterministicConfig};
pub use coverage::{
    get_coverage_output_path, get_global_coverage, init_coverage, is_coverage_enabled, save_global_coverage, Condition,
    CoverageCollector, CoverageReport, CoverageStats, CoverageSummary, Decision, ExecutionPath, FunctionCoverage,
    ModuleCoverage, SourceLoc,
};
pub use di::{
    create_di_match_context, parse_di_config, DependencyGraph, DiBindingRule, DiConfig, DiContainer, DiMode, DiProfile,
    DiResolveError, DiScope,
};
pub use error::{codes as error_codes, typo, CompileError, ErrorContext};
pub use formatter::{FormatConfig, Formatter};
pub use pretty_printer::{PrettyConfig, PrettyPrinter};
pub use i18n::{ExtractionResult, I18nExtractor, I18nString, LocaleFile, LocaleGenerator};
pub use i18n_diagnostics::convert_compiler_error;
pub use interpreter::{
    check_execution_limit, evaluate_module, get_execution_count, get_interpreter_args, is_debug_mode,
    is_execution_limit_enabled, reset_execution_count, set_debug_mode, set_execution_limit,
    set_execution_limit_enabled, set_interpreter_args, set_macro_trace,
    // Stack overflow detection
    is_stack_overflow_detection_enabled, set_stack_overflow_detection_enabled,
    set_max_recursion_depth, reset_recursion_depth,
    // Timeout detection
    is_timeout_exceeded, reset_timeout,
};
pub use watchdog::{start_watchdog, stop_watchdog};
pub use ir_export::{export_ast, export_hir, export_mir, ExportResult};
pub use layout_recorder::{
    clear_recording, export_layout_config, export_layout_sdn, is_recording, merge_with_config, record_function_call,
    record_function_return, record_layout_marker, start_recording, stop_recording,
};
pub use lint::{LintChecker, LintConfig, LintDiagnostic, LintLevel, LintName};
pub use mcp::{ExpandWhat, McpGenerator, McpMetadata, McpMode, McpOutput, McpTools};
pub use mir::ContractMode;
pub use module_resolver::{DirectoryManifest, ModuleResolver, ResolvedModule};
pub use monomorphize::{
    monomorphize_module, CallSiteAnalyzer, ConcreteType, MonomorphizationTable, Monomorphizer, PointerKind,
    SpecializationKey, TypeBindings,
};
pub use parallel::{
    load_module_parallel, parse_all_parallel, parse_files_parallel, ParallelConfig, ParallelParseCache, ParsedFile,
};
pub use pipeline::CompilerPipeline;
pub use pipeline::{extract_startup_config, StartupAppType, StartupConfig, StartupWindowHints};
pub use project::ProjectContext;
pub use runtime_profile::{
    collect_global_metrics, generate_global_feedback, global_profiler, record_call, start_profiling, stop_profiling,
    FunctionStats, LayoutFeedback, ProfileConfig, RuntimeMetrics, RuntimeProfiler,
};
pub use semantic_diff::{ChangeKind, DiffSummary, ImpactLevel, SemanticChange, SemanticDiff, SemanticDiffer};
pub use spec_coverage::{find_spec_file, SpecCoverageReport};
pub use text_diff::{DiffHunk, DiffLine, TextDiff};
pub use trait_coherence::{CoherenceChecker, CoherenceError};
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
pub use verification_checker::{
    can_call, has_unsafe_effect, is_pure_effects, VerificationChecker, VerificationRule, VerificationViolation,
};
pub use web_compiler::{SuiCompilationResult, WebCompiler};
pub use concurrent_providers::{ConcurrentBackend, registry::ConcurrentProviderRegistry};

// LSP MCP exports
pub use lsp_mcp::{
    get_tool_definitions as lsp_mcp_tool_definitions, Diagnostic as LspDiagnostic,
    DiagnosticSeverity as LspDiagnosticSeverity, HoverContents, HoverInfo, Location as LspLocation, LspMcpHandler,
    LspMcpTools, Position as LspPosition, Range as LspRange, ReferenceContext, ReferenceLocation,
    SymbolInfo as LspSymbolInfo, SymbolKind as LspSymbolKind,
};
