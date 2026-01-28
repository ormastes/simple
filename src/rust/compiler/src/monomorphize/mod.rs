//! Monomorphization engine for generic functions and types.
//!
//! This module handles the specialization of generic code by creating
//! concrete instances for each unique combination of type arguments.
//!
//! ## How it works
//!
//! 1. During type checking, generic function/struct calls are recorded
//! 2. The monomorphization pass generates specialized versions
//! 3. HIR/MIR lowering uses the specialized versions
//!
//! ## Example
//!
//! ```simple
//! fn identity[T](x: T) -> T:
//!     return x
//!
//! main = identity[Int](42)  // Generates identity_Int
//! ```
//!
//! ## Interface Binding Specialization
//!
//! This module also handles static polymorphism via interface bindings.
//! When `bind Logger = ConsoleLogger` is declared, method calls on Logger-typed
//! values can be specialized to directly call ConsoleLogger methods.

mod analyzer;
pub mod binding_specializer;
pub mod cache;
pub mod cycle_detector;
pub mod deferred;
mod engine;
pub mod hot_reload;
pub mod metadata;
pub mod note_sdn;
pub mod parallel;
pub mod partition;
mod rewriter;
mod table;
pub mod tracker;
mod types;
mod util;

pub use analyzer::CallSiteAnalyzer;
pub use binding_specializer::{specialize_bindings, BindingSpecializer};
pub use cache::{
    CacheEntryMeta, CachedClass, CachedFunction, CachedStruct, LocalMonoCache, MonoCache, MonoCacheConfig,
    MonoCacheStats,
};
pub use deferred::{CompiledCode, DeferredMonomorphizer, GenericTemplate, InstantiationMode};
pub use engine::Monomorphizer;
pub use metadata::{
    GenericEnumMeta, GenericFunctionMeta, GenericStructMeta, GenericTraitMeta, MonomorphizationMetadata,
    SpecializationEntry, TraitImplEntry,
};
pub use note_sdn::{
    CircularError, CircularWarning, DependencyEdge, DependencyKind, InstantiationEntry, InstantiationStatus,
    NoteSdnMetadata, PossibleInstantiationEntry, TypeInferenceEntry,
};
pub use cycle_detector::{
    analyze_and_update_cycles, detect_cycles, detect_type_inference_cycles, topological_sort,
    would_create_cycle, CycleDetectionResult,
};
pub use parallel::{monomorphize_modules_parallel, MonoStats, ParallelMonoConfig, ParallelMonoTable, ParallelMonomorphizer};
pub use partition::{build_monomorphization_metadata, partition_generic_constructs, GenericTemplates, SpecializedInstances};
pub use rewriter::monomorphize_module;
pub use table::MonomorphizationTable;
pub use types::{ConcreteType, PointerKind, SpecializationKey, TypeBindings};
pub use hot_reload::{HotReloadConfig, HotReloadManager, HotReloadResult, NOTE_SDN_TERMINATOR};
pub use tracker::{InstantiationTracker, TrackingContext};
pub use util::{ast_type_to_concrete, concrete_to_ast_type};
