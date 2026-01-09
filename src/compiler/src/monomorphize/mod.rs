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
mod engine;
pub mod parallel;
mod rewriter;
mod table;
mod types;
mod util;

pub use analyzer::CallSiteAnalyzer;
pub use binding_specializer::{specialize_bindings, BindingSpecializer};
pub use cache::{
    CacheEntryMeta, CachedClass, CachedFunction, CachedStruct, LocalMonoCache, MonoCache,
    MonoCacheConfig, MonoCacheStats,
};
pub use engine::Monomorphizer;
pub use parallel::{
    monomorphize_modules_parallel, MonoStats, ParallelMonoConfig, ParallelMonoTable,
    ParallelMonomorphizer,
};
pub use rewriter::monomorphize_module;
pub use table::MonomorphizationTable;
pub use types::{ConcreteType, PointerKind, SpecializationKey, TypeBindings};
pub use util::{ast_type_to_concrete, concrete_to_ast_type};
