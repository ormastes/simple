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

mod analyzer;
mod engine;
mod rewriter;
mod table;
mod types;
mod util;

pub use analyzer::CallSiteAnalyzer;
pub use engine::Monomorphizer;
pub use rewriter::monomorphize_module;
pub use table::MonomorphizationTable;
pub use types::{ConcreteType, PointerKind, SpecializationKey, TypeBindings};
pub use util::{ast_type_to_concrete, concrete_to_ast_type};
