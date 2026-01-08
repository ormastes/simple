//! Macro invocation and expansion for the Simple compiler/interpreter
//!
//! This module handles both builtin macros (println, vec, assert, etc.) and
//! user-defined macros with const evaluation, hygiene, and template substitution.
//!
//! ## Architecture
//!
//! - `helpers`: Const binding evaluation for macro parameters
//! - `invocation`: Builtin macro implementations and dispatch
//! - `expansion`: User-defined macro expansion with contracts
//! - `hygiene`: Hygienic identifier renaming to prevent variable capture
//! - `substitution`: Template string substitution for const parameters
//!
//! ## Public API
//!
//! - `evaluate_macro_invocation()`: Main entry point for macro evaluation
//! - `take_macro_introduced_symbols()`: Retrieve symbols introduced by macro expansion
//! - `enter_block_scope()`: Track block scope for tail injection
//! - `exit_block_scope()`: Pop block scope and return tail injections
//! - `queue_tail_injection()`: Queue tail injection for current scope
//! - `set_macro_trace()`: Enable/disable macro trace output
//! - `build_macro_const_bindings()`: Helper for const parameter evaluation
//! - `const_value_to_string()`: Helper for converting values to strings

// Module declarations
mod helpers;
mod invocation;
mod expansion;
mod hygiene;
mod state;
mod substitution;

// Re-export public API (accessible from parent interpreter module)
pub(crate) use helpers::{build_macro_const_bindings, const_value_to_string};
pub(crate) use invocation::evaluate_macro_invocation;
pub(crate) use state::{
    enter_block_scope, exit_block_scope, queue_tail_injection,
    take_macro_introduced_symbols,
};
pub use state::set_macro_trace;
