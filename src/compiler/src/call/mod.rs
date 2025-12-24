//! Call expression evaluation module
//!
//! This module handles all aspects of function and method calls in the interpreter:
//! - BDD testing state and builtins
//! - Call evaluation (evaluate_call - the main entry point)
//! - Argument binding to parameters
//! - Function execution (lambdas, regular functions, class instantiation)
//! - Dependency injection resolution

mod bdd_state;
mod evaluation;
mod binding;
mod execution;
mod injection;

// Re-export public items
pub(crate) use evaluation::{evaluate_call, exec_block_value};
pub(crate) use execution::{exec_function, instantiate_class};
pub(crate) use binding::bind_args;

// Re-export BDD state for use by interpreter_control.rs
pub(crate) use bdd_state::{BDD_INDENT, BDD_COUNTS, BDD_SHARED_EXAMPLES, BDD_CONTEXT_DEFS,
                            BDD_BEFORE_EACH, BDD_AFTER_EACH, BDD_LAZY_VALUES};
