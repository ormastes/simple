//! Effect checking for async functions.
//!
//! This module tracks blocking operations and validates that async
//! functions don't perform blocking operations.

use crate::CompileError;
use simple_parser::ast::Effect;
use std::cell::RefCell;

/// Operations that are considered "blocking" and not allowed in async functions
const BLOCKING_OPERATIONS: &[&str] = &[
    "recv",      // Blocking receive from channel
    "join",      // Blocking wait for actor/future
    "await",     // Blocking await (in this context)
    "sleep",     // Thread sleep
    "read_file", // File I/O
    "write_file",
    "print", // I/O operations
    "println",
    "input", // User input
];

thread_local! {
    /// Current function effect for effect checking (Async, None)
    pub(crate) static CURRENT_EFFECT: RefCell<Option<Effect>> = RefCell::new(None);
}

/// Check if an operation is blocking (not allowed in async functions)
pub fn is_blocking_operation(name: &str) -> bool {
    BLOCKING_OPERATIONS.contains(&name)
}

/// Check if we're in an async context and report error if blocking operation is used
pub fn check_async_violation(operation: &str) -> Result<(), CompileError> {
    CURRENT_EFFECT.with(|cell| {
        if let Some(Effect::Async) = *cell.borrow() {
            if is_blocking_operation(operation) {
                return Err(CompileError::Semantic(format!(
                    "blocking operation '{}' not allowed in async function",
                    operation
                )));
            }
        }
        Ok(())
    })
}
