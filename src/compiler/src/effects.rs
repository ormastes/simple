//! Effect checking for waitless functions.
//!
//! This module tracks blocking operations and validates that waitless
//! functions don't perform blocking operations.

use std::cell::RefCell;
use simple_parser::ast::Effect;
use crate::CompileError;

/// Operations that are considered "blocking" and not allowed in waitless functions
const BLOCKING_OPERATIONS: &[&str] = &[
    "recv",      // Blocking receive from channel
    "join",      // Blocking wait for actor/future
    "await",     // Blocking await (in this context)
    "sleep",     // Thread sleep
    "read_file", // File I/O
    "write_file",
    "print",     // I/O operations
    "println",
    "input",     // User input
];

thread_local! {
    /// Current function effect for effect checking (Waitless, Async, None)
    pub(crate) static CURRENT_EFFECT: RefCell<Option<Effect>> = RefCell::new(None);
}

/// Check if an operation is blocking (not allowed in waitless functions)
pub fn is_blocking_operation(name: &str) -> bool {
    BLOCKING_OPERATIONS.contains(&name)
}

/// Check if we're in a waitless context and report error if blocking operation is used
pub fn check_waitless_violation(operation: &str) -> Result<(), CompileError> {
    CURRENT_EFFECT.with(|cell| {
        if let Some(Effect::Waitless) = *cell.borrow() {
            if is_blocking_operation(operation) {
                return Err(CompileError::Semantic(format!(
                    "blocking operation '{}' not allowed in waitless function",
                    operation
                )));
            }
        }
        Ok(())
    })
}
