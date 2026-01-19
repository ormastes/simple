//! Effect checking for functions with effect annotations.
//!
//! This module tracks effects and validates that:
//! - `@async` functions don't perform blocking operations
//! - `@pure` functions don't perform any I/O, network, or filesystem operations
//! - Functions have required capabilities for operations they perform

use crate::CompileError;
use simple_parser::ast::Effect;
use std::cell::RefCell;
use std::collections::HashSet;

/// Operations that are considered "blocking" and not allowed in @async functions
/// Note: await is NOT blocking in async - it yields control. Only truly blocking ops here.
const BLOCKING_OPERATIONS: &[&str] = &[
    "recv_blocking", // Blocking receive from channel (sync version)
    "join_blocking", // Blocking wait for actor/future (sync version)
    "sleep_blocking", // Thread sleep (sync version)
                     // Note: await, print, read_file etc are OK in async - they're async-aware
];

/// Operations that require @io effect (console I/O)
const IO_OPERATIONS: &[&str] = &["print", "println", "eprint", "eprintln", "input", "flush"];

/// Operations that require @fs effect (filesystem)
const FS_OPERATIONS: &[&str] = &[
    "read_file",
    "write_file",
    "read_dir",
    "list_dir",
    "create_dir",
    "remove_file",
    "remove_dir",
    "rename",
    "copy",
    "exists",
    "is_file",
    "is_dir",
    "native_fs_read",
    "native_fs_write",
    "native_fs_exists",
    "native_fs_remove",
    "native_fs_rename",
    "native_fs_create_dir",
    "native_fs_remove_dir",
    "native_fs_list_dir",
    "native_fs_metadata",
    "native_fs_is_file",
    "native_fs_is_dir",
    "native_file_create",
    "native_file_open",
    "native_file_read",
    "native_file_write",
    "native_file_close",
    "native_file_seek",
    "native_file_flush",
];

/// Operations that require @net effect (network)
const NET_OPERATIONS: &[&str] = &[
    "http_get",
    "http_post",
    "tcp_connect",
    "tcp_listen",
    "udp_bind",
    "udp_send",
    "dns_lookup",
];

thread_local! {
    /// Current function effects for effect checking
    /// Empty set = unrestricted (no effect annotations)
    pub(crate) static CURRENT_EFFECTS: RefCell<HashSet<Effect>> = RefCell::new(HashSet::new());
}

/// Check if an operation is blocking (not allowed in @async functions)
pub fn is_blocking_operation(name: &str) -> bool {
    BLOCKING_OPERATIONS.contains(&name)
}

/// Check if an operation requires @io effect
pub fn is_io_operation(name: &str) -> bool {
    IO_OPERATIONS.contains(&name)
}

/// Check if an operation requires @fs effect
pub fn is_fs_operation(name: &str) -> bool {
    FS_OPERATIONS.contains(&name)
}

/// Check if an operation requires @net effect
pub fn is_net_operation(name: &str) -> bool {
    NET_OPERATIONS.contains(&name)
}

/// Check if an operation has any side effects (for @pure checking)
pub fn has_side_effects(name: &str) -> bool {
    is_io_operation(name) || is_fs_operation(name) || is_net_operation(name)
}

/// Check if we're in an @async context and report error if blocking operation is used
pub fn check_async_violation(operation: &str) -> Result<(), CompileError> {
    CURRENT_EFFECTS.with(|cell| {
        let effects = cell.borrow();
        if effects.contains(&Effect::Async) {
            if is_blocking_operation(operation) {
                return Err(crate::error::factory::blocking_in_async(operation));
            }
        }
        Ok(())
    })
}

/// Check if we're in a @pure context and report error if side-effecting operation is used
pub fn check_pure_violation(operation: &str) -> Result<(), CompileError> {
    CURRENT_EFFECTS.with(|cell| {
        let effects = cell.borrow();
        if effects.contains(&Effect::Pure) {
            if has_side_effects(operation) {
                // Determine which effect is needed
                let needed_effect = if is_io_operation(operation) {
                    "@io"
                } else if is_fs_operation(operation) {
                    "@fs"
                } else if is_net_operation(operation) {
                    "@net"
                } else {
                    "@io" // default
                };

                return Err(crate::error::factory::side_effect_in_pure(operation, needed_effect));
            }
        }
        Ok(())
    })
}

/// Check all effect violations for an operation.
/// Returns Ok if the operation is allowed, Err with message otherwise.
pub fn check_effect_violations(operation: &str) -> Result<(), CompileError> {
    // Check @async constraint
    check_async_violation(operation)?;

    // Check @pure constraint
    check_pure_violation(operation)?;

    Ok(())
}

/// Set the current effects for effect checking.
/// Returns the previous effects so they can be restored.
pub fn set_current_effects(effects: &[Effect]) -> HashSet<Effect> {
    CURRENT_EFFECTS.with(|cell| {
        let prev = cell.borrow().clone();
        *cell.borrow_mut() = effects.iter().copied().collect();
        prev
    })
}

/// Restore previously saved effects.
pub fn restore_effects(effects: HashSet<Effect>) {
    CURRENT_EFFECTS.with(|cell| {
        *cell.borrow_mut() = effects;
    });
}

/// Check if currently in a function with the given effect.
pub fn has_effect(effect: Effect) -> bool {
    CURRENT_EFFECTS.with(|cell| cell.borrow().contains(&effect))
}

/// Check if calling a function with `callee_effects` is allowed from the current effect context.
/// Returns an error if the call would violate effect restrictions.
///
/// Rules:
/// - @pure functions can only call @pure functions (no side effects allowed)
/// - @async functions can call any function (no restrictions on callee)
/// - Functions without effects can call anything (unrestricted)
pub fn check_call_compatibility(callee_name: &str, callee_effects: &[Effect]) -> Result<(), CompileError> {
    CURRENT_EFFECTS.with(|cell| {
        let caller_effects = cell.borrow();

        // If caller has no effects, it's unrestricted
        if caller_effects.is_empty() {
            return Ok(());
        }

        // If caller is @pure, callee must also be @pure
        if caller_effects.contains(&Effect::Pure) {
            // Callee must be pure (no side effects)
            if !callee_effects.contains(&Effect::Pure) && !callee_effects.is_empty() {
                return Err(crate::error::factory::pure_calls_impure(
                    callee_name,
                    &format_effects(callee_effects)
                ));
            }

            // If callee has any side-effecting decorators, reject
            for effect in callee_effects {
                if matches!(effect, Effect::Io | Effect::Net | Effect::Fs | Effect::Unsafe) {
                    return Err(crate::error::factory::pure_calls_effect(
                        callee_name,
                        effect.decorator_name()
                    ));
                }
            }
        }

        Ok(())
    })
}

/// Format effects for error messages
fn format_effects(effects: &[Effect]) -> String {
    if effects.is_empty() {
        return "none".to_string();
    }
    effects
        .iter()
        .map(|e| format!("@{}", e.decorator_name()))
        .collect::<Vec<_>>()
        .join(", ")
}
