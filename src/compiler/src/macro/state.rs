use std::cell::RefCell;

use simple_parser::ast::Block;

use crate::macro_contracts::MacroContractResult;

use crate::error::CompileError;

/// Maximum depth for recursive macro expansion (prevents stack overflow)
const MAX_MACRO_EXPANSION_DEPTH: usize = 128;

thread_local! {
    /// Accumulates symbols introduced by macro expansion
    /// These need to be registered by the caller after macro invocation
    static MACRO_INTRODUCED_SYMBOLS: RefCell<Option<MacroContractResult>> = RefCell::new(None);

    /// Flag to enable macro expansion tracing
    static MACRO_TRACE_ENABLED: RefCell<bool> = RefCell::new(false);

    /// Current macro expansion depth (for recursion limit)
    static MACRO_EXPANSION_DEPTH: RefCell<usize> = RefCell::new(0);

    /// Pending tail injections - blocks to execute at the end of the current block
    /// Each entry is (depth, block) where depth is the block nesting level
    static PENDING_TAIL_INJECTIONS: RefCell<Vec<(usize, Block)>> = RefCell::new(Vec::new());

    /// Current block nesting depth for tail injection tracking
    static BLOCK_DEPTH: RefCell<usize> = RefCell::new(0);

    /// Cache for pre-processed macro contracts (definition-time optimization)
    /// For macros without const parameters, contracts can be processed once at definition
    /// time and reused for all invocations, avoiding redundant processing.
    static MACRO_CONTRACT_CACHE: RefCell<std::collections::HashMap<String, MacroContractResult>> = RefCell::new(std::collections::HashMap::new());
}

/// Enable or disable macro expansion tracing
pub fn set_macro_trace(enabled: bool) {
    MACRO_TRACE_ENABLED.with(|cell| {
        *cell.borrow_mut() = enabled;
    });
}

/// Check if macro tracing is enabled
pub(super) fn is_macro_trace_enabled() -> bool {
    MACRO_TRACE_ENABLED.with(|cell| *cell.borrow())
}

/// Print a macro trace message if tracing is enabled
pub(super) fn macro_trace(msg: &str) {
    if is_macro_trace_enabled() {
        eprintln!("[macro] {}", msg);
    }
}

/// Increment macro expansion depth and check for overflow
pub(super) fn push_macro_depth(macro_name: &str) -> Result<(), CompileError> {
    let depth = MACRO_EXPANSION_DEPTH.with(|cell| {
        let mut d = cell.borrow_mut();
        *d += 1;
        *d
    });

    if depth > MAX_MACRO_EXPANSION_DEPTH {
        MACRO_EXPANSION_DEPTH.with(|cell| *cell.borrow_mut() -= 1);
        return Err(crate::error::factory::macro_expansion_depth_exceeded(
            MAX_MACRO_EXPANSION_DEPTH,
            macro_name,
        ));
    }

    if is_macro_trace_enabled() && depth > 1 {
        macro_trace(&format!("  (depth: {})", depth));
    }

    Ok(())
}

/// Decrement macro expansion depth
pub(super) fn pop_macro_depth() {
    MACRO_EXPANSION_DEPTH.with(|cell| {
        let mut d = cell.borrow_mut();
        if *d > 0 {
            *d -= 1;
        }
    });
}

/// Get and clear introduced symbols from last macro expansion
pub(crate) fn take_macro_introduced_symbols() -> Option<MacroContractResult> {
    MACRO_INTRODUCED_SYMBOLS.with(|cell| cell.borrow_mut().take())
}

pub(crate) fn store_macro_introduced_symbols(contract_result: MacroContractResult) {
    MACRO_INTRODUCED_SYMBOLS.with(|cell| {
        *cell.borrow_mut() = Some(contract_result);
    });
}

/// Enter a new block scope for tail injection tracking
pub(crate) fn enter_block_scope() -> usize {
    BLOCK_DEPTH.with(|cell| {
        let mut d = cell.borrow_mut();
        *d += 1;
        *d
    })
}

/// Exit a block scope and return any pending tail injections for this depth
pub(crate) fn exit_block_scope() -> Vec<Block> {
    let current_depth = BLOCK_DEPTH.with(|cell| {
        let mut d = cell.borrow_mut();
        let depth = *d;
        if *d > 0 {
            *d -= 1;
        }
        depth
    });

    // Collect and remove all pending injections at this depth
    let result = PENDING_TAIL_INJECTIONS.with(|cell| {
        let mut pending = cell.borrow_mut();
        let mut result = Vec::new();
        pending.retain(|(depth, block)| {
            if *depth == current_depth {
                result.push(block.clone());
                false // Remove from pending
            } else {
                true // Keep in pending
            }
        });
        result
    });

    if is_macro_trace_enabled() && !result.is_empty() {
        macro_trace(&format!(
            "  executing {} tail injection(s) at depth {}",
            result.len(),
            current_depth
        ));
    }

    result
}

/// Queue a block for tail injection at the current block scope
pub(crate) fn queue_tail_injection(block: Block) {
    let current_depth = BLOCK_DEPTH.with(|cell| *cell.borrow());
    if is_macro_trace_enabled() {
        macro_trace(&format!("  queuing tail injection at depth {}", current_depth));
    }
    PENDING_TAIL_INJECTIONS.with(|cell| {
        cell.borrow_mut().push((current_depth, block));
    });
}

/// Cache a pre-processed contract result for a macro (definition-time optimization)
/// Only call this for macros without const parameters.
pub(crate) fn cache_macro_contract(macro_name: &str, contract_result: MacroContractResult) {
    if is_macro_trace_enabled() {
        macro_trace(&format!(
            "  caching contract for macro '{}' (definition-time processing)",
            macro_name
        ));
    }
    MACRO_CONTRACT_CACHE.with(|cell| {
        cell.borrow_mut().insert(macro_name.to_string(), contract_result);
    });
}

/// Get a cached contract result for a macro, if available
/// Returns None if the macro has const parameters or hasn't been cached.
pub(crate) fn get_cached_macro_contract(macro_name: &str) -> Option<MacroContractResult> {
    MACRO_CONTRACT_CACHE.with(|cell| cell.borrow().get(macro_name).cloned())
}

/// Check if a cached contract exists for a macro
pub(crate) fn has_cached_macro_contract(macro_name: &str) -> bool {
    MACRO_CONTRACT_CACHE.with(|cell| cell.borrow().contains_key(macro_name))
}
