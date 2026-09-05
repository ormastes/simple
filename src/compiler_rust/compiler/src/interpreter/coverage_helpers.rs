//! Helper functions for coverage instrumentation in the interpreter
//!
//! This module provides utilities for extracting location information from
//! AST nodes and converting it to coverage data format.

use simple_parser::ast::{Node, Expr};
use simple_parser::token::Span;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Extract source location from a Node's span
///
/// Returns (file_path, line, column) if available, otherwise None
pub fn extract_node_location(node: &Node) -> Option<(String, usize, usize)> {
    let span = match node {
        Node::Let(stmt) => Some(&stmt.span),
        Node::Const(stmt) => Some(&stmt.span),
        Node::Static(stmt) => Some(&stmt.span),
        Node::Assignment(stmt) => Some(&stmt.span),
        Node::If(stmt) => Some(&stmt.span),
        Node::While(stmt) => Some(&stmt.span),
        Node::For(stmt) => Some(&stmt.span),
        Node::Loop(stmt) => Some(&stmt.span),
        Node::Return(stmt) => Some(&stmt.span),
        Node::Break(stmt) => Some(&stmt.span),
        Node::Continue(stmt) => Some(&stmt.span),
        Node::Match(stmt) => Some(&stmt.span),
        Node::With(stmt) => Some(&stmt.span),
        Node::Context(stmt) => Some(&stmt.span),
        // Expression nodes - not typically tracked for line coverage
        _ => None,
    };

    span.map(span_to_location)
}

/// Extract source location from specific expression types
///
/// Note: Expression nodes typically don't have direct span fields.
/// For now, this is a placeholder for future expansion if needed.
pub fn extract_expr_location(_expr: &Expr) -> Option<(String, usize, usize)> {
    // Most expressions don't have reliable span information
    // This could be enhanced in the future with better AST metadata
    None
}

/// Convert a Span to (file_path, line, column)
///
/// `Span` carries only line/column — no file — so the file has to come from
/// execution state. `CURRENT_EXEC_MODULE` is the module owning the function
/// body currently executing; it is saved/restored around `execute_function_body`,
/// the single choke point every function-execution path funnels through.
///
/// This used to return the constant `"<source>"` for EVERY node, which made
/// `Coverage::record_line` pool every file's hits into one bucket keyed by line
/// number alone. A line executed in file A then marked the same line number in
/// file B as covered, inflating reported coverage in the flattering direction
/// only (a fixture where file B's lines 4..11 never execute reported 100%
/// instead of 20%). Reporting `total_files: 1` for a multi-file run was the
/// visible symptom. The debugger's breakpoint file matching
/// (`DebugState::should_stop`) consumed the same placeholder and was equally
/// broken by it.
///
/// `None`, or the literal `"<entry>"` sentinel (module top-level statements,
/// entry-script-defined functions, lambdas with no known owner), falls back
/// to the entry script's own real path when one is known (see
/// `current_coverage_file`), and only to the `"<entry>"` string itself when
/// no real path is available (e.g. an in-memory `-c` source string with no
/// backing file).
fn span_to_location(span: &Span) -> (String, usize, usize) {
    let file = current_coverage_file();
    let line = span.line;
    let column = span.column;
    (file, line, column)
}

/// Resolve the file owning the currently-executing function body, for coverage
/// call sites that already have a real line/column (from a statement's own
/// `Span`) but historically hardcoded the file to the `"<source>"` placeholder.
///
/// Shares the same `CURRENT_EXEC_MODULE` thread-local as `span_to_location`
/// (see its doc comment for why file can't come from `Span` itself and why
/// pooling every file under one placeholder previously inflated coverage).
///
/// `CURRENT_EXEC_MODULE` resolves to something other than a real path for two
/// very different situations that must not be conflated:
///   1. Top-level statements of the *entry script itself*, executed directly
///      at module-evaluation time before any function call — these never run
///      through `execute_function_body`'s owner-tag save/restore at all, so
///      `CURRENT_EXEC_MODULE` is simply `None`.
///   1b. Functions *defined* in the entry script: `evaluate_module_impl`
///      (interpreter_eval.rs) DOES tag these in `FUNCTION_MODULE_OWNER`, but
///      deliberately with the literal string `"<entry>"` rather than a real
///      path — it needs a stable, distinct tie-break bucket for entry-script
///      functions (see its doc comment), not a coverage-accurate one. Calling
///      such a function sets `CURRENT_EXEC_MODULE` to `Some("<entry>")`.
///   2. A function whose `FUNCTION_MODULE_OWNER` lookup came back empty
///      (e.g. a lambda) — those inherit whatever the *caller's* frame left in
///      `CURRENT_EXEC_MODULE`, which is a separate, correct mechanism and is
///      not touched here.
/// Falling back to `CURRENT_FILE` (set by the driver to the entry file's own
/// path around `evaluate_module`, e.g. `run_file_interpreted_with_args` in
/// `driver/src/exec_core.rs`) resolves cases 1 and 1b to a real path instead
/// of the `<entry>` placeholder. This is coverage-display-only: it reads
/// `CURRENT_EXEC_MODULE`/`FUNCTION_MODULE_OWNER` but never writes them, so
/// `module_global_target`'s Legacy/Owned dispatch and `select_overload`'s
/// same-name tie-break — both of which key off the literal `"<entry>"` owner
/// string, not off this function's return value — are byte-for-byte
/// unaffected. `CURRENT_FILE` is unset for in-memory source (`-c`,
/// `run_source_in_memory_native`), which correctly leaves the final fallback
/// at `"<entry>"`.
pub fn current_coverage_file() -> String {
    let owner = crate::interpreter::CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    let needs_entry_fallback = match &owner {
        None => true,
        Some(o) => o.as_ref() == "<entry>",
    };
    if !needs_entry_fallback {
        return owner.unwrap().to_string();
    }
    crate::interpreter::get_current_file()
        .map(|p| crate::interpreter::normalize_path_key(&p).to_string_lossy().to_string())
        .unwrap_or_else(|| "<entry>".to_string())
}

/// Generate a deterministic decision ID from location info
///
/// Used to uniquely identify control flow decisions (if/while/match statements)
/// for coverage tracking.
pub fn generate_decision_id(file: &str, line: usize, column: usize) -> u32 {
    let mut hasher = DefaultHasher::new();
    file.hash(&mut hasher);
    line.hash(&mut hasher);
    column.hash(&mut hasher);
    (hasher.finish() as u32) ^ 0xDEADBEEF // XOR with magic to avoid 0
}

/// Generate a deterministic decision ID from a Span
pub fn decision_id_from_span(span: &Span) -> u32 {
    let mut hasher = DefaultHasher::new();
    span.line.hash(&mut hasher);
    span.column.hash(&mut hasher);
    span.start.hash(&mut hasher);
    (hasher.finish() as u32) ^ 0xDEADBEEF
}

/// Check if coverage is enabled without allocating
///
/// Uses a fast path that checks the environment variable cache
#[inline]
pub fn is_coverage_enabled() -> bool {
    crate::coverage::is_coverage_enabled()
}

/// Record line coverage for a node if coverage is enabled
///
/// This is a convenience function that:
/// 1. Checks if coverage is enabled (fast return if not)
/// 2. Extracts the node's location
/// 3. Records the line in the global coverage collector
/// 4. Silently fails if the lock is poisoned
pub fn record_node_coverage(node: &Node) {
    if !is_coverage_enabled() {
        return;
    }

    if let Some((file, line, _col)) = extract_node_location(node) {
        if let Some(cov) = crate::coverage::get_global_coverage() {
            if let Ok(mut cov) = cov.lock() {
                cov.record_line(std::path::Path::new(&file), line);
            }
        }
    }
}

#[inline]
/// Decision probe for the CURRENT function's file. Checks `is_coverage_enabled()`
/// BEFORE resolving the file: `current_coverage_file()` borrows the
/// `CURRENT_EXEC_MODULE` thread-local and allocates a `String` for the path,
/// and every `if`/`elif`/`while`/`match` decision used to pay that on the
/// default (coverage-off) path before `record_decision_coverage_sffi` could
/// early-return. Same probe, same id, same file when coverage IS on.
/// doc/08_tracking/bug/hir_phase_per_module_cost_2026-08-21.md (7th session).
pub fn record_decision_coverage_here(line: usize, column: usize, decision_result: bool) {
    if !is_coverage_enabled() {
        return;
    }
    record_decision_coverage_sffi(&current_coverage_file(), line, column, decision_result);
}

/// Record decision coverage for a statement via SFFI
///
/// Typically called from if/while/match statements with the outcome
/// This uses the runtime SFFI to record decision coverage when running compiled code
#[inline(always)]
pub fn record_decision_coverage_sffi(file: &str, line: usize, column: usize, decision_result: bool) {
    if !is_coverage_enabled() {
        return;
    }

    let decision_id = generate_decision_id(file, line, column);
    let file_cstr = std::ffi::CString::new(file).unwrap_or_else(|_| std::ffi::CString::new("<error>").unwrap());

    unsafe {
        simple_runtime::rt_coverage_decision_probe(
            decision_id,
            decision_result,
            file_cstr.as_ptr(),
            line as u32,
            column as u32,
        );
    }
}

/// Record condition coverage for && and || operators
///
/// For compound boolean expressions, we track each individual operand.
/// Uses a modified decision ID to distinguish from decision-level coverage.
///
/// Example: `if (x > 0) && (y < 10):`
/// - Records overall decision: the if condition (decision coverage)
/// - Records left condition: x > 0 (condition coverage)
/// - Records right condition: y < 10 (condition coverage)
pub fn record_condition_coverage(
    file: &str,
    line: usize,
    column: usize,
    condition_index: u32, // 0 for left operand, 1 for right operand
    condition_result: bool,
) {
    if !is_coverage_enabled() {
        return;
    }

    // Generate a unique ID by combining decision ID with condition index
    let base_id = generate_decision_id(file, line, column);
    let condition_id = base_id.wrapping_mul(31).wrapping_add(condition_index);

    let file_cstr = std::ffi::CString::new(file).unwrap_or_else(|_| std::ffi::CString::new("<error>").unwrap());

    unsafe {
        // Use decision probe with modified ID to track condition coverage
        // In the future, we could use rt_coverage_condition_probe when available
        simple_runtime::rt_coverage_decision_probe(
            condition_id,
            condition_result,
            file_cstr.as_ptr(),
            line as u32,
            column.wrapping_add(condition_index as usize) as u32,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decision_id_deterministic() {
        let id1 = generate_decision_id("test.spl", 10, 5);
        let id2 = generate_decision_id("test.spl", 10, 5);
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_decision_id_different_for_different_locations() {
        let id1 = generate_decision_id("test.spl", 10, 5);
        let id2 = generate_decision_id("test.spl", 10, 6);
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_decision_id_not_zero() {
        let id = generate_decision_id("test.spl", 10, 5);
        assert_ne!(id, 0);
    }
}
