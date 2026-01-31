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

    span.map(|s| span_to_location(s))
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
/// The file path is extracted from the span's source info if available,
/// otherwise defaults to "<unknown>".
fn span_to_location(span: &Span) -> (String, usize, usize) {
    // In Simple's parser, file information is stored elsewhere in the AST
    // For now, use a placeholder that can be enhanced with better source tracking
    let file = "<source>".to_string();
    let line = span.line;
    let column = span.column;
    (file, line, column)
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

/// Record decision coverage for a statement via FFI
///
/// Typically called from if/while/match statements with the outcome
/// This uses the runtime FFI to record decision coverage when running compiled code
pub fn record_decision_coverage_ffi(file: &str, line: usize, column: usize, decision_result: bool) {
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
