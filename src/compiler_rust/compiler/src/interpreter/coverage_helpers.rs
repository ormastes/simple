//! Helper functions for coverage instrumentation in the interpreter
//!
//! This module provides utilities for extracting location information from
//! AST nodes and converting it to coverage data format.

use simple_parser::ast::{BinOp, ClassDef, Expr, FunctionDef, Node};
use simple_parser::token::Span;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::{evaluate_expr, Enums, ImplMethods};
use crate::error::CompileError;
use crate::value::{Env, Value};

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
    coverage_file_for_owner(owner.as_deref())
}

/// Coverage file for a module owner key. Shared by the runtime probes (via
/// `current_coverage_file`) and the static site enumeration
/// (`coverage_sites.rs`) so both produce byte-identical file strings — a
/// differing string would put a phantom zero-count row beside the visited one.
pub(crate) fn coverage_file_for_owner(owner: Option<&str>) -> String {
    match owner {
        Some(o) if o != "<entry>" => o.to_string(),
        _ => crate::interpreter::get_current_file()
            .map(|p| crate::interpreter::normalize_path_key(&p).to_string_lossy().to_string())
            .unwrap_or_else(|| "<entry>".to_string()),
    }
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

// ---------------------------------------------------------------------------
// Decision / condition sites
//
// A decision site is identified by (file, anchor line, anchor column, sub):
//   * `if` / `while`            -> its own statement span, SUB_STMT
//   * `elif` #i                 -> the parent `if` span, sub_elif(i)
//   * match-arm guard           -> the arm span, SUB_GUARD
//   * if-expression             -> the enclosing function's span (FN_ANCHOR),
//                                  sub = hash of the condition
//   * standalone `and`/`or`     -> the enclosing function's span,
//                                  sub = hash of the whole expression
// `Expr` carries no span, which is why the last two anchor on the function.
// A condition is an atomic operand of an `and`/`or` tree, numbered in
// pre-order; `not` is transparent (a leaf `not x` has the same covered
// status as `x`). The static enumeration in `coverage_sites.rs` produces the
// same keys, so a site that never runs is still in the denominator.
// ---------------------------------------------------------------------------

pub(crate) const SUB_STMT: u64 = 0;
pub(crate) const SUB_GUARD: u64 = 0x4755_4152_4400_0000;
pub(crate) const TAG_IF_EXPR: &str = "if-expr";
pub(crate) const TAG_AND_OR: &str = "and-or";

#[inline]
pub(crate) fn sub_elif(idx: usize) -> u64 {
    1 + idx as u64
}

thread_local! {
    /// Span (line, column) of the function body currently executing; the
    /// anchor of expression-level decision sites. Maintained by
    /// `execute_function_body` only while coverage is enabled.
    static FN_ANCHOR: std::cell::Cell<(u32, u32)> = const { std::cell::Cell::new((0, 0)) };
}

/// Set the expression-site anchor, returning the previous one for restore.
pub(crate) fn swap_fn_anchor(anchor: (u32, u32)) -> (u32, u32) {
    FN_ANCHOR.with(|cell| cell.replace(anchor))
}

fn fn_anchor() -> (u32, u32) {
    FN_ANCHOR.with(|cell| cell.get())
}

pub(crate) fn site_decision_id(file: &str, line: u32, column: u32, sub: u64) -> u32 {
    if sub == SUB_STMT {
        return generate_decision_id(file, line as usize, column as usize);
    }
    let mut hasher = DefaultHasher::new();
    file.hash(&mut hasher);
    line.hash(&mut hasher);
    column.hash(&mut hasher);
    sub.hash(&mut hasher);
    (hasher.finish() as u32) ^ 0xDEADBEEF
}

/// Discriminator for an expression-level site (top bit set so it can never
/// equal SUB_STMT, an elif index, or SUB_GUARD).
pub(crate) fn expr_site_sub(tag: &str, expr: &Expr) -> u64 {
    let mut hasher = DefaultHasher::new();
    tag.hash(&mut hasher);
    format!("{:?}", expr).hash(&mut hasher);
    hasher.finish() | (1u64 << 63)
}

#[inline]
pub(crate) fn is_and_or(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Binary {
            op: BinOp::And | BinOp::Or,
            ..
        }
    )
}

/// Atomic operands of an `and`/`or` tree (1 for anything else).
pub(crate) fn count_tree_leaves(expr: &Expr) -> u32 {
    match expr {
        Expr::Binary {
            op: BinOp::And | BinOp::Or,
            left,
            right,
        } => count_tree_leaves(left) + count_tree_leaves(right),
        _ => 1,
    }
}

/// Number of condition sites a decision with this condition owns.
pub(crate) fn decision_condition_count(cond: &Expr) -> u32 {
    if is_and_or(cond) {
        count_tree_leaves(cond)
    } else {
        0
    }
}

/// Record a decision outcome at a site. No-op (one load) with coverage off.
pub(crate) fn record_decision_site(line: usize, column: usize, sub: u64, result: bool) {
    if !is_coverage_enabled() {
        return;
    }
    let file = current_coverage_file();
    let (line, column) = (line as u32, column as u32);
    let id = site_decision_id(&file, line, column, sub);
    simple_runtime::coverage::coverage_record_decision(id, result, &file, line, column);
}

/// Evaluate a decision's condition. With coverage off, or when the condition
/// is not an `and`/`or` tree, this is exactly `evaluate_expr`. Otherwise the
/// tree is evaluated here with the same short-circuit semantics as
/// `eval_op_expr`'s `BinOp::And`/`BinOp::Or` (left/right presence via
/// `is_condition_present`, result `Value::Bool`), recording each evaluated
/// leaf as a condition of this decision. The caller still records the
/// decision outcome.
#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_decision_cond(
    cond: &Expr,
    line: usize,
    column: usize,
    sub: u64,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if !is_coverage_enabled() || !is_and_or(cond) {
        return evaluate_expr(cond, env, functions, classes, enums, impl_methods);
    }
    let file = current_coverage_file();
    let (line, column) = (line as u32, column as u32);
    let id = site_decision_id(&file, line, column, sub);
    let mut probe = CondProbe {
        decision_id: id,
        file: &file,
        line,
        column,
        next_leaf: 0,
    };
    let result = probe.eval(cond, env, functions, classes, enums, impl_methods)?;
    Ok(Value::Bool(result))
}

/// Coverage-on evaluation of a standalone `and`/`or` expression (one not in
/// a decision's condition position): it is its own decision, anchored on the
/// enclosing function. Called from `eval_op_expr` only when coverage is on.
pub(crate) fn eval_and_or_decision(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let (line, column) = fn_anchor();
    let sub = expr_site_sub(TAG_AND_OR, expr);
    let value = eval_decision_cond(
        expr,
        line as usize,
        column as usize,
        sub,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )?;
    record_decision_site(line as usize, column as usize, sub, value.truthy());
    Ok(value)
}

/// Site (line, column, sub) of an if-expression with this condition.
pub(crate) fn if_expr_site(condition: &Expr) -> (usize, usize, u64) {
    let (line, column) = fn_anchor();
    (line as usize, column as usize, expr_site_sub(TAG_IF_EXPR, condition))
}

struct CondProbe<'a> {
    decision_id: u32,
    file: &'a str,
    line: u32,
    column: u32,
    next_leaf: u32,
}

impl CondProbe<'_> {
    fn eval(
        &mut self,
        expr: &Expr,
        env: &mut Env,
        functions: &mut HashMap<String, Arc<FunctionDef>>,
        classes: &mut HashMap<String, Arc<ClassDef>>,
        enums: &Enums,
        impl_methods: &ImplMethods,
    ) -> Result<bool, CompileError> {
        match expr {
            Expr::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                left,
                right,
            } => {
                let l = self.eval(left, env, functions, classes, enums, impl_methods)?;
                let short_circuit = if matches!(op, BinOp::And) { !l } else { l };
                if short_circuit {
                    // Right operand not evaluated: its leaves keep their numbers.
                    self.next_leaf += count_tree_leaves(right);
                    return Ok(l);
                }
                self.eval(right, env, functions, classes, enums, impl_methods)
            }
            _ => {
                let value = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
                let result = super::interpreter_control::is_condition_present(expr, &value);
                simple_runtime::coverage::coverage_record_condition(
                    self.decision_id,
                    self.next_leaf,
                    result,
                    self.file,
                    self.line,
                    self.column,
                );
                self.next_leaf += 1;
                Ok(result)
            }
        }
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
