//! Control flow execution functions for the interpreter
//!
//! This module provides implementations for control flow constructs:
//! - If/else statements
//! - Match expressions
//! - While loops
//! - For loops
//! - Loop control (break, continue)

use std::sync::Arc;
use crate::error::CompileError;

/// Check if user requested interrupt (Ctrl-C) and return error if so.
///
/// This macro should be called at the start of each loop iteration to allow
/// graceful interruption of long-running computations.
/// Only active in debug mode to avoid performance overhead in release builds.
#[cfg(debug_assertions)]
macro_rules! check_interrupt {
    () => {
        if crate::interpreter::is_interrupted() {
            return Err(CompileError::InterruptedByUser);
        }
    };
}

/// No-op version for release builds (zero overhead)
#[cfg(not(debug_assertions))]
macro_rules! check_interrupt {
    () => {
        // No-op in release mode for maximum performance
    };
}

/// Check execution limit and return error if exceeded.
/// Only active in debug builds by default (controlled by EXECUTION_LIMIT_ENABLED).
macro_rules! check_execution_limit {
    () => {
        crate::interpreter::check_execution_limit()?;
    };
}

/// Check if the watchdog timeout has been exceeded.
macro_rules! check_timeout {
    () => {
        if crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
    };
}
use crate::value::{Env, Value, ATTR_STRONG, BUILTIN_ARRAY, BUILTIN_RANGE};
use simple_parser::ast::{
    ClassDef, ContextStmt, Expr, ForStmt, FunctionDef, IfStmt, LoopStmt, MatchStmt, WhileStmt, WithStmt,
};
use std::cell::RefCell;
use std::collections::HashMap;

// Import parent interpreter types and functions
use super::{
    await_value, evaluate_expr, exec_block, exec_block_fn, Control, Enums, ImplMethods, BDD_CONTEXT_DEFS, BDD_INDENT,
    BDD_LAZY_VALUES, CONST_NAMES, CONTEXT_OBJECT, CONTEXT_VAR_NAME, IMMUTABLE_VARS,
};

// Import helpers for pattern binding
use super::interpreter_helpers::{bind_pattern, iter_to_vec};

// Import from interpreter_call for exec_block_value (sibling module)
use super::interpreter_call::exec_block_value;

// Import pattern matching functions from sibling module
use super::interpreter_patterns::{is_catch_all_pattern, pattern_matches};

// Import coverage helpers
use super::coverage_helpers::{record_decision_coverage_ffi, decision_id_from_span};

/// Handle loop control flow result. Returns Some if we should exit the loop.
/// `my_label` is this loop's label (if any).
#[inline]
fn handle_loop_control_labeled(ctrl: Control, my_label: &Option<String>) -> Option<Result<Control, CompileError>> {
    match ctrl {
        Control::Next => None,
        Control::Continue(ref lbl) => {
            // If continue has a label and it doesn't match this loop, propagate
            if let Some(target) = lbl {
                if my_label.as_deref() != Some(target.as_str()) {
                    return Some(Ok(ctrl));
                }
            }
            None // continue to next iteration of this loop
        }
        Control::Break(_, ref lbl) => {
            // If break has a label and it doesn't match this loop, propagate
            if let Some(target) = lbl {
                if my_label.as_deref() != Some(target.as_str()) {
                    return Some(Ok(ctrl));
                }
            }
            Some(Ok(Control::Next)) // break out of this loop
        }
        ret @ Control::Return(_) => Some(Ok(ret)),
    }
}

/// Handle loop control flow result. Returns Some if we should exit the loop.
#[inline]
fn handle_loop_control(ctrl: Control) -> Option<Result<Control, CompileError>> {
    handle_loop_control_labeled(ctrl, &None)
}

pub(super) fn exec_if(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Handle if-let: if let PATTERN = EXPR:
    if let Some(pattern) = &if_stmt.let_pattern {
        let value = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
        let mut bindings = HashMap::new();
        if pattern_matches(pattern, &value, &mut bindings, enums)? {
            // Pattern matched - add bindings and execute then block
            for (name, val) in bindings {
                env.insert(name, val);
            }
            return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
        } else if let Some(block) = &if_stmt.else_block {
            // Pattern didn't match - execute else block
            return exec_block(block, env, functions, classes, enums, impl_methods);
        }
        return Ok(Control::Next);
    }

    // Normal if condition
    // For if~ (is_suspend), await the condition value before checking truthiness
    let cond_val = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
    let cond_val = if if_stmt.is_suspend {
        await_value(cond_val)?
    } else {
        cond_val
    };

    let decision_result = cond_val.truthy();

    // COVERAGE: Record decision for if statement
    record_decision_coverage_ffi("<source>", if_stmt.span.line, if_stmt.span.column, decision_result);

    if decision_result {
        return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
    }

    for (idx, (pattern, cond, block)) in if_stmt.elif_branches.iter().enumerate() {
        if let Some(pattern) = pattern {
            // elif val PATTERN = EXPR: pattern binding
            let value = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            let mut bindings = HashMap::new();
            if pattern_matches(pattern, &value, &mut bindings, enums)? {
                for (name, val) in bindings {
                    env.insert(name, val);
                }
                return exec_block(block, env, functions, classes, enums, impl_methods);
            }
        } else {
            let elif_val = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            let elif_val = if if_stmt.is_suspend {
                await_value(elif_val)?
            } else {
                elif_val
            };
            let elif_decision = elif_val.truthy();

            // COVERAGE: Record decision for elif statement
            let elif_decision_id = if_stmt.span.line as u32 + idx as u32;
            record_decision_coverage_ffi("<source>", if_stmt.span.line + idx, if_stmt.span.column, elif_decision);

            if elif_decision {
                return exec_block(block, env, functions, classes, enums, impl_methods);
            }
        }
    }

    if let Some(block) = &if_stmt.else_block {
        return exec_block(block, env, functions, classes, enums, impl_methods);
    }
    Ok(Control::Next)
}

pub(super) fn exec_while(
    while_stmt: &simple_parser::ast::WhileStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Handle while-let: while let PATTERN = EXPR:
    if let Some(pattern) = &while_stmt.let_pattern {
        loop {
            check_interrupt!();
            check_execution_limit!();
            check_timeout!();
            let value = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
            let mut bindings = HashMap::new();
            if !pattern_matches(pattern, &value, &mut bindings, enums)? {
                break;
            }
            // Pattern matched - add bindings and execute body
            for (name, val) in bindings {
                env.insert(name, val);
            }
            let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
            if let Some(result) = handle_loop_control_labeled(ctrl, &while_stmt.label) {
                return result;
            }
        }
        return Ok(Control::Next);
    }

    // Normal while loop
    // For while~ (is_suspend), await the condition value before checking truthiness
    //
    // OPTIMIZATION: Loop-invariant hoisting for patterns like
    //   `while i < arr.len():` / `while i < text.len():`
    // When the receiver is a bare local that is NOT mutated anywhere in the loop
    // body (and the body has no function calls that could alias it), we evaluate
    // the `.len()` / `.size()` / `.count()` once before the loop and compare
    // against the cached integer each iteration. See `try_hoist_loop_invariant_len`
    // and `body_may_mutate_var` below.
    let hoist = if !while_stmt.is_suspend {
        try_hoist_loop_invariant_len(
            &while_stmt.condition,
            &while_stmt.body,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?
    } else {
        None
    };

    if let Some(hoisted) = hoist {
        loop {
            check_interrupt!();
            check_execution_limit!();
            check_timeout!();

            // Evaluate only the "other" (variant) side of the comparison and
            // compare against the cached length integer directly.
            let other_val = evaluate_expr(&hoisted.other_expr, env, functions, classes, enums, impl_methods)?;
            let other_int = match other_val {
                Value::Int(n) => n,
                _ => {
                    // Variant side didn't evaluate to an int — bail out of the fast path
                    // and re-run this iteration with the slow path semantics.
                    // This should be very rare; fall through to a full condition eval.
                    let cond_val = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
                    let decision_result = cond_val.truthy();
                    record_decision_coverage_ffi(
                        "<source>",
                        while_stmt.span.line,
                        while_stmt.span.column,
                        decision_result,
                    );
                    if !decision_result {
                        break;
                    }
                    let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
                    if let Some(result) = handle_loop_control_labeled(ctrl, &while_stmt.label) {
                        return result;
                    }
                    continue;
                }
            };

            let cached = hoisted.cached_len;
            // Compare: the cached value is always on `side_is_right` side of the op.
            // If cached is on right: lhs op rhs  == other_int op cached
            // If cached is on left:  lhs op rhs  == cached op other_int
            let decision_result = if hoisted.cached_on_right {
                match hoisted.op {
                    HoistOp::Lt => other_int < cached,
                    HoistOp::LtEq => other_int <= cached,
                    HoistOp::Gt => other_int > cached,
                    HoistOp::GtEq => other_int >= cached,
                    HoistOp::Eq => other_int == cached,
                    HoistOp::NotEq => other_int != cached,
                }
            } else {
                match hoisted.op {
                    HoistOp::Lt => cached < other_int,
                    HoistOp::LtEq => cached <= other_int,
                    HoistOp::Gt => cached > other_int,
                    HoistOp::GtEq => cached >= other_int,
                    HoistOp::Eq => cached == other_int,
                    HoistOp::NotEq => cached != other_int,
                }
            };

            record_decision_coverage_ffi(
                "<source>",
                while_stmt.span.line,
                while_stmt.span.column,
                decision_result,
            );

            if !decision_result {
                break;
            }
            let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
            if let Some(result) = handle_loop_control_labeled(ctrl, &while_stmt.label) {
                return result;
            }
        }
        return Ok(Control::Next);
    }

    loop {
        check_interrupt!();
        check_execution_limit!();
        check_timeout!();
        let cond_val = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
        let cond_val = if while_stmt.is_suspend {
            await_value(cond_val)?
        } else {
            cond_val
        };

        let decision_result = cond_val.truthy();

        // COVERAGE: Record decision for while condition on each iteration
        record_decision_coverage_ffi(
            "<source>",
            while_stmt.span.line,
            while_stmt.span.column,
            decision_result,
        );

        if !decision_result {
            break;
        }
        let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
        if let Some(result) = handle_loop_control_labeled(ctrl, &while_stmt.label) {
            return result;
        }
    }
    Ok(Control::Next)
}

/// Result of analyzing a while-loop condition for loop-invariant `.len()` hoisting.
struct HoistedLenLoop<'a> {
    /// The precomputed cached length (evaluated once before loop entry).
    cached_len: i64,
    /// The non-cached side of the comparison (still evaluated each iteration).
    other_expr: &'a Expr,
    /// True if the cached value was on the right-hand side of the original Binary.
    cached_on_right: bool,
    /// Which comparison operator was used.
    op: HoistOp,
}

#[derive(Clone, Copy)]
enum HoistOp {
    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    NotEq,
}

/// Try to detect and precompute a loop-invariant `.len()`/`.size()`/`.count()`
/// call in the condition of a while loop.
///
/// Safe to fire ONLY if:
/// - The condition is a `Binary { op: comparison, left, right }`.
/// - Exactly one side is a `MethodCall` on a bare `Identifier(name)` receiver,
///   with method name in {len, size, count}, zero args, zero generic args.
/// - The body contains NO assignments to `name`, no mutating method calls on
///   `name` (push/pop/append/insert/remove/clear/extend/sort/reverse), no index
///   assignments to `name[_]`, and no general function calls (which could
///   mutate via aliasing — conservative bail-out).
///
/// Returns `Some(HoistedLenLoop)` with the precomputed length on success,
/// `None` to fall back to the slow path.
fn try_hoist_loop_invariant_len<'a>(
    condition: &'a Expr,
    body: &simple_parser::ast::Block,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<HoistedLenLoop<'a>>, CompileError> {
    use simple_parser::ast::BinOp;

    // Condition must be a binary comparison.
    let (op, left, right) = match condition {
        Expr::Binary { op, left, right } => (*op, left.as_ref(), right.as_ref()),
        _ => return Ok(None),
    };
    let hop = match op {
        BinOp::Lt => HoistOp::Lt,
        BinOp::LtEq => HoistOp::LtEq,
        BinOp::Gt => HoistOp::Gt,
        BinOp::GtEq => HoistOp::GtEq,
        BinOp::Eq => HoistOp::Eq,
        BinOp::NotEq => HoistOp::NotEq,
        _ => return Ok(None),
    };

    // Check if either side is a hoistable method call and capture the receiver name.
    fn as_hoistable_len_call(e: &Expr) -> Option<&str> {
        if let Expr::MethodCall {
            receiver,
            method,
            args,
            generic_args,
        } = e
        {
            if !args.is_empty() || !generic_args.is_empty() {
                return None;
            }
            if method != "len" && method != "size" && method != "count" {
                return None;
            }
            if let Expr::Identifier(name) = receiver.as_ref() {
                return Some(name.as_str());
            }
        }
        None
    }

    let (recv_name, other_expr, cached_on_right) = if let Some(name) = as_hoistable_len_call(right) {
        (name, left, true)
    } else if let Some(name) = as_hoistable_len_call(left) {
        (name, right, false)
    } else {
        return Ok(None);
    };

    // Conservative body scan: bail on any mutation of `recv_name` or any function call.
    if body_may_mutate_var(&body.statements, recv_name) {
        return Ok(None);
    }

    // Evaluate the `.len()` once. Re-use evaluate_expr on a fresh synthetic call by
    // evaluating the receiver identifier and extracting length directly. We avoid
    // re-calling evaluate_expr on the MethodCall to keep the cost minimal.
    let recv_val = match env.get(recv_name) {
        Some(v) => v.clone(),
        None => return Ok(None),
    };
    let cached_len: i64 = match &recv_val {
        Value::Array(a) => a.len() as i64,
        Value::FrozenArray(a) => a.len() as i64,
        Value::FixedSizeArray { data, .. } => data.len() as i64,
        Value::Str(s) => s.chars().count() as i64,
        Value::Tuple(t) => t.len() as i64,
        _ => return Ok(None), // dict/other — bail; user might mean something custom
    };

    Ok(Some(HoistedLenLoop {
        cached_len,
        other_expr,
        cached_on_right,
        op: hop,
    }))
}

/// Returns true if any statement in `stmts` (recursively) may mutate the variable
/// named `var` or could call a function (worst-case aliasing).
///
/// Conservative: err on the side of returning `true` (= no hoisting).
fn body_may_mutate_var(stmts: &[simple_parser::ast::Node], var: &str) -> bool {
    use simple_parser::ast::Node;
    for s in stmts {
        if node_may_mutate_var(s, var) {
            return true;
        }
    }
    false
}

fn node_may_mutate_var(node: &simple_parser::ast::Node, var: &str) -> bool {
    use simple_parser::ast::{AssignOp, Node};
    match node {
        Node::Let(l) => {
            // Conservative: if the `let` binds a pattern that shadows `var`, treat as mutation.
            if pattern_binds_var(&l.pattern, var) {
                return true;
            }
            if let Some(v) = &l.value {
                if expr_may_mutate_var(v, var) {
                    return true;
                }
            }
            false
        }
        Node::Assignment(a) => {
            // Any assignment whose target is `var` (or `var[...]`, or a field/index of `var`)
            // or uses any AugAssign form on `var` is a mutation.
            if assign_target_touches_var(&a.target, var) {
                return true;
            }
            // += / -= etc. to anything involving var (e.g. `var += [x]`) also mutates.
            if !matches!(a.op, AssignOp::Assign) && assign_target_touches_var(&a.target, var) {
                return true;
            }
            if expr_may_mutate_var(&a.value, var) {
                return true;
            }
            false
        }
        Node::Expression(e) => expr_may_mutate_var(e, var),
        Node::Return(r) => {
            if let Some(v) = &r.value {
                expr_may_mutate_var(v, var)
            } else {
                false
            }
        }
        Node::If(iff) => {
            if expr_may_mutate_var(&iff.condition, var) {
                return true;
            }
            if body_may_mutate_var(&iff.then_block.statements, var) {
                return true;
            }
            for (_pat, cond, blk) in &iff.elif_branches {
                if expr_may_mutate_var(cond, var) {
                    return true;
                }
                if body_may_mutate_var(&blk.statements, var) {
                    return true;
                }
            }
            if let Some(eb) = &iff.else_block {
                if body_may_mutate_var(&eb.statements, var) {
                    return true;
                }
            }
            false
        }
        Node::While(w) => {
            if expr_may_mutate_var(&w.condition, var) {
                return true;
            }
            body_may_mutate_var(&w.body.statements, var)
        }
        Node::For(f) => {
            if expr_may_mutate_var(&f.iterable, var) {
                return true;
            }
            body_may_mutate_var(&f.body.statements, var)
        }
        Node::Loop(l) => body_may_mutate_var(&l.body.statements, var),
        Node::Match(m) => {
            if expr_may_mutate_var(&m.subject, var) {
                return true;
            }
            for arm in &m.arms {
                if let Some(g) = &arm.guard {
                    if expr_may_mutate_var(g, var) {
                        return true;
                    }
                }
                if body_may_mutate_var(&arm.body.statements, var) {
                    return true;
                }
            }
            false
        }
        // Anything else (Defer, complex constructs, break/continue/pass): assume unsafe.
        Node::Break(_) | Node::Continue(_) | Node::Pass(_) => false,
        _ => true,
    }
}

fn pattern_binds_var(pat: &simple_parser::ast::Pattern, var: &str) -> bool {
    use simple_parser::ast::Pattern;
    match pat {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => n == var,
        Pattern::Tuple(ps) | Pattern::Array(ps) | Pattern::Or(ps) => ps.iter().any(|p| pattern_binds_var(p, var)),
        Pattern::Struct { fields, .. } => fields.iter().any(|(_, p)| pattern_binds_var(p, var)),
        Pattern::Enum { payload: Some(ps), .. } => ps.iter().any(|p| pattern_binds_var(p, var)),
        Pattern::Typed { pattern, .. } => pattern_binds_var(pattern, var),
        _ => false,
    }
}

fn assign_target_touches_var(target: &Expr, var: &str) -> bool {
    match target {
        Expr::Identifier(n) => n == var,
        Expr::Index { receiver, .. } => assign_target_touches_var(receiver, var),
        Expr::FieldAccess { receiver, .. } => assign_target_touches_var(receiver, var),
        Expr::TupleIndex { receiver, .. } => assign_target_touches_var(receiver, var),
        _ => false,
    }
}

/// Returns true if `e` contains:
/// - any `Call { ... }` (function call — worst-case, could mutate via captured refs)
/// - any `MethodCall` on `var` with a mutating method name
/// - any `MethodCall` on anything else (conservative: could invoke user code)
/// - any reference to `var` as the receiver of a mutating op
///
/// For read-only patterns like `arr[j]` and `arr.len()` in the RHS of `sum + arr[j]`,
/// this returns false.
fn expr_may_mutate_var(e: &Expr, var: &str) -> bool {
    match e {
        // Plain reads.
        Expr::Integer(_)
        | Expr::Float(_)
        | Expr::TypedInteger(_, _)
        | Expr::TypedFloat(_, _)
        | Expr::String(_)
        | Expr::TypedString(_, _)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Symbol(_)
        | Expr::Atom(_)
        | Expr::Identifier(_)
        | Expr::Path(_)
        | Expr::ContractResult => false,

        Expr::Binary { left, right, .. } => expr_may_mutate_var(left, var) || expr_may_mutate_var(right, var),
        Expr::Unary { operand, .. } => expr_may_mutate_var(operand, var),

        Expr::Index { receiver, index } => expr_may_mutate_var(receiver, var) || expr_may_mutate_var(index, var),
        Expr::FieldAccess { receiver, .. } => expr_may_mutate_var(receiver, var),
        Expr::TupleIndex { receiver, .. } => expr_may_mutate_var(receiver, var),

        // Any function call: conservative bail-out.
        Expr::Call { .. } => true,
        Expr::KernelLaunch { .. } => true,
        Expr::MacroInvocation { .. } => true,

        // Method calls: only allow-list read-only methods on our tracked var;
        // any other method call is assumed unsafe.
        Expr::MethodCall {
            receiver, method, args, ..
        } => {
            // Read-only methods on the tracked var that we know cannot mutate it.
            const RO: &[&str] = &["len", "size", "count", "is_empty"];
            let receiver_is_var_ident = matches!(receiver.as_ref(), Expr::Identifier(n) if n == var);
            if receiver_is_var_ident && RO.contains(&method.as_str()) && args.is_empty() {
                return false;
            }
            // Anything else: assume it might mutate or run arbitrary code.
            true
        }
        Expr::OptionalMethodCall { .. } => true,

        Expr::Array(items) | Expr::Tuple(items) | Expr::VecLiteral(items) => {
            items.iter().any(|x| expr_may_mutate_var(x, var))
        }
        Expr::ArrayRepeat { value, count } => expr_may_mutate_var(value, var) || expr_may_mutate_var(count, var),
        Expr::Dict(pairs) => pairs
            .iter()
            .any(|(k, v)| expr_may_mutate_var(k, var) || expr_may_mutate_var(v, var)),

        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            expr_may_mutate_var(condition, var)
                || expr_may_mutate_var(then_branch, var)
                || else_branch.as_ref().map_or(false, |e| expr_may_mutate_var(e, var))
        }

        Expr::Cast { expr, .. } => expr_may_mutate_var(expr, var),
        Expr::Range { start, end, .. } => {
            start.as_ref().map_or(false, |e| expr_may_mutate_var(e, var))
                || end.as_ref().map_or(false, |e| expr_may_mutate_var(e, var))
        }

        // Anything exotic: bail.
        _ => true,
    }
}

pub(super) fn exec_loop(
    loop_stmt: &simple_parser::ast::LoopStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        check_interrupt!();
        check_execution_limit!();
        check_timeout!();
        let ctrl = exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)?;
        if let Some(result) = handle_loop_control_labeled(ctrl, &loop_stmt.label) {
            return result;
        }
    }
}

pub(super) fn exec_context(
    ctx_stmt: &ContextStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // BDD_INDENT, BDD_LAZY_VALUES, BDD_CONTEXT_DEFS are defined in interpreter_call.rs
    // which is also include!d into interpreter.rs, so they're in scope directly

    let context_obj = evaluate_expr(&ctx_stmt.context, env, functions, classes, enums, impl_methods)?;

    // Check if this is a BDD-style context (string or symbol description)
    match &context_obj {
        Value::Str(name) | Value::Symbol(name) => {
            // BDD-style context: context "description": block
            let name_str = if matches!(context_obj, Value::Symbol(_)) {
                format!("with {}", name)
            } else {
                name.clone()
            };

            // Check if this is a symbol referencing a context_def
            let ctx_def_blocks = if matches!(context_obj, Value::Symbol(_)) {
                BDD_CONTEXT_DEFS.with(|cell: &RefCell<HashMap<String, Vec<Value>>>| cell.borrow().get(name).cloned())
            } else {
                None
            };

            // Get current indent level
            let indent = BDD_INDENT.with(|cell: &RefCell<usize>| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            // Print context name
            println!("{}{}", indent_str, name_str);

            // Increase indent for nested blocks
            BDD_INDENT.with(|cell: &RefCell<usize>| *cell.borrow_mut() += 1);

            // If this is a context_def reference, execute its givens first
            if let Some(ctx_blocks) = ctx_def_blocks {
                for ctx_block in ctx_blocks {
                    exec_block_value(ctx_block, env, functions, classes, enums, impl_methods)?;
                }
            }

            // Execute the block
            let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);

            // Clear lazy values after context exits
            BDD_LAZY_VALUES.with(|cell: &RefCell<HashMap<String, (Value, Option<Value>)>>| cell.borrow_mut().clear());

            // Restore indent
            BDD_INDENT.with(|cell: &RefCell<usize>| *cell.borrow_mut() -= 1);

            result
        }
        _ => {
            // Non-BDD context: set context object and execute block
            // Extract variable name if context is an identifier (for mutation persistence)
            let var_name = if let Expr::Identifier(name) = &ctx_stmt.context {
                Some(name.clone())
            } else {
                None
            };

            let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
            let prev_var_name = CONTEXT_VAR_NAME.with(|cell| cell.borrow().clone());

            CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));
            CONTEXT_VAR_NAME.with(|cell| *cell.borrow_mut() = var_name.clone());

            let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);

            // After block execution, persist any mutations to the original variable
            if let Some(name) = &var_name {
                if let Some(updated_obj) = CONTEXT_OBJECT.with(|cell| cell.borrow().clone()) {
                    env.insert(name.clone(), updated_obj);
                }
            }

            CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);
            CONTEXT_VAR_NAME.with(|cell| *cell.borrow_mut() = prev_var_name);
            result
        }
    }
}

/// Execute a with statement (context manager pattern)
/// with resource as name:
///     body
/// Calls __enter__ before body, __exit__ after (even on error)
pub fn exec_with(
    with_stmt: &WithStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let resource = evaluate_expr(&with_stmt.resource, env, functions, classes, enums, impl_methods)?;

    // Call __enter__ if it exists
    let enter_result = call_method_if_exists(
        &resource,
        "__enter__",
        &[],
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )?;

    // Bind the result to the name if provided
    if let Some(name) = &with_stmt.name {
        env.insert(name.clone(), enter_result.unwrap_or(resource.clone()));
    }

    // Execute the body
    let result = exec_block(&with_stmt.body, env, functions, classes, enums, impl_methods);

    // Always call cleanup (even if body failed)
    // First try __exit__, then fall back to close() for Resource types
    // Pass nil as exception argument (TODO: pass actual exception if body errored)
    let exc_arg = Value::Nil;
    let exit_result = call_method_if_exists(
        &resource,
        "__exit__",
        &[exc_arg],
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )?;
    if exit_result.is_none() {
        // No __exit__ method found - try close() for Resource trait compatibility
        let _ = call_method_if_exists(&resource, "close", &[], env, functions, classes, enums, impl_methods);
    }

    // Remove the binding if it was created
    if let Some(name) = &with_stmt.name {
        env.remove(name);
    }

    result
}

/// Helper to execute a method body with self and fields bound
#[allow(clippy::too_many_arguments)]
fn exec_method_body(
    method: &FunctionDef,
    receiver: &Value,
    fields: &HashMap<String, Value>,
    args: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Save current CONST_NAMES and IMMUTABLE_VARS, clear for method scope
    // This prevents const/immutable names from caller leaking into callee
    let saved_const_names = CONST_NAMES.with(|cell| cell.borrow().clone());
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    let saved_immutable_vars = IMMUTABLE_VARS.with(|cell| cell.borrow().clone());
    IMMUTABLE_VARS.with(|cell| cell.borrow_mut().clear());

    let mut local_env = env.clone();
    local_env.insert("self".to_string(), receiver.clone());
    for (k, v) in fields {
        local_env.insert(k.clone(), v.clone());
    }
    // Bind method parameters to argument values, skipping `self` since it's already bound
    let non_self_params: Vec<_> = method.params.iter().filter(|p| p.name != "self").collect();
    for (i, param) in non_self_params.iter().enumerate() {
        let arg_val = args.get(i).cloned().unwrap_or(Value::Nil);
        local_env.insert(param.name.clone(), arg_val);
    }
    // Use exec_block_fn to handle implicit returns properly
    let result = exec_block_fn(&method.body, &mut local_env, functions, classes, enums, impl_methods);

    // ALWAYS restore CONST_NAMES and IMMUTABLE_VARS before returning to avoid leaking to caller
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);

    let (control, implicit_val) = result?;
    // Return explicit return value if present, otherwise implicit value, otherwise Nil
    Ok(match control {
        Control::Return(val) => val,
        _ => implicit_val.unwrap_or(Value::Nil),
    })
}

/// Helper to call a method if it exists on an object
#[allow(clippy::too_many_arguments)]
pub(crate) fn call_method_if_exists(
    receiver: &Value,
    method_name: &str,
    args: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if let Value::Object { class, fields } = receiver {
        // Check if the class has the method
        if let Some(class_def) = classes.get(class).cloned() {
            if let Some(method) = class_def.methods.iter().find(|m| m.name == method_name).cloned() {
                return Ok(Some(exec_method_body(
                    &method,
                    receiver,
                    fields,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?));
            }
        }
        // Check impl_methods
        if let Some(methods) = impl_methods.get(class) {
            if let Some(method) = methods.iter().find(|m| m.name == method_name) {
                return Ok(Some(exec_method_body(
                    method,
                    receiver,
                    fields,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?));
            }
        }
    }
    Ok(None)
}

pub(super) fn exec_for(
    for_stmt: &simple_parser::ast::ForStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let iterable = evaluate_expr(&for_stmt.iterable, env, functions, classes, enums, impl_methods)?;

    // For for~ (is_suspend), await the iterable if it's a Promise
    let iterable = if for_stmt.is_suspend {
        await_value(iterable)?
    } else {
        iterable
    };

    // Check if iterating over a Dict - auto_enumerate doesn't apply since
    // dict iteration already returns (key, value) tuples
    let is_dict_iteration = matches!(&iterable, Value::Dict(_));

    // Use iter_to_vec to handle all iterable types uniformly
    let items = iter_to_vec(&iterable)?;

    // If auto_enumerate, wrap items with indices as tuples
    // But NOT for dict iteration - dict items are already (key, value) tuples
    for (index, item) in items.into_iter().enumerate() {
        check_interrupt!();
        check_execution_limit!();
        check_timeout!();

        // For for~ (is_suspend), await each item if it's a Promise
        let item = if for_stmt.is_suspend { await_value(item)? } else { item };

        // Create the value to bind - either (index, item) tuple or just item
        // For dict iteration, items are already (key, value) tuples, so don't wrap
        let bind_value = if for_stmt.auto_enumerate && !is_dict_iteration {
            Value::Tuple(vec![Value::Int(index as i64), item])
        } else {
            item
        };

        // Use bind_pattern to handle all pattern types (identifier, tuple, etc.)
        if !bind_pattern(&for_stmt.pattern, &bind_value, env) {
            // Pattern didn't match - skip this iteration
            continue;
        }

        let ctrl = exec_block(&for_stmt.body, env, functions, classes, enums, impl_methods)?;
        if let Some(result) = handle_loop_control_labeled(ctrl, &for_stmt.label) {
            return result;
        }
    }
    Ok(Control::Next)
}

/// Core match execution logic shared between exec_match and exec_match_expr.
/// Returns (Control, Option<Value>) where the value is from the matched arm.
fn exec_match_core(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    let subject = evaluate_expr(&match_stmt.subject, env, functions, classes, enums, impl_methods)?;

    // Check for strong enum - disallow wildcard/catch-all patterns
    if let Value::Enum { enum_name, .. } = &subject {
        if let Some(enum_def) = enums.get(enum_name) {
            let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);
            if is_strong {
                for arm in &match_stmt.arms {
                    if is_catch_all_pattern(&arm.pattern) {
                        return Err(crate::error::factory::strong_enum_no_wildcard(enum_name));
                    }
                }
            }
        }
    }

    for (arm_index, arm) in match_stmt.arms.iter().enumerate() {
        let mut bindings = HashMap::new();
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums)? {
            if let Some(guard) = &arm.guard {
                let mut guard_env = env.clone();
                for (name, value) in &bindings {
                    guard_env.insert(name.clone(), value.clone());
                }
                if !evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?.truthy() {
                    continue;
                }
            }

            // COVERAGE: Record that this match arm was taken
            record_decision_coverage_ffi(
                "<source>",
                match_stmt.span.line + arm_index,
                match_stmt.span.column,
                true, // We matched an arm
            );

            for (name, value) in bindings {
                env.insert(name, value);
            }

            // Execute the match arm body and capture both flow and value
            let (flow, last_val) = exec_block_fn(&arm.body, env, functions, classes, enums, impl_methods)?;
            return Ok((flow, last_val));
        }
    }

    // No arm matched
    Ok((Control::Next, None))
}

pub(super) fn exec_match(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let (flow, _last_val) = exec_match_core(match_stmt, env, functions, classes, enums, impl_methods)?;
    match flow {
        Control::Return(_) | Control::Break(..) | Control::Continue(_) => Ok(flow),
        Control::Next => {
            // Match arm completed normally - continue after match
            // Note: implicit return from match arms should NOT return from function
            Ok(Control::Next)
        }
    }
}

/// Execute an if statement as an expression, returning the branch's implicit value.
/// Used for implicit return when if is the last statement in a function.
pub(crate) fn exec_if_expr(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Handle if-let: if let PATTERN = EXPR:
    if let Some(pattern) = &if_stmt.let_pattern {
        let value = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
        let mut bindings = HashMap::new();
        if pattern_matches(pattern, &value, &mut bindings, enums)? {
            // Pattern matched - add bindings and execute then block
            for (name, val) in bindings {
                env.insert(name, val);
            }
            let (flow, last_val) = exec_block_fn(&if_stmt.then_block, env, functions, classes, enums, impl_methods)?;
            return match flow {
                Control::Return(v) => Ok(v),
                _ => Ok(last_val.unwrap_or(Value::Nil)),
            };
        } else if let Some(block) = &if_stmt.else_block {
            let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
            return match flow {
                Control::Return(v) => Ok(v),
                _ => Ok(last_val.unwrap_or(Value::Nil)),
            };
        }
        return Ok(Value::Nil);
    }

    // Normal if condition
    let cond_val = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
    let cond_val = if if_stmt.is_suspend {
        await_value(cond_val)?
    } else {
        cond_val
    };

    if cond_val.truthy() {
        let (flow, last_val) = exec_block_fn(&if_stmt.then_block, env, functions, classes, enums, impl_methods)?;
        return match flow {
            Control::Return(v) => Ok(v),
            _ => Ok(last_val.unwrap_or(Value::Nil)),
        };
    }

    for (pattern, cond, block) in if_stmt.elif_branches.iter() {
        if let Some(pattern) = pattern {
            let value = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            let mut bindings = HashMap::new();
            if pattern_matches(pattern, &value, &mut bindings, enums)? {
                for (name, val) in bindings {
                    env.insert(name, val);
                }
                let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
                return match flow {
                    Control::Return(v) => Ok(v),
                    _ => Ok(last_val.unwrap_or(Value::Nil)),
                };
            }
        } else {
            let elif_val = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            let elif_val = if if_stmt.is_suspend {
                await_value(elif_val)?
            } else {
                elif_val
            };
            if elif_val.truthy() {
                let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
                return match flow {
                    Control::Return(v) => Ok(v),
                    _ => Ok(last_val.unwrap_or(Value::Nil)),
                };
            }
        }
    }

    if let Some(block) = &if_stmt.else_block {
        let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
        return match flow {
            Control::Return(v) => Ok(v),
            _ => Ok(last_val.unwrap_or(Value::Nil)),
        };
    }

    Ok(Value::Nil)
}

/// Execute a match statement as an expression, returning the match arm's value.
/// Used for implicit return when match is the last statement in a function.
pub(crate) fn exec_match_expr(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let (flow, last_val) = exec_match_core(match_stmt, env, functions, classes, enums, impl_methods)?;
    match flow {
        Control::Return(v) => Ok(v),
        Control::Break(..) | Control::Continue(_) => Ok(Value::Nil),
        Control::Next => {
            // Return the implicit value from the match arm
            Ok(last_val.unwrap_or(Value::Nil))
        }
    }
}
