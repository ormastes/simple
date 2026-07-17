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
    AssignOp, BinOp, ClassDef, ContextStmt, Expr, ForStmt, FunctionDef, IfStmt, LoopStmt, MatchStmt, Node, Pattern,
    RangeBound, UnaryOp, WhileStmt, WithStmt,
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
use super::coverage_helpers::{decision_id_from_span, is_coverage_enabled, record_decision_coverage_sffi};

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

/// Result of evaluating an `if val IDENT = expr` / `elif val IDENT = expr`
/// optional-binding condition.
///
/// `pub(crate)` so `interpreter_call::block_execution`'s lambda/block-closure/BDD
/// if-let handling can reuse it too (see `optional_let_binding` doc comment and
/// bug #188a — that sibling executor had its own copy of the pre-fix
/// `pattern_matches`-only logic and never received this fix).
pub(crate) enum LetBind {
    /// Pattern is not a simple identifier binding — defer to `pattern_matches`.
    NotApplicable,
    /// Value is absent (nil / Option::None) — skip this branch.
    Skip,
    /// Value is present — take the branch, binding `name` to the *unwrapped* value.
    Bind(String, Value),
}

/// `if val IDENT = expr` is an optional-binding: take the branch only when the
/// value is present, binding IDENT to the *unwrapped* value. Running a bare
/// identifier pattern through `pattern_matches` instead always matches and binds
/// the whole value — so the branch was wrongly taken for `None`/`nil` and IDENT
/// held the Option wrapper rather than its payload. Handle the identifier case
/// here with correct semantics; defer structural patterns (Some(x), enums,
/// tuples, …) to `pattern_matches`.
pub(crate) fn optional_let_binding(pattern: &Pattern, value: &Value) -> LetBind {
    let name = match pattern {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => n.clone(),
        _ => return LetBind::NotApplicable,
    };
    match value {
        Value::Nil => LetBind::Skip,
        Value::Enum {
            enum_name,
            variant,
            payload,
        } if enum_name == "Option" => {
            if variant == "Some" {
                match payload.as_ref().map(|b| &**b) {
                    Some(Value::Nil) | None => LetBind::Skip,
                    Some(inner) => LetBind::Bind(name, inner.clone()),
                }
            } else {
                LetBind::Skip
            }
        }
        // Other enum values keep their existing semantics (a bare identifier may
        // name a unit variant) — let `pattern_matches` decide.
        Value::Enum { .. } => LetBind::NotApplicable,
        // Any other present value binds as-is.
        other => LetBind::Bind(name, other.clone()),
    }
}

#[cfg(test)]
mod optional_let_binding_tests {
    use super::*;

    #[test]
    fn skips_some_nil_optional_binding() {
        let pattern = Pattern::Identifier("value".to_string());
        let value = Value::some(Value::Nil);

        match optional_let_binding(&pattern, &value) {
            LetBind::Skip => {}
            _ => panic!("if val must not bind nil payloads"),
        }
    }
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
        match optional_let_binding(pattern, &value) {
            LetBind::Bind(name, inner) => {
                env.insert(name, inner);
                return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
            }
            // value absent — fall through to elif branches / else below.
            LetBind::Skip => {}
            LetBind::NotApplicable => {
                let mut bindings = HashMap::new();
                if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                    // Pattern matched - add bindings and execute then block
                    for (name, val) in bindings {
                        env.insert(name, val);
                    }
                    return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
                }
                // Pattern didn't match - fall through to elif branches / else below.
                // (Previously this returned the else block directly, silently skipping
                // every `elif`/`elif val ...` branch.)
            }
        }
    } else {
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
        record_decision_coverage_sffi("<source>", if_stmt.span.line, if_stmt.span.column, decision_result);

        if decision_result {
            return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
        }
    }

    for (idx, (pattern, cond, block)) in if_stmt.elif_branches.iter().enumerate() {
        if let Some(pattern) = pattern {
            // elif val PATTERN = EXPR: pattern binding
            let value = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            match optional_let_binding(pattern, &value) {
                LetBind::Bind(name, inner) => {
                    env.insert(name, inner);
                    return exec_block(block, env, functions, classes, enums, impl_methods);
                }
                LetBind::Skip => {}
                LetBind::NotApplicable => {
                    let mut bindings = HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                        for (name, val) in bindings {
                            env.insert(name, val);
                        }
                        return exec_block(block, env, functions, classes, enums, impl_methods);
                    }
                }
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
            record_decision_coverage_sffi("<source>", if_stmt.span.line + idx, if_stmt.span.column, elif_decision);

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
    if let Some(ctrl) = try_exec_indexed_int_array_match_count_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_indexed_int_array_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_indexed_float_array_match_count_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_indexed_float_array_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_indexed_string_match_count_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_direct_float_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_direct_int_match_count_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_direct_int_while_loop(while_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_one_arg_int_helper_while_loop(while_stmt, env, functions)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_two_arg_int_helper_while_loop(while_stmt, env, functions)? {
        return Ok(ctrl);
    }

    // Handle while-let: while let PATTERN = EXPR:
    if let Some(pattern) = &while_stmt.let_pattern {
        loop {
            check_interrupt!();
            check_execution_limit!();
            check_timeout!();
            let value = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
            let mut bindings = HashMap::new();
            if !pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
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
            let other_val = evaluate_expr(hoisted.other_expr, env, functions, classes, enums, impl_methods)?;
            let other_int = match other_val {
                Value::Int(n) => n,
                _ => {
                    // Variant side didn't evaluate to an int — bail out of the fast path
                    // and re-run this iteration with the slow path semantics.
                    // This should be very rare; fall through to a full condition eval.
                    let cond_val = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
                    let decision_result = cond_val.truthy();
                    record_decision_coverage_sffi(
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

            record_decision_coverage_sffi(
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
        record_decision_coverage_sffi(
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

#[derive(Clone)]
enum InlineIntOperand {
    Target,
    Index,
    IndexPlus { delta: i64 },
    IndexMinus { delta: i64 },
    IndexModulo { divisor: i64 },
    IndexTimes { factor: i64 },
    IndexBitAnd { mask: i64 },
    IndexBitOr { mask: i64 },
    IndexBitXor { mask: i64 },
    IndexShiftLeft { bits: u32 },
    IndexShiftRight { bits: u32 },
    Const(i64),
    EnvVar(String),
    LenOf(String),
    DictValue { dict: String, key: String },
}

struct TwoArgIntHelperLoop {
    target: String,
    index: String,
    end: InlineIntOperand,
    op: BinOp,
    left: InlineIntOperand,
    right: InlineIntOperand,
}

struct OneArgIntHelperLoop {
    target: String,
    index: String,
    end: InlineIntOperand,
    op: BinOp,
    left: InlineIntOperand,
    right: InlineIntOperand,
}

struct DirectIntWhileLoop {
    target: String,
    index: String,
    end: InlineIntOperand,
    op: BinOp,
    left: InlineIntOperand,
    right: InlineIntOperand,
}

struct DirectIntMatchCountWhileLoop {
    target: String,
    index: String,
    end: InlineIntOperand,
    predicate: DirectIntBranchPredicate,
    op: BinOp,
    left: InlineIntOperand,
    right: InlineIntOperand,
}

enum DirectIntBranchPredicate {
    IndexEquals {
        needle: i64,
        match_when_equal: bool,
    },
    IndexModuloEquals {
        divisor: i64,
        remainder: i64,
        match_when_equal: bool,
    },
    IndexBitAndEquals {
        mask: i64,
        expected: i64,
        match_when_equal: bool,
    },
}

enum InlineFloatOperand {
    Target,
    Const(f64),
}

struct DirectFloatWhileLoop {
    target: String,
    index: String,
    end: InlineIntOperand,
    op: BinOp,
    left: InlineFloatOperand,
    right: InlineFloatOperand,
}

struct IndexedIntArrayWhileLoop {
    target: String,
    index: String,
    array: String,
    op: BinOp,
    left: IndexedIntArrayOperand,
    right: IndexedIntArrayOperand,
}

struct IndexedIntArrayMatchCountWhileLoop {
    target: String,
    index: String,
    array: String,
    needle: i64,
    match_when_equal: bool,
    op: BinOp,
    left: IndexedIntArrayOperand,
    right: IndexedIntArrayOperand,
}

enum IndexedIntArrayOperand {
    Target,
    Index,
    Element,
    DictValue { dict: String, key: String },
    Const(i64),
}

struct IndexedFloatArrayWhileLoop {
    target: String,
    index: String,
    array: String,
    op: BinOp,
    left: IndexedFloatArrayOperand,
    right: IndexedFloatArrayOperand,
}

struct IndexedFloatArrayMatchCountWhileLoop {
    target: String,
    index: String,
    array: String,
    needle: f64,
    match_when_equal: bool,
    op: BinOp,
    left: IndexedIntArrayOperand,
    right: IndexedIntArrayOperand,
}

struct IndexedStringMatchCountWhileLoop {
    target: String,
    index: String,
    text: String,
    needle: char,
    match_when_equal: bool,
    op: BinOp,
    left: IndexedIntArrayOperand,
    right: IndexedIntArrayOperand,
}

enum IndexedFloatArrayOperand {
    Target,
    Element,
    Const(f64),
}

fn try_exec_direct_float_while_loop(while_stmt: &WhileStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_direct_float_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || inline_operand_is_env_var(&loop_shape.end, &loop_shape.target)
        || inline_operand_len_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Float(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let end = match eval_stable_inline_operand(&loop_shape.end, env, 0, index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let left_value = eval_float_operand(&loop_shape.left, target);
        let right_value = eval_float_operand(&loop_shape.right, target);
        target = match loop_shape.op {
            BinOp::Add => left_value + right_value,
            BinOp::Sub => left_value - right_value,
            BinOp::Mul => left_value * right_value,
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Float(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_direct_float_while_loop(while_stmt: &WhileStmt) -> Option<DirectFloatWhileLoop> {
    let (index, end) = parse_simple_index_less_than(&while_stmt.condition)?;
    let [assignment_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::Assignment(assign) = assignment_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(DirectFloatWhileLoop {
        target: target.clone(),
        index,
        end,
        op: *op,
        left: parse_float_operand(left, target)?,
        right: parse_float_operand(right, target)?,
    })
}

fn parse_float_operand(expr: &Expr, target: &str) -> Option<InlineFloatOperand> {
    match expr {
        Expr::Identifier(name) if name == target => Some(InlineFloatOperand::Target),
        Expr::Float(value) | Expr::TypedFloat(value, _) => Some(InlineFloatOperand::Const(*value)),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(InlineFloatOperand::Const(*value as f64)),
        _ => None,
    }
}

fn eval_float_operand(operand: &InlineFloatOperand, target: f64) -> f64 {
    match operand {
        InlineFloatOperand::Target => target,
        InlineFloatOperand::Const(value) => *value,
    }
}

fn try_exec_indexed_float_array_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_indexed_float_array_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || loop_shape.target == loop_shape.array
        || loop_shape.index == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Float(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let end = values.len() as i64;

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let element = match values.get(index as usize) {
            Some(Value::Float(value)) => *value,
            _ => return Ok(None),
        };
        let left_value = eval_indexed_float_array_operand(&loop_shape.left, target, element);
        let right_value = eval_indexed_float_array_operand(&loop_shape.right, target, element);
        target = match loop_shape.op {
            BinOp::Add => left_value + right_value,
            BinOp::Sub => left_value - right_value,
            BinOp::Mul => left_value * right_value,
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Float(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_indexed_float_array_while_loop(while_stmt: &WhileStmt) -> Option<IndexedFloatArrayWhileLoop> {
    let (index, array) = parse_index_less_than_len_call(&while_stmt.condition)?;
    let [assignment_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::Assignment(assign) = assignment_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(IndexedFloatArrayWhileLoop {
        target: target.clone(),
        index: index.clone(),
        array: array.clone(),
        op: *op,
        left: parse_indexed_float_array_operand(left, target, &index, &array)?,
        right: parse_indexed_float_array_operand(right, target, &index, &array)?,
    })
}

fn parse_indexed_float_array_operand(
    expr: &Expr,
    target: &str,
    index: &str,
    array: &str,
) -> Option<IndexedFloatArrayOperand> {
    match expr {
        Expr::Identifier(name) if name == target => Some(IndexedFloatArrayOperand::Target),
        Expr::Float(value) | Expr::TypedFloat(value, _) => Some(IndexedFloatArrayOperand::Const(*value)),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(IndexedFloatArrayOperand::Const(*value as f64)),
        Expr::Index {
            receiver,
            index: index_expr,
        } if matches!(receiver.as_ref(), Expr::Identifier(name) if name == array)
            && matches!(index_expr.as_ref(), Expr::Identifier(name) if name == index) =>
        {
            Some(IndexedFloatArrayOperand::Element)
        }
        _ => None,
    }
}

fn eval_indexed_float_array_operand(operand: &IndexedFloatArrayOperand, target: f64, element: f64) -> f64 {
    match operand {
        IndexedFloatArrayOperand::Target => target,
        IndexedFloatArrayOperand::Element => element,
        IndexedFloatArrayOperand::Const(value) => *value,
    }
}

fn try_exec_indexed_string_match_count_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_indexed_string_match_count_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || loop_shape.target == loop_shape.text
        || loop_shape.index == loop_shape.text
        || !loop_shape.needle.is_ascii()
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(None),
    };
    let text = match env.get(&loop_shape.text) {
        Some(Value::Str(value)) if value.is_ascii() => value.clone(),
        _ => return Ok(None),
    };
    let left = match lower_indexed_int_array_operand(&loop_shape.left, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_indexed_int_array_operand(&loop_shape.right, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let end = text.len() as i64;
    let needle = loop_shape.needle as u8;
    let bytes = text.as_bytes();

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let byte = bytes[index as usize];
        if (byte == needle) == loop_shape.match_when_equal {
            let left_value = eval_indexed_int_array_operand(&left, target, index, 0);
            let right_value = eval_indexed_int_array_operand(&right, target, index, 0);
            target = match loop_shape.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_indexed_string_match_count_while_loop(while_stmt: &WhileStmt) -> Option<IndexedStringMatchCountWhileLoop> {
    let (index, text) = parse_index_less_than_len_call(&while_stmt.condition)?;
    let [if_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::If(if_stmt) = if_node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_indexed_string_equality_condition(&if_stmt.condition, &index, &text)?;

    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    let left = parse_indexed_int_array_operand(left, target, &index, &text)?;
    let right = parse_indexed_int_array_operand(right, target, &index, &text)?;
    if indexed_int_array_operand_uses_element(&left) || indexed_int_array_operand_uses_element(&right) {
        return None;
    }

    Some(IndexedStringMatchCountWhileLoop {
        target: target.clone(),
        index: index.clone(),
        text: text.clone(),
        needle,
        match_when_equal,
        op: *op,
        left,
        right,
    })
}

fn try_exec_indexed_float_array_match_count_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_indexed_float_array_match_count_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || loop_shape.target == loop_shape.array
        || loop_shape.index == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_indexed_int_array_operand(&loop_shape.left, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_indexed_int_array_operand(&loop_shape.right, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let end = values.len() as i64;

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let element = match values.get(index as usize) {
            Some(Value::Float(value)) => *value,
            _ => return Ok(None),
        };
        if (element == loop_shape.needle) == loop_shape.match_when_equal {
            let left_value = eval_indexed_int_array_operand(&left, target, index, 0);
            let right_value = eval_indexed_int_array_operand(&right, target, index, 0);
            target = match loop_shape.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_indexed_float_array_match_count_while_loop(
    while_stmt: &WhileStmt,
) -> Option<IndexedFloatArrayMatchCountWhileLoop> {
    let (index, array) = parse_index_less_than_len_call(&while_stmt.condition)?;
    let [if_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::If(if_stmt) = if_node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_indexed_float_array_equality_condition(&if_stmt.condition, &index, &array)?;

    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(IndexedFloatArrayMatchCountWhileLoop {
        target: target.clone(),
        index: index.clone(),
        array: array.clone(),
        needle,
        match_when_equal,
        op: *op,
        left: parse_indexed_int_array_operand(left, target, &index, &array)?,
        right: parse_indexed_int_array_operand(right, target, &index, &array)?,
    })
}

fn try_exec_indexed_int_array_match_count_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_indexed_int_array_match_count_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || loop_shape.target == loop_shape.array
        || loop_shape.index == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_indexed_int_array_operand(&loop_shape.left, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_indexed_int_array_operand(&loop_shape.right, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let end = values.len() as i64;

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let element = match values.get(index as usize) {
            Some(Value::Int(value)) => *value,
            _ => return Ok(None),
        };
        if (element == loop_shape.needle) == loop_shape.match_when_equal {
            let left_value = eval_indexed_int_array_operand(&left, target, index, element);
            let right_value = eval_indexed_int_array_operand(&right, target, index, element);
            target = match loop_shape.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_indexed_int_array_match_count_while_loop(
    while_stmt: &WhileStmt,
) -> Option<IndexedIntArrayMatchCountWhileLoop> {
    let (index, array) = parse_index_less_than_len_call(&while_stmt.condition)?;
    let [if_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::If(if_stmt) = if_node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_indexed_int_array_equality_condition(&if_stmt.condition, &index, &array)?;

    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(IndexedIntArrayMatchCountWhileLoop {
        target: target.clone(),
        index: index.clone(),
        array: array.clone(),
        needle,
        match_when_equal,
        op: *op,
        left: parse_indexed_int_array_operand(left, target, &index, &array)?,
        right: parse_indexed_int_array_operand(right, target, &index, &array)?,
    })
}

fn try_exec_indexed_int_array_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_indexed_int_array_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || loop_shape.target == loop_shape.array
        || loop_shape.index == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_indexed_int_array_operand(&loop_shape.left, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_indexed_int_array_operand(&loop_shape.right, env) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let end = values.len() as i64;

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let element = match values.get(index as usize) {
            Some(Value::Int(value)) => *value,
            _ => return Ok(None),
        };
        let left_value = eval_indexed_int_array_operand(&left, target, index, element);
        let right_value = eval_indexed_int_array_operand(&right, target, index, element);
        target = match loop_shape.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_indexed_int_array_while_loop(while_stmt: &WhileStmt) -> Option<IndexedIntArrayWhileLoop> {
    let (index, array) = parse_index_less_than_len_call(&while_stmt.condition)?;
    let [assignment_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::Assignment(assign) = assignment_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(IndexedIntArrayWhileLoop {
        target: target.clone(),
        index: index.clone(),
        array: array.clone(),
        op: *op,
        left: parse_indexed_int_array_operand(left, target, &index, &array)?,
        right: parse_indexed_int_array_operand(right, target, &index, &array)?,
    })
}

fn parse_index_less_than_len_call(expr: &Expr) -> Option<(String, String)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    if *op != BinOp::Lt {
        return None;
    }
    let Expr::Identifier(index) = left.as_ref() else {
        return None;
    };
    let Expr::MethodCall {
        receiver,
        method,
        args,
        generic_args,
    } = right.as_ref()
    else {
        return None;
    };
    if method != "len" || !args.is_empty() || !generic_args.is_empty() {
        return None;
    }
    let Expr::Identifier(array) = receiver.as_ref() else {
        return None;
    };
    Some((index.clone(), array.clone()))
}

fn parse_indexed_int_array_equality_condition(expr: &Expr, index: &str, array: &str) -> Option<(i64, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if is_indexed_array_element(left, index, array) {
        Some((parse_static_int(right)?, match_when_equal))
    } else if is_indexed_array_element(right, index, array) {
        Some((parse_static_int(left)?, match_when_equal))
    } else {
        None
    }
}

fn parse_indexed_float_array_equality_condition(expr: &Expr, index: &str, array: &str) -> Option<(f64, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if is_indexed_array_element(left, index, array) {
        Some((parse_static_float(right)?, match_when_equal))
    } else if is_indexed_array_element(right, index, array) {
        Some((parse_static_float(left)?, match_when_equal))
    } else {
        None
    }
}

fn parse_indexed_string_equality_condition(expr: &Expr, index: &str, text: &str) -> Option<(char, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if is_indexed_array_element(left, index, text) {
        Some((parse_single_static_char(right)?, match_when_equal))
    } else if is_indexed_array_element(right, index, text) {
        Some((parse_single_static_char(left)?, match_when_equal))
    } else {
        None
    }
}

fn is_indexed_array_element(expr: &Expr, index: &str, array: &str) -> bool {
    let Expr::Index {
        receiver,
        index: index_expr,
    } = expr
    else {
        return false;
    };
    matches!(receiver.as_ref(), Expr::Identifier(name) if name == array)
        && matches!(index_expr.as_ref(), Expr::Identifier(name) if name == index)
}

fn indexed_int_array_operand_uses_element(operand: &IndexedIntArrayOperand) -> bool {
    matches!(operand, IndexedIntArrayOperand::Element)
}

fn parse_indexed_int_array_operand(
    expr: &Expr,
    target: &str,
    index: &str,
    array: &str,
) -> Option<IndexedIntArrayOperand> {
    match expr {
        Expr::Identifier(name) if name == target => Some(IndexedIntArrayOperand::Target),
        Expr::Identifier(name) if name == index => Some(IndexedIntArrayOperand::Index),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(IndexedIntArrayOperand::Const(*value)),
        Expr::Index {
            receiver,
            index: index_expr,
        } => {
            if matches!(receiver.as_ref(), Expr::Identifier(name) if name == array)
                && matches!(index_expr.as_ref(), Expr::Identifier(name) if name == index)
            {
                Some(IndexedIntArrayOperand::Element)
            } else if let Expr::Identifier(dict) = receiver.as_ref() {
                let key = parse_static_string_key(index_expr)?;
                Some(IndexedIntArrayOperand::DictValue {
                    dict: dict.clone(),
                    key,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

fn lower_indexed_int_array_operand(
    operand: &IndexedIntArrayOperand,
    env: &Env,
) -> Result<IndexedIntArrayOperand, CompileError> {
    match operand {
        IndexedIntArrayOperand::DictValue { dict, key } => {
            let value = match env.get(dict) {
                Some(Value::Dict(values)) | Some(Value::FrozenDict(values)) => values.get(key),
                _ => None,
            };
            match value {
                Some(Value::Int(value)) => Ok(IndexedIntArrayOperand::Const(*value)),
                _ => Err(CompileError::runtime(format!(
                    "integer loop dict lookup `{dict}[{key}]` is not an integer"
                ))),
            }
        }
        IndexedIntArrayOperand::Target => Ok(IndexedIntArrayOperand::Target),
        IndexedIntArrayOperand::Index => Ok(IndexedIntArrayOperand::Index),
        IndexedIntArrayOperand::Element => Ok(IndexedIntArrayOperand::Element),
        IndexedIntArrayOperand::Const(value) => Ok(IndexedIntArrayOperand::Const(*value)),
    }
}

fn eval_indexed_int_array_operand(operand: &IndexedIntArrayOperand, target: i64, index: i64, element: i64) -> i64 {
    match operand {
        IndexedIntArrayOperand::Target => target,
        IndexedIntArrayOperand::Index => index,
        IndexedIntArrayOperand::Element => element,
        IndexedIntArrayOperand::DictValue { .. } => unreachable!("dict lookup operand was not lowered"),
        IndexedIntArrayOperand::Const(value) => *value,
    }
}

fn try_exec_direct_int_match_count_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_direct_int_match_count_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || inline_operand_is_env_var(&loop_shape.end, &loop_shape.target)
        || inline_operand_len_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let end = match eval_stable_inline_operand(&loop_shape.end, env, target, index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let left = match lower_stable_inline_operand(loop_shape.left, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_stable_inline_operand(loop_shape.right, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        if eval_direct_int_branch_predicate(&loop_shape.predicate, index) {
            let left_value = eval_inline_operand(&left, target, index);
            let right_value = eval_inline_operand(&right, target, index);
            target = match loop_shape.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_direct_int_match_count_while_loop(while_stmt: &WhileStmt) -> Option<DirectIntMatchCountWhileLoop> {
    let (index, end) = parse_simple_index_less_than(&while_stmt.condition)?;
    let [if_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::If(if_stmt) = if_node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let predicate = parse_index_branch_condition(&if_stmt.condition, &index)?;

    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(DirectIntMatchCountWhileLoop {
        target: target.clone(),
        index,
        end,
        predicate,
        op: *op,
        left: parse_inline_call_arg(left)?,
        right: parse_inline_call_arg(right)?,
    })
}

fn try_exec_direct_int_while_loop(while_stmt: &WhileStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_direct_int_while_loop(while_stmt) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || inline_operand_is_env_var(&loop_shape.end, &loop_shape.target)
        || inline_operand_len_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let end = match eval_stable_inline_operand(&loop_shape.end, env, target, index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let left = match lower_stable_inline_operand(loop_shape.left, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_stable_inline_operand(loop_shape.right, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let left_value = eval_inline_operand(&left, target, index);
        let right_value = eval_inline_operand(&right, target, index);
        target = match loop_shape.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_direct_int_while_loop(while_stmt: &WhileStmt) -> Option<DirectIntWhileLoop> {
    let (index, end) = parse_simple_index_less_than(&while_stmt.condition)?;
    let [assignment_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };

    let Node::Assignment(assign) = assignment_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    let left = parse_direct_int_body_operand(left, &index)?;
    let right = parse_direct_int_body_operand(right, &index)?;

    Some(DirectIntWhileLoop {
        target: target.clone(),
        index,
        end,
        op: *op,
        left,
        right,
    })
}

fn try_exec_one_arg_int_helper_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_one_arg_int_helper_loop(while_stmt, functions) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || inline_operand_is_env_var(&loop_shape.end, &loop_shape.target)
        || inline_operand_len_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let end = match eval_stable_inline_operand(&loop_shape.end, env, target, index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let left = match lower_stable_inline_operand(loop_shape.left, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_stable_inline_operand(loop_shape.right, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let left_value = eval_inline_operand(&left, target, index);
        let right_value = eval_inline_operand(&right, target, index);
        target = match loop_shape.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_one_arg_int_helper_loop(
    while_stmt: &WhileStmt,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Option<OneArgIntHelperLoop> {
    let (index, end) = parse_simple_index_less_than(&while_stmt.condition)?;
    let [call_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(call_assign) = call_node else {
        return None;
    };
    if call_assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &call_assign.target else {
        return None;
    };
    let Expr::Call { callee, args } = &call_assign.value else {
        return None;
    };
    let Expr::Identifier(function_name) = callee.as_ref() else {
        return None;
    };
    let [arg] = args.as_slice() else {
        return None;
    };
    if arg.name.is_some() || arg.label.is_some() {
        return None;
    }

    let function = functions.get(function_name)?;
    let [param] = function.params.as_slice() else {
        return None;
    };
    if param.default.is_some() || param.variadic {
        return None;
    }

    let body_expr = match function.body.statements.as_slice() {
        [Node::Expression(expr)] => expr,
        [Node::Return(ret)] => ret.value.as_ref()?,
        _ => return None,
    };
    let Expr::Binary { op, left, right } = body_expr else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let call_arg = parse_inline_call_arg(&arg.value)?;
    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(OneArgIntHelperLoop {
        target: target.clone(),
        index,
        end,
        op: *op,
        left: substitute_one_arg_inline_operand(left, param.name.as_str(), &call_arg)?,
        right: substitute_one_arg_inline_operand(right, param.name.as_str(), &call_arg)?,
    })
}

fn try_exec_two_arg_int_helper_while_loop(
    while_stmt: &WhileStmt,
    env: &mut Env,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Result<Option<Control>, CompileError> {
    if while_stmt.is_suspend
        || while_stmt.let_pattern.is_some()
        || while_stmt.label.is_some()
        || !while_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_two_arg_int_helper_loop(while_stmt, functions) else {
        return Ok(None);
    };
    if loop_shape.target == loop_shape.index
        || inline_operand_is_env_var(&loop_shape.end, &loop_shape.target)
        || inline_operand_len_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_len_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.end, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.left, &loop_shape.target, &loop_shape.index)
        || inline_operand_dict_receiver_conflicts(&loop_shape.right, &loop_shape.target, &loop_shape.index)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.target))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.index))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let mut index = match env.get(&loop_shape.index) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let end = match eval_stable_inline_operand(&loop_shape.end, env, target, index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let left = match lower_stable_inline_operand(loop_shape.left, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_stable_inline_operand(loop_shape.right, env, &loop_shape.target, &loop_shape.index) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut iterations = 0u64;
    while index < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let left_value = eval_inline_operand(&left, target, index);
        let right_value = eval_inline_operand(&right, target, index);
        target = match loop_shape.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        index = index.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.target, Value::Int(target));
    env.insert(loop_shape.index, Value::Int(index));
    Ok(Some(Control::Next))
}

fn parse_two_arg_int_helper_loop(
    while_stmt: &WhileStmt,
    functions: &HashMap<String, Arc<FunctionDef>>,
) -> Option<TwoArgIntHelperLoop> {
    let (index, end) = parse_simple_index_less_than(&while_stmt.condition)?;
    let [call_node, increment_node] = while_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(call_assign) = call_node else {
        return None;
    };
    if call_assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &call_assign.target else {
        return None;
    };
    let Expr::Call { callee, args } = &call_assign.value else {
        return None;
    };
    let Expr::Identifier(function_name) = callee.as_ref() else {
        return None;
    };
    let [first_arg, second_arg] = args.as_slice() else {
        return None;
    };
    if first_arg.name.is_some() || first_arg.label.is_some() || second_arg.name.is_some() || second_arg.label.is_some()
    {
        return None;
    }

    let function = functions.get(function_name)?;
    let [first_param, second_param] = function.params.as_slice() else {
        return None;
    };
    if first_param.default.is_some() || first_param.variadic || second_param.default.is_some() || second_param.variadic
    {
        return None;
    }

    let body_expr = match function.body.statements.as_slice() {
        [Node::Expression(expr)] => expr,
        [Node::Return(ret)] => ret.value.as_ref()?,
        _ => return None,
    };
    let Expr::Binary { op, left, right } = body_expr else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    let call_args = [
        parse_inline_call_arg(&first_arg.value)?,
        parse_inline_call_arg(&second_arg.value)?,
    ];
    let params = [first_param.name.as_str(), second_param.name.as_str()];

    let Node::Assignment(increment_assign) = increment_node else {
        return None;
    };
    if increment_assign.op != AssignOp::Assign
        || !matches!(&increment_assign.target, Expr::Identifier(name) if name == &index)
    {
        return None;
    }
    if !is_increment_by_one(&increment_assign.value, &index) {
        return None;
    }

    Some(TwoArgIntHelperLoop {
        target: target.clone(),
        index,
        end,
        op: *op,
        left: substitute_inline_operand(left, &params, &call_args)?,
        right: substitute_inline_operand(right, &params, &call_args)?,
    })
}

fn parse_simple_index_less_than(expr: &Expr) -> Option<(String, InlineIntOperand)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    if *op != BinOp::Lt {
        return None;
    }
    let Expr::Identifier(index) = left.as_ref() else {
        return None;
    };
    Some((index.clone(), parse_inline_call_arg(right)?))
}

fn parse_index_branch_condition(expr: &Expr, index: &str) -> Option<DirectIntBranchPredicate> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if matches!(left.as_ref(), Expr::Identifier(name) if name == index) {
        Some(DirectIntBranchPredicate::IndexEquals {
            needle: parse_static_int(right)?,
            match_when_equal,
        })
    } else if matches!(right.as_ref(), Expr::Identifier(name) if name == index) {
        Some(DirectIntBranchPredicate::IndexEquals {
            needle: parse_static_int(left)?,
            match_when_equal,
        })
    } else if let Some((divisor, remainder)) = parse_index_modulo_static_equality(left, right, index) {
        Some(DirectIntBranchPredicate::IndexModuloEquals {
            divisor,
            remainder,
            match_when_equal,
        })
    } else if let Some((divisor, remainder)) = parse_index_modulo_static_equality(right, left, index) {
        Some(DirectIntBranchPredicate::IndexModuloEquals {
            divisor,
            remainder,
            match_when_equal,
        })
    } else if let Some((mask, expected)) = parse_index_bitand_static_equality(left, right, index) {
        Some(DirectIntBranchPredicate::IndexBitAndEquals {
            mask,
            expected,
            match_when_equal,
        })
    } else if let Some((mask, expected)) = parse_index_bitand_static_equality(right, left, index) {
        Some(DirectIntBranchPredicate::IndexBitAndEquals {
            mask,
            expected,
            match_when_equal,
        })
    } else {
        None
    }
}

fn parse_index_modulo_static_equality(mod_expr: &Expr, expected_expr: &Expr, index: &str) -> Option<(i64, i64)> {
    let Expr::Binary { op, left, right } = mod_expr else {
        return None;
    };
    if *op != BinOp::Mod || !matches!(left.as_ref(), Expr::Identifier(name) if name == index) {
        return None;
    }
    let divisor = parse_static_int(right)?;
    if divisor == 0 {
        return None;
    }
    let remainder = parse_static_int(expected_expr)?;
    Some((divisor, remainder))
}

fn parse_index_bitand_static_equality(bitand_expr: &Expr, expected_expr: &Expr, index: &str) -> Option<(i64, i64)> {
    let Expr::Binary { op, left, right } = bitand_expr else {
        return None;
    };
    if *op != BinOp::BitAnd {
        return None;
    }
    let mask = if matches!(left.as_ref(), Expr::Identifier(name) if name == index) {
        parse_static_int(right)?
    } else if matches!(right.as_ref(), Expr::Identifier(name) if name == index) {
        parse_static_int(left)?
    } else {
        return None;
    };
    let expected = parse_static_int(expected_expr)?;
    Some((mask, expected))
}

fn eval_direct_int_branch_predicate(predicate: &DirectIntBranchPredicate, index: i64) -> bool {
    match predicate {
        DirectIntBranchPredicate::IndexEquals {
            needle,
            match_when_equal,
        } => (index == *needle) == *match_when_equal,
        DirectIntBranchPredicate::IndexModuloEquals {
            divisor,
            remainder,
            match_when_equal,
        } => (index % *divisor == *remainder) == *match_when_equal,
        DirectIntBranchPredicate::IndexBitAndEquals {
            mask,
            expected,
            match_when_equal,
        } => (index & *mask == *expected) == *match_when_equal,
    }
}

fn inline_operand_is_env_var(operand: &InlineIntOperand, expected: &str) -> bool {
    matches!(operand, InlineIntOperand::EnvVar(name) if name == expected)
}

fn inline_operand_len_receiver_conflicts(operand: &InlineIntOperand, target: &str, index: &str) -> bool {
    matches!(operand, InlineIntOperand::LenOf(name) if name == target || name == index)
}

fn inline_operand_dict_receiver_conflicts(operand: &InlineIntOperand, target: &str, index: &str) -> bool {
    matches!(operand, InlineIntOperand::DictValue { dict, .. } if dict == target || dict == index)
}

fn parse_inline_call_arg(expr: &Expr) -> Option<InlineIntOperand> {
    match expr {
        Expr::Identifier(name) => Some(InlineIntOperand::EnvVar(name.clone())),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(InlineIntOperand::Const(*value)),
        Expr::Index { receiver, index } => {
            let Expr::Identifier(dict) = receiver.as_ref() else {
                return None;
            };
            let key = parse_static_string_key(index)?;
            Some(InlineIntOperand::DictValue {
                dict: dict.clone(),
                key,
            })
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
            generic_args,
        } if (method == "len" || method == "length") && args.is_empty() && generic_args.is_empty() => {
            let Expr::Identifier(name) = receiver.as_ref() else {
                return None;
            };
            Some(InlineIntOperand::LenOf(name.clone()))
        }
        _ => None,
    }
}

fn parse_direct_int_body_operand(expr: &Expr, index: &str) -> Option<InlineIntOperand> {
    if let Some(operand) = parse_inline_call_arg(expr) {
        return Some(operand);
    }
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    match op {
        BinOp::Add if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexPlus {
                delta: parse_static_int(right)?,
            })
        }
        BinOp::Add if matches!(right.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexPlus {
                delta: parse_static_int(left)?,
            })
        }
        BinOp::Sub if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexMinus {
                delta: parse_static_int(right)?,
            })
        }
        BinOp::Mod if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            let divisor = parse_static_int(right)?;
            if divisor == 0 {
                return None;
            }
            Some(InlineIntOperand::IndexModulo { divisor })
        }
        BinOp::Mul if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexTimes {
                factor: parse_static_int(right)?,
            })
        }
        BinOp::Mul if matches!(right.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexTimes {
                factor: parse_static_int(left)?,
            })
        }
        BinOp::BitAnd if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitAnd {
                mask: parse_static_int(right)?,
            })
        }
        BinOp::BitAnd if matches!(right.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitAnd {
                mask: parse_static_int(left)?,
            })
        }
        BinOp::BitOr if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitOr {
                mask: parse_static_int(right)?,
            })
        }
        BinOp::BitOr if matches!(right.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitOr {
                mask: parse_static_int(left)?,
            })
        }
        BinOp::BitXor if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitXor {
                mask: parse_static_int(right)?,
            })
        }
        BinOp::BitXor if matches!(right.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexBitXor {
                mask: parse_static_int(left)?,
            })
        }
        BinOp::ShiftLeft if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexShiftLeft {
                bits: parse_static_shift(right)?,
            })
        }
        BinOp::ShiftRight if matches!(left.as_ref(), Expr::Identifier(name) if name == index) => {
            Some(InlineIntOperand::IndexShiftRight {
                bits: parse_static_shift(right)?,
            })
        }
        _ => None,
    }
}

fn parse_static_shift(expr: &Expr) -> Option<u32> {
    let bits = parse_static_int(expr)?;
    if (0..64).contains(&bits) {
        Some(bits as u32)
    } else {
        None
    }
}

fn parse_static_string_key(expr: &Expr) -> Option<String> {
    match expr {
        Expr::String(key) | Expr::TypedString(key, _) => Some(key.clone()),
        Expr::FString { parts, .. } => {
            let mut key = String::new();
            for part in parts {
                match part {
                    simple_parser::ast::FStringPart::Literal(value) => key.push_str(value),
                    simple_parser::ast::FStringPart::Expr(_)
                    | simple_parser::ast::FStringPart::ExprWithFormat(_, _) => return None,
                }
            }
            Some(key)
        }
        _ => None,
    }
}

fn substitute_inline_operand(
    expr: &Expr,
    params: &[&str; 2],
    call_args: &[InlineIntOperand; 2],
) -> Option<InlineIntOperand> {
    match expr {
        Expr::Identifier(name) if name == params[0] => Some(call_args[0].clone()),
        Expr::Identifier(name) if name == params[1] => Some(call_args[1].clone()),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(InlineIntOperand::Const(*value)),
        _ => None,
    }
}

fn substitute_one_arg_inline_operand(
    expr: &Expr,
    param: &str,
    call_arg: &InlineIntOperand,
) -> Option<InlineIntOperand> {
    match expr {
        Expr::Identifier(name) if name == param => Some(call_arg.clone()),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(InlineIntOperand::Const(*value)),
        _ => None,
    }
}

fn is_increment_by_one(expr: &Expr, name: &str) -> bool {
    let Expr::Binary { op, left, right } = expr else {
        return false;
    };
    if *op != BinOp::Add {
        return false;
    }
    (matches!(left.as_ref(), Expr::Identifier(n) if n == name) && is_int_const(right, 1))
        || (matches!(right.as_ref(), Expr::Identifier(n) if n == name) && is_int_const(left, 1))
}

fn is_int_const(expr: &Expr, expected: i64) -> bool {
    match expr {
        Expr::Integer(value) | Expr::TypedInteger(value, _) => *value == expected,
        _ => false,
    }
}

fn lower_stable_inline_operand(
    operand: InlineIntOperand,
    env: &Env,
    target: &str,
    index: &str,
) -> Result<InlineIntOperand, CompileError> {
    match operand {
        InlineIntOperand::EnvVar(name) if name == target => Ok(InlineIntOperand::Target),
        InlineIntOperand::EnvVar(name) if name == index => Ok(InlineIntOperand::Index),
        InlineIntOperand::IndexPlus { delta } => Ok(InlineIntOperand::IndexPlus { delta }),
        InlineIntOperand::IndexMinus { delta } => Ok(InlineIntOperand::IndexMinus { delta }),
        InlineIntOperand::EnvVar(name) => match env.get(&name) {
            Some(Value::Int(value)) => Ok(InlineIntOperand::Const(*value)),
            _ => Err(CompileError::runtime(format!(
                "integer helper loop captured non-integer `{name}`"
            ))),
        },
        InlineIntOperand::LenOf(name) => match env.get(&name) {
            Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => {
                Ok(InlineIntOperand::Const(values.len() as i64))
            }
            Some(Value::FixedSizeArray { size, .. }) => Ok(InlineIntOperand::Const(*size as i64)),
            Some(Value::Str(value)) => Ok(InlineIntOperand::Const(value.chars().count() as i64)),
            Some(Value::Tuple(values)) => Ok(InlineIntOperand::Const(values.len() as i64)),
            _ => Err(CompileError::runtime(format!(
                "integer loop len receiver `{name}` does not have a stable length"
            ))),
        },
        InlineIntOperand::IndexModulo { divisor } => Ok(InlineIntOperand::IndexModulo { divisor }),
        InlineIntOperand::IndexTimes { factor } => Ok(InlineIntOperand::IndexTimes { factor }),
        InlineIntOperand::IndexBitAnd { mask } => Ok(InlineIntOperand::IndexBitAnd { mask }),
        InlineIntOperand::IndexBitOr { mask } => Ok(InlineIntOperand::IndexBitOr { mask }),
        InlineIntOperand::IndexBitXor { mask } => Ok(InlineIntOperand::IndexBitXor { mask }),
        InlineIntOperand::IndexShiftLeft { bits } => Ok(InlineIntOperand::IndexShiftLeft { bits }),
        InlineIntOperand::IndexShiftRight { bits } => Ok(InlineIntOperand::IndexShiftRight { bits }),
        InlineIntOperand::DictValue { dict, key } => match env.get(&dict) {
            Some(Value::Dict(values)) | Some(Value::FrozenDict(values)) => match values.get(&key) {
                Some(Value::Int(value)) => Ok(InlineIntOperand::Const(*value)),
                _ => Err(CompileError::runtime(format!(
                    "integer loop dict lookup `{dict}[{key}]` is not an integer"
                ))),
            },
            _ => Err(CompileError::runtime(format!(
                "integer loop dict receiver `{dict}` is not a dict"
            ))),
        },
        other => Ok(other),
    }
}

fn eval_stable_inline_operand(
    operand: &InlineIntOperand,
    env: &Env,
    target: i64,
    index: i64,
) -> Result<i64, CompileError> {
    match operand {
        InlineIntOperand::Target => Ok(target),
        InlineIntOperand::Index => Ok(index),
        InlineIntOperand::IndexPlus { delta } => Ok(index.wrapping_add(*delta)),
        InlineIntOperand::IndexMinus { delta } => Ok(index.wrapping_sub(*delta)),
        InlineIntOperand::IndexModulo { divisor } => Ok(index % *divisor),
        InlineIntOperand::IndexTimes { factor } => Ok(index.wrapping_mul(*factor)),
        InlineIntOperand::IndexBitAnd { mask } => Ok(index & *mask),
        InlineIntOperand::IndexBitOr { mask } => Ok(index | *mask),
        InlineIntOperand::IndexBitXor { mask } => Ok(index ^ *mask),
        InlineIntOperand::IndexShiftLeft { bits } => Ok(index << *bits),
        InlineIntOperand::IndexShiftRight { bits } => Ok(index >> *bits),
        InlineIntOperand::Const(value) => Ok(*value),
        InlineIntOperand::EnvVar(name) => match env.get(name) {
            Some(Value::Int(value)) => Ok(*value),
            _ => Err(CompileError::runtime(format!(
                "integer helper loop bound `{name}` is not an integer"
            ))),
        },
        InlineIntOperand::LenOf(name) => match env.get(name) {
            Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => Ok(values.len() as i64),
            Some(Value::FixedSizeArray { size, .. }) => Ok(*size as i64),
            Some(Value::Str(value)) => Ok(value.chars().count() as i64),
            Some(Value::Tuple(values)) => Ok(values.len() as i64),
            _ => Err(CompileError::runtime(format!(
                "integer loop len receiver `{name}` does not have a stable length"
            ))),
        },
        InlineIntOperand::DictValue { dict, key } => match env.get(dict) {
            Some(Value::Dict(values)) | Some(Value::FrozenDict(values)) => match values.get(key) {
                Some(Value::Int(value)) => Ok(*value),
                _ => Err(CompileError::runtime(format!(
                    "integer loop dict lookup `{dict}[{key}]` is not an integer"
                ))),
            },
            _ => Err(CompileError::runtime(format!(
                "integer loop dict receiver `{dict}` is not a dict"
            ))),
        },
    }
}

fn eval_inline_operand(operand: &InlineIntOperand, target: i64, index: i64) -> i64 {
    match operand {
        InlineIntOperand::Target => target,
        InlineIntOperand::Index => index,
        InlineIntOperand::IndexPlus { delta } => index.wrapping_add(*delta),
        InlineIntOperand::IndexMinus { delta } => index.wrapping_sub(*delta),
        InlineIntOperand::IndexModulo { divisor } => index % *divisor,
        InlineIntOperand::IndexTimes { factor } => index.wrapping_mul(*factor),
        InlineIntOperand::IndexBitAnd { mask } => index & *mask,
        InlineIntOperand::IndexBitOr { mask } => index | *mask,
        InlineIntOperand::IndexBitXor { mask } => index ^ *mask,
        InlineIntOperand::IndexShiftLeft { bits } => index << *bits,
        InlineIntOperand::IndexShiftRight { bits } => index >> *bits,
        InlineIntOperand::Const(value) => *value,
        InlineIntOperand::EnvVar(_) | InlineIntOperand::LenOf(_) | InlineIntOperand::DictValue { .. } => {
            unreachable!("stable integer operand was not lowered")
        }
    }
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
                || else_branch.as_ref().is_some_and(|e| expr_may_mutate_var(e, var))
        }

        Expr::Cast { expr, .. } => expr_may_mutate_var(expr, var),
        Expr::Range { start, end, .. } => {
            start.as_ref().is_some_and(|e| expr_may_mutate_var(e, var))
                || end.as_ref().is_some_and(|e| expr_may_mutate_var(e, var))
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
        Value::Str(_) | Value::Symbol(_) => {
            let name = match &context_obj {
                Value::Str(name) => name.as_str(),
                Value::Symbol(name) => name.as_str(),
                _ => unreachable!(),
            };
            // BDD-style context: context "description": block
            let name_str = if matches!(context_obj, Value::Symbol(_)) {
                format!("with {}", name)
            } else {
                name.to_string()
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
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
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
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
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
    if let Some(ctrl) = try_exec_enumerated_int_array_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_string_match_count_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_string_count_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_float_array_match_count_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_float_array_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_int_array_match_count_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_int_array_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

    if let Some(ctrl) = try_exec_int_range_for_loop(for_stmt, env)? {
        return Ok(ctrl);
    }

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

#[derive(Clone)]
enum RangeForOperand {
    LoopVar,
    Var(String),
    Const(i64),
}

struct RangeForAssign {
    target: String,
    left: RangeForOperand,
    op: BinOp,
    right: RangeForOperand,
}

struct IntRangeForLoop {
    loop_var: String,
    start: RangeForOperand,
    end: RangeForOperand,
    inclusive: bool,
    assignments: Vec<RangeForAssign>,
}

struct IntArrayForLoop {
    loop_var: String,
    array: String,
    assignment: RangeForAssign,
}

struct IntArrayMatchCountForLoop {
    loop_var: String,
    array: String,
    needle: i64,
    match_when_equal: bool,
    assignment: RangeForAssign,
}

enum EnumeratedIntArrayOperand {
    Target,
    Index,
    Item,
    Const(i64),
}

struct EnumeratedIntArrayAssign {
    target: String,
    left: EnumeratedIntArrayOperand,
    op: BinOp,
    right: EnumeratedIntArrayOperand,
}

struct EnumeratedIntArrayForLoop {
    index_var: String,
    item_var: String,
    array: String,
    assignment: EnumeratedIntArrayAssign,
}

enum FloatForOperand {
    Target,
    LoopVar,
    Const(f64),
}

struct FloatForAssign {
    target: String,
    left: FloatForOperand,
    op: BinOp,
    right: FloatForOperand,
}

struct FloatArrayForLoop {
    loop_var: String,
    array: String,
    assignment: FloatForAssign,
}

struct FloatArrayMatchCountForLoop {
    loop_var: String,
    array: String,
    needle: f64,
    match_when_equal: bool,
    assignment: RangeForAssign,
}

struct StringCountForLoop {
    loop_var: String,
    text: String,
    assignment: RangeForAssign,
}

struct StringMatchCountForLoop {
    loop_var: String,
    text: String,
    needle: char,
    match_when_equal: bool,
    assignment: RangeForAssign,
}

fn try_exec_enumerated_int_array_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || !for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_enumerated_int_array_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.index_var
        || loop_shape.assignment.target == loop_shape.item_var
        || loop_shape.assignment.target == loop_shape.array
        || loop_shape.index_var == loop_shape.item_var
        || loop_shape.index_var == loop_shape.array
        || loop_shape.item_var == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.index_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.item_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };

    let uses_item = enumerated_int_array_operand_uses_item(&loop_shape.assignment.left)
        || enumerated_int_array_operand_uses_item(&loop_shape.assignment.right);
    let mut last_index: Option<i64> = None;
    let mut last_item: Option<Value> = None;
    let mut iterations = 0u64;
    for (idx, item) in values.iter().enumerate() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let loop_value = if uses_item {
            let Value::Int(loop_value) = item else {
                return Ok(None);
            };
            *loop_value
        } else {
            0
        };
        let index = idx as i64;
        let left_value = eval_enumerated_int_array_operand(&loop_shape.assignment.left, target, index, loop_value);
        let right_value = eval_enumerated_int_array_operand(&loop_shape.assignment.right, target, index, loop_value);
        target = match loop_shape.assignment.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        last_index = Some(index);
        last_item = Some(item.clone());
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(value) = last_index {
        env.insert(loop_shape.index_var, Value::Int(value));
    }
    if let Some(value) = last_item {
        env.insert(loop_shape.item_var, value);
    }
    Ok(Some(Control::Next))
}

fn parse_enumerated_int_array_for_loop(for_stmt: &ForStmt) -> Option<EnumeratedIntArrayForLoop> {
    let Pattern::Tuple(patterns) = &for_stmt.pattern else {
        return None;
    };
    let [Pattern::Identifier(index_var), Pattern::Identifier(item_var)] = patterns.as_slice() else {
        return None;
    };
    let Expr::Identifier(array) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(EnumeratedIntArrayForLoop {
        index_var: index_var.clone(),
        item_var: item_var.clone(),
        array: array.clone(),
        assignment: EnumeratedIntArrayAssign {
            target: target.clone(),
            left: parse_enumerated_int_array_operand(left, target, index_var, item_var)?,
            op: *op,
            right: parse_enumerated_int_array_operand(right, target, index_var, item_var)?,
        },
    })
}

fn parse_enumerated_int_array_operand(
    expr: &Expr,
    target: &str,
    index_var: &str,
    item_var: &str,
) -> Option<EnumeratedIntArrayOperand> {
    match expr {
        Expr::Identifier(name) if name == target => Some(EnumeratedIntArrayOperand::Target),
        Expr::Identifier(name) if name == index_var => Some(EnumeratedIntArrayOperand::Index),
        Expr::Identifier(name) if name == item_var => Some(EnumeratedIntArrayOperand::Item),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(EnumeratedIntArrayOperand::Const(*value)),
        _ => None,
    }
}

fn eval_enumerated_int_array_operand(operand: &EnumeratedIntArrayOperand, target: i64, index: i64, item: i64) -> i64 {
    match operand {
        EnumeratedIntArrayOperand::Target => target,
        EnumeratedIntArrayOperand::Index => index,
        EnumeratedIntArrayOperand::Item => item,
        EnumeratedIntArrayOperand::Const(value) => *value,
    }
}

fn enumerated_int_array_operand_uses_item(operand: &EnumeratedIntArrayOperand) -> bool {
    matches!(operand, EnumeratedIntArrayOperand::Item)
}

fn try_exec_string_match_count_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_string_match_count_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.text
        || loop_shape.loop_var == loop_shape.text
        || range_operand_uses_loop_var(&loop_shape.assignment.left)
        || range_operand_uses_loop_var(&loop_shape.assignment.right)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let text = match env.get(&loop_shape.text) {
        Some(Value::Str(text)) => text.clone(),
        _ => return Ok(None),
    };
    let left = match lower_single_range_for_operand(
        &loop_shape.assignment.left,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_single_range_for_operand(
        &loop_shape.assignment.right,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut last_value: Option<char> = None;
    let mut iterations = 0u64;
    for ch in text.chars() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        if (ch == loop_shape.needle) == loop_shape.match_when_equal {
            let left_value = eval_single_range_for_operand(&left, target, 0);
            let right_value = eval_single_range_for_operand(&right, target, 0);
            target = match loop_shape.assignment.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        last_value = Some(ch);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(ch) = last_value {
        env.insert(loop_shape.loop_var, Value::text(ch.to_string()));
    }
    Ok(Some(Control::Next))
}

fn parse_string_match_count_for_loop(for_stmt: &ForStmt) -> Option<StringMatchCountForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(text) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::If(if_stmt) = node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_char_equality_condition(&if_stmt.condition, &loop_var)?;
    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(StringMatchCountForLoop {
        loop_var: loop_var.clone(),
        text: text.clone(),
        needle,
        match_when_equal,
        assignment: RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        },
    })
}

fn parse_char_equality_condition(expr: &Expr, loop_var: &str) -> Option<(char, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if matches!(left.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_single_static_char(right)?, match_when_equal))
    } else if matches!(right.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_single_static_char(left)?, match_when_equal))
    } else {
        None
    }
}

fn parse_single_static_char(expr: &Expr) -> Option<char> {
    let value = parse_static_string_key(expr)?;
    let mut chars = value.chars();
    let ch = chars.next()?;
    if chars.next().is_none() {
        Some(ch)
    } else {
        None
    }
}

fn try_exec_string_count_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_string_count_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.text
        || loop_shape.loop_var == loop_shape.text
        || range_operand_uses_loop_var(&loop_shape.assignment.left)
        || range_operand_uses_loop_var(&loop_shape.assignment.right)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let text = match env.get(&loop_shape.text) {
        Some(Value::Str(text)) => text.clone(),
        _ => return Ok(None),
    };
    let left = match lower_single_range_for_operand(
        &loop_shape.assignment.left,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_single_range_for_operand(
        &loop_shape.assignment.right,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut last_value: Option<char> = None;
    let mut iterations = 0u64;
    for ch in text.chars() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let left_value = eval_single_range_for_operand(&left, target, 0);
        let right_value = eval_single_range_for_operand(&right, target, 0);
        target = match loop_shape.assignment.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        last_value = Some(ch);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(ch) = last_value {
        env.insert(loop_shape.loop_var, Value::text(ch.to_string()));
    }
    Ok(Some(Control::Next))
}

fn parse_string_count_for_loop(for_stmt: &ForStmt) -> Option<StringCountForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(text) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(StringCountForLoop {
        loop_var: loop_var.clone(),
        text: text.clone(),
        assignment: RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        },
    })
}

fn try_exec_float_array_match_count_for_loop(
    for_stmt: &ForStmt,
    env: &mut Env,
) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_float_array_match_count_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.array
        || loop_shape.loop_var == loop_shape.array
        || range_operand_uses_loop_var(&loop_shape.assignment.left)
        || range_operand_uses_loop_var(&loop_shape.assignment.right)
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_single_range_for_operand(
        &loop_shape.assignment.left,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_single_range_for_operand(
        &loop_shape.assignment.right,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut last_value: Option<f64> = None;
    let mut iterations = 0u64;
    for item in values.iter() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let Value::Float(loop_value) = item else {
            return Ok(None);
        };
        if (*loop_value == loop_shape.needle) == loop_shape.match_when_equal {
            let left_value = eval_single_range_for_operand(&left, target, 0);
            let right_value = eval_single_range_for_operand(&right, target, 0);
            target = match loop_shape.assignment.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        last_value = Some(*loop_value);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(value) = last_value {
        env.insert(loop_shape.loop_var, Value::Float(value));
    }
    Ok(Some(Control::Next))
}

fn parse_float_array_match_count_for_loop(for_stmt: &ForStmt) -> Option<FloatArrayMatchCountForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(array) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::If(if_stmt) = node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_float_equality_condition(&if_stmt.condition, &loop_var)?;
    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(FloatArrayMatchCountForLoop {
        loop_var: loop_var.clone(),
        array: array.clone(),
        needle,
        match_when_equal,
        assignment: RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        },
    })
}

fn parse_float_equality_condition(expr: &Expr, loop_var: &str) -> Option<(f64, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if matches!(left.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_static_float(right)?, match_when_equal))
    } else if matches!(right.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_static_float(left)?, match_when_equal))
    } else {
        None
    }
}

fn parse_static_float(expr: &Expr) -> Option<f64> {
    match expr {
        Expr::Float(value) | Expr::TypedFloat(value, _) => Some(*value),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(*value as f64),
        _ => None,
    }
}

fn try_exec_float_array_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_float_array_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.array
        || loop_shape.loop_var == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Float(value)) => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };

    let mut last_value: Option<f64> = None;
    let mut iterations = 0u64;
    for item in values.iter() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let Value::Float(loop_value) = item else {
            return Ok(None);
        };
        let left_value = eval_float_for_operand(&loop_shape.assignment.left, target, *loop_value);
        let right_value = eval_float_for_operand(&loop_shape.assignment.right, target, *loop_value);
        target = match loop_shape.assignment.op {
            BinOp::Add => left_value + right_value,
            BinOp::Sub => left_value - right_value,
            BinOp::Mul => left_value * right_value,
            _ => return Ok(None),
        };
        last_value = Some(*loop_value);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Float(target));
    if let Some(value) = last_value {
        env.insert(loop_shape.loop_var, Value::Float(value));
    }
    Ok(Some(Control::Next))
}

fn parse_float_array_for_loop(for_stmt: &ForStmt) -> Option<FloatArrayForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(array) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(FloatArrayForLoop {
        loop_var: loop_var.clone(),
        array: array.clone(),
        assignment: FloatForAssign {
            target: target.clone(),
            left: parse_float_for_operand(left, target, &loop_var)?,
            op: *op,
            right: parse_float_for_operand(right, target, &loop_var)?,
        },
    })
}

fn parse_float_for_operand(expr: &Expr, target: &str, loop_var: &str) -> Option<FloatForOperand> {
    match expr {
        Expr::Identifier(name) if name == target => Some(FloatForOperand::Target),
        Expr::Identifier(name) if name == loop_var => Some(FloatForOperand::LoopVar),
        Expr::Float(value) | Expr::TypedFloat(value, _) => Some(FloatForOperand::Const(*value)),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(FloatForOperand::Const(*value as f64)),
        _ => None,
    }
}

fn eval_float_for_operand(operand: &FloatForOperand, target: f64, loop_value: f64) -> f64 {
    match operand {
        FloatForOperand::Target => target,
        FloatForOperand::LoopVar => loop_value,
        FloatForOperand::Const(value) => *value,
    }
}

fn try_exec_int_array_match_count_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_int_array_match_count_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.array
        || loop_shape.loop_var == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_single_range_for_operand(
        &loop_shape.assignment.left,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_single_range_for_operand(
        &loop_shape.assignment.right,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut last_value: Option<i64> = None;
    let mut iterations = 0u64;
    for item in values.iter() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let Value::Int(loop_value) = item else {
            return Ok(None);
        };
        if (*loop_value == loop_shape.needle) == loop_shape.match_when_equal {
            let left_value = eval_single_range_for_operand(&left, target, *loop_value);
            let right_value = eval_single_range_for_operand(&right, target, *loop_value);
            target = match loop_shape.assignment.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
        }
        last_value = Some(*loop_value);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(value) = last_value {
        env.insert(loop_shape.loop_var, Value::Int(value));
    }
    Ok(Some(Control::Next))
}

fn parse_int_array_match_count_for_loop(for_stmt: &ForStmt) -> Option<IntArrayMatchCountForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(array) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::If(if_stmt) = node else {
        return None;
    };
    if if_stmt.is_suspend
        || if_stmt.let_pattern.is_some()
        || !if_stmt.elif_branches.is_empty()
        || if_stmt.else_block.is_some()
    {
        return None;
    }
    let (needle, match_when_equal) = parse_int_equality_condition(&if_stmt.condition, &loop_var)?;
    let [then_node] = if_stmt.then_block.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = then_node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(IntArrayMatchCountForLoop {
        loop_var: loop_var.clone(),
        array: array.clone(),
        needle,
        match_when_equal,
        assignment: RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        },
    })
}

fn parse_int_equality_condition(expr: &Expr, loop_var: &str) -> Option<(i64, bool)> {
    let Expr::Binary { op, left, right } = expr else {
        return None;
    };
    let match_when_equal = match op {
        BinOp::Eq => true,
        BinOp::NotEq => false,
        _ => return None,
    };
    if matches!(left.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_static_int(right)?, match_when_equal))
    } else if matches!(right.as_ref(), Expr::Identifier(name) if name == loop_var) {
        Some((parse_static_int(left)?, match_when_equal))
    } else {
        None
    }
}

fn parse_static_int(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(*value),
        Expr::Unary {
            op: UnaryOp::Neg,
            operand,
        } => parse_static_int(operand)?.checked_neg(),
        _ => None,
    }
}

fn try_exec_int_array_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_int_array_for_loop(for_stmt) else {
        return Ok(None);
    };
    if loop_shape.assignment.target == loop_shape.loop_var
        || loop_shape.assignment.target == loop_shape.array
        || loop_shape.loop_var == loop_shape.array
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var))
        || CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
        || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&loop_shape.assignment.target))
    {
        return Ok(None);
    }

    let mut target = match env.get(&loop_shape.assignment.target) {
        Some(Value::Int(value)) => *value,
        _ => return Ok(None),
    };
    let values = match env.get(&loop_shape.array) {
        Some(Value::Array(values)) | Some(Value::FrozenArray(values)) => values.clone(),
        _ => return Ok(None),
    };
    let left = match lower_single_range_for_operand(
        &loop_shape.assignment.left,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let right = match lower_single_range_for_operand(
        &loop_shape.assignment.right,
        env,
        &loop_shape.assignment.target,
        &loop_shape.loop_var,
    ) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };

    let mut last_value: Option<i64> = None;
    let mut iterations = 0u64;
    for item in values.iter() {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        let Value::Int(loop_value) = item else {
            return Ok(None);
        };
        let left_value = eval_single_range_for_operand(&left, target, *loop_value);
        let right_value = eval_single_range_for_operand(&right, target, *loop_value);
        target = match loop_shape.assignment.op {
            BinOp::Add => left_value.wrapping_add(right_value),
            BinOp::Sub => left_value.wrapping_sub(right_value),
            BinOp::Mul => left_value.wrapping_mul(right_value),
            _ => return Ok(None),
        };
        last_value = Some(*loop_value);
        iterations = iterations.wrapping_add(1);
    }

    env.insert(loop_shape.assignment.target, Value::Int(target));
    if let Some(value) = last_value {
        env.insert(loop_shape.loop_var, Value::Int(value));
    }
    Ok(Some(Control::Next))
}

fn parse_int_array_for_loop(for_stmt: &ForStmt) -> Option<IntArrayForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Identifier(array) = &for_stmt.iterable else {
        return None;
    };
    let [node] = for_stmt.body.statements.as_slice() else {
        return None;
    };
    let Node::Assignment(assign) = node else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let Expr::Identifier(target) = &assign.target else {
        return None;
    };
    let Expr::Binary { op, left, right } = &assign.value else {
        return None;
    };
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }

    Some(IntArrayForLoop {
        loop_var: loop_var.clone(),
        array: array.clone(),
        assignment: RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        },
    })
}

fn range_operand_uses_loop_var(operand: &RangeForOperand) -> bool {
    matches!(operand, RangeForOperand::LoopVar)
}

fn try_exec_int_range_for_loop(for_stmt: &ForStmt, env: &mut Env) -> Result<Option<Control>, CompileError> {
    if for_stmt.is_suspend
        || for_stmt.auto_enumerate
        || for_stmt.label.is_some()
        || !for_stmt.invariants.is_empty()
        || is_coverage_enabled()
        || crate::interpreter::is_execution_limit_enabled()
    {
        return Ok(None);
    }

    let Some(loop_shape) = parse_int_range_for_loop(for_stmt) else {
        return Ok(None);
    };
    if CONST_NAMES.with(|cell| cell.borrow().contains(&loop_shape.loop_var)) {
        return Ok(None);
    }

    let start = eval_range_for_stable_operand(&loop_shape.start, env)?;
    let mut end = eval_range_for_stable_operand(&loop_shape.end, env)?;
    if loop_shape.inclusive {
        let Some(inclusive_end) = end.checked_add(1) else {
            return Ok(None);
        };
        end = inclusive_end;
    }

    if loop_shape.assignments.len() == 1 {
        let assignment = &loop_shape.assignments[0];
        if assignment.target == loop_shape.loop_var
            || CONST_NAMES.with(|cell| cell.borrow().contains(&assignment.target))
            || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&assignment.target))
        {
            return Ok(None);
        }
        let mut target = match env.get(&assignment.target) {
            Some(Value::Int(value)) => *value,
            _ => return Ok(None),
        };
        let left = lower_single_range_for_operand(&assignment.left, env, &assignment.target, &loop_shape.loop_var)?;
        let right = lower_single_range_for_operand(&assignment.right, env, &assignment.target, &loop_shape.loop_var)?;
        let mut current = start;
        let mut last_value: Option<i64> = None;
        let mut iterations = 0u64;
        while current < end {
            if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
                return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
            }
            let left_value = eval_single_range_for_operand(&left, target, current);
            let right_value = eval_single_range_for_operand(&right, target, current);
            target = match assignment.op {
                BinOp::Add => left_value.wrapping_add(right_value),
                BinOp::Sub => left_value.wrapping_sub(right_value),
                BinOp::Mul => left_value.wrapping_mul(right_value),
                _ => return Ok(None),
            };
            last_value = Some(current);
            current = current.wrapping_add(1);
            iterations = iterations.wrapping_add(1);
        }
        env.insert(assignment.target.clone(), Value::Int(target));
        if let Some(value) = last_value {
            env.insert(loop_shape.loop_var, Value::Int(value));
        }
        return Ok(Some(Control::Next));
    }

    let mut locals: HashMap<String, i64> = HashMap::new();
    for assignment in &loop_shape.assignments {
        if assignment.target == loop_shape.loop_var
            || CONST_NAMES.with(|cell| cell.borrow().contains(&assignment.target))
            || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(&assignment.target))
        {
            return Ok(None);
        }
        if !locals.contains_key(&assignment.target) {
            match env.get(&assignment.target) {
                Some(Value::Int(value)) => {
                    locals.insert(assignment.target.clone(), *value);
                }
                _ => return Ok(None),
            }
        }
        collect_range_for_operand_var(&assignment.left, env, &mut locals, &loop_shape.loop_var)?;
        collect_range_for_operand_var(&assignment.right, env, &mut locals, &loop_shape.loop_var)?;
    }

    let mut current = start;
    let mut last_value: Option<i64> = None;
    let mut iterations = 0u64;
    while current < end {
        if iterations & 0x3ff == 0 && crate::interpreter::is_timeout_exceeded() {
            return Err(CompileError::TimeoutExceeded { timeout_secs: 0 });
        }
        for assignment in &loop_shape.assignments {
            let left = eval_range_for_operand(&assignment.left, &locals, current)?;
            let right = eval_range_for_operand(&assignment.right, &locals, current)?;
            let value = match assignment.op {
                BinOp::Add => left.wrapping_add(right),
                BinOp::Sub => left.wrapping_sub(right),
                BinOp::Mul => left.wrapping_mul(right),
                _ => return Ok(None),
            };
            locals.insert(assignment.target.clone(), value);
        }
        last_value = Some(current);
        current = current.wrapping_add(1);
        iterations = iterations.wrapping_add(1);
    }

    for assignment in &loop_shape.assignments {
        if let Some(value) = locals.get(&assignment.target) {
            env.insert(assignment.target.clone(), Value::Int(*value));
        }
    }
    if let Some(value) = last_value {
        env.insert(loop_shape.loop_var, Value::Int(value));
    }
    Ok(Some(Control::Next))
}

#[derive(Clone)]
enum SingleRangeForOperand {
    Target,
    LoopVar,
    Const(i64),
}

fn lower_single_range_for_operand(
    operand: &RangeForOperand,
    env: &Env,
    target: &str,
    loop_var: &str,
) -> Result<SingleRangeForOperand, CompileError> {
    match operand {
        RangeForOperand::LoopVar => Ok(SingleRangeForOperand::LoopVar),
        RangeForOperand::Const(value) => Ok(SingleRangeForOperand::Const(*value)),
        RangeForOperand::Var(name) if name == target => Ok(SingleRangeForOperand::Target),
        RangeForOperand::Var(name) if name == loop_var => Ok(SingleRangeForOperand::LoopVar),
        RangeForOperand::Var(name) => match env.get(name) {
            Some(Value::Int(value)) => Ok(SingleRangeForOperand::Const(*value)),
            _ => Err(CompileError::runtime(format!(
                "integer range for operand `{name}` is not an integer"
            ))),
        },
    }
}

fn eval_single_range_for_operand(operand: &SingleRangeForOperand, target: i64, loop_value: i64) -> i64 {
    match operand {
        SingleRangeForOperand::Target => target,
        SingleRangeForOperand::LoopVar => loop_value,
        SingleRangeForOperand::Const(value) => *value,
    }
}

fn parse_int_range_for_loop(for_stmt: &ForStmt) -> Option<IntRangeForLoop> {
    let loop_var = parse_for_loop_identifier(&for_stmt.pattern)?;
    let Expr::Range { start, end, bound } = &for_stmt.iterable else {
        return None;
    };
    let end = parse_range_for_operand(end.as_ref()?)?;
    let start = match start {
        Some(expr) => parse_range_for_operand(expr)?,
        None => RangeForOperand::Const(0),
    };

    let mut assignments = Vec::with_capacity(for_stmt.body.statements.len());
    for node in &for_stmt.body.statements {
        let Node::Assignment(assign) = node else {
            return None;
        };
        if assign.op != AssignOp::Assign {
            return None;
        }
        let Expr::Identifier(target) = &assign.target else {
            return None;
        };
        let Expr::Binary { op, left, right } = &assign.value else {
            return None;
        };
        if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
            return None;
        }
        assignments.push(RangeForAssign {
            target: target.clone(),
            left: parse_range_for_body_operand(left, &loop_var)?,
            op: *op,
            right: parse_range_for_body_operand(right, &loop_var)?,
        });
    }
    if assignments.is_empty() {
        return None;
    }

    Some(IntRangeForLoop {
        loop_var,
        start,
        end,
        inclusive: *bound == RangeBound::Inclusive,
        assignments,
    })
}

fn parse_for_loop_identifier(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) => Some(name.clone()),
        Pattern::Typed { pattern, .. } => parse_for_loop_identifier(pattern),
        _ => None,
    }
}

fn parse_range_for_operand(expr: &Expr) -> Option<RangeForOperand> {
    match expr {
        Expr::Identifier(name) => Some(RangeForOperand::Var(name.clone())),
        Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(RangeForOperand::Const(*value)),
        _ => None,
    }
}

fn parse_range_for_body_operand(expr: &Expr, loop_var: &str) -> Option<RangeForOperand> {
    match expr {
        Expr::Identifier(name) if name == loop_var => Some(RangeForOperand::LoopVar),
        _ => parse_range_for_operand(expr),
    }
}

fn eval_range_for_stable_operand(operand: &RangeForOperand, env: &Env) -> Result<i64, CompileError> {
    match operand {
        RangeForOperand::Const(value) => Ok(*value),
        RangeForOperand::Var(name) => match env.get(name) {
            Some(Value::Int(value)) => Ok(*value),
            _ => Err(CompileError::runtime(format!(
                "integer range for bound `{name}` is not an integer"
            ))),
        },
        RangeForOperand::LoopVar => Err(CompileError::runtime(
            "integer range for bound cannot use loop variable".to_string(),
        )),
    }
}

fn collect_range_for_operand_var(
    operand: &RangeForOperand,
    env: &Env,
    locals: &mut HashMap<String, i64>,
    loop_var: &str,
) -> Result<(), CompileError> {
    let RangeForOperand::Var(name) = operand else {
        return Ok(());
    };
    if name == loop_var || locals.contains_key(name) {
        return Ok(());
    }
    match env.get(name) {
        Some(Value::Int(value)) => {
            locals.insert(name.clone(), *value);
            Ok(())
        }
        _ => Err(CompileError::runtime(format!(
            "integer range for operand `{name}` is not an integer"
        ))),
    }
}

fn eval_range_for_operand(
    operand: &RangeForOperand,
    locals: &HashMap<String, i64>,
    loop_value: i64,
) -> Result<i64, CompileError> {
    match operand {
        RangeForOperand::LoopVar => Ok(loop_value),
        RangeForOperand::Const(value) => Ok(*value),
        RangeForOperand::Var(name) => locals
            .get(name)
            .copied()
            .ok_or_else(|| CompileError::runtime(format!("integer range for missing local `{name}`"))),
    }
}

/// Core match execution logic shared between exec_match and exec_match_expr.
/// Returns (Control, Option<Value>) where the value is from the matched arm.
/// Unlike exec_match_expr, this does NOT collapse Control::Return — callers
/// that need to propagate early returns must use this function directly.
pub(crate) fn exec_match_core(
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
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums, classes)? {
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
            record_decision_coverage_sffi(
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

/// Execute an if statement, returning (Control, Value).
/// Unlike exec_if_expr, this preserves Control::Return/Break/Continue so that
/// early returns nested inside match arms (or other block contexts) propagate
/// correctly up to the enclosing function.
pub(crate) fn exec_if_core(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Value), CompileError> {
    // Handle if-let: if let PATTERN = EXPR:
    if let Some(pattern) = &if_stmt.let_pattern {
        let value = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
        // `if val IDENT = expr:` is an optional-binding — try `optional_let_binding`
        // first (bug #188a). `pattern_matches` alone always matches a bare
        // identifier pattern, even against nil/None, so relying on it directly
        // wrongly takes this branch when the value is absent. This is the
        // `exec_if_core` sibling of the fix already landed in `exec_if` — `if val`
        // reaches THIS function instead whenever the `if` is the last statement
        // of a function/block body (implicit-return / value position).
        match optional_let_binding(pattern, &value) {
            LetBind::Bind(name, inner) => {
                env.insert(name, inner);
                let (flow, last_val) = exec_block_fn(&if_stmt.then_block, env, functions, classes, enums, impl_methods)?;
                return match flow {
                    Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                    other => Ok((other, Value::Nil)),
                };
            }
            LetBind::Skip => {}
            LetBind::NotApplicable => {
                let mut bindings = HashMap::new();
                if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                    for (name, val) in bindings {
                        env.insert(name, val);
                    }
                    let (flow, last_val) =
                        exec_block_fn(&if_stmt.then_block, env, functions, classes, enums, impl_methods)?;
                    return match flow {
                        Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                        other => Ok((other, Value::Nil)),
                    };
                }
                // Pattern didn't match - fall through to elif branches / else below.
                // (Previously this returned the else block directly, silently skipping
                // every `elif`/`elif val ...` branch in if-expression position.)
            }
        }
    } else {
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
                Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                other => Ok((other, Value::Nil)),
            };
        }
    }

    for (pattern, cond, block) in if_stmt.elif_branches.iter() {
        if let Some(pattern) = pattern {
            let value = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
            match optional_let_binding(pattern, &value) {
                LetBind::Bind(name, inner) => {
                    env.insert(name, inner);
                    let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
                    return match flow {
                        Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                        other => Ok((other, Value::Nil)),
                    };
                }
                LetBind::Skip => {}
                LetBind::NotApplicable => {
                    let mut bindings = HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums, classes)? {
                        for (name, val) in bindings {
                            env.insert(name, val);
                        }
                        let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
                        return match flow {
                            Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                            other => Ok((other, Value::Nil)),
                        };
                    }
                }
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
                    Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
                    other => Ok((other, Value::Nil)),
                };
            }
        }
    }

    if let Some(block) = &if_stmt.else_block {
        let (flow, last_val) = exec_block_fn(block, env, functions, classes, enums, impl_methods)?;
        return match flow {
            Control::Next => Ok((Control::Next, last_val.unwrap_or(Value::Nil))),
            other => Ok((other, Value::Nil)),
        };
    }

    Ok((Control::Next, Value::Nil))
}

#[cfg(test)]
mod exec_if_core_tests {
    use super::*;
    use simple_parser::Parser;

    /// Parse `src` (must define `fn probe(): ...`) and return the LAST statement
    /// of its body as an `IfStmt` — the shape `exec_block_fn` dispatches to
    /// `exec_if_core` for (an `if` used in value/implicit-return position).
    fn parse_trailing_if(src: &str) -> IfStmt {
        let mut parser = Parser::new(src);
        let module = parser.parse().expect("parse probe");
        let body = module
            .items
            .iter()
            .find_map(|node| match node {
                Node::Function(function) if function.name == "probe" => Some(function.body.statements.clone()),
                _ => None,
            })
            .expect("probe function");
        match body.last().cloned().expect("body has statements") {
            Node::If(if_stmt) => if_stmt,
            other => panic!("expected trailing If statement, got {:?}", other),
        }
    }

    /// Bug #188a: `if val v = x:` in VALUE POSITION — an `if` that is the last
    /// statement of a function body is executed by `exec_if_core` (not `exec_if`,
    /// which was already fixed). `exec_if_core` had its own copy of the pre-fix
    /// `pattern_matches`-only logic, which always matches a bare identifier
    /// pattern — even against nil/None — so the branch was wrongly TAKEN when
    /// the value is absent. It must be SKIPPED instead.
    #[test]
    fn exec_if_core_skips_if_val_when_absent() {
        let if_stmt = parse_trailing_if("fn probe():\n    if val v = x:\n        \"TAKEN\"\n    else:\n        \"SKIPPED\"\n");
        let mut env = Env::new();
        env.insert("x".to_string(), Value::Nil);
        let (flow, value) = exec_if_core(
            &if_stmt,
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("exec_if_core");
        assert!(matches!(flow, Control::Next));
        assert_eq!(value.to_display_string(), "SKIPPED");
    }

    /// Companion case: a genuinely present value must still take the branch,
    /// with the identifier bound to the (unwrapped) value.
    #[test]
    fn exec_if_core_takes_if_val_when_present() {
        let if_stmt = parse_trailing_if("fn probe():\n    if val v = x:\n        v\n    else:\n        99\n");
        let mut env = Env::new();
        env.insert("x".to_string(), Value::Int(42));
        let (flow, value) = exec_if_core(
            &if_stmt,
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("exec_if_core");
        assert!(matches!(flow, Control::Next));
        assert_eq!(value.as_int().expect("int"), 42);
    }
}

/// Execute an if statement as an expression, returning the branch's implicit value.
/// Used for implicit return when if is the last statement in a function.
/// NOTE: This collapses Control::Return into the return value. Only use this
/// when the if-statement is truly being used as a pure expression (not when
/// it may contain early returns that need to propagate).
pub(crate) fn exec_if_expr(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let (flow, val) = exec_if_core(if_stmt, env, functions, classes, enums, impl_methods)?;
    match flow {
        Control::Return(v) => Ok(v),
        _ => Ok(val),
    }
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
