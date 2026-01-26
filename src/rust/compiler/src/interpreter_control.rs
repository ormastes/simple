//! Control flow execution functions for the interpreter
//!
//! This module provides implementations for control flow constructs:
//! - If/else statements
//! - Match expressions
//! - While loops
//! - For loops
//! - Loop control (break, continue)

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
use crate::value::{Env, Value, ATTR_STRONG, BUILTIN_ARRAY, BUILTIN_RANGE};
use simple_parser::ast::{
    ClassDef, ContextStmt, Expr, ForStmt, FunctionDef, IfStmt, LoopStmt, MatchStmt, WhileStmt, WithStmt,
};
use std::cell::RefCell;
use std::collections::HashMap;

// Import parent interpreter types and functions
use super::{
    await_value, evaluate_expr, exec_block, exec_block_fn, Control, Enums, ImplMethods, BDD_CONTEXT_DEFS, BDD_INDENT,
    BDD_LAZY_VALUES, CONTEXT_OBJECT, CONTEXT_VAR_NAME,
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
#[inline]
fn handle_loop_control(ctrl: Control) -> Option<Result<Control, CompileError>> {
    match ctrl {
        Control::Next => None,
        Control::Continue => None, // caller handles continue
        Control::Break(_) => Some(Ok(Control::Next)),
        ret @ Control::Return(_) => Some(Ok(ret)),
    }
}

pub(super) fn exec_if(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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

    for (idx, (cond, block)) in if_stmt.elif_branches.iter().enumerate() {
        let elif_val = evaluate_expr(cond, env, functions, classes, enums, impl_methods)?;
        let elif_val = if if_stmt.is_suspend {
            await_value(elif_val)?
        } else {
            elif_val
        };
        let elif_decision = elif_val.truthy();

        // COVERAGE: Record decision for elif statement
        // Compute a different decision ID for each elif by incorporating the index
        let elif_decision_id = if_stmt.span.line as u32 + idx as u32;
        record_decision_coverage_ffi("<source>", if_stmt.span.line + idx, if_stmt.span.column, elif_decision);

        if elif_decision {
            return exec_block(block, env, functions, classes, enums, impl_methods);
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Handle while-let: while let PATTERN = EXPR:
    if let Some(pattern) = &while_stmt.let_pattern {
        loop {
            check_interrupt!();
            check_execution_limit!();
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
            if matches!(ctrl, Control::Continue) {
                continue;
            }
            if let Some(result) = handle_loop_control(ctrl) {
                return result;
            }
        }
        return Ok(Control::Next);
    }

    // Normal while loop
    // For while~ (is_suspend), await the condition value before checking truthiness
    loop {
        check_interrupt!();
        check_execution_limit!();
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
        if matches!(ctrl, Control::Continue) {
            continue;
        }
        if let Some(result) = handle_loop_control(ctrl) {
            return result;
        }
    }
    Ok(Control::Next)
}

pub(super) fn exec_loop(
    loop_stmt: &simple_parser::ast::LoopStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        check_interrupt!();
        check_execution_limit!();
        let ctrl = exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) {
            continue;
        }
        if let Some(result) = handle_loop_control(ctrl) {
            return result;
        }
    }
}

pub(super) fn exec_context(
    ctx_stmt: &ContextStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    let exit_result = call_method_if_exists(&resource, "__exit__", &[], env, functions, classes, enums, impl_methods)?;
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
fn exec_method_body(
    method: &FunctionDef,
    receiver: &Value,
    fields: &HashMap<String, Value>,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = env.clone();
    local_env.insert("self".to_string(), receiver.clone());
    for (k, v) in fields {
        local_env.insert(k.clone(), v.clone());
    }
    let result = exec_block(&method.body, &mut local_env, functions, classes, enums, impl_methods)?;
    Ok(if let Control::Return(val) = result {
        val
    } else {
        Value::Nil
    })
}

/// Helper to call a method if it exists on an object
fn call_method_if_exists(
    receiver: &Value,
    method_name: &str,
    _args: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
        if matches!(ctrl, Control::Continue) {
            continue;
        }
        if let Some(result) = handle_loop_control(ctrl) {
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let (flow, _last_val) = exec_match_core(match_stmt, env, functions, classes, enums, impl_methods)?;
    match flow {
        Control::Return(_) | Control::Break(_) | Control::Continue => Ok(flow),
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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

    for (cond, block) in if_stmt.elif_branches.iter() {
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let (flow, last_val) = exec_match_core(match_stmt, env, functions, classes, enums, impl_methods)?;
    match flow {
        Control::Return(v) => Ok(v),
        Control::Break(_) | Control::Continue => Ok(Value::Nil),
        Control::Next => {
            // Return the implicit value from the match arm
            Ok(last_val.unwrap_or(Value::Nil))
        }
    }
}
