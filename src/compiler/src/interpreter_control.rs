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
macro_rules! check_interrupt {
    () => {
        if crate::interpreter::is_interrupted() {
            return Err(CompileError::InterruptedByUser);
        }
    };
}
use crate::value::{Env, Value, ATTR_STRONG, BUILTIN_ARRAY, BUILTIN_RANGE};
use simple_parser::ast::{
    ClassDef, ContextStmt, EnumDef, Expr, ForStmt, FStringPart, FunctionDef, IfStmt, LoopStmt,
    MatchStmt, Pattern, Type, WhileStmt, WithStmt,
};
use std::cell::RefCell;
use std::collections::HashMap;

// Import parent interpreter types and functions
use super::{
    evaluate_expr, exec_block, Control, Enums, ImplMethods,
    CONTEXT_OBJECT, BDD_CONTEXT_DEFS, BDD_INDENT, BDD_LAZY_VALUES,
};

// Import helpers for pattern binding
use super::interpreter_helpers::{bind_pattern, iter_to_vec};

// Import from interpreter_call for exec_block_value (sibling module)
use super::interpreter_call::exec_block_value;

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
    if evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
        return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
    }
    for (cond, block) in &if_stmt.elif_branches {
        if evaluate_expr(cond, env, functions, classes, enums, impl_methods)?.truthy() {
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
            if matches!(ctrl, Control::Continue) { continue; }
            if let Some(result) = handle_loop_control(ctrl) { return result; }
        }
        return Ok(Control::Next);
    }

    // Normal while loop
    loop {
        check_interrupt!();
        if !evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
            break;
        }
        let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
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
        let ctrl = exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
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
                BDD_CONTEXT_DEFS.with(|cell: &RefCell<HashMap<String, Vec<Value>>>| {
                    cell.borrow().get(name).cloned()
                })
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
            let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
            CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));
            let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);
            CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);
            result
        }
    }
}

/// Execute a with statement (context manager pattern)
/// with resource as name:
///     body
/// Calls __enter__ before body, __exit__ after (even on error)
pub(super) fn exec_with(
    with_stmt: &WithStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let resource = evaluate_expr(&with_stmt.resource, env, functions, classes, enums, impl_methods)?;

    // Call __enter__ if it exists
    let enter_result = call_method_if_exists(&resource, "__enter__", &[], env, functions, classes, enums, impl_methods)?;

    // Bind the result to the name if provided
    if let Some(name) = &with_stmt.name {
        env.insert(name.clone(), enter_result.unwrap_or(resource.clone()));
    }

    // Execute the body
    let result = exec_block(&with_stmt.body, env, functions, classes, enums, impl_methods);

    // Always call __exit__ (even if body failed)
    let _ = call_method_if_exists(&resource, "__exit__", &[], env, functions, classes, enums, impl_methods);

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
    env: &Env,
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
    Ok(if let Control::Return(val) = result { val } else { Value::Nil })
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
                return Ok(Some(exec_method_body(&method, receiver, fields, env, functions, classes, enums, impl_methods)?));
            }
        }
        // Check impl_methods
        if let Some(methods) = impl_methods.get(class) {
            if let Some(method) = methods.iter().find(|m| m.name == method_name) {
                return Ok(Some(exec_method_body(method, receiver, fields, env, functions, classes, enums, impl_methods)?));
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

    // Use iter_to_vec to handle all iterable types uniformly
    let items = iter_to_vec(&iterable)?;

    for item in items {
        check_interrupt!();
        // Use bind_pattern to handle all pattern types (identifier, tuple, etc.)
        if !bind_pattern(&for_stmt.pattern, &item, env) {
            // Pattern didn't match - skip this iteration
            continue;
        }

        let ctrl = exec_block(&for_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
    }
    Ok(Control::Next)
}

/// Check if a pattern is a catch-all that covers any value.
pub(crate) fn is_catch_all_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(_) | Pattern::MutIdentifier(_) => true,
        Pattern::Or(patterns) => patterns.iter().any(is_catch_all_pattern),
        Pattern::Typed { pattern, .. } => is_catch_all_pattern(pattern),
        _ => false,
    }
}

pub(super) fn exec_match(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let subject = evaluate_expr(&match_stmt.subject, env, functions, classes, enums, impl_methods)?;

    // Check for strong enum - disallow wildcard/catch-all patterns
    if let Value::Enum { enum_name, .. } = &subject {
        if let Some(enum_def) = enums.get(enum_name) {
            let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);
            if is_strong {
                for arm in &match_stmt.arms {
                    if is_catch_all_pattern(&arm.pattern) {
                        return Err(CompileError::Semantic(format!(
                            "strong enum '{}' does not allow wildcard or catch-all patterns in match",
                            enum_name
                        )));
                    }
                }
            }
        }
    }

    for arm in &match_stmt.arms {
        let mut bindings = HashMap::new();
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums)? {
            if let Some(guard) = &arm.guard {
                let mut guard_env = env.clone();
                for (name, value) in &bindings {
                    guard_env.insert(name.clone(), value.clone());
                }
                if !evaluate_expr(guard, &guard_env, functions, classes, enums, impl_methods)?.truthy() {
                    continue;
                }
            }

            for (name, value) in bindings {
                env.insert(name, value);
            }

            return exec_block(&arm.body, env, functions, classes, enums, impl_methods);
        }
    }

    Ok(Control::Next)
}

fn match_sequence_pattern(
    value: &Value,
    patterns: &[Pattern],
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
    is_tuple: bool,
) -> Result<bool, CompileError> {
    let values = if is_tuple {
        if let Value::Tuple(vals) = value {
            vals
        } else {
            return Ok(false);
        }
    } else if let Value::Array(vals) = value {
        vals
    } else {
        return Ok(false);
    };

    // Check for Rest pattern to support variable-length matching
    // e.g., [first, ..rest] or [first, second, ..]
    let rest_index = patterns.iter().position(|p| matches!(p, Pattern::Rest));

    if let Some(rest_idx) = rest_index {
        // Patterns before the rest
        let before_rest = &patterns[..rest_idx];
        // Patterns after the rest (if any - skip the Rest itself)
        let after_rest = if rest_idx + 1 < patterns.len() {
            &patterns[rest_idx + 1..]
        } else {
            &[]
        };

        // Minimum values needed: before_rest.len() + after_rest.len()
        let min_needed = before_rest.len() + after_rest.len();
        if values.len() < min_needed {
            return Ok(false);
        }

        // Match patterns before rest
        for (pat, val) in before_rest.iter().zip(values.iter()) {
            if !pattern_matches(pat, val, bindings, enums)? {
                return Ok(false);
            }
        }

        // Match patterns after rest (from the end)
        for (i, pat) in after_rest.iter().enumerate() {
            let val_idx = values.len() - after_rest.len() + i;
            if !pattern_matches(pat, &values[val_idx], bindings, enums)? {
                return Ok(false);
            }
        }

        // Collect rest elements
        let rest_start = before_rest.len();
        let rest_end = values.len() - after_rest.len();
        let rest_values: Vec<Value> = values[rest_start..rest_end].to_vec();

        // If there's an identifier after .., bind it to the rest
        // Look for NamedRest pattern which would be Pattern::Identifier after Rest
        // For now, rest patterns just match (they don't bind)
        // A future enhancement could support [first, ..rest] with named rest

        // Store rest in a special binding if followed by an identifier
        // This is a simplified approach - full support would need parser changes
        bindings.insert("__rest__".to_string(), Value::Array(rest_values));

        Ok(true)
    } else {
        // No rest pattern - exact match required
        if patterns.len() != values.len() {
            return Ok(false);
        }

        for (pat, val) in patterns.iter().zip(values.iter()) {
            if !pattern_matches(pat, val, bindings, enums)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

pub(crate) fn pattern_matches(
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
) -> Result<bool, CompileError> {
    match pattern {
        Pattern::Wildcard => Ok(true),

        Pattern::Identifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MutIdentifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::Literal(lit_expr) => {
            match lit_expr.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => {
                    if let Value::Int(v) = value {
                        Ok(*v == *i)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Float(f) | Expr::TypedFloat(f, _) => {
                    if let Value::Float(v) = value {
                        Ok((*v - *f).abs() < f64::EPSILON)
                    } else {
                        Ok(false)
                    }
                }
                Expr::String(s) => {
                    if let Value::Str(v) = value {
                        Ok(v == s)
                    } else {
                        Ok(false)
                    }
                }
                // Handle FString patterns (strings parsed as f-strings with only literal parts)
                Expr::FString(parts) => {
                    // Build the full string from literal parts
                    let mut pattern_str = String::new();
                    for part in parts {
                        match part {
                            FStringPart::Literal(s) => pattern_str.push_str(s),
                            FStringPart::Expr(_) => {
                                // FStrings with expressions cannot be used as patterns
                                return Ok(false);
                            }
                        }
                    }
                    if let Value::Str(v) = value {
                        Ok(v == &pattern_str)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Symbol(sym) => {
                    if let Value::Symbol(v) = value {
                        Ok(v == sym)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Bool(b) => {
                    if let Value::Bool(v) = value {
                        Ok(*v == *b)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Nil => Ok(matches!(value, Value::Nil)),
                _ => Ok(false),
            }
        }

        Pattern::Enum { name: enum_name, variant, payload } => {
            if let Value::Enum { enum_name: ve, variant: vv, payload: value_payload } = value {
                if enum_name == ve && variant == vv {
                    // Both have no payload
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    // Pattern has payload patterns, value has payload
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        if patterns.len() == 1 {
                            // Single payload - match directly
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)? {
                                return Ok(true);
                            }
                        } else {
                            // Multiple payload patterns - payload should be a tuple
                            if let Value::Tuple(values) = vp.as_ref() {
                                if patterns.len() == values.len() {
                                    let mut all_match = true;
                                    for (pat, val) in patterns.iter().zip(values.iter()) {
                                        if !pattern_matches(pat, val, bindings, enums)? {
                                            all_match = false;
                                            break;
                                        }
                                    }
                                    if all_match {
                                        return Ok(true);
                                    }
                                }
                            }
                        }
                    }
                    // Pattern has no payload but value does - match any payload
                    if payload.is_none() && value_payload.is_some() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        Pattern::Tuple(patterns) => match_sequence_pattern(value, patterns, bindings, enums, true),
        Pattern::Array(patterns) => match_sequence_pattern(value, patterns, bindings, enums, false),

        Pattern::Struct { name, fields } => {
            if let Value::Object { class, fields: obj_fields } = value {
                if class == name {
                    for (field_name, field_pat) in fields {
                        if let Some(field_val) = obj_fields.get(field_name) {
                            if !pattern_matches(field_pat, field_val, bindings, enums)? {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Or(patterns) => {
            for pat in patterns {
                let mut temp_bindings = HashMap::new();
                if pattern_matches(pat, value, &mut temp_bindings, enums)? {
                    bindings.extend(temp_bindings);
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Typed { pattern, ty } => {
            let type_matches = match ty {
                Type::Simple(name) => value.matches_type(name),
                Type::Union(types) => {
                    types.iter().any(|t| {
                        if let Type::Simple(name) = t {
                            value.matches_type(name)
                        } else {
                            true
                        }
                    })
                }
                _ => true,
            };

            if type_matches {
                pattern_matches(pattern, value, bindings, enums)
            } else {
                Ok(false)
            }
        }

        Pattern::Range { start, end, inclusive } => {
            // Range patterns only work with integers
            let Value::Int(val) = value else {
                return Ok(false);
            };
            // Evaluate start and end expressions (must be integer literals)
            let start_val = match start.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            let end_val = match end.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            // Check if value is in range
            if *inclusive {
                Ok(*val >= start_val && *val <= end_val)
            } else {
                Ok(*val >= start_val && *val < end_val)
            }
        }

        Pattern::Rest => {
            Ok(true)
        }
    }
}

/// Extract the covered variant name from a pattern (for exhaustiveness checking).
/// Returns Some(variant_name) for enum patterns, None for wildcards/catch-all.
fn extract_covered_variant(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Enum { variant, .. } => Some(variant.clone()),
        Pattern::Or(patterns) => {
            // Or patterns cover all their sub-patterns
            // Return the first one for simplicity (all should be checked)
            patterns.first().and_then(extract_covered_variant)
        }
        Pattern::Typed { pattern, .. } => extract_covered_variant(pattern),
        // Wildcard, Identifier, etc. are catch-all - they cover everything
        _ => None,
    }
}

/// Collect all variant names covered by a list of match arm patterns.
/// Returns (covered_variants, has_catch_all).
pub(crate) fn collect_covered_variants(patterns: &[&Pattern]) -> (Vec<String>, bool) {
    let mut covered = Vec::new();
    let mut has_catch_all = false;

    for pattern in patterns {
        if is_catch_all_pattern(pattern) {
            has_catch_all = true;
        } else if let Some(variant) = extract_covered_variant(pattern) {
            if !covered.contains(&variant) {
                covered.push(variant);
            }
        }
        // For Or patterns, collect all sub-variants
        if let Pattern::Or(sub_patterns) = pattern {
            for sub_pat in sub_patterns {
                if let Some(variant) = extract_covered_variant(sub_pat) {
                    if !covered.contains(&variant) {
                        covered.push(variant);
                    }
                }
            }
        }
    }

    (covered, has_catch_all)
}

/// Check if a match expression covers all variants of an enum.
/// Returns None if exhaustive, Some(missing_variants) otherwise.
pub(crate) fn check_enum_exhaustiveness(
    enum_name: &str,
    arm_patterns: &[&Pattern],
    enums: &Enums,
) -> Option<Vec<String>> {
    // Get the enum definition
    let enum_def = enums.get(enum_name)?;

    // Get all variant names from the enum definition
    let all_variants: Vec<String> = enum_def.variants.iter().map(|v| v.name.clone()).collect();

    // Collect covered variants from patterns
    let (covered, has_catch_all) = collect_covered_variants(arm_patterns);

    // If there's a catch-all, all variants are covered
    if has_catch_all {
        return None;
    }

    // Find missing variants
    let missing: Vec<String> = all_variants
        .into_iter()
        .filter(|v| !covered.contains(v))
        .collect();

    if missing.is_empty() {
        None
    } else {
        Some(missing)
    }
}
