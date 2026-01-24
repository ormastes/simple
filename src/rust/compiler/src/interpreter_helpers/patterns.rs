//! Pattern matching and binding

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Pattern};
use std::collections::HashMap;

use super::super::{evaluate_expr, evaluate_method_call_with_self_update, find_and_exec_method_with_self, Enums, ImplMethods, CONST_NAMES};

use super::collections::bind_sequence_pattern;
use super::method_dispatch::call_method_on_value;
use crate::value::{OptionVariant, ResultVariant};

pub(crate) fn bind_pattern(pattern: &Pattern, value: &Value, env: &mut Env) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::MoveIdentifier(name) => {
            // Move pattern - transfers ownership during pattern matching
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::Tuple(patterns) => bind_sequence_pattern(value, patterns, env, true),
        Pattern::Array(patterns) => bind_sequence_pattern(value, patterns, env, false),
        _ => {
            // For other patterns, just try identifier binding
            false
        }
    }
}

// === Helper functions to reduce duplication in interpreter.rs ===

/// Handle functional update expression: target.&method(args)
/// Returns Ok(Some(new_value)) if successfully processed, Ok(None) if not applicable
pub(crate) fn handle_functional_update(
    target: &Expr,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(String, Value)>, CompileError> {
    if let Expr::Identifier(name) = target {
        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help(format!("consider using '{name}_' for a mutable variable"));
            return Err(CompileError::semantic_with_context(
                format!("cannot use functional update on const '{name}'"),
                ctx,
            ));
        }
        let recv_val = env.get(name).cloned().ok_or_else(|| {
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_VARIABLE)
                .with_help("ensure the variable is defined before use");

            if let Some(suggestion) = crate::error::typo::suggest_name(name, known_names.clone()) {
                ctx = ctx.with_help(format!("did you mean `{suggestion}`?"));
            }

            if !known_names.is_empty() && known_names.len() <= 5 {
                let names_list = known_names.join(", ");
                ctx = ctx.with_note(format!("available names: {}", names_list));
            }

            CompileError::semantic_with_context(format!("undefined variable: {name}"), ctx)
        })?;
        let method_call = Expr::MethodCall {
            receiver: Box::new(Expr::Identifier(name.clone())),
            method: method.to_string(),
            args: args.to_vec(),
        };
        let result = evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
        let new_value = match (&recv_val, &result) {
            (Value::Array(_), Value::Array(_)) => result,
            (Value::Dict(_), Value::Dict(_)) => result,
            (Value::Str(_), Value::Str(_)) => result,
            (Value::Tuple(_), Value::Tuple(_)) => result,
            (Value::Object { .. }, Value::Object { .. }) => result,
            _ => env.get(name).cloned().unwrap_or(recv_val),
        };
        Ok(Some((name.clone(), new_value)))
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_PATTERN)
            .with_help("functional update target must be a simple identifier");
        Err(CompileError::semantic_with_context(
            "functional update target must be an identifier".to_string(),
            ctx,
        ))
    }
}

/// Array methods that mutate and should update the binding
const ARRAY_MUTATING_METHODS: &[&str] = &[
    "append",
    "push",
    "pop",
    "insert",
    "remove",
    "reverse",
    "concat",
    "extend",
    "sort",
    "sort_desc",
    "clear",
];

/// Handle method call on object with self-update tracking
/// Returns (result, optional_updated_self) where updated_self is the object with mutations
pub(crate) fn handle_method_call_with_self_update(
    value_expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<(String, Value)>), CompileError> {
    if let Expr::MethodCall { receiver, method, args } = value_expr {
        // Handle nested method calls like self.advance().unwrap()
        // The receiver itself might be a method call that mutates an object
        if let Expr::MethodCall { .. } = receiver.as_ref() {
            // Recursively handle the inner method call first
            let (inner_result, inner_update) =
                handle_method_call_with_self_update(receiver, env, functions, classes, enums, impl_methods)?;

            // If there was an update from the inner method call, we need to use
            // the updated environment for the outer method call
            let mut working_env = if let Some((ref obj_name, ref new_self)) = inner_update {
                let mut temp_env = env.clone();
                temp_env.insert(obj_name.clone(), new_self.clone());
                temp_env
            } else {
                env.clone()
            };

            // Now call the outer method on the inner result
            // Evaluate the arguments first
            let mut eval_args = Vec::new();
            for arg in args {
                let val = evaluate_expr(&arg.value, &mut working_env, functions, classes, enums, impl_methods)?;
                eval_args.push(val);
            }

            // Call the method on the inner_result value
            let outer_result = call_method_on_value(
                inner_result.clone(),
                method,
                &eval_args,
                &mut working_env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            // For chained mutable method calls, propagate the final result
            // If the outer method returned an object of the same type, it's likely
            // the modified self from a `me` method
            if let Some((ref obj_name, _)) = inner_update {
                // If outer_result is an Object, use it as the final update
                // This handles chains like m.when("foo").returns(42) where
                // both methods modify and return self
                if matches!(outer_result, Value::Object { .. }) {
                    return Ok((outer_result.clone(), Some((obj_name.clone(), outer_result))));
                }
            }
            // Fall back to propagating the inner update for non-object results
            return Ok((outer_result, inner_update));
        }

        // Handle FieldAccess receivers: self.data.method()
        // When calling a mutating method on a nested object field, we need to:
        // 1. Get the parent object
        // 2. Get the field value
        // 3. Call the method on the field (with self-update tracking)
        // 4. Update the parent's field with the mutated value
        // 5. Update the parent in env
        if let Expr::FieldAccess { receiver: parent_receiver, field } = receiver.as_ref() {
            if let Expr::Identifier(parent_name) = parent_receiver.as_ref() {
                // Get parent object
                if let Some(parent_val) = env.get(parent_name).cloned() {
                    if let Value::Object { class: parent_class, mut fields } = parent_val {
                        // Get the field value
                        if let Some(field_val) = fields.get(field).cloned() {
                            // For Object field values, use find_and_exec_method_with_self
                            // to properly execute the method and get the updated self
                            if let Value::Object { class: field_class, fields: field_fields } = &field_val {
                                if let Some((result, updated_field)) = find_and_exec_method_with_self(
                                    method,
                                    args,
                                    field_class,
                                    field_fields,
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                )? {
                                    // Update the field in parent with the mutated nested object
                                    fields.insert(field.clone(), updated_field);

                                    // Create updated parent
                                    let updated_parent = Value::Object {
                                        class: parent_class.clone(),
                                        fields,
                                    };

                                    // Return result and update instruction for parent
                                    return Ok((result, Some((parent_name.clone(), updated_parent))));
                                }
                            }

                            // For non-Object field values, fall through to regular evaluation
                        }
                    }
                }
            }
        }

        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            // Handle Object mutations
            if let Some(Value::Object { .. }) = env.get(obj_name) {
                let (result, updated_self) = evaluate_method_call_with_self_update(
                    receiver,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                if let Some(new_self) = updated_self {
                    return Ok((result, Some((obj_name.clone(), new_self))));
                }
                return Ok((result, None));
            }
            // Handle Array mutations for mutating methods
            if let Some(Value::Array(_)) = env.get(obj_name) {
                if ARRAY_MUTATING_METHODS.contains(&method.as_str()) {
                    // Check if variable is mutable
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(obj_name));
                    if is_const {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help(format!("consider using '{obj_name}_' for a mutable variable"));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "cannot call mutating method '{}' on immutable array '{}'",
                                method, obj_name
                            ),
                            ctx,
                        ));
                    }
                    // Evaluate the method call - it returns the new array
                    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                    if let Value::Array(new_arr) = &result {
                        // Return both the new array as result AND the update for self-mutation
                        let new_array_val = Value::Array(new_arr.clone());
                        return Ok((new_array_val.clone(), Some((obj_name.clone(), new_array_val))));
                    }
                }
            }
            // Handle Dict mutations for mutating methods
            if let Some(Value::Dict(_)) = env.get(obj_name) {
                let dict_mutating = ["set", "insert", "remove", "delete", "merge", "extend", "clear"];
                if dict_mutating.contains(&method.as_str()) {
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(obj_name));
                    if is_const {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help(format!("consider using '{obj_name}_' for a mutable variable"));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "cannot call mutating method '{}' on immutable dict '{}'",
                                method, obj_name
                            ),
                            ctx,
                        ));
                    }
                    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(new_dict) = &result {
                        // Return both the new dict as result AND the update for self-mutation
                        let new_dict_val = Value::Dict(new_dict.clone());
                        return Ok((new_dict_val.clone(), Some((obj_name.clone(), new_dict_val))));
                    }
                }
            }
        }
    }
    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}

/// Bind a single pattern element from a let statement
/// Updates const names set if the binding is immutable
fn bind_let_pattern_element(pat: &Pattern, val: Value, is_mutable: bool, env: &mut Env) {
    match pat {
        Pattern::Identifier(name) => {
            env.insert(name.clone(), val);
            if !is_mutable {
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
            }
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), val);
        }
        Pattern::MoveIdentifier(name) => {
            // Move pattern - transfers ownership
            env.insert(name.clone(), val);
        }
        Pattern::Typed { pattern, .. } => {
            bind_let_pattern_element(pattern, val, is_mutable, env);
        }
        _ => {}
    }
}

/// Bind any pattern from a let statement.
pub(crate) fn bind_pattern_value(pat: &Pattern, val: Value, is_mutable: bool, env: &mut Env) {
    match pat {
        Pattern::Tuple(patterns) => {
            // Allow tuple pattern to match both Tuple and Array
            let values: Vec<Value> = match val {
                Value::Tuple(v) => v,
                Value::Array(v) => v,
                _ => Vec::new(),
            };
            bind_collection_pattern(patterns, values, is_mutable, env);
        }
        Pattern::Array(patterns) => {
            if let Value::Array(values) = val {
                bind_collection_pattern(patterns, values, is_mutable, env);
            }
        }
        _ => bind_let_pattern_element(pat, val, is_mutable, env),
    }
}

/// Bind a collection pattern (tuple or array) from a let statement.
fn bind_collection_pattern(patterns: &[Pattern], values: Vec<Value>, is_mutable: bool, env: &mut Env) {
    for (pat, val) in patterns.iter().zip(values.into_iter()) {
        bind_pattern_value(pat, val, is_mutable, env);
    }
}
