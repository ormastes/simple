use std::collections::HashMap;

use tracing::instrument;

use simple_parser::ast::Expr;

use crate::effects::check_effect_violations;
use crate::error::{codes, ErrorContext};
use crate::value::{OptionVariant, ResultVariant, SpecialEnumType};

use super::{
    evaluate_macro_invocation, spawn_actor_with_expr, take_macro_introduced_symbols, ClassDef, CompileError, Enums,
    Env, FunctionDef, ImplMethods, Value, GENERATOR_YIELDS, evaluate_method_call, exec_lambda,
    exec_function_with_captured_env,
};

/// Helper to unwrap Option or Result values, returning Some(inner_value) or None
fn try_unwrap_option_or_result(val: &Value) -> Option<Value> {
    match val {
        Value::Enum {
            ref enum_name,
            ref variant,
            ref payload,
        } => {
            if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) {
                if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
                    payload.as_ref().map(|p| p.as_ref().clone())
                } else {
                    None
                }
            } else if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) {
                if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
                    payload.as_ref().map(|p| p.as_ref().clone())
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Helper to call a closure/lambda value with no arguments
fn call_closure_no_args(
    closure: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match closure {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut captured_clone = captured.clone();
            exec_lambda(
                &params,  // params is already Vec<String>
                &body,
                &[],
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::Function {
            def, captured_env, ..
        } => {
            let mut captured_env_clone = captured_env.clone();
            exec_function_with_captured_env(
                &def,
                &[],
                env,
                &mut captured_env_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("expected a closure or function");
            Err(CompileError::semantic_with_context(
                format!("expected callable, got {}", closure.type_name()),
                ctx,
            ))
        }
    }
}

/// Helper to get a field value from an object-like value
fn get_field_value(val: &Value, field: &str) -> Result<Value, CompileError> {
    match val {
        Value::Object { fields, class, .. } => {
            if let Some(v) = fields.get(field) {
                Ok(v.clone())
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_FIELD)
                    .with_help("check the field name");
                Err(CompileError::semantic_with_context(
                    format!("class `{}` has no field named `{}`", class, field),
                    ctx,
                ))
            }
        }
        Value::Dict(map) => {
            if let Some(v) = map.get(field) {
                Ok(v.clone())
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_FIELD)
                    .with_help("key not found in dict");
                Err(CompileError::semantic_with_context(
                    format!("key `{}` not found in dict", field),
                    ctx,
                ))
            }
        }
        Value::Str(s) => match field {
            "len" => Ok(Value::Int(s.len() as i64)),
            "is_empty" => Ok(Value::Bool(s.is_empty())),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_FIELD)
                    .with_help("available properties on String: len, is_empty");
                Err(CompileError::semantic_with_context(
                    format!("unknown property '{field}' on String"),
                    ctx,
                ))
            }
        },
        Value::Array(arr) => match field {
            "len" => Ok(Value::Int(arr.len() as i64)),
            "is_empty" => Ok(Value::Bool(arr.is_empty())),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNDEFINED_FIELD)
                    .with_help("available properties on Array: len, is_empty");
                Err(CompileError::semantic_with_context(
                    format!("unknown property '{field}' on Array"),
                    ctx,
                ))
            }
        },
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_FIELD)
                .with_help("field access requires an object, dict, or value with properties");
            Err(CompileError::semantic_with_context(
                format!("cannot access field '{}' on this value type", field),
                ctx,
            ))
        }
    }
}

mod calls;
mod collections;
mod control;
mod literals;
mod ops;

mod casting;
mod units;

/// Evaluate a constant expression at compile time
#[instrument(skip(env, functions, classes, enums, impl_methods))]
pub(crate) fn evaluate_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Some(value) = literals::eval_literal_expr(expr, env, functions, classes, enums, impl_methods)? {
        return Ok(value);
    }
    if let Some(value) = ops::eval_op_expr(expr, env, functions, classes, enums, impl_methods)? {
        return Ok(value);
    }
    if let Some(value) = control::eval_control_expr(expr, env, functions, classes, enums, impl_methods)? {
        return Ok(value);
    }
    if let Some(value) = calls::eval_call_expr(expr, env, functions, classes, enums, impl_methods)? {
        return Ok(value);
    }
    if let Some(value) = collections::eval_collection_expr(expr, env, functions, classes, enums, impl_methods)? {
        return Ok(value);
    }

    match expr {
        Expr::Spawn(inner) => Ok(spawn_actor_with_expr(
            inner,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )),
        Expr::Await(inner) => {
            check_effect_violations("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => f.await_result().map_err(|e| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::AWAIT_FAILED)
                        .with_help("ensure the future completes successfully");
                    CompileError::semantic_with_context(format!("await failed: {}", e), ctx)
                }),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::AWAIT_FAILED)
                            .with_help("ensure the actor completes successfully");
                        CompileError::semantic_with_context(format!("await failed: {}", e), ctx)
                    })?;
                    Ok(Value::Nil)
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::AWAIT_FAILED)
                        .with_help("await can only be used on Future or Actor values");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "await failed: requires a Future or Actor handle, got {}",
                            val.type_name()
                        ),
                        ctx,
                    ))
                }
            }
        }
        Expr::Yield(maybe_val) => {
            let yield_val = match maybe_val {
                Some(expr) => evaluate_expr(expr, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };

            let added = GENERATOR_YIELDS.with(|cell| {
                if let Some(yields) = cell.borrow_mut().as_mut() {
                    yields.push(yield_val.clone());
                    true
                } else {
                    false
                }
            });

            if !added {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("yield can only be used inside a generator function");
                return Err(CompileError::semantic_with_context(
                    "invalid operation: yield called outside of generator",
                    ctx,
                ));
            }

            Ok(Value::Nil)
        }
        Expr::MacroInvocation { name, args: macro_args } => {
            let result = evaluate_macro_invocation(name, macro_args, env, functions, classes, enums, impl_methods)?;

            // Register symbols introduced by macro contracts (#1303)
            if let Some(introduced) = take_macro_introduced_symbols() {
                // Register introduced functions
                for (func_name, func_def) in introduced.introduced_functions {
                    functions.insert(func_name, func_def);
                }

                // Register introduced classes
                for (class_name, class_def) in introduced.introduced_classes {
                    classes.insert(class_name, class_def);
                }

                // Register introduced types (stored as Nil for now)
                for (name, _ty) in introduced.introduced_types {
                    env.insert(name, Value::Nil);
                }

                // Register introduced variables
                for (name, _ty, _is_const) in introduced.introduced_vars {
                    // Initialize with Nil placeholder
                    // The macro's emit block should assign the actual value
                    env.insert(name, Value::Nil);
                }

                // NOTE: Inject code execution is FULLY IMPLEMENTED in macro/expansion.rs
                // - MacroAnchor::Here blocks execute immediately at callsite (line 138-141)
                // - MacroAnchor::Head blocks execute immediately with a trace warning (line 130-137)
                // - MacroAnchor::Tail blocks queue via queue_tail_injection() (line 125-129)
                //   and execute at block exit via exit_block_scope() (interpreter.rs:658-671)
                //
                // The inject labels from contracts are used to route emit blocks to the
                // correct execution path based on their anchor type.
            }

            Ok(result)
        }
        Expr::Try(inner) => {
            // Try operator: expr? - unwrap Ok or propagate Err
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) => {
                    match ResultVariant::from_name(variant) {
                        Some(ResultVariant::Ok) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(ResultVariant::Err) => {
                            // Return the Err as a TryError that should be propagated
                            Err(CompileError::TryError(val))
                        }
                        None => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_PATTERN)
                                .with_help("Result variants are Ok and Err");
                            Err(CompileError::semantic_with_context(
                                format!("invalid pattern: invalid Result variant: {}", variant),
                                ctx,
                            ))
                        }
                    }
                }
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) => {
                    match OptionVariant::from_name(variant) {
                        Some(OptionVariant::Some) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(OptionVariant::None) => {
                            // Return None as a TryError
                            Err(CompileError::TryError(val))
                        }
                        None => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_PATTERN)
                                .with_help("Option variants are Some and None");
                            Err(CompileError::semantic_with_context(
                                format!("invalid pattern: invalid Option variant: {}", variant),
                                ctx,
                            ))
                        }
                    }
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("try operator (?) can only be used on Result or Option types");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: ? operator requires Result or Option type, got {}",
                            val.type_name()
                        ),
                        ctx,
                    ))
                }
            }
        }
        // Existence check: expr.? - returns bool indicating if value is present
        Expr::ExistsCheck(inner) => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            let exists = match &val {
                // Option: Some is present, None is not
                Value::Enum { enum_name, variant, .. }
                    if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) =>
                {
                    OptionVariant::from_name(variant) == Some(OptionVariant::Some)
                }
                // Result: Ok is present, Err is not
                Value::Enum { enum_name, variant, .. }
                    if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) =>
                {
                    ResultVariant::from_name(variant) == Some(ResultVariant::Ok)
                }
                // Nil is not present
                Value::Nil => false,
                // Empty collections are not present
                Value::Array(arr) => !arr.is_empty(),
                Value::Dict(dict) => !dict.is_empty(),
                // Empty strings are not present
                Value::Str(s) => !s.is_empty(),
                // Objects with class "Set" - check if inner items are empty
                Value::Object { class, fields } if class == "Set" => {
                    // Set is typically stored with an "items" field containing a Dict
                    if let Some(Value::Dict(items)) = fields.get("items") {
                        !items.is_empty()
                    } else {
                        true // If no items field, treat as present
                    }
                }
                // All other values (numbers, bools, structs, etc.) are present
                _ => true,
            };
            Ok(Value::Bool(exists))
        }
        // Safe unwrap: expr unwrap or: default
        Expr::UnwrapOr { expr: inner, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                evaluate_expr(default, env, functions, classes, enums, impl_methods)
            }
        }
        // Safe unwrap with lazy default: expr unwrap else: closure
        Expr::UnwrapElse { expr: inner, fallback_fn } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                // Evaluate the fallback closure and call it
                let closure = evaluate_expr(fallback_fn, env, functions, classes, enums, impl_methods)?;
                call_closure_no_args(closure, env, functions, classes, enums, impl_methods)
            }
        }
        // Safe unwrap or early return: expr unwrap or_return:
        Expr::UnwrapOrReturn(inner) => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                // Return the None/Err as a TryError to propagate
                Err(CompileError::TryError(val))
            }
        }
        // Null coalescing: expr ?? default
        Expr::Coalesce { expr: inner, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                Ok(unwrapped)
            } else {
                evaluate_expr(default, env, functions, classes, enums, impl_methods)
            }
        }
        // Optional chaining: expr?.field
        Expr::OptionalChain { expr: inner, field } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                // Access the field on the unwrapped value
                let field_val = get_field_value(&unwrapped, field)?;
                // Wrap result in Some
                Ok(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(field_val)),
                })
            } else {
                // Return None
                Ok(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: None,
                })
            }
        }
        // Optional method call: expr?.method(args)
        Expr::OptionalMethodCall { receiver, method, args } => {
            let val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?;
            if let Some(unwrapped) = try_unwrap_option_or_result(&val) {
                // Create a synthetic method call expression on the unwrapped value
                // We'll temporarily store the unwrapped value in env and call the method
                let temp_var_name = "__optional_chain_temp__".to_string();
                env.insert(temp_var_name.clone(), unwrapped);
                let temp_receiver = Box::new(Expr::Identifier(temp_var_name.clone()));
                let result = evaluate_method_call(&temp_receiver, method, args, env, functions, classes, enums, impl_methods)?;
                env.remove(&temp_var_name);
                // Wrap result in Some
                Ok(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(result)),
                })
            } else {
                // Return None
                Ok(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: None,
                })
            }
        }
        // Safe cast with default: expr as Type or: default
        Expr::CastOr { expr: inner, target_type, default } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => evaluate_expr(default, env, functions, classes, enums, impl_methods),
            }
        }
        // Safe cast with lazy default: expr as Type else: closure
        Expr::CastElse { expr: inner, target_type, fallback_fn } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => {
                    let closure = evaluate_expr(fallback_fn, env, functions, classes, enums, impl_methods)?;
                    call_closure_no_args(closure, env, functions, classes, enums, impl_methods)
                }
            }
        }
        // Safe cast or early return: expr as Type or_return:
        Expr::CastOrReturn { expr: inner, target_type } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match casting::cast_value(val, target_type) {
                Ok(cast_val) => Ok(cast_val),
                Err(_) => {
                    // Return None to signal early return
                    let none_val = Value::Enum {
                        enum_name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: None,
                    };
                    Err(CompileError::TryError(none_val))
                }
            }
        }
        // Contract expressions - not supported in interpreter yet
        Expr::ContractResult => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("contract 'result' keyword can only be used in contract blocks");
            Err(CompileError::semantic_with_context(
                "invalid operation: contract 'result' keyword can only be used in contract blocks".to_string(),
                ctx,
            ))
        }
        Expr::ContractOld(_) => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("contract old() expression can only be used in ensures blocks");
            Err(CompileError::semantic_with_context(
                "invalid operation: contract old() expression can only be used in ensures blocks".to_string(),
                ctx,
            ))
        }
        #[allow(unreachable_patterns)]
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("this expression type is not supported in this context");
            Err(CompileError::semantic_with_context(
                format!("invalid operation: unsupported expression type: {:?}", expr),
                ctx,
            ))
        }
    }
}
