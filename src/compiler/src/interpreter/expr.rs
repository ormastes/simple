use std::collections::HashMap;

use tracing::instrument;

use simple_parser::ast::Expr;

use crate::effects::check_effect_violations;
use crate::error::{codes, ErrorContext};
use crate::value::{OptionVariant, ResultVariant, SpecialEnumType};

use super::{
    evaluate_macro_invocation, spawn_actor_with_expr, take_macro_introduced_symbols, ClassDef, CompileError, Enums,
    Env, FunctionDef, ImplMethods, Value, GENERATOR_YIELDS,
};

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
                    CompileError::semantic_with_context(
                        format!("await failed: {}", e),
                        ctx,
                    )
                }),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::AWAIT_FAILED)
                            .with_help("ensure the actor completes successfully");
                        CompileError::semantic_with_context(
                            format!("await failed: {}", e),
                            ctx,
                        )
                    })?;
                    Ok(Value::Nil)
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::AWAIT_FAILED)
                        .with_help("await can only be used on Future or Actor values");
                    Err(CompileError::semantic_with_context(
                        format!("await failed: requires a Future or Actor handle, got {}", val.type_name()),
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
                        },
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
                        },
                    }
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("try operator (?) can only be used on Result or Option types");
                    Err(CompileError::semantic_with_context(
                        format!("invalid operation: ? operator requires Result or Option type, got {}", val.type_name()),
                        ctx,
                    ))
                },
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
        },
        Expr::ContractOld(_) => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("contract old() expression can only be used in ensures blocks");
            Err(CompileError::semantic_with_context(
                "invalid operation: contract old() expression can only be used in ensures blocks".to_string(),
                ctx,
            ))
        },
        #[allow(unreachable_patterns)]
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("this expression type is not supported in this context");
            Err(CompileError::semantic_with_context(
                format!("invalid operation: unsupported expression type: {:?}", expr),
                ctx,
            ))
        },
    }
}
