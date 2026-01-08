use std::collections::HashMap;

use tracing::instrument;

use simple_parser::ast::Expr;

use crate::effects::check_effect_violations;
use crate::value::{OptionVariant, ResultVariant, SpecialEnumType};

use super::{
    evaluate_macro_invocation, spawn_actor_with_expr, take_macro_introduced_symbols,
    ClassDef, CompileError, Env, Enums, FunctionDef, ImplMethods, Value, GENERATOR_YIELDS,
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
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Some(value) = literals::eval_literal_expr(
        expr,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )? {
        return Ok(value);
    }
    if let Some(value) = ops::eval_op_expr(
        expr,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )? {
        return Ok(value);
    }
    if let Some(value) = control::eval_control_expr(
        expr,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )? {
        return Ok(value);
    }
    if let Some(value) = calls::eval_call_expr(
        expr,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )? {
        return Ok(value);
    }
    if let Some(value) = collections::eval_collection_expr(
        expr,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )? {
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
                Value::Future(f) => f.await_result().map_err(|e| CompileError::Semantic(e)),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| CompileError::Semantic(e))?;
                    Ok(Value::Nil)
                }
                _ => Err(CompileError::Semantic(
                    "await requires a Future or Actor handle".into(),
                )),
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
                return Err(CompileError::Semantic(
                    "yield called outside of generator".into(),
                ));
            }

            Ok(Value::Nil)
        }
        Expr::MacroInvocation { name, args: macro_args } => {
            let result = evaluate_macro_invocation(
                name,
                macro_args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

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

                // TODO: Execute inject code
                // NOTE: Inject code requires mutable environment access and block-level modification
                // Currently inject code is extracted and stored in contract result, but not executed
                // Full implementation requires:
                // 1. Mutable env access (currently expressions have &Env, not &mut Env)
                // 2. Block-level handling for head/tail/here injection points
                // 3. Statement-level macro invocation handling (not just expressions)
                //
                // For now, inject contract items are parsed, validated, and extracted,
                // but the code is not yet spliced into the callsite.

                // TODO: Register types, variables when those contract types are implemented
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
                        None => Err(CompileError::Semantic(format!(
                            "invalid Result variant: {}",
                            variant
                        ))),
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
                        None => Err(CompileError::Semantic(format!(
                            "invalid Option variant: {}",
                            variant
                        ))),
                    }
                }
                _ => Err(CompileError::Semantic(
                    "? operator requires Result or Option type".into(),
                )),
            }
        }
        // Contract expressions - not supported in interpreter yet
        Expr::ContractResult => Err(CompileError::Semantic(
            "contract 'result' keyword can only be used in contract blocks".into(),
        )),
        Expr::ContractOld(_) => Err(CompileError::Semantic(
            "contract old() expression can only be used in ensures blocks".into(),
        )),
        #[allow(unreachable_patterns)]
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}
