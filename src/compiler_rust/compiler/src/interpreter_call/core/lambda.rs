// Lambda execution support

use std::sync::Arc;
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{await_value, evaluate_expr};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef};
use simple_runtime::value::diagram_sffi;
use std::collections::HashMap;

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn exec_lambda(
    params: &[String],
    body: &simple_parser::ast::Expr,
    args: &[Argument],
    call_env: &mut Env,
    captured_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::super::block_execution::exec_block_closure_into;

    // Diagram tracing for lambda execution
    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_call("<lambda>");
    }

    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        // Automatically await Promise arguments
        let val = await_value(val)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help(format!("lambda expects {} argument(s)", params.len()));
                return Err(CompileError::semantic_with_context(
                    "too many arguments to lambda".to_string(),
                    ctx,
                ));
            }
            local_env.insert(params[positional_idx].clone(), val);
            positional_idx += 1;
        }
    }

    for param in params {
        if !local_env.contains_key(param) {
            local_env.insert(param.clone(), Value::Nil);
        }
    }

    let result = if let Expr::DoBlock(nodes) = body {
        // Run the block against local_env in place (same statement semantics as the
        // clone-isolated wrapper) so a `me`-method's mutation to an object argument
        // is observable for write-back below.
        match exec_block_closure_into(nodes, &mut local_env, functions, classes, enums, impl_methods) {
            // A `return` inside this lambda's block body (bug #188b) exits THIS
            // lambda call, yielding the returned value as the call's result — it
            // must not escape further as an error. See `CompileError::BlockReturn`.
            Err(CompileError::BlockReturn(value)) => Ok(value),
            other => other,
        }
    } else {
        evaluate_expr(body, &mut local_env, functions, classes, enums, impl_methods)
    };

    // Write back mutated container arguments to the caller's bindings, mirroring the
    // function-call write-back in `core::function_exec` (Bug #19). A lambda parameter
    // lives only in this throwaway local_env, so without this a mutation a `me`-method
    // performed on an Object/Array/Dict/Tuple argument would be lost to the caller.
    // Only identifier and `obj.field` arguments map 1:1 to a caller binding; primitives
    // keep value semantics. (Higher-order builtins like map/filter invoke lambdas via a
    // separate value-based path, not exec_lambda, so they never reach this.)
    if result.is_ok() {
        let mut positional_idx = 0usize;
        for arg in args {
            let param_name = if let Some(name) = &arg.name {
                name.clone()
            } else {
                let p = match params.get(positional_idx) {
                    Some(p) => p.clone(),
                    None => {
                        positional_idx += 1;
                        continue;
                    }
                };
                positional_idx += 1;
                p
            };
            match &arg.value {
                Expr::Identifier(caller_name) => {
                    if let Some(callee_val) = local_env.get(&param_name) {
                        if matches!(
                            callee_val,
                            Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                        ) && call_env.contains_key(caller_name)
                        {
                            let new_val = callee_val.clone();
                            call_env.insert(caller_name.clone(), new_val);
                        }
                    }
                }
                Expr::FieldAccess { receiver, field } => {
                    if let Expr::Identifier(obj_name) = receiver.as_ref() {
                        if let Some(callee_val) = local_env.get(&param_name).cloned() {
                            if matches!(
                                callee_val,
                                Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                            ) {
                                if let Some(Value::Object { class, mut fields }) = call_env.get(obj_name).cloned() {
                                    Arc::make_mut(&mut fields).insert(field.clone(), callee_val);
                                    call_env.insert(obj_name.clone(), Value::Object { class, fields });
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    result
}
