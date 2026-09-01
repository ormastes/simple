//! Argument evaluation utilities

use std::sync::Arc;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef};
use std::collections::HashMap;

use super::super::{evaluate_expr, Enums, ImplMethods};
use crate::interpreter::interpreter_call::exec_function_with_values;

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn eval_arg(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: Value,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    args.get(idx)
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .transpose()
        .map(|opt| opt.unwrap_or(default))
}

/// Evaluate an argument as i64 with default
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn eval_arg_int(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: i64,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<i64, CompileError> {
    eval_arg(
        args,
        idx,
        Value::Int(default),
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )?
    .as_int()
}

/// Evaluate an argument as usize with default
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn eval_arg_usize(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: usize,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<usize, CompileError> {
    // Saturate negatives to 0 rather than letting `as usize` wrap them.
    // A bare `as usize` turned `-5` into 18446744073709551611, which every
    // caller then treated as a real length: `"ab".pad_left(-5)` reached
    // `repeat_n(pad_char, huge)` and PANICKED the interpreter with "capacity
    // overflow". All 21 call sites pass a count, width, or index, so a negative
    // argument means "none" -- never "usize::MAX".
    let raw = eval_arg_int(args, idx, default as i64, env, functions, classes, enums, impl_methods)?;
    Ok(if raw < 0 { 0 } else { raw as usize })
}

/// Apply a lambda or named function to each item in an array, returning Vec of results.
pub(crate) fn apply_lambda_to_vec(
    arr: &[Value],
    lambda_val: &Value,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Value>, CompileError> {
    match lambda_val {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut results = Vec::new();
            for item in arr {
                let mut local_env = Env::clone(captured);
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), item.clone());
                }
                let result = super::lambda_body::eval_lambda_body(
                    body,
                    &mut local_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                results.push(result);
            }
            Ok(results)
        }
        Value::Function { def, captured_env, .. } => {
            let mut results = Vec::new();
            for item in arr {
                let mut call_env = Env::clone(captured_env);
                let result = exec_function_with_values(
                    def,
                    std::slice::from_ref(item),
                    &mut call_env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                results.push(result);
            }
            Ok(results)
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("provide a lambda expression or named function as argument");
            Err(CompileError::semantic_with_context(
                "expected lambda or function argument".to_string(),
                ctx,
            ))
        }
    }
}
