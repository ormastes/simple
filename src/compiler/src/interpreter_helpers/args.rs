//! Argument evaluation utilities

use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef};
use std::collections::HashMap;

use super::super::{evaluate_expr, Enums, ImplMethods};

pub(crate) fn eval_arg(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    args.get(idx)
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .transpose()
        .map(|opt| opt.unwrap_or(default))
}

/// Evaluate an argument as i64 with default
pub(crate) fn eval_arg_int(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: i64,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
pub(crate) fn eval_arg_usize(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: usize,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<usize, CompileError> {
    Ok(eval_arg_int(args, idx, default as i64, env, functions, classes, enums, impl_methods)? as usize)
}

/// Apply a lambda to each item in an array, returning Vec of results.
pub(crate) fn apply_lambda_to_vec(
    arr: &[Value],
    lambda_val: &Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Value>, CompileError> {
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = lambda_val
    {
        let mut results = Vec::new();
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let result = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
            results.push(result);
        }
        Ok(results)
    } else {
        Err(CompileError::Semantic("expected lambda argument".into()))
    }
}
