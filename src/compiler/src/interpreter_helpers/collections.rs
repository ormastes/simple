//! Collection operations (map, filter, reduce, etc.)

use crate::error::CompileError;
use crate::value::{Env, Value, BUILTIN_RANGE};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, LambdaParam, Pattern};
use std::collections::HashMap;

use super::super::{evaluate_expr, exec_function, Control, Enums, ImplMethods};
use super::args::apply_lambda_to_vec;
use super::patterns::bind_pattern;

pub(crate) fn eval_array_map(
    arr: &[Value],
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let results = apply_lambda_to_vec(arr, &func, functions, classes, enums, impl_methods)?;
    Ok(Value::Array(results))
}

/// Setup environment with single parameter binding for a lambda
fn bind_lambda_param(captured: &Env, params: &[String], value: &Value) -> Env {
    let mut env = captured.clone();
    if let Some(param) = params.first() {
        env.insert(param.clone(), value.clone());
    }
    env
}

/// Helper for array predicate operations (filter, find, any, all)
fn with_lambda_predicate<F>(func: Value, operation: &str, mut process: F) -> Result<Value, CompileError>
where
    F: FnMut(&[String], &Expr, &Env) -> Result<Value, CompileError>,
{
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = func
    {
        process(&params, &body, &captured)
    } else {
        Err(CompileError::Semantic(format!("{operation} expects lambda argument")))
    }
}

/// Array filter: keep elements where lambda returns truthy
pub(crate) fn eval_array_filter(
    arr: &[Value],
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_lambda_predicate(func, "filter", |params, body, captured| {
        let mut results = Vec::new();
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                results.push(item.clone());
            }
        }
        Ok(Value::Array(results))
    })
}

/// Array reduce: fold over elements with accumulator
pub(crate) fn eval_array_reduce(
    arr: &[Value],
    init: Value,
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = func
    {
        let mut acc = init;
        for item in arr {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), acc);
                local_env.insert(params[1].clone(), item.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            acc = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
        }
        Ok(acc)
    } else {
        Err(CompileError::Semantic("reduce expects lambda argument".into()))
    }
}

/// Array find: return first element where lambda is truthy
pub(crate) fn eval_array_find(
    arr: &[Value],
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_lambda_predicate(func, "find", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(item.clone());
            }
        }
        Ok(Value::Nil)
    })
}

/// Array any: return true if any element satisfies lambda
pub(crate) fn eval_array_any(
    arr: &[Value],
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_lambda_predicate(func, "any", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    })
}

/// Array all: return true if all elements satisfy lambda
pub(crate) fn eval_array_all(
    arr: &[Value],
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_lambda_predicate(func, "all", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if !evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    })
}

/// Helper for dict operations with lambda
fn with_dict_lambda<F>(func: Value, operation: &str, process: F) -> Result<Value, CompileError>
where
    F: FnOnce(&[String], &Expr, &Env) -> Result<Value, CompileError>,
{
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = func
    {
        process(&params, &body, &captured)
    } else {
        Err(CompileError::Semantic(format!("{operation} expects lambda argument")))
    }
}

/// Dict map_values: apply lambda to each value
pub(crate) fn eval_dict_map_values(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_dict_lambda(func, "map_values", |params, body, captured| {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let local_env = bind_lambda_param(captured, params, v);
            let new_val = evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?;
            new_map.insert(k.clone(), new_val);
        }
        Ok(Value::Dict(new_map))
    })
}

/// Dict filter: keep entries where lambda returns truthy
pub(crate) fn eval_dict_filter(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_dict_lambda(func, "filter", |params, body, captured| {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), Value::Str(k.clone()));
                local_env.insert(params[1].clone(), v.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), v.clone());
            }
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                new_map.insert(k.clone(), v.clone());
            }
        }
        Ok(Value::Dict(new_map))
    })
}

// === Helper functions for comprehensions and slicing ===

// Option and Result helpers from a separate module
#[path = "../interpreter_helpers_option_result.rs"]
mod interpreter_helpers_option_result;
pub(crate) use interpreter_helpers_option_result::*;

/// Convert a value to an iterable vector (for comprehensions)
pub(crate) fn iter_to_vec(val: &Value) -> Result<Vec<Value>, CompileError> {
    match val {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(tup) => Ok(tup.clone()),
        Value::Str(s) => Ok(s.chars().map(|c| Value::Str(c.to_string())).collect()),
        Value::Dict(map) => Ok(map.keys().map(|k| Value::Str(k.clone())).collect()),
        Value::Object { class, fields } if class == BUILTIN_RANGE => {
            // Range object
            let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
            let end = fields.get("end").and_then(|v| v.as_int().ok()).unwrap_or(0);
            let inclusive = fields.get("inclusive").map(|v| v.truthy()).unwrap_or(false);
            let items: Vec<Value> = if inclusive {
                (start..=end).map(Value::Int).collect()
            } else {
                (start..end).map(Value::Int).collect()
            };
            Ok(items)
        }
        _ => Err(CompileError::Semantic("cannot iterate over this type".into())),
    }
}

/// Helper for binding sequence patterns (Tuple and Array) during comprehensions
pub(crate) fn bind_sequence_pattern(value: &Value, patterns: &[Pattern], env: &mut Env, allow_tuple: bool) -> bool {
    let values = match value {
        Value::Tuple(vals) if allow_tuple => vals,
        Value::Array(vals) => vals,
        _ => return false,
    };

    if patterns.len() != values.len() {
        return false;
    }

    for (pat, val) in patterns.iter().zip(values.iter()) {
        if !bind_pattern(pat, val, env) {
            return false;
        }
    }
    true
}
