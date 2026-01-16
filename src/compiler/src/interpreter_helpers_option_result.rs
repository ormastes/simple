//! Option and Result helper functions for the interpreter
//!
//! This module contains helper functions for Option and Result type methods:
//! - map, and_then, or_else, filter for Option
//! - map, map_err, and_then, or_else for Result
//! - Message to Value conversion

use crate::error::CompileError;
use crate::value::{Env, OptionVariant, ResultVariant, Value};
use simple_common::actor::Message;
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;

// Import from interpreter module (this file is included via #[path] from collections.rs)
use super::super::super::{eval_arg, evaluate_expr, exec_block, Control, Enums, ImplMethods};

/// Convert a Message to a Value
pub(crate) fn message_to_value(msg: Message) -> Value {
    match msg {
        Message::Value(s) => Value::Str(s),
        Message::Bytes(b) => Value::Str(String::from_utf8_lossy(&b).to_string()),
    }
}

/// Helper: Apply a lambda to a value with the given environment and contexts
/// Returns the result of evaluating the lambda body
fn apply_lambda_to_value(
    val: &Value,
    lambda_arg: Value,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = lambda_arg
    {
        let mut local_env = captured.clone();
        if let Some(param) = params.first() {
            local_env.insert(param.clone(), val.clone());
        }
        evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)
    } else {
        Ok(Value::Nil)
    }
}

/// Generic function to handle Option map/and_then operations on Some variant
/// - mapper: function to apply to the value
/// - wrap_result: function to wrap the result (Some for map, identity for and_then)
fn handle_option_operation<F, W>(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    _mapper: F,
    wrap_result: W,
) -> Result<Value, CompileError>
where
    F: Fn(
        &Value,
        Value,
        &mut HashMap<String, FunctionDef>,
        &mut HashMap<String, ClassDef>,
        &Enums,
        &ImplMethods,
    ) -> Result<Value, CompileError>,
    W: Fn(Value) -> Value,
{
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(wrap_result(result));
        }
    }
    Ok(Value::none())
}

/// Generic function to handle Result map operations on Ok variant
/// - wrap_ok: function to wrap Ok result
/// - wrap_err: function to wrap Err result
fn handle_result_map_operation<WOk, WErr>(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    check_ok: bool,
    wrap_ok: WOk,
    wrap_err: WErr,
) -> Result<Value, CompileError>
where
    WOk: Fn(Value) -> Value,
    WErr: Fn() -> Value,
{
    let is_ok = ResultVariant::from_name(variant) == Some(ResultVariant::Ok);

    if is_ok == check_ok {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(wrap_ok(result));
        }
    }

    // Return the other variant as-is
    Ok(wrap_err())
}

/// Option map: apply lambda to Some value
pub(crate) fn eval_option_map(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    handle_option_operation(
        variant,
        payload,
        args,
        env,
        functions,
        classes,
        enums,
        impl_methods,
        apply_lambda_to_value,
        Value::some,
    )
}

/// Option and_then: flat-map - apply lambda that returns Option to Some value
pub(crate) fn eval_option_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    handle_option_operation(
        variant,
        payload,
        args,
        env,
        functions,
        classes,
        enums,
        impl_methods,
        apply_lambda_to_value,
        |v| v, // Identity - don't wrap result
    )
}

/// Option or_else: if None, call function to get alternative Option
pub(crate) fn eval_option_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        // Return Some(payload) as-is
        return Ok(Value::Enum {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: payload.clone(),
        });
    }
    // None case: call the function to get alternative
    let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
    if let Value::Lambda {
        params: _,
        body,
        env: captured,
    } = func_arg
    {
        return evaluate_expr(&body, &mut captured, functions, classes, enums, impl_methods);
    }
    Ok(Value::none())
}

/// Option filter: if Some and predicate returns true, keep Some; else None
pub(crate) fn eval_option_filter(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func_arg
            {
                let mut local_env = captured.clone();
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), val.as_ref().clone());
                }
                let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                if result.truthy() {
                    return Ok(Value::some(val.as_ref().clone()));
                }
            }
        }
    }
    Ok(Value::none())
}

/// Result map: apply lambda to Ok value
pub(crate) fn eval_result_map(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let is_ok = ResultVariant::from_name(variant) == Some(ResultVariant::Ok);

    if is_ok {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(Value::ok(result));
        }
    }
    // Return Err as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result map_err: apply lambda to Err value
pub(crate) fn eval_result_map_err(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let is_err = ResultVariant::from_name(variant) == Some(ResultVariant::Err);

    if is_err {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(Value::err(result));
        }
    }
    // Return Ok as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result and_then: flat-map - apply lambda that returns Result to Ok value
pub(crate) fn eval_result_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            // Return result as-is (should be Result)
            return apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods);
        }
    }
    // Return Err as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result or_else: if Err, call function to get alternative Result
pub(crate) fn eval_result_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        // Return Ok as-is
        return Ok(Value::Enum {
            enum_name: "Result".to_string(),
            variant: "Ok".to_string(),
            payload: payload.clone(),
        });
    }
    // Err case: call the function with error value
    if let Some(err_val) = payload {
        let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
        if let Value::Lambda {
            params,
            body,
            env: captured,
        } = func_arg
        {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), err_val.as_ref().clone());
            }
            return evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods);
        }
    }
    Ok(Value::err(Value::Nil))
}
