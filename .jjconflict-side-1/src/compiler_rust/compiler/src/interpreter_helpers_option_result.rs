//! Option and Result helper functions for the interpreter
//!
//! This module contains helper functions for Option and Result type methods:
//! - map, and_then, or_else, filter for Option
//! - map, map_err, and_then, or_else for Result
//! - Message to Value conversion

use std::sync::Arc;
use crate::error::CompileError;
use crate::value::{enum_names, Env, OptionVariant, ResultVariant, Value};
use simple_common::actor::Message;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef};
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

pub(crate) struct OptionResultEvalContext<'a> {
    env: &'a mut Env,
    functions: &'a mut HashMap<String, Arc<FunctionDef>>,
    classes: &'a mut HashMap<String, Arc<ClassDef>>,
    enums: &'a Enums,
    impl_methods: &'a ImplMethods,
}

impl<'a> OptionResultEvalContext<'a> {
    pub(crate) fn new(
        env: &'a mut Env,
        functions: &'a mut HashMap<String, Arc<FunctionDef>>,
        classes: &'a mut HashMap<String, Arc<ClassDef>>,
        enums: &'a Enums,
        impl_methods: &'a ImplMethods,
    ) -> Self {
        Self {
            env,
            functions,
            classes,
            enums,
            impl_methods,
        }
    }
}

/// Helper: Apply a lambda to a value with the given environment and contexts
/// Returns the result of evaluating the lambda body
fn apply_lambda_to_value(
    val: &Value,
    lambda_arg: Value,
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    if let Value::Lambda {
        params,
        body,
        env: captured,
    } = lambda_arg
    {
        let mut local_env = Env::clone(&captured);
        if let Some(param) = params.first() {
            local_env.insert(param.clone(), val.clone());
        }
        evaluate_expr(
            &body,
            &mut local_env,
            ctx.functions,
            ctx.classes,
            ctx.enums,
            ctx.impl_methods,
        )
    } else {
        Ok(Value::Nil)
    }
}

/// Generic function to handle Option map/and_then operations on Some variant
/// - wrap_result: function to wrap the result (Some for map, identity for and_then)
fn handle_option_operation<W>(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
    wrap_result: W,
) -> Result<Value, CompileError>
where
    W: Fn(Value) -> Value,
{
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let lambda = eval_arg(
                args,
                0,
                Value::Nil,
                ctx.env,
                ctx.functions,
                ctx.classes,
                ctx.enums,
                ctx.impl_methods,
            )?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, ctx)?;
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
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
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
            let lambda = eval_arg(
                args,
                0,
                Value::Nil,
                ctx.env,
                ctx.functions,
                ctx.classes,
                ctx.enums,
                ctx.impl_methods,
            )?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, ctx)?;
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
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    handle_option_operation(variant, payload, args, ctx, Value::some)
}

/// Option and_then: flat-map - apply lambda that returns Option to Some value
pub(crate) fn eval_option_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    handle_option_operation(variant, payload, args, ctx, |v| v)
}

/// Option or_else: if None, call function to get alternative Option
pub(crate) fn eval_option_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        // Return Some(payload) as-is
        return Ok(Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::SOME.to_string(),
            payload: payload.clone(),
        });
    }
    // None case: call the function to get alternative
    let func_arg = eval_arg(
        args,
        0,
        Value::Nil,
        ctx.env,
        ctx.functions,
        ctx.classes,
        ctx.enums,
        ctx.impl_methods,
    )?;
    if let Value::Lambda {
        params: _,
        body,
        env: captured,
    } = func_arg
    {
        let mut local_env = Env::clone(&captured);
        return evaluate_expr(
            &body,
            &mut local_env,
            ctx.functions,
            ctx.classes,
            ctx.enums,
            ctx.impl_methods,
        );
    }
    Ok(Value::none())
}

/// Option filter: if Some and predicate returns true, keep Some; else None
pub(crate) fn eval_option_filter(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let func_arg = eval_arg(
                args,
                0,
                Value::Nil,
                ctx.env,
                ctx.functions,
                ctx.classes,
                ctx.enums,
                ctx.impl_methods,
            )?;
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func_arg
            {
                let mut local_env = Env::clone(&captured);
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), val.as_ref().clone());
                }
                let result = evaluate_expr(
                    &body,
                    &mut local_env,
                    ctx.functions,
                    ctx.classes,
                    ctx.enums,
                    ctx.impl_methods,
                )?;
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
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    handle_result_map_operation(variant, payload, args, ctx, true, Value::ok, || Value::Enum {
        enum_name: enum_names::RESULT.to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result map_err: apply lambda to Err value
pub(crate) fn eval_result_map_err(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    handle_result_map_operation(variant, payload, args, ctx, false, Value::err, || Value::Enum {
        enum_name: enum_names::RESULT.to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result and_then: flat-map - apply lambda that returns Result to Ok value
pub(crate) fn eval_result_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        if let Some(val) = payload {
            let lambda = eval_arg(
                args,
                0,
                Value::Nil,
                ctx.env,
                ctx.functions,
                ctx.classes,
                ctx.enums,
                ctx.impl_methods,
            )?;
            // Return result as-is (should be Result)
            return apply_lambda_to_value(val.as_ref(), lambda, ctx);
        }
    }
    // Return Err as-is
    Ok(Value::Enum {
        enum_name: enum_names::RESULT.to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result or_else: if Err, call function to get alternative Result
pub(crate) fn eval_result_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[Argument],
    ctx: &mut OptionResultEvalContext<'_>,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        // Return Ok as-is
        return Ok(Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::OK.to_string(),
            payload: payload.clone(),
        });
    }
    // Err case: call the function with error value
    if let Some(err_val) = payload {
        let func_arg = eval_arg(
            args,
            0,
            Value::Nil,
            ctx.env,
            ctx.functions,
            ctx.classes,
            ctx.enums,
            ctx.impl_methods,
        )?;
        if let Value::Lambda {
            params,
            body,
            env: captured,
        } = func_arg
        {
            let mut local_env = Env::clone(&captured);
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), err_val.as_ref().clone());
            }
            return evaluate_expr(
                &body,
                &mut local_env,
                ctx.functions,
                ctx.classes,
                ctx.enums,
                ctx.impl_methods,
            );
        }
    }
    Ok(Value::err(Value::Nil))
}
