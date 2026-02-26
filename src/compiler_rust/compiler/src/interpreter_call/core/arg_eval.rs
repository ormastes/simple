// Argument evaluation helpers for builtins and mocks
//
// This module provides utilities for evaluating function arguments with defaults
// and type conversions, used by both builtin functions and mock matchers.

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::evaluate_expr;
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Evaluate an argument at a given index, returning a default value if not present
///
/// Uses `handle_method_call_with_self_update` to ensure that method calls
/// on mutable objects (with 'me' methods) are properly persisted back to the environment.
pub(crate) fn eval_arg(
    args: &[Argument],
    index: usize,
    default: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::super::super::handle_method_call_with_self_update;

    if let Some(arg) = args.get(index) {
        // Handle method calls with self-update (e.g., m.call("method", []))
        // This ensures mutations from 'me' methods are persisted back to the environment
        let (value, update) =
            handle_method_call_with_self_update(&arg.value, env, functions, classes, enums, impl_methods)?;
        if let Some((obj_name, new_self)) = update {
            env.insert(obj_name, new_self);
        }
        Ok(value)
    } else {
        Ok(default)
    }
}

/// Evaluate an argument at a given index as an integer, returning a default if not present
///
/// # Arguments
/// * `error_context` - Description of what the argument is for (e.g., "builtin function", "mock matcher")
pub(crate) fn eval_arg_int(
    args: &[Argument],
    index: usize,
    default: i64,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    error_context: &str,
) -> Result<i64, CompileError> {
    let val = eval_arg(
        args,
        index,
        Value::Int(default),
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )?;
    val.as_int().map_err(|_| {
        let ctx = ErrorContext::new()
            .with_code(codes::TYPE_MISMATCH)
            .with_help(format!("{} argument must be an integer", error_context));
        CompileError::semantic_with_context(format!("expected integer value for {}", error_context), ctx)
    })
}
