//! Context method dispatch (part of interpreter module)
//!
//! Handles method dispatch for context objects, including method_missing hooks
//! and value-to-expression conversion.

use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, Expr, FunctionDef};
use std::collections::HashMap;

// Import parent interpreter types and functions
use super::interpreter_helpers::try_method_missing;
use super::interpreter_method::find_and_exec_method_with_self;
use super::{evaluate_expr, Enums, ImplMethods, CONTEXT_OBJECT};

pub(super) fn dispatch_context_method(
    ctx: &Value,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Object { class, fields } = ctx {
        // Try to find and execute the method, tracking self updates
        if let Some((result, updated_self)) = find_and_exec_method_with_self(
            method,
            args,
            class.as_str(),
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            // Update the context object with the modified self
            CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(updated_self));
            return Ok(result);
        }
        // Try method_missing hook if direct method not found
        if let Some(result) = try_method_missing(
            method,
            args,
            class.as_str(),
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            return Ok(result);
        }
        return Err(CompileError::Semantic(format!(
            "context object has no method '{}'",
            method
        )));
    }

    let recv_expr = value_to_expr(ctx)?;
    let method_call = Expr::MethodCall {
        receiver: Box::new(recv_expr),
        method: method.to_string(),
        args: args.to_vec(),
    };
    evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
}

fn value_to_expr(val: &Value) -> Result<Expr, CompileError> {
    Ok(match val {
        Value::Int(i) => Expr::Integer(*i),
        Value::Bool(b) => Expr::Bool(*b),
        Value::Str(s) => Expr::String(s.clone()),
        Value::Symbol(s) => Expr::Symbol(s.clone()),
        Value::Nil => Expr::Nil,
        Value::Array(items) => {
            let exprs: Result<Vec<_>, _> = items.iter().map(value_to_expr).collect();
            Expr::Array(exprs?)
        }
        Value::Tuple(items) => {
            let exprs: Result<Vec<_>, _> = items.iter().map(value_to_expr).collect();
            Expr::Tuple(exprs?)
        }
        _ => return Err(CompileError::Semantic("cannot convert value to expression".into())),
    })
}
