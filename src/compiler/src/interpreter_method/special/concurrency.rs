//! Future, Channel, and ThreadPool methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::interpreter_helpers::spawn_future_with_callable;
use crate::interpreter::{eval_arg, Enums, ImplMethods};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;

pub fn handle_future_methods(future: &crate::value::FutureValue, method: &str) -> Result<Option<Value>, CompileError> {
    match method {
        "join" | "await" | "get" => {
            return Ok(Some(future.await_result().map_err(|e| {
                let ctx = ErrorContext::new()
                    .with_code(codes::AWAIT_FAILED)
                    .with_help("ensure the future completed successfully");
                CompileError::semantic_with_context(e, ctx)
            })?));
        }
        "is_ready" => {
            return Ok(Some(Value::Bool(future.is_ready())));
        }
        _ => {}
    }
    Ok(None)
}

/// Handle Channel methods (send, recv, try_recv)
pub fn handle_channel_methods(
    channel: &crate::value::ChannelValue,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match method {
        "send" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            channel.send(val).map_err(|e| CompileError::Semantic(e))?;
            return Ok(Some(Value::Nil));
        }
        "recv" => {
            let val = channel.recv().map_err(|e| CompileError::Semantic(e))?;
            return Ok(Some(val));
        }
        "try_recv" => {
            return Ok(Some(match channel.try_recv() {
                Some(val) => Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(val)),
                },
                None => Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: None,
                },
            }));
        }
        _ => {}
    }
    Ok(None)
}

/// Handle ThreadPool methods (submit)
pub fn handle_threadpool_methods(
    _pool: &crate::value::ThreadPoolValue,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match method {
        "submit" => {
            // pool.submit(func, arg) - submit a task to the pool
            let func_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let arg_val = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let future = spawn_future_with_callable(func_val, arg_val, functions, classes, enums, impl_methods);
            return Ok(Some(Value::Future(future)));
        }
        _ => {}
    }
    Ok(None)
}
