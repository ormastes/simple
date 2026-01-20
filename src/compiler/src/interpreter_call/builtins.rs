// Built-in functions for interpreter
// Range, Option, Result, Actor primitives, Futures, Generators, etc.

use super::core::{eval_arg, eval_arg_int};
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    check_effect_violations, create_range_object, evaluate_expr, message_to_value, spawn_actor_with_expr,
    spawn_future_with_callable_and_env, spawn_future_with_expr, ACTOR_INBOX, ACTOR_OUTBOX, GENERATOR_YIELDS,
};
use crate::value::*;
use simple_common::actor::Message;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef, RangeBound};
use simple_runtime::value::diagram_ffi;
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

pub(super) fn eval_builtin(
    name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Diagram tracing for builtin function calls
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call(name);
    }

    match name {
        "range" => {
            // Handle range(n) as range(0, n) and range(start, end)
            let (start, end) = if args.len() == 1 {
                // Single argument: range(n) means range(0, n)
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods, "builtin function")?;
                (0, n)
            } else {
                // Two arguments: range(start, end)
                let start = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods, "builtin function")?;
                let end = eval_arg_int(args, 1, 0, env, functions, classes, enums, impl_methods, "builtin function")?;
                (start, end)
            };
            let inclusive = eval_arg(
                args,
                2,
                Value::Bool(false),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .truthy();
            let bound = if inclusive {
                RangeBound::Inclusive
            } else {
                RangeBound::Exclusive
            };
            Ok(Some(create_range_object(start, end, bound)))
        }
        "Some" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::some(val)))
        }
        "None" => Ok(Some(Value::none())),
        "Ok" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::ok(val)))
        }
        "Err" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::err(val)))
        }
        "len" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Array(a) => Ok(Some(Value::Int(a.len() as i64))),
                Value::Tuple(t) => Ok(Some(Value::Int(t.len() as i64))),
                Value::Dict(d) => Ok(Some(Value::Int(d.len() as i64))),
                Value::Str(s) => Ok(Some(Value::Int(s.len() as i64))),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("len() can only be used with arrays, tuples, dicts, or strings");
                    Err(CompileError::semantic_with_context(
                        "len expects array, tuple, dict, or string argument".to_string(),
                        ctx,
                    ))
                }
            }
        }
        "send" => {
            let target = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("send() requires an actor handle as first argument");
                CompileError::semantic_with_context("send() expects actor handle".to_string(), ctx)
            })?;
            let msg_arg = args.get(1).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("send() requires a message as second argument");
                CompileError::semantic_with_context("send() expects message".to_string(), ctx)
            })?;
            let target_val = evaluate_expr(&target.value, env, functions, classes, enums, impl_methods)?;
            let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Actor(handle) = target_val {
                handle.send(Message::Value(msg_val.to_display_string())).map_err(|e| {
                    // E1201 - Actor Send Failed
                    let ctx = ErrorContext::new()
                        .with_code(codes::ACTOR_SEND_FAILED)
                        .with_help("check that the actor is still running")
                        .with_note(format!("send error: {}", e));
                    CompileError::semantic_with_context("failed to send message to actor".to_string(), ctx)
                })?;
                return Ok(Some(Value::Nil));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("send() requires an actor handle as first argument");
            return Err(CompileError::semantic_with_context(
                "send target must be an actor".to_string(),
                ctx,
            ));
        }
        "recv" => {
            check_effect_violations("recv")?;
            if args.is_empty() {
                let msg = ACTOR_INBOX.with(|cell| {
                    cell.borrow()
                        .as_ref()
                        .ok_or_else(|| {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_CONTEXT)
                                .with_help("recv() must be called within an actor context");
                            CompileError::semantic_with_context("recv() called outside actor".to_string(), ctx)
                        })
                        .and_then(|rx| {
                            rx.lock()
                                .map_err(|_| {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::INVALID_CONTEXT)
                                        .with_help("actor inbox lock was poisoned");
                                    CompileError::semantic_with_context("actor inbox lock poisoned".to_string(), ctx)
                                })
                                .and_then(|receiver| {
                                    receiver.recv_timeout(std::time::Duration::from_secs(5)).map_err(|e| {
                                        // E1202 - Actor Recv Failed
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::ACTOR_RECV_FAILED)
                                            .with_help("check that the actor is still running")
                                            .with_note(format!("recv error: {}", e));
                                        CompileError::semantic_with_context(
                                            "failed to receive message from actor".to_string(),
                                            ctx,
                                        )
                                    })
                                })
                        })
                })?;
                return Ok(Some(message_to_value(msg)));
            } else {
                let handle_val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                if let Value::Actor(handle) = handle_val {
                    let msg = handle.recv_timeout(std::time::Duration::from_secs(5)).map_err(|e| {
                        // E1202 - Actor Recv Failed
                        let ctx = ErrorContext::new()
                            .with_code(codes::ACTOR_RECV_FAILED)
                            .with_help("check that the actor is still running")
                            .with_note(format!("recv error: {}", e));
                        CompileError::semantic_with_context("failed to receive message from actor".to_string(), ctx)
                    })?;
                    return Ok(Some(message_to_value(msg)));
                }
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("recv() requires an actor handle as argument");
                return Err(CompileError::semantic_with_context(
                    "recv expects actor handle".to_string(),
                    ctx,
                ));
            }
        }
        "reply" => {
            let msg_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("reply() requires a message as argument");
                CompileError::semantic_with_context("reply() expects message".to_string(), ctx)
            })?;
            let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
            ACTOR_OUTBOX.with(|cell| {
                cell.borrow()
                    .as_ref()
                    .ok_or_else(|| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_CONTEXT)
                            .with_help("reply() must be called within an actor context");
                        CompileError::semantic_with_context("reply() called outside actor".to_string(), ctx)
                    })
                    .and_then(|tx| {
                        tx.send(Message::Value(msg_val.to_display_string())).map_err(|e| {
                            // E1201 - Actor Send Failed
                            let ctx = ErrorContext::new()
                                .with_code(codes::ACTOR_SEND_FAILED)
                                .with_help("check that the reply channel is still active")
                                .with_note(format!("reply error: {}", e));
                            CompileError::semantic_with_context("failed to send reply to actor".to_string(), ctx)
                        })
                    })
            })?;
            Ok(Some(Value::Nil))
        }
        "join" => {
            check_effect_violations("join")?;
            let handle_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("join() requires an actor handle as argument");
                CompileError::semantic_with_context("join() expects actor handle".to_string(), ctx)
            })?;
            let handle_val = evaluate_expr(&handle_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Actor(handle) = handle_val {
                handle.join().map_err(|e| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::ACTOR_JOIN_FAILED)
                        .with_help("check that the actor completed successfully")
                        .with_note(format!("join error: {}", e));
                    CompileError::semantic_with_context("failed to join actor".to_string(), ctx)
                })?;
                return Ok(Some(Value::Int(1)));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("join() requires an actor handle as argument");
            return Err(CompileError::semantic_with_context(
                "join target must be an actor".to_string(),
                ctx,
            ));
        }
        "spawn" => {
            let inner_expr = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("spawn() requires a thunk (lambda) as argument");
                CompileError::semantic_with_context("spawn() expects a thunk".to_string(), ctx)
            })?;
            Ok(Some(spawn_actor_with_expr(
                &inner_expr.value,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )))
        }
        "spawn_isolated" => {
            let func_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("spawn_isolated() requires a function as argument");
                CompileError::semantic_with_context("spawn_isolated() expects a function".to_string(), ctx)
            })?;
            let func_val = evaluate_expr(&func_arg.value, env, functions, classes, enums, impl_methods)?;
            let arg_val = if args.len() > 1 {
                evaluate_expr(&args[1].value, env, functions, classes, enums, impl_methods)?
            } else {
                Value::Nil
            };
            let future =
                spawn_future_with_callable_and_env(func_val, arg_val, env, functions, classes, enums, impl_methods);
            Ok(Some(Value::Future(future)))
        }
        "async" | "future" => {
            let inner_expr = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("async/future requires an expression as argument");
                CompileError::semantic_with_context("async/future expects an expression".to_string(), ctx)
            })?;
            let future = spawn_future_with_expr(inner_expr.value.clone(), env, functions, classes, enums, impl_methods);
            Ok(Some(Value::Future(future)))
        }
        "is_ready" => {
            let future_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("is_ready() requires a future as argument");
                CompileError::semantic_with_context("is_ready() expects a future".to_string(), ctx)
            })?;
            let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Future(f) = val {
                return Ok(Some(Value::Bool(f.is_ready())));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("is_ready() requires a Future value");
            return Err(CompileError::semantic_with_context(
                "is_ready expects a future".to_string(),
                ctx,
            ));
        }
        "async_mode" => {
            if args.is_empty() {
                let mode = if simple_runtime::is_manual_mode() {
                    "manual"
                } else {
                    "threaded"
                };
                return Ok(Some(Value::Str(mode.to_string())));
            }
            let mode_arg = eval_arg(
                args,
                0,
                Value::Str("threaded".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            match mode_arg {
                Value::Str(s) => {
                    match s.as_str() {
                        "threaded" => simple_runtime::configure_async_mode(simple_runtime::AsyncMode::Threaded),
                        "manual" | "embedded" => {
                            simple_runtime::configure_async_mode(simple_runtime::AsyncMode::Manual)
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("valid async modes are 'threaded' or 'manual'");
                            return Err(CompileError::semantic_with_context(
                                format!("async_mode: invalid mode '{}', expected 'threaded' or 'manual'", s),
                                ctx,
                            ));
                        }
                    }
                    return Ok(Some(Value::Nil));
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("async_mode() requires a string argument");
                    return Err(CompileError::semantic_with_context(
                        "async_mode expects a string".to_string(),
                        ctx,
                    ));
                }
            }
        }
        "async_workers" => {
            let count = eval_arg_int(args, 0, 4, env, functions, classes, enums, impl_methods, "builtin function")?;
            simple_runtime::configure_worker_count(count as usize);
            Ok(Some(Value::Nil))
        }
        "poll_future" => {
            let future_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("poll_future() requires a future as argument");
                CompileError::semantic_with_context("poll_future() expects a future".to_string(), ctx)
            })?;
            let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Future(f) = val {
                return Ok(Some(Value::Bool(f.poll())));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("poll_future() requires a Future value");
            return Err(CompileError::semantic_with_context(
                "poll_future expects a future".to_string(),
                ctx,
            ));
        }
        "poll_all_futures" => {
            let count = simple_runtime::poll_all();
            Ok(Some(Value::Int(count as i64)))
        }
        "pending_futures" => {
            let count = simple_runtime::pending_count();
            Ok(Some(Value::Int(count as i64)))
        }
        "resolved" => {
            let value = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Future(FutureValue::resolved(value))))
        }
        "rejected" => {
            let error = eval_arg(
                args,
                0,
                Value::Str("error".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let error_str = error.to_display_string();
            Ok(Some(Value::Future(FutureValue::rejected(error_str))))
        }
        "generator" => {
            let inner_expr = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("generator() requires a lambda function as argument");
                CompileError::semantic_with_context("generator() expects a lambda".to_string(), ctx)
            })?;
            let val = evaluate_expr(&inner_expr.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda {
                body,
                env: mut captured,
                ..
            } = val
            {
                GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = Some(Vec::new()));
                let _ = evaluate_expr(&body, &mut captured, functions, classes, enums, impl_methods);
                let yields = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
                let gen = GeneratorValue::new_with_values(yields);
                return Ok(Some(Value::Generator(gen)));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("generator() requires a lambda function");
            return Err(CompileError::semantic_with_context(
                "generator expects a lambda".to_string(),
                ctx,
            ));
        }
        "next" => {
            let gen_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("next() requires a generator as argument");
                CompileError::semantic_with_context("next() expects a generator".to_string(), ctx)
            })?;
            let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Generator(gen) = val {
                return Ok(Some(gen.next().unwrap_or(Value::Nil)));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("next() requires a Generator value");
            return Err(CompileError::semantic_with_context(
                "next expects a generator".to_string(),
                ctx,
            ));
        }
        "collect" => {
            let gen_arg = args.get(0).ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("collect() requires a generator or array as argument");
                CompileError::semantic_with_context("collect() expects a generator".to_string(), ctx)
            })?;
            let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Generator(gen) = val {
                return Ok(Some(Value::Array(gen.collect_remaining())));
            }
            if let Value::Array(arr) = val {
                return Ok(Some(Value::Array(arr)));
            }
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("collect() requires a Generator or Array value");
            return Err(CompileError::semantic_with_context(
                "collect expects a generator or array".to_string(),
                ctx,
            ));
        }
        "ThreadPool" => {
            let workers = args
                .iter()
                .find_map(|arg| {
                    if arg.name.as_deref() == Some("workers") {
                        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                            .ok()
                            .and_then(|v| v.as_int().ok())
                            .map(|n| n as usize)
                    } else {
                        None
                    }
                })
                .unwrap_or(4);
            Ok(Some(Value::ThreadPool(ThreadPoolValue::new(workers))))
        }
        _ => Ok(None),
    }
}

