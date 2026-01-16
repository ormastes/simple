// Built-in functions for interpreter
// Range, Option, Result, Actor primitives, Futures, Generators, etc.

use crate::error::CompileError;
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
            let start = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let end = eval_arg_int(args, 1, 0, env, functions, classes, enums, impl_methods)?;
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
                _ => Err(semantic_err!("len expects array, tuple, dict, or string")),
            }
        }
        "send" => {
            let target = args.get(0).ok_or_else(|| semantic_err!("send expects actor handle"))?;
            let msg_arg = args.get(1).ok_or_else(|| semantic_err!("send expects message"))?;
            let target_val = evaluate_expr(&target.value, env, functions, classes, enums, impl_methods)?;
            let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Actor(handle) = target_val {
                handle
                    .send(Message::Value(msg_val.to_display_string()))
                    .map_err(|e| semantic_err!("{}", e))?;
                return Ok(Some(Value::Nil));
            }
            bail_semantic!("send target must be actor");
        }
        "recv" => {
            check_effect_violations("recv")?;
            if args.is_empty() {
                let msg = ACTOR_INBOX.with(|cell| {
                    cell.borrow()
                        .as_ref()
                        .ok_or_else(|| semantic_err!("recv called outside actor without handle"))
                        .and_then(|rx| {
                            rx.lock()
                                .map_err(|_| semantic_err!("actor inbox lock poisoned"))
                                .and_then(|receiver| {
                                    receiver
                                        .recv_timeout(std::time::Duration::from_secs(5))
                                        .map_err(|e| semantic_err!("recv timeout: {}", e))
                                })
                        })
                })?;
                return Ok(Some(message_to_value(msg)));
            } else {
                let handle_val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                if let Value::Actor(handle) = handle_val {
                    let msg = handle
                        .recv_timeout(std::time::Duration::from_secs(5))
                        .map_err(|e| semantic_err!("{}", e))?;
                    return Ok(Some(message_to_value(msg)));
                }
                bail_semantic!("recv expects actor handle");
            }
        }
        "reply" => {
            let msg_arg = args.get(0).ok_or_else(|| semantic_err!("reply expects message"))?;
            let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
            ACTOR_OUTBOX.with(|cell| {
                cell.borrow()
                    .as_ref()
                    .ok_or_else(|| semantic_err!("reply called outside actor"))
                    .and_then(|tx| {
                        tx.send(Message::Value(msg_val.to_display_string()))
                            .map_err(|e| semantic_err!("reply failed: {}", e))
                    })
            })?;
            Ok(Some(Value::Nil))
        }
        "join" => {
            check_effect_violations("join")?;
            let handle_arg = args.get(0).ok_or_else(|| semantic_err!("join expects actor handle"))?;
            let handle_val = evaluate_expr(&handle_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Actor(handle) = handle_val {
                handle.join().map_err(|e| semantic_err!("{}", e))?;
                return Ok(Some(Value::Int(1)));
            }
            bail_semantic!("join target must be actor");
        }
        "spawn" => {
            let inner_expr = args.get(0).ok_or_else(|| semantic_err!("spawn expects a thunk"))?;
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
            let func_arg = args
                .get(0)
                .ok_or_else(|| semantic_err!("spawn_isolated expects a function"))?;
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
            let inner_expr = args
                .get(0)
                .ok_or_else(|| semantic_err!("async expects an expression"))?;
            let future = spawn_future_with_expr(inner_expr.value.clone(), env, functions, classes, enums, impl_methods);
            Ok(Some(Value::Future(future)))
        }
        "is_ready" => {
            let future_arg = args.get(0).ok_or_else(|| semantic_err!("is_ready expects a future"))?;
            let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Future(f) = val {
                return Ok(Some(Value::Bool(f.is_ready())));
            }
            bail_semantic!("is_ready expects a future");
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
                        _ => bail_semantic!("async_mode expects 'threaded' or 'manual'"),
                    }
                    return Ok(Some(Value::Nil));
                }
                _ => bail_semantic!("async_mode expects a string"),
            }
        }
        "async_workers" => {
            let count = eval_arg_int(args, 0, 4, env, functions, classes, enums, impl_methods)?;
            simple_runtime::configure_worker_count(count as usize);
            Ok(Some(Value::Nil))
        }
        "poll_future" => {
            let future_arg = args
                .get(0)
                .ok_or_else(|| semantic_err!("poll_future expects a future"))?;
            let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Future(f) = val {
                return Ok(Some(Value::Bool(f.poll())));
            }
            bail_semantic!("poll_future expects a future");
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
            let inner_expr = args.get(0).ok_or_else(|| semantic_err!("generator expects a lambda"))?;
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
            bail_semantic!("generator expects a lambda");
        }
        "next" => {
            let gen_arg = args.get(0).ok_or_else(|| semantic_err!("next expects a generator"))?;
            let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Generator(gen) = val {
                return Ok(Some(gen.next().unwrap_or(Value::Nil)));
            }
            bail_semantic!("next expects a generator");
        }
        "collect" => {
            let gen_arg = args
                .get(0)
                .ok_or_else(|| semantic_err!("collect expects a generator"))?;
            let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
            if let Value::Generator(gen) = val {
                return Ok(Some(Value::Array(gen.collect_remaining())));
            }
            if let Value::Array(arr) = val {
                return Ok(Some(Value::Array(arr)));
            }
            bail_semantic!("collect expects a generator or array");
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

fn eval_arg(
    args: &[Argument],
    index: usize,
    default: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Some(arg) = args.get(index) {
        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
    } else {
        Ok(default)
    }
}

fn eval_arg_int(
    args: &[Argument],
    index: usize,
    default: i64,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
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
    val.as_int().map_err(|_| semantic_err!("expected integer"))
}
