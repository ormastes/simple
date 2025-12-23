//! Call expression evaluation

use std::collections::HashMap;
use std::sync::{Arc, atomic::AtomicBool};
use simple_parser::ast::{Expr, Argument};
use crate::value::{Value, BUILTIN_CHANNEL, ChannelValue, FutureValue, GeneratorValue, Message, ThreadPoolValue};
use crate::{ClassDef, CompileError, Enums, FunctionDef, ImplMethods};
use crate::interpreter::env::Env;
use crate::interpreter::expressions::evaluate_expr;
use crate::interpreter::{ACTOR_INBOX, ACTOR_OUTBOX, EXTERN_FUNCTIONS, CONTEXT_OBJECT, GENERATOR_YIELDS, METHOD_SELF, METHOD_NEW, DI_SINGLETONS};
use crate::interpreter::call_extern_function;
use crate::interpreter::dispatch_context_method;
use crate::interpreter::message_to_value;
use crate::interpreter::spawn_actor_with_expr;
use crate::interpreter::spawn_future_with_expr;
use crate::interpreter::spawn_future_with_callable_and_env;
use crate::interpreter::effects::check_effect_violations;
use crate::interpreter::ranges::create_range_object;
use crate::interpreter::eval_arg;
use crate::interpreter::eval_arg_int;
use crate::interpreter::exec_block_closure;
use crate::interpreter::unit_types::{is_unit_type, validate_unit_type};
use crate::{bail_semantic, semantic_err};

use super::bdd_state::*;
use super::binding::*;
use super::execution::*;
use super::injection::*;

/// Execute a block value (lambda or block closure)
pub(super) fn exec_block_value(
    block: Value,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match block {
        Value::Lambda { params, body, env: captured } => {
            exec_lambda(&params, &body, &[], env, &captured, functions, classes, enums, impl_methods)
        }
        Value::BlockClosure { nodes, env: captured } => {
            exec_block_closure(&nodes, &captured, functions, classes, enums, impl_methods)
        }
        _ => Ok(Value::Nil),
    }
}

pub(super) fn evaluate_call(
    callee: &Box<Expr>,
    args: &[Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Expr::Identifier(name) = callee.as_ref() {
        match name.as_str() {
            "range" => {
                let start = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let end = eval_arg_int(args, 1, 0, env, functions, classes, enums, impl_methods)?;
                let inclusive = eval_arg(args, 2, Value::Bool(false), env, functions, classes, enums, impl_methods)?.truthy();
                let bound = if inclusive { simple_parser::ast::RangeBound::Inclusive } else { simple_parser::ast::RangeBound::Exclusive };
                return Ok(create_range_object(start, end, bound));
            }
            "Some" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::some(val));
            }
            "None" => {
                return Ok(Value::none());
            }
            "Ok" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::ok(val));
            }
            "Err" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::err(val));
            }
            "len" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return match val {
                    Value::Array(a) => Ok(Value::Int(a.len() as i64)),
                    Value::Tuple(t) => Ok(Value::Int(t.len() as i64)),
                    Value::Dict(d) => Ok(Value::Int(d.len() as i64)),
                    Value::Str(s) => Ok(Value::Int(s.len() as i64)),
                    _ => Err(semantic_err!("len expects array, tuple, dict, or string")),
                };
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
                    return Ok(Value::Nil);
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
                    return Ok(message_to_value(msg));
                } else {
                    let handle_val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                    if let Value::Actor(handle) = handle_val {
                        let msg = handle.recv_timeout(std::time::Duration::from_secs(5))
                            .map_err(|e| semantic_err!("{}", e))?;
                        return Ok(message_to_value(msg));
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
                return Ok(Value::Nil);
            }
            "join" => {
                check_effect_violations("join")?;
                let handle_arg = args.get(0).ok_or_else(|| semantic_err!("join expects actor handle"))?;
                let handle_val = evaluate_expr(&handle_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Actor(handle) = handle_val {
                    handle.join().map_err(|e| semantic_err!("{}", e))?;
                    return Ok(Value::Nil);
                }
                bail_semantic!("join target must be actor");
            }
            "spawn" => {
                let inner_expr = args.get(0).ok_or_else(|| semantic_err!("spawn expects a thunk"))?;
                return Ok(spawn_actor_with_expr(&inner_expr.value, env, functions, classes, enums, impl_methods));
            }
            "spawn_isolated" => {
                // spawn_isolated(func, arg) - spawns a function in a new thread with isolated data
                let func_arg = args.get(0).ok_or_else(|| semantic_err!("spawn_isolated expects a function"))?;
                let func_val = evaluate_expr(&func_arg.value, env, functions, classes, enums, impl_methods)?;
                let arg_val = if args.len() > 1 {
                    evaluate_expr(&args[1].value, env, functions, classes, enums, impl_methods)?
                } else {
                    Value::Nil
                };
                // Use spawn_future_with_callable_and_env to capture outer environment
                let future = spawn_future_with_callable_and_env(func_val, arg_val, env, functions, classes, enums, impl_methods);
                return Ok(Value::Future(future));
            }
            "async" | "future" => {
                let inner_expr = args.get(0).ok_or_else(|| semantic_err!("async expects an expression"))?;
                let future = spawn_future_with_expr(inner_expr.value.clone(), env, functions, classes, enums, impl_methods);
                return Ok(Value::Future(future));
            }
            "is_ready" => {
                let future_arg = args.get(0).ok_or_else(|| semantic_err!("is_ready expects a future"))?;
                let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Future(f) = val {
                    return Ok(Value::Bool(f.is_ready()));
                }
                bail_semantic!("is_ready expects a future");
            }
            // Async configuration builtins
            "async_mode" => {
                // async_mode() - Get current mode as string
                // async_mode("threaded") - Set threaded mode
                // async_mode("manual") - Set manual mode (for embedded)
                if args.is_empty() {
                    let mode = if simple_runtime::is_manual_mode() {
                        "manual"
                    } else {
                        "threaded"
                    };
                    return Ok(Value::Str(mode.to_string()));
                }
                let mode_arg = eval_arg(args, 0, Value::Str("threaded".to_string()), env, functions, classes, enums, impl_methods)?;
                match mode_arg {
                    Value::Str(s) => {
                        match s.as_str() {
                            "threaded" => simple_runtime::configure_async_mode(simple_runtime::AsyncMode::Threaded),
                            "manual" | "embedded" => simple_runtime::configure_async_mode(simple_runtime::AsyncMode::Manual),
                            _ => bail_semantic!("async_mode expects 'threaded' or 'manual'"),
                        }
                        return Ok(Value::Nil);
                    }
                    _ => bail_semantic!("async_mode expects a string"),
                }
            }
            "async_workers" => {
                // async_workers(n) - Set number of worker threads (only for threaded mode)
                let count = eval_arg_int(args, 0, 4, env, functions, classes, enums, impl_methods)?;
                simple_runtime::configure_worker_count(count as usize);
                return Ok(Value::Nil);
            }
            "poll_future" => {
                // poll_future(f) - Poll a future manually (for embedded mode)
                let future_arg = args.get(0).ok_or_else(|| semantic_err!("poll_future expects a future"))?;
                let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Future(f) = val {
                    return Ok(Value::Bool(f.poll()));
                }
                bail_semantic!("poll_future expects a future");
            }
            "poll_all_futures" => {
                // poll_all_futures() - Poll all pending futures (for embedded mode)
                let count = simple_runtime::poll_all();
                return Ok(Value::Int(count as i64));
            }
            "pending_futures" => {
                // pending_futures() - Get number of pending futures (for embedded mode)
                let count = simple_runtime::pending_count();
                return Ok(Value::Int(count as i64));
            }
            "resolved" => {
                // resolved(value) - Create an already-resolved future
                let value = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Future(FutureValue::resolved(value)));
            }
            "rejected" => {
                // rejected(error) - Create an already-rejected future
                let error = eval_arg(args, 0, Value::Str("error".to_string()), env, functions, classes, enums, impl_methods)?;
                let error_str = error.to_display_string();
                return Ok(Value::Future(FutureValue::rejected(error_str)));
            }
            "generator" => {
                let inner_expr = args.get(0).ok_or_else(|| semantic_err!("generator expects a lambda"))?;
                let val = evaluate_expr(&inner_expr.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda { body, env: captured, .. } = val {
                    GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = Some(Vec::new()));
                    let _ = evaluate_expr(&body, &captured, functions, classes, enums, impl_methods);
                    let yields = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
                    let gen = GeneratorValue::new_with_values(yields);
                    return Ok(Value::Generator(gen));
                }
                bail_semantic!("generator expects a lambda");
            }
            "next" => {
                let gen_arg = args.get(0).ok_or_else(|| semantic_err!("next expects a generator"))?;
                let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Generator(gen) = val {
                    return Ok(gen.next().unwrap_or(Value::Nil));
                }
                bail_semantic!("next expects a generator");
            }
            "collect" => {
                let gen_arg = args.get(0).ok_or_else(|| semantic_err!("collect expects a generator"))?;
                let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Generator(gen) = val {
                    return Ok(Value::Array(gen.collect_remaining()));
                }
                if let Value::Array(arr) = val {
                    return Ok(Value::Array(arr));
                }
                bail_semantic!("collect expects a generator or array");
            }
            "ThreadPool" => {
                // ThreadPool(workers=N) - create a thread pool
                let workers = args.iter().find_map(|arg| {
                    if arg.name.as_deref() == Some("workers") {
                        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                            .ok()
                            .and_then(|v| v.as_int().ok())
                            .map(|n| n as usize)
                    } else {
                        None
                    }
                }).unwrap_or(4); // default to 4 workers
                return Ok(Value::ThreadPool(ThreadPoolValue::new(workers)));
            }
            // BDD testing builtins
            "describe" | "context" => {
                // describe(name, block) or describe "name": block
                // context can also take a symbol to reference a context_def
                let first_arg = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;

                // Check if it's a symbol (context_def reference) or a string (description)
                let (name_str, ctx_def_blocks) = match &first_arg {
                    Value::Symbol(ctx_name) => {
                        // Reference to a context_def
                        let blocks = BDD_CONTEXT_DEFS.with(|cell| {
                            cell.borrow().get(ctx_name).cloned()
                        });
                        (format!("with {}", ctx_name), blocks)
                    }
                    Value::Str(s) => (s.clone(), None),
                    _ => ("unnamed".to_string(), None),
                };

                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Get current indent level
                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                let indent_str = "  ".repeat(indent);

                // Print describe/context name
                println!("{}{}", indent_str, name_str);

                // Increase indent for nested blocks
                BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

                // If this is a context_def reference, execute its givens first
                if let Some(ctx_blocks) = ctx_def_blocks {
                    for ctx_block in ctx_blocks {
                        exec_block_value(ctx_block, env, functions, classes, enums, impl_methods)?;
                    }
                }

                // Execute the block
                let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

                // Note: lazy values persist within the describe block
                // They'll be overwritten if a sibling context defines the same name

                // Restore indent
                BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

                // Print summary and clear lazy values at top level only
                if indent == 0 {
                    // Clear lazy values when exiting the top-level describe
                    BDD_LAZY_VALUES.with(|cell| cell.borrow_mut().clear());
                    let (passed, failed) = BDD_COUNTS.with(|cell| {
                        let counts = cell.borrow();
                        (counts.0, counts.1)
                    });
                    let total = passed + failed;
                    println!();
                    if failed == 0 {
                        println!("\x1b[32m{} example{}, 0 failures\x1b[0m", total, if total == 1 { "" } else { "s" });
                    } else {
                        println!("\x1b[31m{} example{}, {} failure{}\x1b[0m",
                            total, if total == 1 { "" } else { "s" },
                            failed, if failed == 1 { "" } else { "s" });
                    }
                    // Reset counts for next describe block
                    BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
                }

                return result;
            }
            "it" => {
                // it(name, block) - runs a single test example
                let name = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Reset expect failure and message for this test, mark we're inside an it block
                BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
                BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
                BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = true);

                // Reset lazy value cache for this test (each test gets fresh memoization)
                BDD_LAZY_VALUES.with(|cell| {
                    for (_, (_, cached)) in cell.borrow_mut().iter_mut() {
                        *cached = None;
                    }
                });

                // Execute before_each hooks from all levels (outer to inner)
                let before_hooks: Vec<Value> = BDD_BEFORE_EACH.with(|cell| {
                    cell.borrow().iter().flat_map(|level| level.clone()).collect()
                });
                for hook in before_hooks {
                    exec_block_value(hook, env, functions, classes, enums, impl_methods)?;
                }

                // Execute the test block
                let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

                // Execute after_each hooks from all levels (inner to outer - reverse order)
                let after_hooks: Vec<Value> = BDD_AFTER_EACH.with(|cell| {
                    cell.borrow().iter().rev().flat_map(|level| level.clone()).collect()
                });
                for hook in after_hooks {
                    let _ = exec_block_value(hook, env, functions, classes, enums, impl_methods);
                }

                // No longer inside it block
                BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);

                // Check if any expect failed
                let failed = BDD_EXPECT_FAILED.with(|cell| *cell.borrow());
                let failure_msg = BDD_FAILURE_MSG.with(|cell| cell.borrow().clone());
                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                let indent_str = "  ".repeat(indent);

                if failed {
                    println!("{}\x1b[31m✗ {}\x1b[0m", indent_str, name_str);
                    if let Some(msg) = failure_msg {
                        println!("{}  \x1b[31m{}\x1b[0m", indent_str, msg);
                    }
                    BDD_COUNTS.with(|cell| cell.borrow_mut().1 += 1);
                } else {
                    println!("{}\x1b[32m✓ {}\x1b[0m", indent_str, name_str);
                    BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);
                }

                return result;
            }
            "skip" => {
                // skip(name, block) - marks a test as skipped (not executed)
                let name = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                // Don't evaluate the block - just mark as skipped

                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                let indent_str = "  ".repeat(indent);

                // Print skipped test in yellow
                println!("{}\x1b[33m○ {} (skipped)\x1b[0m", indent_str, name_str);

                // Count as passed (skipped tests don't count as failures)
                BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);

                return Ok(Value::Nil);
            }
            "expect" => {
                // expect(condition) - BDD assertion, prints failure if false
                let condition = eval_arg(args, 0, Value::Bool(false), env, functions, classes, enums, impl_methods)?;
                let passed = condition.truthy();

                let inside_it = BDD_INSIDE_IT.with(|cell| *cell.borrow());

                if !passed {
                    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);

                    // Build failure message by inspecting the expression
                    let failure_msg = if !args.is_empty() {
                        build_expect_failure_message(&args[0].value, env, functions, classes, enums, impl_methods)
                    } else {
                        "expected true, got false".to_string()
                    };

                    // Only print/count if not inside an "it" block (standalone expect)
                    if !inside_it {
                        let indent = BDD_INDENT.with(|cell| *cell.borrow());
                        if indent > 0 {
                            let indent_str = "  ".repeat(indent);
                            println!("{}\x1b[31m✗ expectation failed\x1b[0m", indent_str);
                            println!("{}  \x1b[31m{}\x1b[0m", indent_str, failure_msg);
                            BDD_COUNTS.with(|cell| cell.borrow_mut().1 += 1);
                        }
                    } else {
                        // Store failure message for the it block to display
                        BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(failure_msg));
                    }
                } else if !inside_it {
                    // Standalone expect that passes (not inside it block)
                    let indent = BDD_INDENT.with(|cell| *cell.borrow());
                    if indent > 0 {
                        let indent_str = "  ".repeat(indent);
                        println!("{}\x1b[32m✓ expectation passed\x1b[0m", indent_str);
                        BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);
                    }
                }

                return Ok(Value::Bool(passed));
            }
            // TEST-010: shared_examples - define reusable example groups
            "shared_examples" => {
                let name = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Store the block in the shared examples registry
                BDD_SHARED_EXAMPLES.with(|cell| {
                    cell.borrow_mut().insert(name_str.clone(), block);
                });

                return Ok(Value::Nil);
            }
            // TEST-011: it_behaves_like - include shared examples
            "it_behaves_like" | "include_examples" => {
                let name = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };

                // Look up and execute the shared examples block
                let block = BDD_SHARED_EXAMPLES.with(|cell| {
                    cell.borrow().get(&name_str).cloned()
                });

                match block {
                    Some(block) => {
                        // Create a nested context for the shared examples
                        let indent = BDD_INDENT.with(|cell| *cell.borrow());
                        let indent_str = "  ".repeat(indent);
                        println!("{}behaves like {}", indent_str, name_str);

                        BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);
                        let result = exec_block_value(block, env, functions, classes, enums, impl_methods);
                        BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

                        return result;
                    }
                    None => {
                        bail_semantic!("Shared example '{}' not found", name_str);
                    }
                }
            }
            // before_each - add a hook to run before each it block
            "before_each" => {
                let block = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

                BDD_BEFORE_EACH.with(|cell| {
                    let mut hooks = cell.borrow_mut();
                    if let Some(current) = hooks.last_mut() {
                        current.push(block);
                    }
                });

                return Ok(Value::Nil);
            }
            // after_each - add a hook to run after each it block
            "after_each" => {
                let block = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

                BDD_AFTER_EACH.with(|cell| {
                    let mut hooks = cell.borrow_mut();
                    if let Some(current) = hooks.last_mut() {
                        current.push(block);
                    }
                });

                return Ok(Value::Nil);
            }
            // context_def - define a reusable context
            "context_def" => {
                let name = eval_arg(args, 0, Value::Symbol("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Collect givens by executing the block in a special mode
                // For now, just store the block - we'll execute it when referenced
                BDD_CONTEXT_DEFS.with(|cell| {
                    cell.borrow_mut().insert(name_str, vec![block]);
                });

                return Ok(Value::Nil);
            }
            // given_lazy - define a lazy fixture
            "given_lazy" => {
                let name = eval_arg(args, 0, Value::Symbol("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Store the block (not evaluated yet) with no cached value
                BDD_LAZY_VALUES.with(|cell| {
                    cell.borrow_mut().insert(name_str, (block, None));
                });

                return Ok(Value::Nil);
            }
            // given - define an eager fixture (runs immediately)
            "given" => {
                let first_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Check if it's a symbol (context reference) or a block
                match &first_arg {
                    Value::Symbol(ctx_name) => {
                        // Reference to a context_def - execute its givens
                        let ctx_block = BDD_CONTEXT_DEFS.with(|cell| {
                            cell.borrow().get(ctx_name).cloned()
                        });
                        if let Some(blocks) = ctx_block {
                            for block in blocks {
                                exec_block_value(block, env, functions, classes, enums, impl_methods)?;
                            }
                        }
                    }
                    _ => {
                        // It's a block - check if there's a second argument (named given)
                        if args.len() >= 2 {
                            // named given: given :name, \: block
                            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                            exec_block_value(block, env, functions, classes, enums, impl_methods)?;
                        } else {
                            // unnamed given: given { block }
                            exec_block_value(first_arg, env, functions, classes, enums, impl_methods)?;
                        }
                    }
                }

                return Ok(Value::Nil);
            }
            // TEST-012: let_lazy - define a truly lazy memoized value
            "let_lazy" => {
                let name = eval_arg(args, 0, Value::Symbol("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Store the block (not evaluated yet) with no cached value
                BDD_LAZY_VALUES.with(|cell| {
                    cell.borrow_mut().insert(name_str, (block, None));
                });

                return Ok(Value::Nil);
            }
            // get_let - get a lazy memoized value (evaluates on first access)
            "get_let" => {
                let name = eval_arg(args, 0, Value::Symbol("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };

                // Check if we have a cached value
                let cached = BDD_LAZY_VALUES.with(|cell| {
                    cell.borrow().get(&name_str).cloned()
                });

                match cached {
                    Some((_block, Some(value))) => {
                        // Already evaluated - return cached value
                        return Ok(value);
                    }
                    Some((block, None)) => {
                        // Not yet evaluated - evaluate and cache
                        let value = exec_block_value(block.clone(), env, functions, classes, enums, impl_methods)?;
                        BDD_LAZY_VALUES.with(|cell| {
                            if let Some(entry) = cell.borrow_mut().get_mut(&name_str) {
                                entry.1 = Some(value.clone());
                            }
                        });
                        return Ok(value);
                    }
                    None => {
                        bail_semantic!("No lazy value found for '{}'", name_str);
                    }
                }
            }
            // has_let - check if a lazy value exists
            "has_let" => {
                let name = eval_arg(args, 0, Value::Symbol("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };

                let exists = BDD_LAZY_VALUES.with(|cell| {
                    cell.borrow().contains_key(&name_str)
                });

                return Ok(Value::Bool(exists));
            }
            // ================================================================
            // Mock Library Builtins (MOCK-001 through MOCK-012)
            // ================================================================
            // mock(type_name) - Create a mock object
            "mock" => {
                let type_name = eval_arg(args, 0, Value::Str("Mock".to_string()), env, functions, classes, enums, impl_methods)?;
                let type_str = match &type_name {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => "Mock".to_string(),
                };
                return Ok(Value::Mock(crate::value::MockValue::new(type_str)));
            }
            // spy(type_name) - Create a spy object
            "spy" => {
                let type_name = eval_arg(args, 0, Value::Str("Spy".to_string()), env, functions, classes, enums, impl_methods)?;
                let type_str = match &type_name {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => "Spy".to_string(),
                };
                return Ok(Value::Mock(crate::value::MockValue::new_spy(type_str)));
            }
            // any() - Match any argument
            "any" => {
                return Ok(Value::Matcher(crate::value::MatcherValue::Any));
            }
            // eq(value) / be(value) - Match exact value (BDD matchers)
            "eq" | "be" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(val))));
            }
            // be_gt(n) - BDD alias for gt (greater than)
            "be_gt" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::GreaterThan(n)));
            }
            // be_lt(n) - BDD alias for lt (less than)
            "be_lt" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::LessThan(n)));
            }
            // be_nil - Match nil/None value
            "be_nil" => {
                return Ok(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(Value::Nil))));
            }
            // be_empty - Match empty collection/string
            "be_empty" => {
                return Ok(Value::Matcher(crate::value::MatcherValue::Custom(Box::new(Value::Nil)))); // Placeholder
            }
            // include(value) - Match collection/string containing value
            "include" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                match &val {
                    Value::Str(s) => return Ok(Value::Matcher(crate::value::MatcherValue::Contains(s.clone()))),
                    _ => return Ok(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(val)))),
                }
            }
            // start_with(s) - BDD alias for starts_with
            "start_with" => {
                let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let s_str = match &s {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::StartsWith(s_str)));
            }
            // end_with(s) - BDD alias for ends_with
            "end_with" => {
                let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let s_str = match &s {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::EndsWith(s_str)));
            }
            // gt(n) - Match value greater than n
            "gt" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::GreaterThan(n)));
            }
            // lt(n) - Match value less than n
            "lt" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::LessThan(n)));
            }
            // gte(n) - Match value greater than or equal to n
            "gte" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::GreaterOrEqual(n)));
            }
            // lte(n) - Match value less than or equal to n
            "lte" => {
                let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Matcher(crate::value::MatcherValue::LessOrEqual(n)));
            }
            // contains(s) - Match string containing substring
            "contains" => {
                let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let s_str = match &s {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::Contains(s_str)));
            }
            // starts_with(s) - Match string starting with prefix
            "starts_with" => {
                let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let s_str = match &s {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::StartsWith(s_str)));
            }
            // ends_with(s) - Match string ending with suffix
            "ends_with" => {
                let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let s_str = match &s {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::EndsWith(s_str)));
            }
            // of_type(type_name) - Match value of specific type
            "of_type" => {
                let type_name = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
                let type_str = match &type_name {
                    Value::Str(s) => s.clone(),
                    _ => "".to_string(),
                };
                return Ok(Value::Matcher(crate::value::MatcherValue::OfType(type_str)));
            }
            _ => {
                // Check env first for decorated functions and closures
                if let Some(val) = env.get(name) {
                    match val {
                        Value::Function { def, captured_env, .. } => {
                            // Use captured_env for closure semantics
                            return exec_function_with_captured_env(&def, args, env, captured_env, functions, classes, enums, impl_methods);
                        }
                        Value::Lambda { params, body, env: captured } => {
                            return exec_lambda(params, body, args, env, captured, functions, classes, enums, impl_methods);
                        }
                        _ => {}
                    }
                }
                if let Some(func) = functions.get(name) {
                    return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                }
                let is_extern = EXTERN_FUNCTIONS.with(|cell| cell.borrow().contains(name));
                if is_extern {
                    return call_extern_function(name, args, env, functions, classes, enums, impl_methods);
                }
                let context_obj = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
                if let Some(ctx) = context_obj {
                    return dispatch_context_method(&ctx, name, args, env, functions, classes, enums, impl_methods);
                }
            }
        }
    }
    if let Expr::FieldAccess { receiver, field } = callee.as_ref() {
        if let Expr::Identifier(module_name) = receiver.as_ref() {
            if let Some(func) = functions.get(field) {
                return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(field) {
                return instantiate_class(field, args, env, functions, classes, enums, impl_methods);
            } else if let Some(func) = env.get(field) {
                if let Value::Function { def, captured_env, .. } = func {
                    return exec_function_with_captured_env(def, args, env, captured_env, functions, classes, enums, impl_methods);
                }
            }
            bail_semantic!("unknown symbol {}.{}", module_name, field);
        }
    }
    if let Expr::Path(segments) = callee.as_ref() {
        if segments.len() == 2 {
            let type_name = &segments[0];
            let method_name = &segments[1];

            // Check if it's an enum variant constructor
            if let Some(enum_def) = enums.get(type_name) {
                if enum_def.variants.iter().any(|v| &v.name == method_name) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        // Single payload - store directly
                        Some(Box::new(evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?))
                    } else {
                        // Multiple payloads - store as tuple
                        let mut values = Vec::new();
                        for arg in args {
                            values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        Some(Box::new(Value::Tuple(values)))
                    };
                    return Ok(Value::Enum {
                        enum_name: type_name.clone(),
                        variant: method_name.clone(),
                        payload,
                    });
                }
            }

            // Check for associated function call: Type::method(args)
            // Look up in impl_methods for the type
            if let Some(methods) = impl_methods.get(type_name) {
                if let Some(func) = methods.iter().find(|m| m.name == *method_name) {
                    // Associated function - no self context
                    return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                }
            }

            // Check for class associated function (static method in class)
            if let Some(class_def) = classes.get(type_name) {
                if let Some(func) = class_def.methods.iter().find(|m| m.name == *method_name) {
                    // Static class method - no self context
                    return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                }
            }

            // Legacy fallbacks
            if let Some(func) = functions.get(method_name) {
                return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(method_name) {
                return instantiate_class(method_name, args, env, functions, classes, enums, impl_methods);
            }
        }
        bail_semantic!("unsupported path call: {:?}", segments);
    }

    // Handle generic type constructors like Channel[int]()
    if let Expr::Index { receiver, .. } = callee.as_ref() {
        if let Expr::Identifier(name) = receiver.as_ref() {
            if name == BUILTIN_CHANNEL {
                // Create a channel - ignore the type parameter for runtime (type erasure)
                // Check for buffer argument
                let buffer_size = args.iter().find_map(|arg| {
                    if arg.name.as_deref() == Some("buffer") {
                        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                            .ok()
                            .and_then(|v| v.as_int().ok())
                            .map(|n| n as usize)
                    } else {
                        None
                    }
                });

                let channel = if let Some(size) = buffer_size {
                    ChannelValue::with_buffer(size)
                } else {
                    ChannelValue::new()
                };
                return Ok(Value::Channel(channel));
            }
        }
    }

    let callee_val = evaluate_expr(callee, env, functions, classes, enums, impl_methods)?;
    match callee_val {
        Value::Lambda { params, body, env: captured } => {
            exec_lambda(&params, &body, args, env, &captured, functions, classes, enums, impl_methods)
        }
        Value::BlockClosure { nodes, env: captured } => {
            // Execute block closure - a sequence of statements, return last value
            exec_block_closure(&nodes, &captured, functions, classes, enums, impl_methods)
        }
        Value::Function { def, captured_env, .. } => {
            // Call a first-class function value with captured environment for closure
            exec_function_with_captured_env(&def, args, env, &captured_env, functions, classes, enums, impl_methods)
        }
        Value::NativeFunction(native) => {
            let evaluated: Vec<Value> = args
                .iter()
                .map(|a| {
                    if a.name.is_some() {
                        return Err(CompileError::Semantic(
                            "native function does not support named arguments".into(),
                        ));
                    }
                    evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)
                })
                .collect::<Result<Vec<_>, _>>()?;
            (native.func)(&evaluated)
        }
        Value::Constructor { class_name } => {
            // Call a constructor to create an instance
            instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods)
        }
        _ => Err(semantic_err!("unsupported callee")),
    }
}
