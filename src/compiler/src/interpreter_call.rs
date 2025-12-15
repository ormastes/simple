// Call expression evaluation (part of interpreter module)

// BDD testing state (thread-local for test isolation)
thread_local! {
    // Current indentation level for nested describe/context blocks
    static BDD_INDENT: RefCell<usize> = RefCell::new(0);
    // (passed, failed) counts for current describe block
    static BDD_COUNTS: RefCell<(usize, usize)> = RefCell::new((0, 0));
    // Whether current "it" block has a failed expectation
    static BDD_EXPECT_FAILED: RefCell<bool> = RefCell::new(false);
    // Whether we're currently inside an "it" block (expect should be silent)
    static BDD_INSIDE_IT: RefCell<bool> = RefCell::new(false);
    // Failure message from expect (for display in it block)
    static BDD_FAILURE_MSG: RefCell<Option<String>> = RefCell::new(None);
}

/// Build a helpful failure message for expect by inspecting the expression
fn build_expect_failure_message(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> String {
    use simple_parser::ast::BinOp;

    match expr {
        Expr::Binary { left, op, right } => {
            // Evaluate left and right sides to show actual values
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());

            match op {
                BinOp::Eq => format!("expected {} to equal {}", left_val, right_val),
                BinOp::NotEq => format!("expected {} to not equal {}", left_val, right_val),
                BinOp::Lt => format!("expected {} < {}", left_val, right_val),
                BinOp::LtEq => format!("expected {} <= {}", left_val, right_val),
                BinOp::Gt => format!("expected {} > {}", left_val, right_val),
                BinOp::GtEq => format!("expected {} >= {}", left_val, right_val),
                _ => "expected expression to be true, got false".to_string(),
            }
        }
        Expr::Unary { op: simple_parser::ast::UnaryOp::Not, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());
            format!("expected {} to be falsy", val)
        }
        Expr::Identifier(name) => {
            let val = env.get(name)
                .map(|v| format_value_for_message(v))
                .unwrap_or_else(|| "undefined".to_string());
            format!("expected {} ({}) to be truthy", name, val)
        }
        _ => "expected true, got false".to_string(),
    }
}

/// Format a value for display in error messages
fn format_value_for_message(val: &Value) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Nil => "nil".to_string(),
        Value::Array(items) => {
            let items_str: Vec<String> = items.iter().map(|v| format_value_for_message(v)).collect();
            format!("[{}]", items_str.join(", "))
        }
        _ => format!("{:?}", val),
    }
}

/// Execute a block value (lambda or block closure)
fn exec_block_value(
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

fn evaluate_call(
    callee: &Box<Expr>,
    args: &[simple_parser::ast::Argument],
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
                check_async_violation("recv")?;
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
                check_async_violation("join")?;
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
                // Prints the name, evaluates the block, shows summary
                let name = eval_arg(args, 0, Value::Str("unnamed".to_string()), env, functions, classes, enums, impl_methods)?;
                let name_str = match &name {
                    Value::Str(s) => s.clone(),
                    _ => "unnamed".to_string(),
                };
                let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // Get current indent level
                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                let indent_str = "  ".repeat(indent);

                // Print describe/context name
                println!("{}{}", indent_str, name_str);

                // Increase indent for nested blocks
                BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

                // Execute the block
                let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

                // Restore indent
                BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

                // Print summary at top level
                if indent == 0 {
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

                // Execute the block
                let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

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
            let enum_name = &segments[0];
            let variant = &segments[1];
            if let Some(enum_def) = enums.get(enum_name) {
                if enum_def.variants.iter().any(|v| &v.name == variant) {
                    let payload = if !args.is_empty() {
                        Some(Box::new(evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?))
                    } else {
                        None
                    };
                    return Ok(Value::Enum {
                        enum_name: enum_name.clone(),
                        variant: variant.clone(),
                        payload,
                    });
                }
            } else if let Some(func) = functions.get(variant) {
                return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(variant) {
                return instantiate_class(variant, args, env, functions, classes, enums, impl_methods);
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
        Value::Constructor { class_name } => {
            // Call a constructor to create an instance
            instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods)
        }
        _ => Err(semantic_err!("unsupported callee")),
    }
}

fn bind_args(
    params: &[simple_parser::ast::Parameter],
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: simple_parser::ast::SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            if !params_to_bind.iter().any(|p| &p.name == name) {
                bail_semantic!("unknown argument {}", name);
            }
            bound.insert(name.clone(), val);
        } else {
            if positional_idx >= params_to_bind.len() {
                bail_semantic!("too many arguments");
            }
            let param = params_to_bind[positional_idx];
            bound.insert(param.name.clone(), val);
            positional_idx += 1;
        }
    }

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                bound.insert(param.name.clone(), v);
            } else {
                bail_semantic!("missing argument {}", param.name);
            }
        }
    }

    Ok(bound)
}

fn exec_lambda(
    params: &[String],
    body: &Expr,
    args: &[simple_parser::ast::Argument],
    call_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                bail_semantic!("too many arguments to lambda");
            }
            local_env.insert(params[positional_idx].clone(), val);
            positional_idx += 1;
        }
    }

    for param in params {
        if !local_env.contains_key(param) {
            local_env.insert(param.clone(), Value::Nil);
        }
    }

    // If body is a DoBlock, execute its statements directly instead of
    // returning a BlockClosure value
    if let Expr::DoBlock(nodes) = body {
        return exec_block_closure(nodes, &local_env, functions, classes, enums, impl_methods);
    }

    evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
}

/// Execute a block closure (BDD DSL colon-block)
/// Executes each statement in sequence and returns the last expression's value (or Nil)
fn exec_block_closure(
    nodes: &[simple_parser::ast::Node],
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use simple_parser::ast::Node;

    let mut local_env = captured_env.clone();
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                last_value = evaluate_expr(expr, &local_env, functions, classes, enums, impl_methods)?;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, &local_env, functions, classes, enums, impl_methods)?;
                    // Extract name from pattern
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, &local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    local_env.insert(name.clone(), val);
                }
                last_value = Value::Nil;
            }
            _ => {
                // For other node types, just skip for now
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}

fn exec_function(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    with_effect_context(&func.effect, || {
        exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx)
    })
}

/// Execute a function with a captured environment for closure semantics
fn exec_function_with_captured_env(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_context(&func.effect, || {
        // Start with the captured environment (for closure variables)
        let mut local_env = captured_env.clone();

        // Bind arguments
        let self_mode = simple_parser::ast::SelfMode::IncludeSelf;
        let bound_args = bind_args(&func.params, args, outer_env, functions, classes, enums, impl_methods, self_mode)?;
        for (name, value) in bound_args {
            local_env.insert(name, value);
        }

        // Execute the function body with implicit return support
        let result = exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods);
        match result {
            Ok((Control::Return(v), _)) => Ok(v),
            Ok((_, Some(v))) => Ok(v), // Implicit return from last expression
            Ok((_, None)) => Ok(Value::Nil),
            Err(e) => Err(e),
        }
    })
}

fn exec_function_inner(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    let mut local_env = Env::new();
    if let Some((class_name, fields)) = self_ctx {
        local_env.insert(
            "self".into(),
            Value::Object {
                class: class_name.to_string(),
                fields: fields.clone(),
            },
        );
    }
    let self_mode = if self_ctx.is_some() {
        simple_parser::ast::SelfMode::SkipSelf
    } else {
        simple_parser::ast::SelfMode::IncludeSelf
    };
    let bound = bind_args(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => Ok(v),
        Ok((_, Some(v))) => Ok(v), // Implicit return from last expression
        Ok((_, None)) => Ok(Value::Nil),
        // TryError from ? operator - propagate as return value
        Err(CompileError::TryError(val)) => Ok(val),
        Err(e) => Err(e),
    }
}

/// Instantiate a class by calling its constructor (the 'new' method if present)
/// or by creating an object with default field values.
fn instantiate_class(
    class_name: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let class_def = classes.get(class_name).ok_or_else(|| {
        semantic_err!("unknown class: {}", class_name)
    })?;

    // Initialize fields with defaults
    let mut fields: HashMap<String, Value> = HashMap::new();
    for field in &class_def.fields {
        let val = if let Some(default_expr) = &field.default {
            evaluate_expr(default_expr, env, functions, classes, enums, impl_methods)?
        } else {
            Value::Nil
        };
        fields.insert(field.name.clone(), val);
    }

    // Look for 'new' constructor method
    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == METHOD_NEW) {
        // Call the constructor with self
        let self_val = Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        };

        let mut local_env = env.clone();
        local_env.insert(METHOD_SELF.to_string(), self_val);

        // Add fields to environment so constructor can access them
        for (k, v) in &fields {
            local_env.insert(k.clone(), v.clone());
        }

        let self_mode = simple_parser::ast::SelfMode::SkipSelf;
        let bound = bind_args(&new_method.params, args, env, functions, classes, enums, impl_methods, self_mode)?;
        for (name, val) in bound {
            local_env.insert(name, val);
        }

        match exec_block(&new_method.body, &mut local_env, functions, classes, enums, impl_methods) {
            Ok(Control::Return(v)) => Ok(v),
            Ok(_) => {
                // Return the self object (possibly modified by constructor)
                Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields,
                }))
            }
            Err(CompileError::TryError(val)) => Ok(val),
            Err(e) => Err(e),
        }
    } else {
        // No constructor - just return object with field values from args
        // Match arguments to fields positionally or by name
        let mut positional_idx = 0;
        for arg in args {
            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
            if let Some(name) = &arg.name {
                if !fields.contains_key(name) {
                    bail_semantic!("unknown field {} for class {}", name, class_name);
                }
                fields.insert(name.clone(), val);
            } else {
                // Positional argument - match to field in declaration order
                if positional_idx < class_def.fields.len() {
                    let field_name = &class_def.fields[positional_idx].name;
                    fields.insert(field_name.clone(), val);
                    positional_idx += 1;
                } else {
                    bail_semantic!("too many arguments for class {}", class_name);
                }
            }
        }

        Ok(Value::Object {
            class: class_name.to_string(),
            fields,
        })
    }
}
