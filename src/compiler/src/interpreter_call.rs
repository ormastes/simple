// Call expression evaluation (part of interpreter module)

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
                return Ok(Value::Enum {
                    enum_name: "Option".into(),
                    variant: "Some".into(),
                    payload: Some(Box::new(val)),
                });
            }
            "None" => {
                return Ok(Value::Enum {
                    enum_name: "Option".into(),
                    variant: "None".into(),
                    payload: None,
                });
            }
            "Ok" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Enum {
                    enum_name: "Result".into(),
                    variant: "Ok".into(),
                    payload: Some(Box::new(val)),
                });
            }
            "Err" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Enum {
                    enum_name: "Result".into(),
                    variant: "Err".into(),
                    payload: Some(Box::new(val)),
                });
            }
            "len" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return match val {
                    Value::Array(a) => Ok(Value::Int(a.len() as i64)),
                    Value::Tuple(t) => Ok(Value::Int(t.len() as i64)),
                    Value::Dict(d) => Ok(Value::Int(d.len() as i64)),
                    Value::Str(s) => Ok(Value::Int(s.len() as i64)),
                    _ => Err(CompileError::Semantic("len expects array, tuple, dict, or string".into())),
                };
            }
            "send" => {
                let target = args.get(0).ok_or_else(|| CompileError::Semantic("send expects actor handle".into()))?;
                let msg_arg = args.get(1).ok_or_else(|| CompileError::Semantic("send expects message".into()))?;
                let target_val = evaluate_expr(&target.value, env, functions, classes, enums, impl_methods)?;
                let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Actor(handle) = target_val {
                    handle
                        .send(Message::Value(msg_val.to_display_string()))
                        .map_err(|e| CompileError::Semantic(e))?;
                    return Ok(Value::Nil);
                }
                return Err(CompileError::Semantic("send target must be actor".into()));
            }
            "recv" => {
                check_async_violation("recv")?;
                if args.is_empty() {
                    let msg = ACTOR_INBOX.with(|cell| {
                        cell.borrow()
                            .as_ref()
                            .ok_or_else(|| CompileError::Semantic("recv called outside actor without handle".into()))
                            .and_then(|rx| {
                                rx.lock()
                                    .map_err(|_| CompileError::Semantic("actor inbox lock poisoned".into()))
                                    .and_then(|receiver| {
                                        receiver
                                            .recv_timeout(std::time::Duration::from_secs(5))
                                            .map_err(|e| CompileError::Semantic(format!("recv timeout: {e}")))
                                    })
                            })
                    })?;
                    return Ok(message_to_value(msg));
                } else {
                    let handle_val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                    if let Value::Actor(handle) = handle_val {
                        let msg = handle.recv_timeout(std::time::Duration::from_secs(5))
                            .map_err(|e| CompileError::Semantic(e))?;
                        return Ok(message_to_value(msg));
                    }
                    return Err(CompileError::Semantic("recv expects actor handle".into()));
                }
            }
            "reply" => {
                let msg_arg = args.get(0).ok_or_else(|| CompileError::Semantic("reply expects message".into()))?;
                let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
                ACTOR_OUTBOX.with(|cell| {
                    cell.borrow()
                        .as_ref()
                        .ok_or_else(|| CompileError::Semantic("reply called outside actor".into()))
                        .and_then(|tx| {
                            tx.send(Message::Value(msg_val.to_display_string()))
                                .map_err(|e| CompileError::Semantic(format!("reply failed: {e}")))
                        })
                })?;
                return Ok(Value::Nil);
            }
            "join" => {
                check_async_violation("join")?;
                let handle_arg = args.get(0).ok_or_else(|| CompileError::Semantic("join expects actor handle".into()))?;
                let handle_val = evaluate_expr(&handle_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Actor(handle) = handle_val {
                    handle.join().map_err(|e| CompileError::Semantic(e))?;
                    return Ok(Value::Nil);
                }
                return Err(CompileError::Semantic("join target must be actor".into()));
            }
            "spawn" => {
                let inner_expr = args.get(0).ok_or_else(|| CompileError::Semantic("spawn expects a thunk".into()))?;
                return Ok(spawn_actor_with_expr(&inner_expr.value, env, functions, classes, enums, impl_methods));
            }
            "async" | "future" => {
                let inner_expr = args.get(0).ok_or_else(|| CompileError::Semantic("async expects an expression".into()))?;
                let expr_clone = inner_expr.value.clone();
                let env_clone = env.clone();
                let funcs = functions.clone();
                let classes_clone = classes.clone();
                let enums_clone = enums.clone();
                let impls_clone = impl_methods.clone();
                let future = FutureValue::new(move || {
                    evaluate_expr(&expr_clone, &env_clone, &funcs, &classes_clone, &enums_clone, &impls_clone)
                        .map_err(|e| format!("{:?}", e))
                });
                return Ok(Value::Future(future));
            }
            "is_ready" => {
                let future_arg = args.get(0).ok_or_else(|| CompileError::Semantic("is_ready expects a future".into()))?;
                let val = evaluate_expr(&future_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Future(f) = val {
                    return Ok(Value::Bool(f.is_ready()));
                }
                return Err(CompileError::Semantic("is_ready expects a future".into()));
            }
            "generator" => {
                let inner_expr = args.get(0).ok_or_else(|| CompileError::Semantic("generator expects a lambda".into()))?;
                let val = evaluate_expr(&inner_expr.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda { body, env: captured, .. } = val {
                    GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = Some(Vec::new()));
                    let _ = evaluate_expr(&body, &captured, functions, classes, enums, impl_methods);
                    let yields = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
                    let gen = GeneratorValue::new_with_values(yields);
                    return Ok(Value::Generator(gen));
                }
                return Err(CompileError::Semantic("generator expects a lambda".into()));
            }
            "next" => {
                let gen_arg = args.get(0).ok_or_else(|| CompileError::Semantic("next expects a generator".into()))?;
                let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Generator(gen) = val {
                    return Ok(gen.next().unwrap_or(Value::Nil));
                }
                return Err(CompileError::Semantic("next expects a generator".into()));
            }
            "collect" => {
                let gen_arg = args.get(0).ok_or_else(|| CompileError::Semantic("collect expects a generator".into()))?;
                let val = evaluate_expr(&gen_arg.value, env, functions, classes, enums, impl_methods)?;
                if let Value::Generator(gen) = val {
                    return Ok(Value::Array(gen.collect_remaining()));
                }
                if let Value::Array(arr) = val {
                    return Ok(Value::Array(arr));
                }
                return Err(CompileError::Semantic("collect expects a generator or array".into()));
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
            }
        }
        return Err(CompileError::Semantic(format!("unsupported path call: {:?}", segments)));
    }

    let callee_val = evaluate_expr(callee, env, functions, classes, enums, impl_methods)?;
    match callee_val {
        Value::Lambda { params, body, env: captured } => {
            exec_lambda(&params, &body, args, env, &captured, functions, classes, enums, impl_methods)
        }
        Value::Function { def, captured_env, .. } => {
            // Call a first-class function value with captured environment for closure
            exec_function_with_captured_env(&def, args, env, &captured_env, functions, classes, enums, impl_methods)
        }
        Value::Constructor { class_name } => {
            // Call a constructor to create an instance
            instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods)
        }
        _ => Err(CompileError::Semantic("unsupported callee".into())),
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
        .filter(|p| !(self_mode.should_skip_self() && p.name == "self"))
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            if !params_to_bind.iter().any(|p| &p.name == name) {
                return Err(CompileError::Semantic(format!("unknown argument {name}")));
            }
            bound.insert(name.clone(), val);
        } else {
            if positional_idx >= params_to_bind.len() {
                return Err(CompileError::Semantic("too many arguments".into()));
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
                return Err(CompileError::Semantic(format!("missing argument {}", param.name)));
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
                return Err(CompileError::Semantic("too many arguments to lambda".into()));
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

    evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
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
    let prev_effect = CURRENT_EFFECT.with(|cell| cell.borrow().clone());
    if func.effect.is_some() {
        CURRENT_EFFECT.with(|cell| *cell.borrow_mut() = func.effect.clone());
    }

    let result = exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx);

    CURRENT_EFFECT.with(|cell| *cell.borrow_mut() = prev_effect);

    result
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
    let prev_effect = CURRENT_EFFECT.with(|cell| cell.borrow().clone());
    if func.effect.is_some() {
        CURRENT_EFFECT.with(|cell| *cell.borrow_mut() = func.effect.clone());
    }

    // Start with the captured environment (for closure variables)
    let mut local_env = captured_env.clone();

    // Bind arguments
    let self_mode = simple_parser::ast::SelfMode::IncludeSelf;
    let bound_args = bind_args(&func.params, args, outer_env, functions, classes, enums, impl_methods, self_mode)?;
    for (name, value) in bound_args {
        local_env.insert(name, value);
    }

    // Execute the function body
    let result = exec_block(&func.body, &mut local_env, functions, classes, enums, impl_methods);

    CURRENT_EFFECT.with(|cell| *cell.borrow_mut() = prev_effect);

    match result {
        Ok(Control::Return(v)) => Ok(v),
        Ok(Control::Next) => Ok(Value::Nil),
        Ok(Control::Break(_)) => Err(CompileError::Semantic("break outside loop".into())),
        Ok(Control::Continue) => Err(CompileError::Semantic("continue outside loop".into())),
        Err(e) => Err(e),
    }
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
    match exec_block(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok(Control::Return(v)) => Ok(v),
        Ok(_) => Ok(Value::Nil),
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
        CompileError::Semantic(format!("unknown class: {class_name}"))
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
    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == "new") {
        // Call the constructor with self
        let self_val = Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        };

        let mut local_env = env.clone();
        local_env.insert("self".to_string(), self_val);

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
                    return Err(CompileError::Semantic(format!("unknown field {name} for class {class_name}")));
                }
                fields.insert(name.clone(), val);
            } else {
                // Positional argument - match to field in declaration order
                if positional_idx < class_def.fields.len() {
                    let field_name = &class_def.fields[positional_idx].name;
                    fields.insert(field_name.clone(), val);
                    positional_idx += 1;
                } else {
                    return Err(CompileError::Semantic(format!("too many arguments for class {class_name}")));
                }
            }
        }

        Ok(Value::Object {
            class: class_name.to_string(),
            fields,
        })
    }
}
