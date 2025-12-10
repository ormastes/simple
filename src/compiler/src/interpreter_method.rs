// Method call evaluation (part of interpreter module)

fn evaluate_method_call(
    receiver: &Box<Expr>,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Built-in methods for Array
    if let Value::Array(ref arr) = recv_val {
        match method {
            "len" => return Ok(Value::Int(arr.len() as i64)),
            "is_empty" => return Ok(Value::Bool(arr.is_empty())),
            "first" => return Ok(arr.first().cloned().unwrap_or(Value::Nil)),
            "last" => return Ok(arr.last().cloned().unwrap_or(Value::Nil)),
            "get" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(arr.get(idx).cloned().unwrap_or(Value::Nil));
            }
            "contains" => {
                let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Bool(arr.contains(&needle)));
            }
            "push" | "append" => {
                let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                new_arr.push(item);
                return Ok(Value::Array(new_arr));
            }
            "pop" => {
                let mut new_arr = arr.clone();
                new_arr.pop();
                return Ok(Value::Array(new_arr));
            }
            "concat" | "extend" => {
                let other = eval_arg(args, 0, Value::Array(vec![]), env, functions, classes, enums, impl_methods)?;
                if let Value::Array(other_arr) = other {
                    let mut new_arr = arr.clone();
                    new_arr.extend(other_arr);
                    return Ok(Value::Array(new_arr));
                }
                return Err(CompileError::Semantic("concat expects array argument".into()));
            }
            "insert" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let item = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                if idx <= new_arr.len() {
                    new_arr.insert(idx, item);
                }
                return Ok(Value::Array(new_arr));
            }
            "remove" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                if idx < new_arr.len() {
                    new_arr.remove(idx);
                }
                return Ok(Value::Array(new_arr));
            }
            "reverse" => {
                let mut new_arr = arr.clone();
                new_arr.reverse();
                return Ok(Value::Array(new_arr));
            }
            "slice" => {
                let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let end = args.get(1)
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .transpose()?
                    .map(|v| v.as_int().unwrap_or(arr.len() as i64) as usize)
                    .unwrap_or(arr.len());
                let end = end.min(arr.len());
                let start = start.min(end);
                return Ok(Value::Array(arr[start..end].to_vec()));
            }
            "map" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_map(arr, func, functions, classes, enums, impl_methods);
            }
            "filter" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_filter(arr, func, functions, classes, enums, impl_methods);
            }
            "reduce" | "fold" => {
                let init = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
                let func = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_reduce(arr, init, func, functions, classes, enums, impl_methods);
            }
            "find" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_find(arr, func, functions, classes, enums, impl_methods);
            }
            "any" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_any(arr, func, functions, classes, enums, impl_methods);
            }
            "all" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_all(arr, func, functions, classes, enums, impl_methods);
            }
            "join" => {
                let sep = eval_arg(args, 0, Value::Str("".into()), env, functions, classes, enums, impl_methods)?.to_display_string();
                let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "sum" => {
                let mut total: i64 = 0;
                for item in arr {
                    if let Value::Int(n) = item {
                        total += n;
                    }
                }
                return Ok(Value::Int(total));
            }
            "index_of" => {
                let needle = args.get(0)
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                for (i, item) in arr.iter().enumerate() {
                    if item == &needle {
                        return Ok(Value::Int(i as i64));
                    }
                }
                return Ok(Value::Int(-1));
            }
            _ => {}
        }
    }

    // Built-in methods for Tuple
    if let Value::Tuple(ref tup) = recv_val {
        match method {
            "len" => return Ok(Value::Int(tup.len() as i64)),
            "get" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(tup.get(idx).cloned().unwrap_or(Value::Nil));
            }
            _ => {}
        }
    }

    // Built-in methods for Dict
    if let Value::Dict(ref map) = recv_val {
        match method {
            "len" => return Ok(Value::Int(map.len() as i64)),
            "is_empty" => return Ok(Value::Bool(map.is_empty())),
            "contains_key" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(map.contains_key(&key)));
            }
            "get" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(map.get(&key).cloned().unwrap_or(Value::Nil));
            }
            "keys" => {
                let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
                return Ok(Value::Array(keys));
            }
            "values" => {
                let vals: Vec<Value> = map.values().cloned().collect();
                return Ok(Value::Array(vals));
            }
            "set" | "insert" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let value = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_map = map.clone();
                new_map.insert(key, value);
                return Ok(Value::Dict(new_map));
            }
            "remove" | "delete" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let mut new_map = map.clone();
                new_map.remove(&key);
                return Ok(Value::Dict(new_map));
            }
            "merge" | "extend" => {
                let other = eval_arg(args, 0, Value::Dict(HashMap::new()), env, functions, classes, enums, impl_methods)?;
                if let Value::Dict(other_map) = other {
                    let mut new_map = map.clone();
                    new_map.extend(other_map);
                    return Ok(Value::Dict(new_map));
                }
                return Err(CompileError::Semantic("merge expects dict argument".into()));
            }
            "get_or" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(map.get(&key).cloned().unwrap_or(default));
            }
            "entries" | "items" => {
                let entries: Vec<Value> = map.iter()
                    .map(|(k, v)| Value::Tuple(vec![Value::Str(k.clone()), v.clone()]))
                    .collect();
                return Ok(Value::Array(entries));
            }
            "map_values" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_dict_map_values(map, func, functions, classes, enums, impl_methods);
            }
            "filter" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_dict_filter(map, func, functions, classes, enums, impl_methods);
            }
            _ => {}
        }
    }

    // Built-in methods for String
    if let Value::Str(ref s) = recv_val {
        match method {
            "len" => return Ok(Value::Int(s.len() as i64)),
            "is_empty" => return Ok(Value::Bool(s.is_empty())),
            "chars" => {
                let chars: Vec<Value> = s.chars().map(|c| Value::Str(c.to_string())).collect();
                return Ok(Value::Array(chars));
            }
            "contains" => {
                let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.contains(&needle)));
            }
            "starts_with" => {
                let prefix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.starts_with(&prefix)));
            }
            "ends_with" => {
                let suffix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.ends_with(&suffix)));
            }
            "to_upper" => return Ok(Value::Str(s.to_uppercase())),
            "to_lower" => return Ok(Value::Str(s.to_lowercase())),
            "trim" => return Ok(Value::Str(s.trim().to_string())),
            "split" => {
                let sep = eval_arg(args, 0, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?.to_key_string();
                let parts: Vec<Value> = s.split(&sep).map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            _ => {}
        }
    }

    // Built-in methods for Option
    if let Value::Enum { enum_name, variant, payload } = &recv_val {
        if enum_name == "Option" {
            match method {
                "is_some" => return Ok(Value::Bool(variant == "Some")),
                "is_none" => return Ok(Value::Bool(variant == "None")),
                "unwrap" => {
                    if variant == "Some" {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap on None".into()));
                }
                "unwrap_or" => {
                    if variant == "Some" {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "map" => {
                    return eval_option_map(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                _ => {}
            }
        }
        // Built-in methods for Result
        if enum_name == "Result" {
            match method {
                "is_ok" => return Ok(Value::Bool(variant == "Ok")),
                "is_err" => return Ok(Value::Bool(variant == "Err")),
                "unwrap" => {
                    if variant == "Ok" {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    if variant == "Err" {
                        if let Some(err_val) = payload {
                            return Err(CompileError::Semantic(format!("called unwrap on Err: {}", err_val.to_display_string())));
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap on Err".into()));
                }
                "unwrap_or" => {
                    if variant == "Ok" {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "unwrap_err" => {
                    if variant == "Err" {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap_err on Ok".into()));
                }
                "ok" => {
                    if variant == "Ok" {
                        return Ok(Value::Enum {
                            enum_name: "Option".into(),
                            variant: "Some".into(),
                            payload: payload.clone(),
                        });
                    }
                    return Ok(Value::Enum {
                        enum_name: "Option".into(),
                        variant: "None".into(),
                        payload: None,
                    });
                }
                "err" => {
                    if variant == "Err" {
                        return Ok(Value::Enum {
                            enum_name: "Option".into(),
                            variant: "Some".into(),
                            payload: payload.clone(),
                        });
                    }
                    return Ok(Value::Enum {
                        enum_name: "Option".into(),
                        variant: "None".into(),
                        payload: None,
                    });
                }
                _ => {}
            }
        }
    }

    // Object methods (class/struct)
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some(result) = find_and_exec_method(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }
        return Err(CompileError::Semantic(format!("unknown method {method} on {class}")));
    }

    // Future methods (join, await, get, is_ready)
    if let Value::Future(ref future) = recv_val {
        match method {
            "join" | "await" | "get" => {
                return future.await_result().map_err(|e| CompileError::Semantic(e));
            }
            "is_ready" => {
                return Ok(Value::Bool(future.is_ready()));
            }
            _ => return Err(CompileError::Semantic(format!("unknown method {method} on Future"))),
        }
    }

    // Channel methods (send, recv, try_recv)
    if let Value::Channel(ref channel) = recv_val {
        match method {
            "send" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                channel.send(val).map_err(|e| CompileError::Semantic(e))?;
                return Ok(Value::Nil);
            }
            "recv" => {
                let val = channel.recv().map_err(|e| CompileError::Semantic(e))?;
                return Ok(val);
            }
            "try_recv" => {
                return Ok(match channel.try_recv() {
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
                });
            }
            _ => return Err(CompileError::Semantic(format!("unknown method {method} on Channel"))),
        }
    }

    // ThreadPool methods (submit)
    if let Value::ThreadPool(ref pool) = recv_val {
        match method {
            "submit" => {
                // pool.submit(func, arg) - submit a task to the pool
                let func_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let arg_val = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

                // For proper execution, we need to call the function in a thread
                // Clone all the context needed
                let func_clone = func_val.clone();
                let arg_clone = arg_val.clone();
                let env_clone = env.clone();
                let funcs_clone = functions.clone();
                let classes_clone = classes.clone();
                let enums_clone = enums.clone();
                let impls_clone = impl_methods.clone();

                let future = FutureValue::new(move || {
                    match func_clone {
                        Value::Function { ref def, ref captured_env, .. } => {
                            let mut local_env = captured_env.clone();
                            if let Some(first_param) = def.params.first() {
                                local_env.insert(first_param.name.clone(), arg_clone);
                            }
                            match exec_block(&def.body, &mut local_env, &funcs_clone, &classes_clone, &enums_clone, &impls_clone) {
                                Ok(Control::Return(v)) => Ok(v),
                                Ok(_) => Ok(Value::Nil),
                                Err(e) => Err(format!("{:?}", e)),
                            }
                        }
                        Value::Lambda { ref params, ref body, ref env } => {
                            let mut local_env = env.clone();
                            if let Some(first_param) = params.first() {
                                local_env.insert(first_param.clone(), arg_clone);
                            }
                            evaluate_expr(&body, &local_env, &funcs_clone, &classes_clone, &enums_clone, &impls_clone)
                                .map_err(|e| format!("{:?}", e))
                        }
                        _ => Err("submit expects a function or lambda".into()),
                    }
                });
                return Ok(Value::Future(future));
            }
            _ => return Err(CompileError::Semantic(format!("unknown method {method} on ThreadPool"))),
        }
    }

    // Static method calls on class constructor (e.g. Calculator.add(...))
    if let Value::Constructor { ref class_name } = recv_val {
        if let Some(class_def) = classes.get(class_name) {
            // Find static method (no self parameter)
            if let Some(method_def) = class_def.methods.iter().find(|m| m.name == method) {
                // Execute without self
                let mut local_env = env.clone();
                let mut positional_idx = 0;
                for arg in args {
                    let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                    if let Some(name) = &arg.name {
                        local_env.insert(name.clone(), val);
                    } else if positional_idx < method_def.params.len() {
                        let param = &method_def.params[positional_idx];
                        local_env.insert(param.name.clone(), val);
                        positional_idx += 1;
                    }
                }
                return match exec_block(&method_def.body, &mut local_env, functions, classes, enums, impl_methods) {
                    Ok(Control::Return(v)) => Ok(v),
                    Ok(_) => Ok(Value::Nil),
                    Err(e) => Err(e),
                };
            }
            return Err(CompileError::Semantic(format!("unknown static method {method} on class {class_name}")));
        }
        return Err(CompileError::Semantic(format!("unknown class {class_name}")));
    }

    Err(CompileError::Semantic(format!("method call on unsupported type: {method}")))
}

/// Evaluate a method call and return both the result and the potentially modified self.
/// This is used when we need to persist mutations to self back to the calling environment.
fn evaluate_method_call_with_self_update(
    receiver: &Box<Expr>,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<Value>), CompileError> {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Only handle Object methods with self mutation
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some((result, updated_self)) = find_and_exec_method_with_self(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok((result, Some(updated_self)));
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            // method_missing returns just a result, self is not mutated
            return Ok((result, None));
        }
        // Fall back to regular method call if not found
        return Err(CompileError::Semantic(format!("unknown method {method} on {class}")));
    }

    // For non-objects, just use regular method call
    let result = evaluate_method_call(receiver, method, args, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}

/// Find and execute a method, returning both result and modified self.
fn find_and_exec_method_with_self(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class) {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(func, args, env, functions, classes, enums, impl_methods, class, fields)?;
            return Ok(Some((result, updated_self)));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(func, args, env, functions, classes, enums, impl_methods, class, fields)?;
            return Ok(Some((result, updated_self)));
        }
    }
    Ok(None)
}

/// Execute a function and return both the result and the modified self value.
fn exec_function_with_self_return(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: &HashMap<String, Value>,
) -> Result<(Value, Value), CompileError> {
    let mut local_env = Env::new();

    // Set up self
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        },
    );

    // Bind arguments (skip self parameter)
    let self_mode = simple_parser::ast::SelfMode::SkipSelf;
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

    // Execute the function body
    let result = match exec_block(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok(Control::Return(v)) => v,
        Ok(_) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    // Get the potentially modified self
    let updated_self = local_env.get("self").cloned().unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: fields.clone(),
    });

    Ok((result, updated_self))
}
