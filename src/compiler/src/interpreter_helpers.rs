// ============================================================================
// Helper functions to reduce duplication across interpreter modules
// ============================================================================

/// Build method_missing arguments from method name and original args
fn build_method_missing_args(method: &str, args: &[simple_parser::ast::Argument]) -> Vec<simple_parser::ast::Argument> {
    vec![
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Symbol(method.to_string()),
        },
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
        },
        simple_parser::ast::Argument {
            name: None,
            value: Expr::Nil,
        },
    ]
}

/// Internal helper: find and execute a method by name on a class/struct object.
/// Searches in class_def methods first, then impl_methods.
/// Returns Ok(Some(value)) if method found, Ok(None) if not found.
fn find_method_and_exec(
    method_name: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class) {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method_name) {
            return Ok(Some(exec_function(func, args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method_name) {
            return Ok(Some(exec_function(func, args, env, functions, classes, enums, impl_methods, Some((class, fields)))?));
        }
    }
    Ok(None)
}

/// Find and execute a method on a class/struct object.
/// Searches in class_def methods first, then impl_methods.
/// Returns Ok(Some(value)) if method found, Ok(None) if not found.
fn find_and_exec_method<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    find_method_and_exec(method, args, class, fields, env, functions, classes, enums, impl_methods)
}

/// Try to call method_missing hook on a class/struct object.
/// Returns Ok(Some(value)) if method_missing found, Ok(None) if not found.
fn try_method_missing<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let mm_args = build_method_missing_args(method, args);
    find_method_and_exec(METHOD_MISSING, &mm_args, class, fields, env, functions, classes, enums, impl_methods)
}

/// Create a range object with start, end, and bound type fields.
/// The bound is stored as a boolean for runtime compatibility.
fn create_range_object(start: i64, end: i64, bound: RangeBound) -> Value {
    let mut fields = HashMap::new();
    fields.insert("start".into(), Value::Int(start));
    fields.insert("end".into(), Value::Int(end));
    // Store as boolean for runtime iteration compatibility
    fields.insert("inclusive".into(), Value::Bool(bound.is_inclusive()));
    Value::Object {
        class: BUILTIN_RANGE.into(),
        fields,
    }
}

/// Spawn an actor with the given expression and environment
fn spawn_actor_with_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Value {
    let expr_clone = expr.clone();
    let env_clone = env.clone();
    let funcs = functions.clone();
    let classes_clone = classes.clone();
    let enums_clone = enums.clone();
    let impls_clone = impl_methods.clone();
    let handle = ACTOR_SPAWNER.with(|s| s.spawn(move |inbox, outbox| {
        let inbox = Arc::new(Mutex::new(inbox));
        ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
        ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));
        let _ = evaluate_expr(&expr_clone, &env_clone, &funcs, &classes_clone, &enums_clone, &impls_clone);
        ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
        ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
    }));
    Value::Actor(handle)
}

/// Evaluate an optional argument at given index with a default value.
/// This is a common pattern in method calls: args.get(idx).map(eval).transpose()?.unwrap_or(default)
fn eval_arg(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: Value,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    args.get(idx)
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .transpose()
        .map(|opt| opt.unwrap_or(default))
}

/// Evaluate an argument as i64 with default
fn eval_arg_int(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: i64,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<i64, CompileError> {
    eval_arg(args, idx, Value::Int(default), env, functions, classes, enums, impl_methods)?
        .as_int()
}

/// Evaluate an argument as usize with default
fn eval_arg_usize(
    args: &[simple_parser::ast::Argument],
    idx: usize,
    default: usize,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<usize, CompileError> {
    Ok(eval_arg_int(args, idx, default as i64, env, functions, classes, enums, impl_methods)? as usize)
}

/// Apply a lambda to each item in an array, returning Vec of results.
fn apply_lambda_to_vec(
    arr: &[Value],
    lambda_val: &Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Value>, CompileError> {
    if let Value::Lambda { params, body, env: captured } = lambda_val {
        let mut results = Vec::new();
        for item in arr {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            results.push(result);
        }
        Ok(results)
    } else {
        Err(CompileError::Semantic("expected lambda argument".into()))
    }
}

/// Array map: apply lambda to each element
fn eval_array_map(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let results = apply_lambda_to_vec(arr, &func, functions, classes, enums, impl_methods)?;
    Ok(Value::Array(results))
}

/// Setup environment with single parameter binding for a lambda
fn bind_lambda_param(captured: &Env, params: &[String], value: &Value) -> Env {
    let mut env = captured.clone();
    if let Some(param) = params.first() {
        env.insert(param.clone(), value.clone());
    }
    env
}

/// Array filter: keep elements where lambda returns truthy
fn eval_array_filter(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut results = Vec::new();
        for item in arr {
            let local_env = bind_lambda_param(&captured, &params, item);
            if evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                results.push(item.clone());
            }
        }
        Ok(Value::Array(results))
    } else {
        Err(CompileError::Semantic("filter expects lambda argument".into()))
    }
}

/// Array reduce: fold over elements with accumulator
fn eval_array_reduce(
    arr: &[Value],
    init: Value,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut acc = init;
        for item in arr {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), acc);
                local_env.insert(params[1].clone(), item.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), item.clone());
            }
            acc = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
        }
        Ok(acc)
    } else {
        Err(CompileError::Semantic("reduce expects lambda argument".into()))
    }
}

/// Array find: return first element where lambda is truthy
fn eval_array_find(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let local_env = bind_lambda_param(&captured, &params, item);
            if evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(item.clone());
            }
        }
        Ok(Value::Nil)
    } else {
        Err(CompileError::Semantic("find expects lambda argument".into()))
    }
}

/// Array any: return true if any element satisfies lambda
fn eval_array_any(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let local_env = bind_lambda_param(&captured, &params, item);
            if evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    } else {
        Err(CompileError::Semantic("any expects lambda argument".into()))
    }
}

/// Array all: return true if all elements satisfy lambda
fn eval_array_all(
    arr: &[Value],
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        for item in arr {
            let local_env = bind_lambda_param(&captured, &params, item);
            if !evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    } else {
        Err(CompileError::Semantic("all expects lambda argument".into()))
    }
}

/// Dict map_values: apply lambda to each value
fn eval_dict_map_values(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let local_env = bind_lambda_param(&captured, &params, v);
            let new_val = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
            new_map.insert(k.clone(), new_val);
        }
        Ok(Value::Dict(new_map))
    } else {
        Err(CompileError::Semantic("map_values expects lambda argument".into()))
    }
}

/// Dict filter: keep entries where lambda returns truthy
fn eval_dict_filter(
    map: &HashMap<String, Value>,
    func: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = func {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), Value::Str(k.clone()));
                local_env.insert(params[1].clone(), v.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), v.clone());
            }
            if evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                new_map.insert(k.clone(), v.clone());
            }
        }
        Ok(Value::Dict(new_map))
    } else {
        Err(CompileError::Semantic("filter expects lambda argument".into()))
    }
}

/// Convert a Message to a Value
fn message_to_value(msg: Message) -> Value {
    match msg {
        Message::Value(s) => Value::Str(s),
        Message::Bytes(b) => Value::Str(String::from_utf8_lossy(&b).to_string()),
    }
}

/// Option map: apply lambda to Some value
fn eval_option_map(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Use type-safe variant matching
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda { params, body, env: captured } = func_arg {
                let mut local_env = captured.clone();
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), val.as_ref().clone());
                }
                let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                return Ok(Value::some(result));
            }
        }
    }
    Ok(Value::none())
}

// === Helper functions for comprehensions and slicing ===

/// Convert a value to an iterable vector (for comprehensions)
fn iter_to_vec(val: &Value) -> Result<Vec<Value>, CompileError> {
    match val {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(tup) => Ok(tup.clone()),
        Value::Str(s) => Ok(s.chars().map(|c| Value::Str(c.to_string())).collect()),
        Value::Dict(map) => Ok(map.keys().map(|k| Value::Str(k.clone())).collect()),
        Value::Object { class, fields } if class == BUILTIN_RANGE => {
            // Range object
            let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
            let end = fields.get("end").and_then(|v| v.as_int().ok()).unwrap_or(0);
            let inclusive = fields.get("inclusive").map(|v| v.truthy()).unwrap_or(false);
            let items: Vec<Value> = if inclusive {
                (start..=end).map(Value::Int).collect()
            } else {
                (start..end).map(Value::Int).collect()
            };
            Ok(items)
        }
        _ => Err(CompileError::Semantic("cannot iterate over this type".into())),
    }
}

/// Bind a pattern to a value in an environment (returns false if pattern doesn't match)
fn bind_pattern(pattern: &Pattern, value: &Value, env: &mut Env) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::Tuple(patterns) => {
            if let Value::Tuple(values) = value {
                if patterns.len() != values.len() {
                    return false;
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !bind_pattern(pat, val, env) {
                        return false;
                    }
                }
                true
            } else if let Value::Array(values) = value {
                // Allow tuple pattern to match array
                if patterns.len() != values.len() {
                    return false;
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !bind_pattern(pat, val, env) {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
        Pattern::Array(patterns) => {
            if let Value::Array(values) = value {
                if patterns.len() != values.len() {
                    return false;
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !bind_pattern(pat, val, env) {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
        _ => {
            // For other patterns, just try identifier binding
            false
        }
    }
}

/// Normalize a Python-style index (handling negative indices)
fn normalize_index(idx: i64, len: i64) -> i64 {
    if idx < 0 {
        (len + idx).max(0)
    } else {
        idx.min(len)
    }
}

/// Slice a collection with Python-style semantics
fn slice_collection<T: Clone>(items: &[T], start: i64, end: i64, step: i64) -> Vec<T> {
    let len = items.len() as i64;

    if step > 0 {
        let mut result = Vec::new();
        let mut i = start;
        while i < end && i < len {
            if i >= 0 {
                result.push(items[i as usize].clone());
            }
            i += step;
        }
        result
    } else {
        // Negative step: go backwards
        let mut result = Vec::new();
        let actual_start = if start == 0 { len - 1 } else { start.min(len - 1) };
        let actual_end = if end == len { -1 } else { end };
        let mut i = actual_start;
        while i > actual_end && i >= 0 {
            if (i as usize) < items.len() {
                result.push(items[i as usize].clone());
            }
            i += step;
        }
        result
    }
}
