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

/// Helper for array predicate operations (filter, find, any, all)
fn with_lambda_predicate<F>(
    func: Value,
    operation: &str,
    mut process: F,
) -> Result<Value, CompileError>
where
    F: FnMut(&[String], &Expr, &Env) -> Result<Value, CompileError>,
{
    if let Value::Lambda { params, body, env: captured } = func {
        process(&params, &body, &captured)
    } else {
        Err(CompileError::Semantic(format!("{operation} expects lambda argument")))
    }
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
    with_lambda_predicate(func, "filter", |params, body, captured| {
        let mut results = Vec::new();
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                results.push(item.clone());
            }
        }
        Ok(Value::Array(results))
    })
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
    with_lambda_predicate(func, "find", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(item.clone());
            }
        }
        Ok(Value::Nil)
    })
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
    with_lambda_predicate(func, "any", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    })
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
    with_lambda_predicate(func, "all", |params, body, captured| {
        for item in arr {
            let local_env = bind_lambda_param(captured, params, item);
            if !evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    })
}

/// Helper for dict operations with lambda
fn with_dict_lambda<F>(
    func: Value,
    operation: &str,
    process: F,
) -> Result<Value, CompileError>
where
    F: FnOnce(&[String], &Expr, &Env) -> Result<Value, CompileError>,
{
    if let Value::Lambda { params, body, env: captured } = func {
        process(&params, &body, &captured)
    } else {
        Err(CompileError::Semantic(format!("{operation} expects lambda argument")))
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
    with_dict_lambda(func, "map_values", |params, body, captured| {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let local_env = bind_lambda_param(captured, params, v);
            let new_val = evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?;
            new_map.insert(k.clone(), new_val);
        }
        Ok(Value::Dict(new_map))
    })
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
    with_dict_lambda(func, "filter", |params, body, captured| {
        let mut new_map = HashMap::new();
        for (k, v) in map {
            let mut local_env = captured.clone();
            if params.len() >= 2 {
                local_env.insert(params[0].clone(), Value::Str(k.clone()));
                local_env.insert(params[1].clone(), v.clone());
            } else if let Some(param) = params.first() {
                local_env.insert(param.clone(), v.clone());
            }
            if evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                new_map.insert(k.clone(), v.clone());
            }
        }
        Ok(Value::Dict(new_map))
    })
}

// === Helper functions for comprehensions and slicing ===

// Option and Result helpers are included from a separate file
include!("interpreter_helpers_option_result.rs");

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

/// Helper for binding sequence patterns (Tuple and Array) during comprehensions
fn bind_sequence_pattern(value: &Value, patterns: &[Pattern], env: &mut Env, allow_tuple: bool) -> bool {
    let values = match value {
        Value::Tuple(vals) if allow_tuple => vals,
        Value::Array(vals) => vals,
        _ => return false,
    };
    
    if patterns.len() != values.len() {
        return false;
    }
    
    for (pat, val) in patterns.iter().zip(values.iter()) {
        if !bind_pattern(pat, val, env) {
            return false;
        }
    }
    true
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
        Pattern::Tuple(patterns) => bind_sequence_pattern(value, patterns, env, true),
        Pattern::Array(patterns) => bind_sequence_pattern(value, patterns, env, false),
        _ => {
            // For other patterns, just try identifier binding
            false
        }
    }
}

// === Helper functions to reduce duplication in interpreter.rs ===

/// Handle functional update expression: target.&method(args)
/// Returns Ok(Some(new_value)) if successfully processed, Ok(None) if not applicable
fn handle_functional_update(
    target: &Expr,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(String, Value)>, CompileError> {
    if let Expr::Identifier(name) = target {
        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            return Err(CompileError::Semantic(format!(
                "cannot use functional update on const '{name}'"
            )));
        }
        let recv_val = env.get(name).cloned().ok_or_else(|| {
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut msg = format!("undefined variable: {name}");
            if let Some(suggestion) = crate::error::typo::format_suggestion(name, known_names) {
                msg.push_str(&format!("; {}", suggestion));
            }
            CompileError::Semantic(msg)
        })?;
        let method_call = Expr::MethodCall {
            receiver: Box::new(Expr::Identifier(name.clone())),
            method: method.to_string(),
            args: args.to_vec(),
        };
        let result = evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
        let new_value = match (&recv_val, &result) {
            (Value::Array(_), Value::Array(_)) => result,
            (Value::Dict(_), Value::Dict(_)) => result,
            (Value::Str(_), Value::Str(_)) => result,
            (Value::Tuple(_), Value::Tuple(_)) => result,
            (Value::Object { .. }, Value::Object { .. }) => result,
            _ => env.get(name).cloned().unwrap_or(recv_val),
        };
        Ok(Some((name.clone(), new_value)))
    } else {
        Err(CompileError::Semantic(
            "functional update target must be an identifier".into(),
        ))
    }
}

/// Handle method call on object with self-update tracking
/// Returns (result, optional_updated_self) where updated_self is the object with mutations
fn handle_method_call_with_self_update(
    value_expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<(String, Value)>), CompileError> {
    if let Expr::MethodCall { receiver, method, args } = value_expr {
        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            if let Some(Value::Object { .. }) = env.get(obj_name) {
                let (result, updated_self) = evaluate_method_call_with_self_update(
                    receiver, method, args, env, functions, classes, enums, impl_methods
                )?;
                if let Some(new_self) = updated_self {
                    return Ok((result, Some((obj_name.clone(), new_self))));
                }
                return Ok((result, None));
            }
        }
    }
    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}

/// Bind a single pattern element from a let statement
/// Updates const names set if the binding is immutable
fn bind_let_pattern_element(
    pat: &Pattern,
    val: Value,
    is_mutable: bool,
    env: &mut Env,
) {
    match pat {
        Pattern::Identifier(name) => {
            env.insert(name.clone(), val);
            if !is_mutable {
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
            }
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), val);
        }
        Pattern::Typed { pattern, .. } => {
            bind_let_pattern_element(pattern, val, is_mutable, env);
        }
        _ => {}
    }
}

/// Bind any pattern from a let statement.
fn bind_pattern_value(pat: &Pattern, val: Value, is_mutable: bool, env: &mut Env) {
    match pat {
        Pattern::Tuple(patterns) => {
            // Allow tuple pattern to match both Tuple and Array
            let values: Vec<Value> = match val {
                Value::Tuple(v) => v,
                Value::Array(v) => v,
                _ => Vec::new(),
            };
            bind_collection_pattern(patterns, values, is_mutable, env);
        }
        Pattern::Array(patterns) => {
            if let Value::Array(values) = val {
                bind_collection_pattern(patterns, values, is_mutable, env);
            }
        }
        _ => bind_let_pattern_element(pat, val, is_mutable, env),
    }
}

/// Bind a collection pattern (tuple or array) from a let statement.
fn bind_collection_pattern(
    patterns: &[Pattern],
    values: Vec<Value>,
    is_mutable: bool,
    env: &mut Env,
) {
    for (pat, val) in patterns.iter().zip(values.into_iter()) {
        bind_pattern_value(pat, val, is_mutable, env);
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

/// Convert a Control result to a Value result for function return.
/// This is used by multiple interpreter modules to handle function return values.
pub(crate) fn control_to_value(result: Result<Control, CompileError>) -> Result<Value, CompileError> {
    match result {
        Ok(Control::Return(v)) => Ok(v),
        Ok(Control::Next) => Ok(Value::Nil),
        Ok(Control::Break(_)) => Err(CompileError::Semantic("break outside loop".into())),
        Ok(Control::Continue) => Err(CompileError::Semantic("continue outside loop".into())),
        Err(e) => Err(e),
    }
}

/// Iterate over items with pattern binding and optional condition filtering.
/// Returns a vector of environments for items that match the pattern and pass the condition.
/// This is used by both ListComprehension and DictComprehension to avoid code duplication.
fn comprehension_iterate(
    iterable: &Value,
    pattern: &Pattern,
    condition: &Option<Box<Expr>>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Env>, CompileError> {
    let items = iter_to_vec(iterable)?;
    let mut result = Vec::new();

    for item in items {
        // Create a new scope with the pattern binding
        let mut inner_env = env.clone();
        if !bind_pattern(pattern, &item, &mut inner_env) {
            continue;
        }

        // Check condition if present
        if let Some(cond) = condition {
            let cond_val = evaluate_expr(
                cond,
                &mut inner_env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if !cond_val.truthy() {
                continue;
            }
        }

        result.push(inner_env);
    }

    Ok(result)
}

// ============================================================================
// Effect management helpers
// ============================================================================

/// Execute a closure with the given function's effect context.
/// Saves the current effects, sets the function's effects if present,
/// executes the closure, and restores the previous effects.
pub(crate) fn with_effect_context<F, T>(func_effects: &[simple_parser::ast::Effect], f: F) -> T
where
    F: FnOnce() -> T,
{
    use crate::effects::{restore_effects, set_current_effects};

    // Only change context if function has explicit effects
    if func_effects.is_empty() {
        return f();
    }

    let prev_effects = set_current_effects(func_effects);
    let result = f();
    restore_effects(prev_effects);
    result
}

// ============================================================================
// Async execution helpers (reduce duplication in spawn_isolated, async, pool.submit)
// ============================================================================

/// Cloned interpreter context for async execution.
/// Used to pass execution context across thread boundaries.
#[derive(Clone)]
struct ClonedContext {
    functions: HashMap<String, FunctionDef>,
    classes: HashMap<String, ClassDef>,
    enums: Enums,
    impl_methods: ImplMethods,
}

impl ClonedContext {
    /// Clone context from references
    fn from_refs(
        functions: &HashMap<String, FunctionDef>,
        classes: &HashMap<String, ClassDef>,
        enums: &Enums,
        impl_methods: &ImplMethods,
    ) -> Self {
        Self {
            functions: functions.clone(),
            classes: classes.clone(),
            enums: enums.clone(),
            impl_methods: impl_methods.clone(),
        }
    }
}

/// Execute a callable (Function or Lambda) with a single argument.
/// If base_env is provided, it's used as the base environment (for spawn_isolated).
/// Otherwise, the callable's captured_env is used (for pool.submit).
/// Returns Ok(value) or Err(error_message).
fn execute_callable_with_arg(
    callable: Value,
    arg: Value,
    base_env: Option<&Env>,
    ctx: &ClonedContext,
) -> Result<Value, String> {
    match callable {
        Value::Function { ref def, ref captured_env, .. } => {
            // Use base_env if provided (spawn_isolated), otherwise use captured_env (pool.submit)
            let mut local_env = base_env.cloned().unwrap_or_else(|| captured_env.clone());
            if let Some(first_param) = def.params.first() {
                local_env.insert(first_param.name.clone(), arg);
            }
            match exec_block(&def.body, &mut local_env, &ctx.functions, &ctx.classes, &ctx.enums, &ctx.impl_methods) {
                Ok(Control::Return(v)) => Ok(v),
                Ok(_) => Ok(Value::Nil),
                Err(e) => Err(format!("{:?}", e)),
            }
        }
        Value::Lambda { ref params, ref body, ref env } => {
            // For lambdas, always use the captured env (they are closures)
            let mut local_env = env.clone();
            if let Some(first_param) = params.first() {
                local_env.insert(first_param.clone(), arg);
            }
            evaluate_expr(&body, &local_env, &ctx.functions, &ctx.classes, &ctx.enums, &ctx.impl_methods)
                .map_err(|e| format!("{:?}", e))
        }
        _ => Err("expected a function or lambda".into()),
    }
}

/// Create a FutureValue that executes a callable with an argument.
/// Uses the callable's captured environment.
/// Clones all necessary context for thread-safe execution.
fn spawn_future_with_callable(
    callable: Value,
    arg: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || execute_callable_with_arg(callable, arg, None, &ctx))
}

/// Create a FutureValue that executes a callable with an argument and outer environment.
/// Uses the outer environment as the base (for spawn_isolated semantics).
/// Clones all necessary context for thread-safe execution.
fn spawn_future_with_callable_and_env(
    callable: Value,
    arg: Value,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let env_clone = env.clone();
    let ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || execute_callable_with_arg(callable, arg, Some(&env_clone), &ctx))
}

/// Create a FutureValue that evaluates an expression.
/// Clones all necessary context for thread-safe execution.
fn spawn_future_with_expr(
    expr: Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> FutureValue {
    let env_clone = env.clone();
    let ctx = ClonedContext::from_refs(functions, classes, enums, impl_methods);
    FutureValue::new(move || {
        evaluate_expr(&expr, &env_clone, &ctx.functions, &ctx.classes, &ctx.enums, &ctx.impl_methods)
            .map_err(|e| format!("{:?}", e))
    })
}
