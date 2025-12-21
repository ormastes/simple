// Option and Result helper functions for the interpreter
//
// This module contains helper functions for Option and Result type methods:
// - map, and_then, or_else, filter for Option
// - map, map_err, and_then, or_else for Result
// - Message to Value conversion

/// Convert a Message to a Value
fn message_to_value(msg: Message) -> Value {
    match msg {
        Message::Value(s) => Value::Str(s),
        Message::Bytes(b) => Value::Str(String::from_utf8_lossy(&b).to_string()),
    }
}

/// Helper: Apply a lambda to a value with the given environment and contexts
/// Returns the result of evaluating the lambda body
fn apply_lambda_to_value(
    val: &Value,
    lambda_arg: Value,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Lambda { params, body, env: captured } = lambda_arg {
        let mut local_env = captured.clone();
        if let Some(param) = params.first() {
            local_env.insert(param.clone(), val.clone());
        }
        evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)
    } else {
        Ok(Value::Nil)
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
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(Value::some(result));
        }
    }
    Ok(Value::none())
}

/// Option and_then: flat-map - apply lambda that returns Option to Some value
fn eval_option_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            // Return result as-is (should be Option)
            return apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods);
        }
    }
    Ok(Value::none())
}

/// Option or_else: if None, call function to get alternative Option
fn eval_option_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        // Return Some(payload) as-is
        return Ok(Value::Enum {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: payload.clone(),
        });
    }
    // None case: call the function to get alternative
    let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
    if let Value::Lambda { params: _, body, env: captured } = func_arg {
        return evaluate_expr(&body, &captured, functions, classes, enums, impl_methods);
    }
    Ok(Value::none())
}

/// Option filter: if Some and predicate returns true, keep Some; else None
fn eval_option_filter(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if OptionVariant::from_name(variant) == Some(OptionVariant::Some) {
        if let Some(val) = payload {
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda { params, body, env: captured } = func_arg {
                let mut local_env = captured.clone();
                if let Some(param) = params.first() {
                    local_env.insert(param.clone(), val.as_ref().clone());
                }
                let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                if result.truthy() {
                    return Ok(Value::some(val.as_ref().clone()));
                }
            }
        }
    }
    Ok(Value::none())
}

/// Result map: apply lambda to Ok value
fn eval_result_map(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(Value::ok(result));
        }
    }
    // Return Err as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result map_err: apply lambda to Err value
fn eval_result_map_err(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Err) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let result = apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods)?;
            return Ok(Value::err(result));
        }
    }
    // Return Ok as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result and_then: flat-map - apply lambda that returns Result to Ok value
fn eval_result_and_then(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        if let Some(val) = payload {
            let lambda = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            // Return result as-is (should be Result)
            return apply_lambda_to_value(val.as_ref(), lambda, functions, classes, enums, impl_methods);
        }
    }
    // Return Err as-is
    Ok(Value::Enum {
        enum_name: "Result".to_string(),
        variant: variant.to_string(),
        payload: payload.clone(),
    })
}

/// Result or_else: if Err, call function to get alternative Result
fn eval_result_or_else(
    variant: &str,
    payload: &Option<Box<Value>>,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if ResultVariant::from_name(variant) == Some(ResultVariant::Ok) {
        // Return Ok as-is
        return Ok(Value::Enum {
            enum_name: "Result".to_string(),
            variant: "Ok".to_string(),
            payload: payload.clone(),
        });
    }
    // Err case: call the function with error value
    if let Some(err_val) = payload {
        let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
        if let Value::Lambda { params, body, env: captured } = func_arg {
            let mut local_env = captured.clone();
            if let Some(param) = params.first() {
                local_env.insert(param.clone(), err_val.as_ref().clone());
            }
            return evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods);
        }
    }
    Ok(Value::err(Value::Nil))
}
