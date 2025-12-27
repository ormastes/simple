// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::value::{Value, Env, SpecialEnumType, OptionVariant, ResultVariant};
use simple_parser::ast::{Argument, FunctionDef, ClassDef};
use std::collections::HashMap;
use super::super::{
    evaluate_expr,
    eval_arg, eval_arg_int,
    eval_option_map, eval_option_and_then, eval_option_or_else, eval_option_filter,
    eval_result_map, eval_result_map_err, eval_result_and_then, eval_result_or_else,
    spawn_future_with_callable,
    exec_function,
    find_and_exec_method, try_method_missing,
    exec_block,
    bind_args,
    exec_block_fn,
    Control,
    UNIT_SUFFIX_TO_FAMILY, UNIT_FAMILY_CONVERSIONS,
    Enums, ImplMethods,
};
use crate::interpreter_unit::decompose_si_prefix;

/// Extract method name from Symbol or String argument
macro_rules! extract_method_name {
    ($args:expr, $idx:expr, $context:expr, $env:expr, $functions:expr, $classes:expr, $enums:expr, $impl_methods:expr) => {{
        let method_name = eval_arg($args, $idx, Value::Symbol("".to_string()), $env, $functions, $classes, $enums, $impl_methods)?;
        match &method_name {
            Value::Symbol(s) => s.clone(),
            Value::Str(s) => s.clone(),
            _ => return Err(CompileError::Semantic(format!("{} expects symbol or string method name", $context))),
        }
    }};
}

/// Execute operation with current configuring method
macro_rules! with_configuring_method {
    ($mock:expr, $context:expr, $op:expr) => {{
        let configuring = $mock.configuring_method.lock().unwrap();
        if let Some(ref method_name) = *configuring {
            $op(method_name)
        } else {
            Err(CompileError::Semantic(format!("{}() must be chained after verify(:method)", $context)))
        }
    }};
}

/// Extract result from exec_block_fn return value
macro_rules! extract_block_result {
    ($block_exec:expr) => {
        match $block_exec {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(CompileError::TryError(val)) => val,
            Err(e) => return Err(e),
        }
    };
}

/// Handle Unit value methods (value, suffix, family, to_string, to_X)
pub fn handle_unit_methods(
    value: &Box<Value>,
    suffix: &str,
    family: &Option<String>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match method {
        "value" => return Ok(Some((**value).clone())),
        "suffix" => return Ok(Some(Value::Str(suffix.to_string()))),
        "family" => return Ok(Some(family.clone().map_or(Value::Nil, Value::Str))),
        "to_string" => return Ok(Some(Value::Str(format!("{}_{}", value.to_display_string(), suffix)))),
        // For dynamic to_X() conversion methods, check if method starts with "to_"
        other if other.starts_with("to_") => {
            let target_suffix = &other[3..]; // Remove "to_" prefix

            // Get the family name - either from the Unit value or look it up (including SI prefix check)
            let family_name = family.clone().or_else(|| {
                // First try direct lookup
                if let Some(f) = UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned()) {
                    return Some(f);
                }
                // Try SI prefix decomposition
                if let Some((_mult, _base, f)) = decompose_si_prefix(suffix) {
                    return Some(f);
                }
                None
            });

            let Some(family_name) = family_name else {
                return Err(CompileError::Semantic(format!(
                    "Unit '{}' does not belong to a unit family, cannot convert to '{}'",
                    suffix, target_suffix
                )));
            };

            // Look up conversions for this family, with SI prefix support
            let conversion_result = UNIT_FAMILY_CONVERSIONS.with(|cell| {
                let families = cell.borrow();
                let Some(conversions) = families.get(&family_name) else {
                    return Err(CompileError::Semantic(format!(
                        "Unit family '{}' not found", family_name
                    )));
                };

                // Get source conversion factor (check SI prefix if not directly defined)
                // IMPORTANT: For SI-prefixed units, the value is already multiplied by the SI factor
                // when created. So we use factor 1.0 (base unit factor) since the value is in base units.
                let source_factor = if let Some(&f) = conversions.get(suffix) {
                    f
                } else if decompose_si_prefix(suffix).is_some() {
                    // SI prefixed: value is already in base units, so source factor is 1.0
                    1.0
                } else {
                    return Err(CompileError::Semantic(format!(
                        "Unit '{}' not found in family '{}'", suffix, family_name
                    )));
                };

                // Get target conversion factor (check SI prefix if not directly defined)
                let target_factor = if let Some(&f) = conversions.get(target_suffix) {
                    f
                } else if let Some((si_mult, base, _)) = decompose_si_prefix(target_suffix) {
                    // SI prefixed: multiply SI prefix by base unit factor
                    let base_factor = conversions.get(&base).copied().unwrap_or(1.0);
                    si_mult * base_factor
                } else {
                    return Err(CompileError::Semantic(format!(
                        "Target unit '{}' not found in family '{}'. Available: {:?}",
                        target_suffix, family_name, conversions.keys().collect::<Vec<_>>()
                    )));
                };

                Ok((source_factor, target_factor))
            })?;

            let (source_factor, target_factor) = conversion_result;

            // Perform the conversion: new_value = old_value * (source_factor / target_factor)
            // e.g., 2_km to m: 2 * (1000.0 / 1.0) = 2000
            let converted_value = match value.as_ref() {
                Value::Int(n) => {
                    let converted = (*n as f64) * (source_factor / target_factor);
                    // Keep as float if not a whole number
                    if converted.fract() == 0.0 {
                        Value::Int(converted as i64)
                    } else {
                        Value::Float(converted)
                    }
                }
                Value::Float(f) => {
                    Value::Float(f * (source_factor / target_factor))
                }
                _ => {
                    return Err(CompileError::Semantic(format!(
                        "Cannot convert non-numeric unit value: {:?}", value
                    )));
                }
            };

            // Return a new Unit value with the target suffix
            return Ok(Some(Value::Unit {
                value: Box::new(converted_value),
                suffix: target_suffix.to_string(),
                family: Some(family_name),
            }));
        }
        _ => {}
    }
    Ok(None)
}

/// Handle Option methods (is_some, is_none, unwrap, expect, map, and_then, etc.)
pub fn handle_option_methods(
    recv_val: &Value,
    enum_name: &str,
    variant: &str,
    payload: &Option<Box<Value>>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Use typed enum matching for Option
    if SpecialEnumType::from_name(enum_name) != Some(SpecialEnumType::Option) {
        return Ok(None);
    }

    let opt_variant = OptionVariant::from_name(variant);
    let result = match method {
        "is_some" => Value::Bool(opt_variant == Some(OptionVariant::Some)),
        "is_none" => Value::Bool(opt_variant == Some(OptionVariant::None)),
        "unwrap" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            return Err(CompileError::Semantic("called unwrap on None".into()));
        }
        "expect" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            let msg = eval_arg(args, 0, Value::Str("Option was None".into()), env, functions, classes, enums, impl_methods)?;
            return Err(CompileError::Semantic(msg.to_display_string()));
        }
        "unwrap_or" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            return Ok(Some(eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?));
        }
        "unwrap_or_else" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            // Call the function to get default value
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda { params: _, body, env: captured } = func_arg {
                return Ok(Some(evaluate_expr(&body, &captured, functions, classes, enums, impl_methods)?));
            }
            return Ok(Some(Value::Nil));
        }
        "or" => {
            // Returns self if Some, otherwise returns the other Option
            if opt_variant == Some(OptionVariant::Some) {
                return Ok(Some(recv_val.clone()));
            }
            return Ok(Some(eval_arg(args, 0, Value::none(), env, functions, classes, enums, impl_methods)?));
        }
        "ok_or" => {
            // Converts Option to Result: Some(v) -> Ok(v), None -> Err(error)
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(Value::ok(val.as_ref().clone())));
                }
            }
            let error = eval_arg(args, 0, Value::Str("None".into()), env, functions, classes, enums, impl_methods)?;
            return Ok(Some(Value::err(error)));
        }
        "map" => {
            return Ok(Some(eval_option_map(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "and_then" => {
            return Ok(Some(eval_option_and_then(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "or_else" => {
            return Ok(Some(eval_option_or_else(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "filter" => {
            return Ok(Some(eval_option_filter(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "flatten" => {
            // Option<Option<T>> -> Option<T>
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(inner) = payload {
                    // If inner is also an Option, return it
                    if let Value::Enum { enum_name: inner_enum, .. } = inner.as_ref() {
                        if inner_enum == "Option" {
                            return Ok(Some(inner.as_ref().clone()));
                        }
                    }
                }
            }
            Value::none()
        }
        "take" => {
            // Returns the value and replaces with None (for mutable contexts)
            // In immutable context, just returns the value
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            Value::none()
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle Result methods (is_ok, is_err, unwrap, expect, map, map_err, and_then, etc.)
pub fn handle_result_methods(
    recv_val: &Value,
    enum_name: &str,
    variant: &str,
    payload: &Option<Box<Value>>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Use typed enum matching for Result
    if SpecialEnumType::from_name(enum_name) != Some(SpecialEnumType::Result) {
        return Ok(None);
    }

    let res_variant = ResultVariant::from_name(variant);
    match method {
        "is_ok" => return Ok(Some(Value::Bool(res_variant == Some(ResultVariant::Ok)))),
        "is_err" => return Ok(Some(Value::Bool(res_variant == Some(ResultVariant::Err)))),
        "unwrap" => {
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            if res_variant == Some(ResultVariant::Err) {
                if let Some(err_val) = payload {
                    return Err(CompileError::Semantic(format!("called unwrap on Err: {}", err_val.to_display_string())));
                }
            }
            return Err(CompileError::Semantic("called unwrap on Err".into()));
        }
        "expect" => {
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            let msg = eval_arg(args, 0, Value::Str("Result was Err".into()), env, functions, classes, enums, impl_methods)?;
            if res_variant == Some(ResultVariant::Err) {
                if let Some(err_val) = payload {
                    return Err(CompileError::Semantic(format!("{}: {}", msg.to_display_string(), err_val.to_display_string())));
                }
            }
            return Err(CompileError::Semantic(msg.to_display_string()));
        }
        "unwrap_or" => {
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            return Ok(Some(eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?));
        }
        "unwrap_or_else" => {
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            // Call the function with error value to get default
            if let Some(err_val) = payload {
                let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda { params, body, env: captured } = func_arg {
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), err_val.as_ref().clone());
                    }
                    return Ok(Some(evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?));
                }
            }
            return Ok(Some(Value::Nil));
        }
        "unwrap_err" => {
            if res_variant == Some(ResultVariant::Err) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            return Err(CompileError::Semantic("called unwrap_err on Ok".into()));
        }
        "expect_err" => {
            if res_variant == Some(ResultVariant::Err) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            let msg = eval_arg(args, 0, Value::Str("Result was Ok".into()), env, functions, classes, enums, impl_methods)?;
            return Err(CompileError::Semantic(msg.to_display_string()));
        }
        "ok" => {
            if res_variant == Some(ResultVariant::Ok) {
                return Ok(Some(payload.as_ref().map(|p| Value::some(p.as_ref().clone())).unwrap_or_else(Value::none)));
            }
            return Ok(Some(Value::none()));
        }
        "err" => {
            if res_variant == Some(ResultVariant::Err) {
                return Ok(Some(payload.as_ref().map(|p| Value::some(p.as_ref().clone())).unwrap_or_else(Value::none)));
            }
            return Ok(Some(Value::none()));
        }
        "or" => {
            // Returns self if Ok, otherwise returns the other Result
            if res_variant == Some(ResultVariant::Ok) {
                return Ok(Some(recv_val.clone()));
            }
            return Ok(Some(eval_arg(args, 0, Value::err(Value::Nil), env, functions, classes, enums, impl_methods)?));
        }
        "map" => {
            return Ok(Some(eval_result_map(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "map_err" => {
            return Ok(Some(eval_result_map_err(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "and_then" => {
            return Ok(Some(eval_result_and_then(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "or_else" => {
            return Ok(Some(eval_result_or_else(variant, payload, args, env, functions, classes, enums, impl_methods)?));
        }
        "flatten" => {
            // Result<Result<T, E>, E> -> Result<T, E>
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(inner) = payload {
                    // If inner is also a Result, return it
                    if let Value::Enum { enum_name: inner_enum, .. } = inner.as_ref() {
                        if inner_enum == "Result" {
                            return Ok(Some(inner.as_ref().clone()));
                        }
                    }
                }
            }
            // Return Err as-is
            return Ok(Some(recv_val.clone()));
        }
        _ => return Ok(None),
    }
}

/// Handle Mock methods (when, withArgs, returns, returnsOnce, verify, called, calledTimes, calledWith, reset, getCalls)
pub fn handle_mock_methods(
    mock: &crate::value::MockValue,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match method {
        // when(:method_name) - Configure a method for stubbing
        "when" => {
            let method_str = extract_method_name!(args, 0, "when", env, functions, classes, enums, impl_methods);
            mock.when_method(&method_str);
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // withArgs(args...) - Set argument matchers for current configuration
        "withArgs" | "with_args" => {
            let mut matchers = Vec::new();
            for arg in args {
                let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                let matcher = match val {
                    Value::Matcher(m) => m,
                    other => crate::value::MatcherValue::Exact(Box::new(other)),
                };
                matchers.push(matcher);
            }
            mock.with_args(matchers);
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // returns(value) - Set return value for configured method
        "returns" => {
            let return_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            mock.returns(return_val);
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // returnsOnce(value) - Set return value for next call only
        "returnsOnce" | "returns_once" => {
            let return_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            mock.returns_once(return_val);
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // verify(:method_name) - Start verification for a method
        "verify" => {
            let method_str = extract_method_name!(args, 0, "verify", env, functions, classes, enums, impl_methods);
            mock.when_method(&method_str); // Reuse to set current method
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // called() - Check if method was called at least once
        "called" => {
            with_configuring_method!(mock, "called", |method_name| {
                let was_called = mock.was_called(method_name);
                Ok(Some(Value::Bool(was_called)))
            })
        }
        // calledTimes(n) - Check exact call count
        "calledTimes" | "called_times" => {
            let expected = eval_arg_int(args, 0, 1, env, functions, classes, enums, impl_methods)?;
            with_configuring_method!(mock, "calledTimes", |method_name| {
                let actual = mock.call_count(method_name) as i64;
                Ok(Some(Value::Bool(actual == expected)))
            })
        }
        // calledWith(args...) - Check if method was called with specific arguments
        "calledWith" | "called_with" => {
            let mut expected_args = Vec::new();
            for arg in args {
                let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                expected_args.push(val);
            }
            with_configuring_method!(mock, "calledWith", |method_name| {
                let was_called_with = mock.was_called_with(method_name, &expected_args);
                Ok(Some(Value::Bool(was_called_with)))
            })
        }
        // reset() - Clear all call records
        "reset" => {
            mock.reset();
            return Ok(Some(Value::Mock(mock.clone())));
        }
        // getCalls(:method) - Get all calls to a method
        "getCalls" | "get_calls" => {
            let method_str = extract_method_name!(args, 0, "getCalls", env, functions, classes, enums, impl_methods);
            let calls = mock.get_calls(&method_str);
            let call_arrays: Vec<Value> = calls.into_iter().map(Value::Array).collect();
            return Ok(Some(Value::Array(call_arrays)));
        }
        // Any other method is treated as a mock call
        _ => {
            // Evaluate arguments
            let mut call_args = Vec::new();
            for arg in args {
                let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                call_args.push(val);
            }
            // Record the call
            mock.record_call(method, call_args.clone());
            // Return configured value
            return Ok(Some(mock.get_return_value(method, &call_args)));
        }
    }
}

/// Handle Future methods (join, await, get, is_ready)
pub fn handle_future_methods(
    future: &crate::value::FutureValue,
    method: &str,
) -> Result<Option<Value>, CompileError> {
    match method {
        "join" | "await" | "get" => {
            return Ok(Some(future.await_result().map_err(|e| CompileError::Semantic(e))?));
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
    env: &Env,
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
    env: &Env,
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

/// Handle TraitObject dynamic dispatch
pub fn handle_trait_object_methods(
    trait_name: &str,
    inner: &Box<Value>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Extract the inner value's class/type
    if let Value::Object { class, fields } = inner.as_ref() {
        // Try to find and execute the method on the inner object
        if let Some(result) = find_and_exec_method(method, args, class, fields, env, functions, classes, enums, impl_methods)? {
            return Ok(Some(result));
        }
        return Err(CompileError::Semantic(format!(
            "Method '{}' not found on dyn {} (type: {})",
            method, trait_name, class
        )));
    }
    Err(CompileError::Semantic(format!(
        "Cannot call method '{}' on dyn {}: inner value is not an object",
        method, trait_name
    )))
}

/// Handle Constructor static method calls
pub fn handle_constructor_methods(
    class_name: &str,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if let Some(class_def) = classes.get(class_name).cloned() {
        // Find static method (no self parameter)
        if let Some(method_def) = class_def.methods.iter().find(|m| m.name == method) {
            // Execute without self - start with empty local_env to avoid shadowing defaults
            let mut local_env: HashMap<String, Value> = HashMap::new();
            let mut positional_idx = 0;

            // Bind provided arguments
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

            // Bind default values for remaining parameters using an empty scope
            // to prevent caller's variables from shadowing defaults
            let empty_env: HashMap<String, Value> = HashMap::new();
            for param in &method_def.params {
                if !local_env.contains_key(&param.name) {
                    if let Some(default_expr) = &param.default {
                        let default_val = evaluate_expr(default_expr, &empty_env, functions, classes, enums, impl_methods)?;
                        local_env.insert(param.name.clone(), default_val);
                    }
                }
            }

            return match exec_block(&method_def.body, &mut local_env, functions, classes, enums, impl_methods) {
                Ok(Control::Return(v)) => Ok(Some(v)),
                Ok(_) => Ok(Some(Value::Nil)),
                Err(e) => Err(e),
            };
        }
        // Collect available static methods for suggestion
        let available: Vec<&str> = class_def
            .methods
            .iter()
            .filter(|m| !m.params.iter().any(|p| p.name == "self"))
            .map(|m| m.name.as_str())
            .collect();
        let mut msg = format!("unknown static method {method} on class {class_name}");
        if let Some(suggestion) = crate::error::typo::format_suggestion(method, available) {
            msg.push_str(&format!("; {}", suggestion));
        }
        return Err(CompileError::Semantic(msg));
    }
    // Collect available classes for suggestion
    let available: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
    let mut msg = format!("unknown class {class_name}");
    if let Some(suggestion) = crate::error::typo::format_suggestion(class_name, available) {
        msg.push_str(&format!("; {}", suggestion));
    }
    Err(CompileError::Semantic(msg))
}

/// Find and execute a method with self return (for mutation tracking)
pub fn find_and_exec_method_with_self(
    method: &str,
    args: &[Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class).cloned() {
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

/// Execute a function and return both result and modified self
pub fn exec_function_with_self_return(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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

    // Execute the function body with implicit return support
    let result = extract_block_result!(exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods));

    // Get the potentially modified self
    let updated_self = local_env.get("self").cloned().unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: fields.clone(),
    });

    Ok((result, updated_self))
}
