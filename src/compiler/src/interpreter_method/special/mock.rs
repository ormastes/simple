//! Mock type methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::interpreter_helpers::eval_arg_int;
use crate::interpreter::{eval_arg, evaluate_expr, Enums, ImplMethods};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;
/// Extract method name from Symbol or String argument
macro_rules! extract_method_name {
    ($args:expr, $idx:expr, $context:expr, $env:expr, $functions:expr, $classes:expr, $enums:expr, $impl_methods:expr) => {{
        let method_name = eval_arg(
            $args,
            $idx,
            Value::Symbol("".to_string()),
            $env,
            $functions,
            $classes,
            $enums,
            $impl_methods,
        )?;
        match &method_name {
            Value::Symbol(s) => s.clone(),
            Value::Str(s) => s.clone(),
            _ => {
                return Err(CompileError::Semantic(format!(
                    "{} expects symbol or string method name",
                    $context
                )))
            }
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
            Err(CompileError::Semantic(format!(
                "{}() must be chained after verify(:method)",
                $context
            )))
        }
    }};
}

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
