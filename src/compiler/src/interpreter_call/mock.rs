// Mock library for interpreter
// Matchers: mock, spy, any, eq, be, gt, lt, contains, etc.

use crate::value::*;
use crate::error::CompileError;
use crate::interpreter::evaluate_expr;
use simple_parser::ast::{Argument, FunctionDef, ClassDef, EnumDef};
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

fn eval_arg(
    args: &[Argument],
    index: usize,
    default: Value,
    env: &Env,
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
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<i64, CompileError> {
    let val = eval_arg(args, index, Value::Int(default), env, functions, classes, enums, impl_methods)?;
    val.as_int().map_err(|_| semantic_err!("expected integer"))
}

pub(super) fn eval_mock_builtin(
    name: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match name {
        "mock" => {
            let type_name = eval_arg(args, 0, Value::Str("Mock".to_string()), env, functions, classes, enums, impl_methods)?;
            let type_str = match &type_name {
                Value::Str(s) => s.clone(),
                Value::Symbol(s) => s.clone(),
                _ => "Mock".to_string(),
            };
            Ok(Some(Value::Mock(crate::value::MockValue::new(type_str))))
        }
        "spy" => {
            let type_name = eval_arg(args, 0, Value::Str("Spy".to_string()), env, functions, classes, enums, impl_methods)?;
            let type_str = match &type_name {
                Value::Str(s) => s.clone(),
                Value::Symbol(s) => s.clone(),
                _ => "Spy".to_string(),
            };
            Ok(Some(Value::Mock(crate::value::MockValue::new_spy(type_str))))
        }
        "any" => {
            Ok(Some(Value::Matcher(crate::value::MatcherValue::Any)))
        }
        "eq" | "be" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(val)))))
        }
        "be_gt" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::GreaterThan(n))))
        }
        "be_lt" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::LessThan(n))))
        }
        "be_nil" => {
            Ok(Some(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(Value::Nil)))))
        }
        "be_empty" => {
            Ok(Some(Value::Matcher(crate::value::MatcherValue::Custom(Box::new(Value::Nil)))))
        }
        "include" => {
            let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            match &val {
                Value::Str(s) => Ok(Some(Value::Matcher(crate::value::MatcherValue::Contains(s.clone())))),
                _ => Ok(Some(Value::Matcher(crate::value::MatcherValue::Exact(Box::new(val))))),
            }
        }
        "start_with" => {
            let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let s_str = match &s {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::StartsWith(s_str))))
        }
        "end_with" => {
            let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let s_str = match &s {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::EndsWith(s_str))))
        }
        "gt" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::GreaterThan(n))))
        }
        "lt" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::LessThan(n))))
        }
        "gte" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::GreaterOrEqual(n))))
        }
        "lte" => {
            let n = eval_arg_int(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(crate::value::MatcherValue::LessOrEqual(n))))
        }
        "contains" => {
            let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let s_str = match &s {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::Contains(s_str))))
        }
        "starts_with" => {
            let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let s_str = match &s {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::StartsWith(s_str))))
        }
        "ends_with" => {
            let s = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let s_str = match &s {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::EndsWith(s_str))))
        }
        "of_type" => {
            let type_name = eval_arg(args, 0, Value::Str("".to_string()), env, functions, classes, enums, impl_methods)?;
            let type_str = match &type_name {
                Value::Str(s) => s.clone(),
                _ => "".to_string(),
            };
            Ok(Some(Value::Matcher(crate::value::MatcherValue::OfType(type_str))))
        }
        _ => Ok(None),
    }
}
