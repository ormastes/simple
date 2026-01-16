// Primitive type methods: Int, Float, Bool

use super::super::{eval_arg, eval_arg_int, eval_arg_usize, evaluate_expr, Enums, ImplMethods};
use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;

/// Handle Int methods
pub fn handle_int_methods(
    n: i64,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "abs" => Value::Int(n.abs()),
        "sign" | "signum" => Value::Int(n.signum()),
        "is_positive" => Value::Bool(n > 0),
        "is_negative" => Value::Bool(n < 0),
        "is_zero" => Value::Bool(n == 0),
        "is_even" => Value::Bool(n % 2 == 0),
        "is_odd" => Value::Bool(n % 2 != 0),
        "to_float" => Value::Float(n as f64),
        "to_string" => Value::Str(n.to_string()),
        "clamp" => {
            let min = eval_arg(
                args,
                0,
                Value::Int(i64::MIN),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .as_int()
            .unwrap_or(i64::MIN);
            let max = eval_arg(
                args,
                1,
                Value::Int(i64::MAX),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .as_int()
            .unwrap_or(i64::MAX);
            Value::Int(n.clamp(min, max))
        }
        "min" => {
            let other = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(n);
            Value::Int(n.min(other))
        }
        "max" => {
            let other = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(n);
            Value::Int(n.max(other))
        }
        "pow" => {
            let exp = eval_arg(args, 0, Value::Int(1), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(1) as u32;
            Value::Int(n.saturating_pow(exp))
        }
        "bit_count" | "count_ones" => Value::Int(n.count_ones() as i64),
        "leading_zeros" => Value::Int(n.leading_zeros() as i64),
        "trailing_zeros" => Value::Int(n.trailing_zeros() as i64),
        "to_hex" => Value::Str(format!("{:x}", n)),
        "to_bin" => Value::Str(format!("{:b}", n)),
        "to_oct" => Value::Str(format!("{:o}", n)),
        "times" => {
            // Call a function n times, returning array of results
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut results = Vec::new();
            if let Value::Lambda {
                params,
                body,
                env: mut captured,
            } = func
            {
                for i in 0..n.max(0) {
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), Value::Int(i));
                    }
                    let result = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    results.push(result);
                }
            }
            Value::Array(results)
        }
        "up_to" => {
            // Create range from self to n (exclusive)
            let end = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(n);
            let range: Vec<Value> = (n..end).map(Value::Int).collect();
            Value::Array(range)
        }
        "down_to" => {
            // Create range from self down to n (exclusive)
            let end = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(0);
            let range: Vec<Value> = (end..n).rev().map(Value::Int).collect();
            Value::Array(range)
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle Float methods
pub fn handle_float_methods(
    f: f64,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "abs" => Value::Float(f.abs()),
        "sign" | "signum" => Value::Float(f.signum()),
        "is_positive" => Value::Bool(f > 0.0),
        "is_negative" => Value::Bool(f < 0.0),
        "is_zero" => Value::Bool(f == 0.0),
        "is_nan" => Value::Bool(f.is_nan()),
        "is_infinite" => Value::Bool(f.is_infinite()),
        "is_finite" => Value::Bool(f.is_finite()),
        "to_int" | "truncate" => Value::Int(f.trunc() as i64),
        "to_string" => Value::Str(f.to_string()),
        "floor" => Value::Float(f.floor()),
        "ceil" => Value::Float(f.ceil()),
        "round" => Value::Float(f.round()),
        "trunc" => Value::Float(f.trunc()),
        "fract" => Value::Float(f.fract()),
        "sqrt" => Value::Float(f.sqrt()),
        "cbrt" => Value::Float(f.cbrt()),
        "exp" => Value::Float(f.exp()),
        "exp2" => Value::Float(f.exp2()),
        "ln" => Value::Float(f.ln()),
        "log2" => Value::Float(f.log2()),
        "log10" => Value::Float(f.log10()),
        "sin" => Value::Float(f.sin()),
        "cos" => Value::Float(f.cos()),
        "tan" => Value::Float(f.tan()),
        "asin" => Value::Float(f.asin()),
        "acos" => Value::Float(f.acos()),
        "atan" => Value::Float(f.atan()),
        "sinh" => Value::Float(f.sinh()),
        "cosh" => Value::Float(f.cosh()),
        "tanh" => Value::Float(f.tanh()),
        "clamp" => {
            let min = eval_arg(
                args,
                0,
                Value::Float(f64::MIN),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .as_float()
            .unwrap_or(f64::MIN);
            let max = eval_arg(
                args,
                1,
                Value::Float(f64::MAX),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .as_float()
            .unwrap_or(f64::MAX);
            Value::Float(f.clamp(min, max))
        }
        "min" => {
            let other = eval_arg(args, 0, Value::Float(f), env, functions, classes, enums, impl_methods)?
                .as_float()
                .unwrap_or(f);
            Value::Float(f.min(other))
        }
        "max" => {
            let other = eval_arg(args, 0, Value::Float(f), env, functions, classes, enums, impl_methods)?
                .as_float()
                .unwrap_or(f);
            Value::Float(f.max(other))
        }
        "pow" | "powf" => {
            let exp = eval_arg(args, 0, Value::Float(1.0), env, functions, classes, enums, impl_methods)?
                .as_float()
                .unwrap_or(1.0);
            Value::Float(f.powf(exp))
        }
        "powi" => {
            let exp = eval_arg(args, 0, Value::Int(1), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(1) as i32;
            Value::Float(f.powi(exp))
        }
        "log" => {
            let base = eval_arg(
                args,
                0,
                Value::Float(std::f64::consts::E),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .as_float()
            .unwrap_or(std::f64::consts::E);
            Value::Float(f.log(base))
        }
        "atan2" => {
            let other = eval_arg(args, 0, Value::Float(1.0), env, functions, classes, enums, impl_methods)?
                .as_float()
                .unwrap_or(1.0);
            Value::Float(f.atan2(other))
        }
        "hypot" => {
            let other = eval_arg(args, 0, Value::Float(0.0), env, functions, classes, enums, impl_methods)?
                .as_float()
                .unwrap_or(0.0);
            Value::Float(f.hypot(other))
        }
        "to_degrees" => Value::Float(f.to_degrees()),
        "to_radians" => Value::Float(f.to_radians()),
        "round_to" => {
            let places = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(0) as i32;
            let multiplier = 10f64.powi(places);
            Value::Float((f * multiplier).round() / multiplier)
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle Bool methods
pub fn handle_bool_methods(
    b: bool,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "to_int" => Value::Int(if b { 1 } else { 0 }),
        "to_string" => Value::Str(b.to_string()),
        "then" => {
            // Returns Some(result) if true, None if false
            if b {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda {
                    params: _,
                    body,
                    env: mut captured,
                } = func
                {
                    let result = evaluate_expr(&body, &mut captured, functions, classes, enums, impl_methods)?;
                    return Ok(Some(Value::some(result)));
                }
                return Ok(Some(Value::some(Value::Nil)));
            }
            return Ok(Some(Value::none()));
        }
        "then_else" => {
            let then_func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let else_func = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let func = if b { then_func } else { else_func };
            if let Value::Lambda {
                params: _,
                body,
                env: mut captured,
            } = func
            {
                return Ok(Some(evaluate_expr(
                    &body,
                    &mut captured,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?));
            }
            return Ok(Some(Value::Nil));
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}
