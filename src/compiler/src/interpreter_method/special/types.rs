//! Unit, Option, and Result type methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::interpreter_helpers::{
    eval_option_and_then, eval_option_filter, eval_option_map, eval_option_or_else, eval_result_and_then,
    eval_result_map, eval_result_map_err, eval_result_or_else,
};
use crate::interpreter::{
    eval_arg, evaluate_expr, exec_block_fn, Control, Enums, ImplMethods, UNIT_FAMILY_CONVERSIONS, UNIT_SUFFIX_TO_FAMILY,
};
use crate::interpreter_unit::decompose_si_prefix;
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;
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

pub fn handle_unit_methods(
    value: &Box<Value>,
    suffix: &str,
    family: &Option<String>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
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
                        "Unit family '{}' not found",
                        family_name
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
                        "Unit '{}' not found in family '{}'",
                        suffix, family_name
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
                        target_suffix,
                        family_name,
                        conversions.keys().collect::<Vec<_>>()
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
                Value::Float(f) => Value::Float(f * (source_factor / target_factor)),
                _ => {
                    return Err(CompileError::Semantic(format!(
                        "Cannot convert non-numeric unit value: {:?}",
                        value
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
    env: &mut Env,
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
            let msg = eval_arg(
                args,
                0,
                Value::Str("Option was None".into()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            return Err(CompileError::Semantic(msg.to_display_string()));
        }
        "unwrap_or" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            return Ok(Some(eval_arg(
                args,
                0,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "unwrap_or_else" => {
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(val.as_ref().clone()));
                }
            }
            // Call the function to get default value
            let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda {
                params: _,
                body,
                env: mut captured,
            } = func_arg
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
        "or" => {
            // Returns self if Some, otherwise returns the other Option
            if opt_variant == Some(OptionVariant::Some) {
                return Ok(Some(recv_val.clone()));
            }
            return Ok(Some(eval_arg(
                args,
                0,
                Value::none(),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "ok_or" => {
            // Converts Option to Result: Some(v) -> Ok(v), None -> Err(error)
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(val) = payload {
                    return Ok(Some(Value::ok(val.as_ref().clone())));
                }
            }
            let error = eval_arg(
                args,
                0,
                Value::Str("None".into()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            return Ok(Some(Value::err(error)));
        }
        "map" => {
            return Ok(Some(eval_option_map(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "and_then" => {
            return Ok(Some(eval_option_and_then(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "or_else" => {
            return Ok(Some(eval_option_or_else(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "filter" => {
            return Ok(Some(eval_option_filter(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "flatten" => {
            // Option<Option<T>> -> Option<T>
            if opt_variant == Some(OptionVariant::Some) {
                if let Some(inner) = payload {
                    // If inner is also an Option, return it
                    if let Value::Enum {
                        enum_name: inner_enum, ..
                    } = inner.as_ref()
                    {
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
    env: &mut Env,
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
                    return Err(CompileError::Semantic(format!(
                        "called unwrap on Err: {}",
                        err_val.to_display_string()
                    )));
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
            let msg = eval_arg(
                args,
                0,
                Value::Str("Result was Err".into()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if res_variant == Some(ResultVariant::Err) {
                if let Some(err_val) = payload {
                    return Err(CompileError::Semantic(format!(
                        "{}: {}",
                        msg.to_display_string(),
                        err_val.to_display_string()
                    )));
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
            return Ok(Some(eval_arg(
                args,
                0,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
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
                if let Value::Lambda {
                    params,
                    body,
                    env: mut captured,
                } = func_arg
                {
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), err_val.as_ref().clone());
                    }
                    return Ok(Some(evaluate_expr(
                        &body,
                        &mut local_env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?));
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
            let msg = eval_arg(
                args,
                0,
                Value::Str("Result was Ok".into()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            return Err(CompileError::Semantic(msg.to_display_string()));
        }
        "ok" => {
            if res_variant == Some(ResultVariant::Ok) {
                return Ok(Some(
                    payload
                        .as_ref()
                        .map(|p| Value::some(p.as_ref().clone()))
                        .unwrap_or_else(Value::none),
                ));
            }
            return Ok(Some(Value::none()));
        }
        "err" => {
            if res_variant == Some(ResultVariant::Err) {
                return Ok(Some(
                    payload
                        .as_ref()
                        .map(|p| Value::some(p.as_ref().clone()))
                        .unwrap_or_else(Value::none),
                ));
            }
            return Ok(Some(Value::none()));
        }
        "or" => {
            // Returns self if Ok, otherwise returns the other Result
            if res_variant == Some(ResultVariant::Ok) {
                return Ok(Some(recv_val.clone()));
            }
            return Ok(Some(eval_arg(
                args,
                0,
                Value::err(Value::Nil),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "map" => {
            return Ok(Some(eval_result_map(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "map_err" => {
            return Ok(Some(eval_result_map_err(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "and_then" => {
            return Ok(Some(eval_result_and_then(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "or_else" => {
            return Ok(Some(eval_result_or_else(
                variant,
                payload,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "flatten" => {
            // Result<Result<T, E>, E> -> Result<T, E>
            if res_variant == Some(ResultVariant::Ok) {
                if let Some(inner) = payload {
                    // If inner is also a Result, return it
                    if let Value::Enum {
                        enum_name: inner_enum, ..
                    } = inner.as_ref()
                    {
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
