// Argument binding and validation for function calls

use std::sync::Arc;
use super::macros::*;
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::evaluate_expr;
use crate::interpreter::await_value;
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef, Parameter, SelfMode, Type};
use std::collections::{HashMap, HashSet};

type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

const METHOD_SELF: &str = "self";

fn copy_value_type_parameter(value: Value, value_type_names: &HashSet<String>) -> Value {
    match value {
        Value::Object { class, fields } if value_type_names.contains(&class) => Value::Object {
            class,
            fields: Arc::new((*fields).clone()),
        },
        other => other,
    }
}

/// Static empty map to avoid allocation on every `bind_args` call.
static EMPTY_INJECTED: std::sync::LazyLock<HashMap<String, Value>> = std::sync::LazyLock::new(HashMap::new);

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn bind_args(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    bind_args_with_injected(
        params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
        &EMPTY_INJECTED,
    )
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn bind_args_with_injected(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
    injected: &HashMap<String, Value>,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    // Check if there's a variadic parameter (should be last)
    let variadic_param_idx = params_to_bind.iter().position(|p| p.variadic);
    let value_type_names: HashSet<String> = classes
        .iter()
        .filter(|(_, def)| def.is_value_type)
        .map(|(name, _)| name.clone())
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    let mut variadic_values = Vec::new();

    let coerce_param = |value: Value, ty: Option<&Type>| -> Value {
        // Unsigned-int coercion for u8..u64 parameter types.
        let value = match ty {
            Some(Type::Simple(type_name)) if matches!(type_name.as_str(), "u8" | "u16" | "u32" | "u64") => {
                let width: u8 = match type_name.as_str() {
                    "u8" => 8,
                    "u16" => 16,
                    "u32" => 32,
                    "u64" => 64,
                    _ => unreachable!(),
                };
                match value {
                    Value::UInt { .. } => value,
                    Value::Int(i) => {
                        let masked: u64 = match width {
                            8 => (i as u8) as u64,
                            16 => (i as u16) as u64,
                            32 => (i as u32) as u64,
                            64 => i as u64,
                            _ => i as u64,
                        };
                        Value::UInt { value: masked, width }
                    }
                    other => other,
                }
            }
            _ => value,
        };
        // Unwrap Some(x) -> x when binding into a CONCRETE non-Optional parameter.
        // Mirrors the return-value unwrap in function_exec: `-> T?` functions
        // Some-wrap their plain returns, so passing such a value to a `param: T`
        // site (e.g. `if v != nil: emit(v)` where v came from a `-> WidgetNode?`
        // call and `emit(node: WidgetNode)`) must not leave it Option-wrapped.
        if let (
            Some(t),
            Value::Enum {
                enum_name,
                variant,
                payload,
            },
        ) = (ty, &value)
        {
            if enum_name == "Option" && variant == "Some" && super::function_exec::return_type_unwraps_option_some(t) {
                if let Some(inner) = payload {
                    return (**inner).clone();
                }
            }
        }
        copy_value_type_parameter(value, &value_type_names)
    };

    for arg in args {
        // Check if this is a spread expression (args...)
        if let Expr::Spread(inner) = &arg.value {
            // Evaluate the inner expression (should be variadic/array/tuple)
            let spread_val = evaluate_expr(inner, outer_env, functions, classes, enums, impl_methods)?;

            // Extract values from spread
            let spread_values: Vec<Value> = match spread_val {
                Value::Array(arr) => arr.to_vec(),
                Value::Tuple(tup) => tup,
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("the spread operator (...) can only be used with arrays or tuples");
                    return Err(CompileError::semantic_with_context(
                        "spread operator requires array or tuple value".to_string(),
                        ctx,
                    ));
                }
            };

            // Bind each spread value to the next positional parameter
            for spread_item in spread_values {
                if let Some(var_idx) = variadic_param_idx {
                    if positional_idx == var_idx {
                        // This value goes into variadic parameter
                        variadic_values.push(spread_item);
                    } else if positional_idx < var_idx {
                        // Regular parameter before variadic
                        let param = params_to_bind[positional_idx];
                        let val = coerce_param(wrap_trait_object!(spread_item, param.ty.as_ref()), param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    } else {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("check the function signature and provide the correct number of arguments");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "function expects {} argument(s), but more were provided",
                                params_to_bind.len()
                            ),
                            ctx,
                        ));
                    }
                } else {
                    // No variadic - bind to regular parameters
                    if positional_idx >= params_to_bind.len() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("check the function signature and provide the correct number of arguments");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "function expects {} argument(s), but more were provided",
                                params_to_bind.len()
                            ),
                            ctx,
                        ));
                    }
                    let param = params_to_bind[positional_idx];
                    let val = coerce_param(wrap_trait_object!(spread_item, param.ty.as_ref()), param.ty.as_ref());
                    validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                    bound.insert(param.name.clone(), val);
                }
                positional_idx += 1;
            }
        } else {
            // Normal argument (not spread)
            let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
            // Automatically await Promise arguments
            let val = await_value(val)?;

            if let Some(name) = &arg.name {
                // Named argument
                let param = params_to_bind.iter().find(|p| &p.name == name);
                if param.is_none() {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("check the function signature for valid parameter names");
                    return Err(CompileError::semantic_with_context(
                        format!("unknown argument '{}'", name),
                        ctx,
                    ));
                }
                // Validate call-site label on named argument
                if let Some(label) = &arg.label {
                    if let Some(p) = param {
                        if let Some(expected) = &p.call_site_label {
                            if label != expected {
                                let ctx = ErrorContext::new().with_code(codes::TYPE_MISMATCH).with_help(format!(
                                    "parameter '{}' expects label '{}', not '{}'",
                                    name, expected, label
                                ));
                                return Err(CompileError::semantic_with_context(
                                    format!("call-site label mismatch: expected '{}' but got '{}'", expected, label),
                                    ctx,
                                ));
                            }
                        } else {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help(format!("parameter '{}' does not declare a call-site label", name));
                            return Err(CompileError::semantic_with_context(
                                format!("unexpected call-site label '{}' on argument '{}'", label, name),
                                ctx,
                            ));
                        }
                    }
                }
                let val = coerce_param(
                    wrap_trait_object!(val, param.and_then(|p| p.ty.as_ref())),
                    param.and_then(|p| p.ty.as_ref()),
                );
                validate_unit!(&val, param.and_then(|p| p.ty.as_ref()), format!("parameter '{}'", name));
                bound.insert(name.clone(), val);
            } else {
                // Positional argument
                if let Some(var_idx) = variadic_param_idx {
                    if positional_idx >= var_idx {
                        // This and all remaining positional args go into variadic parameter
                        variadic_values.push(val);
                    } else {
                        // Regular positional parameter before variadic
                        let param = params_to_bind[positional_idx];
                        let val = coerce_param(wrap_trait_object!(val, param.ty.as_ref()), param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    }
                } else {
                    // No variadic parameter - normal positional binding
                    if positional_idx >= params_to_bind.len() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("check the function signature and provide the correct number of arguments");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "function expects {} argument(s), but more were provided",
                                params_to_bind.len()
                            ),
                            ctx,
                        ));
                    }
                    let param = params_to_bind[positional_idx];
                    // Validate call-site label on positional argument
                    if let Some(label) = &arg.label {
                        if let Some(expected) = &param.call_site_label {
                            if label != expected {
                                let ctx = ErrorContext::new().with_code(codes::TYPE_MISMATCH).with_help(format!(
                                    "parameter '{}' expects label '{}', not '{}'",
                                    param.name, expected, label
                                ));
                                return Err(CompileError::semantic_with_context(
                                    format!("call-site label mismatch: expected '{}' but got '{}'", expected, label),
                                    ctx,
                                ));
                            }
                        } else {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help(format!("parameter '{}' does not declare a call-site label", param.name));
                            return Err(CompileError::semantic_with_context(
                                format!(
                                    "unexpected call-site label '{}' on argument for parameter '{}'",
                                    label, param.name
                                ),
                                ctx,
                            ));
                        }
                    }
                    let val = coerce_param(wrap_trait_object!(val, param.ty.as_ref()), param.ty.as_ref());
                    validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                    bound.insert(param.name.clone(), val);
                }
                positional_idx += 1;
            }
        }
    }

    // Bind variadic parameter with collected values
    if let Some(var_idx) = variadic_param_idx {
        let param = params_to_bind[var_idx];
        bound.insert(param.name.clone(), Value::Tuple(variadic_values));
    }

    let dbg_all_param_names_tmp: Vec<String> = params_to_bind.iter().map(|p| p.name.clone()).collect();
    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                let v = coerce_param(wrap_trait_object!(v, param.ty.as_ref()), param.ty.as_ref());
                validate_unit!(
                    &v,
                    param.ty.as_ref(),
                    format!("parameter '{}' default value", param.name)
                );
                bound.insert(param.name.clone(), v);
            } else if let Some(injected_val) = injected.get(&param.name) {
                bound.insert(param.name.clone(), injected_val.clone());
            } else {
                if std::env::var("SIMPLE_DEBUG_ARG_BINDING").is_ok() {
                    eprintln!(
                        "[DEBUG arg_binding TMP] missing param '{}'; full param list={:?}; args given={}",
                        param.name,
                        dbg_all_param_names_tmp,
                        args.len()
                    );
                }
                let ctx = ErrorContext::new()
                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                    .with_help("check the function signature and provide the correct number of arguments");
                return Err(CompileError::semantic_with_context(
                    format!(
                        "function expects argument for parameter '{}', but none was provided",
                        param.name
                    ),
                    ctx,
                ));
            }
        }
    }

    Ok(bound)
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn bind_args_with_values(
    params: &[Parameter],
    args: &[Value],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();
    let value_type_names: HashSet<String> = classes
        .iter()
        .filter(|(_, def)| def.is_value_type)
        .map(|(name, _)| name.clone())
        .collect();

    if args.len() > params_to_bind.len() {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("check the function signature and provide the correct number of arguments");
        return Err(CompileError::semantic_with_context(
            format!(
                "function expects {} argument(s), but {} were provided",
                params_to_bind.len(),
                args.len()
            ),
            ctx,
        ));
    }

    let coerce_param = |value: Value, ty: Option<&Type>| -> Value {
        // Unsigned-int coercion for u8..u64 parameter types.
        let value = match ty {
            Some(Type::Simple(type_name)) if matches!(type_name.as_str(), "u8" | "u16" | "u32" | "u64") => {
                let width: u8 = match type_name.as_str() {
                    "u8" => 8,
                    "u16" => 16,
                    "u32" => 32,
                    "u64" => 64,
                    _ => unreachable!(),
                };
                match value {
                    Value::UInt { .. } => value,
                    Value::Int(i) => {
                        let masked: u64 = match width {
                            8 => (i as u8) as u64,
                            16 => (i as u16) as u64,
                            32 => (i as u32) as u64,
                            64 => i as u64,
                            _ => i as u64,
                        };
                        Value::UInt { value: masked, width }
                    }
                    other => other,
                }
            }
            _ => value,
        };
        // Unwrap Some(x) -> x when binding into a CONCRETE non-Optional parameter.
        // Mirrors the return-value unwrap in function_exec: `-> T?` functions
        // Some-wrap their plain returns, so passing such a value to a `param: T`
        // site (e.g. `if v != nil: emit(v)` where v came from a `-> WidgetNode?`
        // call and `emit(node: WidgetNode)`) must not leave it Option-wrapped.
        if let (
            Some(t),
            Value::Enum {
                enum_name,
                variant,
                payload,
            },
        ) = (ty, &value)
        {
            if enum_name == "Option" && variant == "Some" && super::function_exec::return_type_unwraps_option_some(t) {
                if let Some(inner) = payload {
                    return (**inner).clone();
                }
            }
        }
        copy_value_type_parameter(value, &value_type_names)
    };

    let mut bound = HashMap::new();
    if crate::is_debug_mode() {
        eprintln!(
            "[DEBUG bind_args_with_values] called with {} args, {} params",
            args.len(),
            params_to_bind.len()
        );
    }
    for (idx, param) in params_to_bind.iter().enumerate() {
        let value = if idx < args.len() {
            // Automatically await Promise arguments
            await_value(args[idx].clone())?
        } else if let Some(default_expr) = &param.default {
            evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?
        } else {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("check the function signature and provide the correct number of arguments");
            return Err(CompileError::semantic_with_context(
                format!(
                    "function expects argument for parameter '{}', but none was provided",
                    param.name
                ),
                ctx,
            ));
        };

        let value = coerce_param(wrap_trait_object!(value, param.ty.as_ref()), param.ty.as_ref());
        validate_unit!(&value, param.ty.as_ref(), format!("parameter '{}'", param.name));
        bound.insert(param.name.clone(), value);
    }

    Ok(bound)
}
