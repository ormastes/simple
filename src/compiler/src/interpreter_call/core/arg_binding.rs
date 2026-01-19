// Argument binding and validation for function calls

use super::macros::*;
use crate::error::CompileError;
use crate::interpreter::evaluate_expr;
use crate::interpreter::await_value;
use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef, Parameter, SelfMode, Type};
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";

pub(crate) fn bind_args(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
        &HashMap::new(),
    )
}

pub(crate) fn bind_args_with_injected(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    let mut variadic_values = Vec::new();

    for arg in args {
        // Check if this is a spread expression (args...)
        if let Expr::Spread(inner) = &arg.value {
            // Evaluate the inner expression (should be variadic/array/tuple)
            let spread_val = evaluate_expr(inner, outer_env, functions, classes, enums, impl_methods)?;

            // Extract values from spread
            let spread_values: Vec<Value> = match spread_val {
                Value::Array(arr) => arr,
                Value::Tuple(tup) => tup,
                _ => {
                    bail_semantic!("spread operator requires array or tuple value");
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
                        let val = wrap_trait_object!(spread_item, param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    } else {
                        bail_semantic!("too many arguments");
                    }
                } else {
                    // No variadic - bind to regular parameters
                    if positional_idx >= params_to_bind.len() {
                        bail_semantic!("too many arguments");
                    }
                    let param = params_to_bind[positional_idx];
                    let val = wrap_trait_object!(spread_item, param.ty.as_ref());
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
                    bail_semantic!("unknown argument {}", name);
                }
                let val = wrap_trait_object!(val, param.and_then(|p| p.ty.as_ref()));
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
                        let val = wrap_trait_object!(val, param.ty.as_ref());
                        validate_unit!(&val, param.ty.as_ref(), format!("parameter '{}'", param.name));
                        bound.insert(param.name.clone(), val);
                    }
                } else {
                    // No variadic parameter - normal positional binding
                    if positional_idx >= params_to_bind.len() {
                        bail_semantic!("too many arguments");
                    }
                    let param = params_to_bind[positional_idx];
                    let val = wrap_trait_object!(val, param.ty.as_ref());
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

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                let v = wrap_trait_object!(v, param.ty.as_ref());
                validate_unit!(
                    &v,
                    param.ty.as_ref(),
                    format!("parameter '{}' default value", param.name)
                );
                bound.insert(param.name.clone(), v);
            } else if let Some(injected_val) = injected.get(&param.name) {
                bound.insert(param.name.clone(), injected_val.clone());
            } else {
                bail_semantic!("missing argument {}", param.name);
            }
        }
    }

    Ok(bound)
}

pub(crate) fn bind_args_with_values(
    params: &[Parameter],
    args: &[Value],
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: SelfMode,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    if args.len() > params_to_bind.len() {
        bail_semantic!("too many arguments");
    }

    let mut bound = HashMap::new();
    for (idx, param) in params_to_bind.iter().enumerate() {
        let value = if idx < args.len() {
            // Automatically await Promise arguments
            await_value(args[idx].clone())?
        } else if let Some(default_expr) = &param.default {
            evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?
        } else {
            bail_semantic!("missing argument {}", param.name);
        };

        let value = wrap_trait_object!(value, param.ty.as_ref());
        validate_unit!(&value, param.ty.as_ref(), format!("parameter '{}'", param.name));
        bound.insert(param.name.clone(), value);
    }

    Ok(bound)
}
