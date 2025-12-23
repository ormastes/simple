//! Argument binding for function calls

use std::collections::HashMap;
use simple_parser::ast::{Argument, Parameter, Type};
use crate::value::Value;
use crate::{ClassDef, CompileError, Enums, FunctionDef, ImplMethods};
use crate::interpreter::env::Env;
use crate::interpreter::expressions::evaluate_expr;
use crate::interpreter::METHOD_SELF;
use crate::interpreter::unit_types::{is_unit_type, validate_unit_type};
use crate::{bail_semantic, semantic_err};

pub(super) fn bind_args(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: simple_parser::ast::SelfMode,
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

pub(super) fn bind_args_with_injected(
    params: &[Parameter],
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: simple_parser::ast::SelfMode,
    injected: &HashMap<String, Value>,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(self_mode.should_skip_self() && p.name == METHOD_SELF))
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            let param = params_to_bind.iter().find(|p| &p.name == name);
            if param.is_none() {
                bail_semantic!("unknown argument {}", name);
            }
            // Coerce to TraitObject if parameter type is `dyn Trait`
            let val = if let Some(Type::DynTrait(trait_name)) = param.and_then(|p| p.ty.as_ref()) {
                Value::TraitObject {
                    trait_name: trait_name.clone(),
                    inner: Box::new(val),
                }
            } else {
                val
            };
            // Validate unit type annotation if present
            if let Some(Type::Simple(type_name)) = param.and_then(|p| p.ty.as_ref()) {
                if is_unit_type(type_name) {
                    if let Err(e) = validate_unit_type(&val, type_name) {
                        bail_semantic!("parameter '{}': {}", name, e);
                    }
                }
            }
            bound.insert(name.clone(), val);
        } else {
            if positional_idx >= params_to_bind.len() {
                bail_semantic!("too many arguments");
            }
            let param = params_to_bind[positional_idx];
            // Coerce to TraitObject if parameter type is `dyn Trait`
            let val = if let Some(Type::DynTrait(trait_name)) = &param.ty {
                Value::TraitObject {
                    trait_name: trait_name.clone(),
                    inner: Box::new(val),
                }
            } else {
                val
            };
            // Validate unit type annotation if present
            if let Some(Type::Simple(type_name)) = &param.ty {
                if is_unit_type(type_name) {
                    if let Err(e) = validate_unit_type(&val, type_name) {
                        bail_semantic!("parameter '{}': {}", param.name, e);
                    }
                }
            }
            bound.insert(param.name.clone(), val);
            positional_idx += 1;
        }
    }

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                // Coerce to TraitObject if parameter type is `dyn Trait`
                let v = if let Some(Type::DynTrait(trait_name)) = &param.ty {
                    Value::TraitObject {
                        trait_name: trait_name.clone(),
                        inner: Box::new(v),
                    }
                } else {
                    v
                };
                // Validate unit type annotation if present
                if let Some(Type::Simple(type_name)) = &param.ty {
                    if is_unit_type(type_name) {
                        if let Err(e) = validate_unit_type(&v, type_name) {
                            bail_semantic!("parameter '{}' default value: {}", param.name, e);
                        }
                    }
                }
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

pub(super) fn bind_args_with_values(
    params: &[Parameter],
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_mode: simple_parser::ast::SelfMode,
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
            args[idx].clone()
        } else if let Some(default_expr) = &param.default {
            evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?
        } else {
            bail_semantic!("missing argument {}", param.name);
        };

        let value = if let Some(Type::DynTrait(trait_name)) = &param.ty {
            Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: Box::new(value),
            }
        } else {
            value
        };

        if let Some(Type::Simple(type_name)) = &param.ty {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type(&value, type_name) {
                    bail_semantic!("parameter '{}': {}", param.name, e);
                }
            }
        }
        bound.insert(param.name.clone(), value);
    }

    Ok(bound)
}
