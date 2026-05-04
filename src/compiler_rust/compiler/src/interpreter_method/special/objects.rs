//! Trait object and constructor methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use std::sync::Arc;
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{evaluate_expr, exec_block_fn, find_and_exec_method, Control, Enums, ImplMethods};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef, Type};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

// Import IN_NEW_METHOD from interpreter_call module
use crate::interpreter::IN_NEW_METHOD;

fn constructor_value_type_matches_name(value: &Value, expected: &str) -> bool {
    match value {
        Value::Object { class, .. } => class == expected,
        Value::Enum { enum_name, .. } => enum_name == expected,
        Value::Str(_) => matches!(expected, "str" | "text" | "String" | "Str"),
        _ => value.type_name() == expected || value.matches_type(expected),
    }
}

fn constructor_value_matches_type(value: &Value, ty: &Type) -> bool {
    match ty {
        Type::Simple(name) | Type::Generic { name, .. } => constructor_value_type_matches_name(value, name),
        Type::Array { element, .. } => match value {
            Value::Array(items) => items.iter().all(|item| constructor_value_matches_type(item, element)),
            Value::FrozenArray(items) => items.iter().all(|item| constructor_value_matches_type(item, element)),
            Value::Tuple(items) => items.iter().all(|item| constructor_value_matches_type(item, element)),
            _ => false,
        },
        _ => true,
    }
}

fn constructor_overload_score(func: &FunctionDef, values: &[Value]) -> Option<usize> {
    if func.params.len() != values.len() {
        return None;
    }

    let mut score = 0usize;
    for (param, value) in func.params.iter().zip(values.iter()) {
        if let Some(ty) = &param.ty {
            if !constructor_value_matches_type(value, ty) {
                return None;
            }
            score += match ty {
                Type::Array { .. } => 4,
                Type::Simple(_) | Type::Generic { .. } => 2,
                _ => 1,
            };
        }
    }
    Some(score)
}

#[allow(clippy::borrowed_box, clippy::too_many_arguments)] // reason: Box<dyn Trait> dispatch with ABI-locked entry; refactoring deferred
pub fn handle_trait_object_methods(
    trait_name: &str,
    inner: &Box<Value>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    use crate::interpreter::INTERFACE_BINDINGS;

    // Check if there's an interface binding for static polymorphism
    let bound_impl = INTERFACE_BINDINGS.with(|bindings| bindings.borrow().get(trait_name).cloned());

    // Extract the inner value's class/type
    if let Value::Object { class, fields } = inner.as_ref() {
        // If there's a binding, verify the inner object matches the bound type
        // and use static dispatch to the bound implementation
        if let Some(ref bound_type) = bound_impl {
            if class != bound_type {
                // Inner type doesn't match binding - this shouldn't happen in well-typed code
                // Fall back to normal dynamic dispatch
            }
            // Static dispatch: method lookup on the bound implementation type
            if let Some(result) = find_and_exec_method(
                method,
                args,
                bound_type,
                fields,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(Some(result));
            }
        }

        // Dynamic dispatch: method lookup on the actual inner object type
        if let Some(result) = find_and_exec_method(
            method,
            args,
            class,
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            return Ok(Some(result));
        }
        return Err(crate::error::factory::trait_method_not_found(method, trait_name, class));
    }
    Err(crate::error::factory::trait_inner_not_object(method, trait_name))
}

/// Handle Constructor static method calls
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_constructor_methods(
    class_name: &str,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if let Some(class_def) = classes.get(class_name).cloned() {
        let evaluated_args: Vec<(Option<String>, Value)> = args
            .iter()
            .map(|arg| {
                evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                    .map(|value| (arg.name.clone(), value))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let positional_values: Vec<Value> = evaluated_args.iter().map(|(_, value)| value.clone()).collect();
        let mut candidates: Vec<&FunctionDef> = class_def
            .methods
            .iter()
            .filter(|m| m.name == method && (m.is_static || !m.params.iter().any(|p| p.name == "self")))
            .collect();
        if let Some(extra_methods) = impl_methods.get(class_name) {
            candidates.extend(
                extra_methods
                    .iter()
                    .filter(|m| m.name == method && (m.is_static || !m.params.iter().any(|p| p.name == "self")))
                    .map(|m| m.as_ref()),
            );
        }
        // Debug tracing for static method resolution (enable via SIMPLE_DEBUG_STATIC_OVERLOAD=1)
        if std::env::var("SIMPLE_DEBUG_STATIC_OVERLOAD").is_ok() {
            eprintln!(
                "[debug static overload] {}.{} candidates={} arg_types={:?}",
                class_name,
                method,
                candidates.len(),
                positional_values.iter().map(|v| v.type_name()).collect::<Vec<_>>()
            );
        }

        if let Some(method_def) = candidates
            .into_iter()
            .filter_map(|candidate| {
                constructor_overload_score(candidate, &positional_values).map(|score| (score, candidate))
            })
            .max_by_key(|(score, _)| *score)
            .map(|(_, candidate)| candidate)
        {
            // Execute without self - start with empty local_env to avoid shadowing defaults
            let mut local_env: Env = Env::new();
            let mut positional_idx = 0;

            // Bind provided arguments
            for (arg_name, val) in evaluated_args {
                if let Some(name) = arg_name {
                    local_env.insert(name, val);
                } else if positional_idx < method_def.params.len() {
                    let param = &method_def.params[positional_idx];
                    local_env.insert(param.name.clone(), val);
                    positional_idx += 1;
                }
            }

            // Bind default values for remaining parameters using an empty scope
            // to prevent caller's variables from shadowing defaults
            let mut empty_env: Env = Env::new();
            for param in &method_def.params {
                if !local_env.contains_key(&param.name) {
                    if let Some(default_expr) = &param.default {
                        let default_val =
                            evaluate_expr(default_expr, &mut empty_env, functions, classes, enums, impl_methods)?;
                        local_env.insert(param.name.clone(), default_val);
                    }
                }
            }

            // If this is the `new` method, mark it to prevent recursion when the body
            // calls the class constructor (e.g., `ClassName(args)` inside `new()`)
            let is_new_method = method == "new";
            if is_new_method {
                IN_NEW_METHOD.with(|set| set.borrow_mut().insert(class_name.to_string()));
            }

            // Use exec_block_fn to properly capture implicit returns
            let result = match exec_block_fn(
                &method_def.body,
                &mut local_env,
                functions,
                classes,
                enums,
                impl_methods,
            ) {
                Ok((Control::Return(v), _)) => Ok(Some(v)),
                Ok((_, Some(implicit_val))) => Ok(Some(implicit_val)), // Implicit return from last expression
                Ok((_, None)) => Ok(Some(Value::Nil)),
                Err(e) => Err(e),
            };

            // Remove from tracking set
            if is_new_method {
                IN_NEW_METHOD.with(|set| set.borrow_mut().remove(class_name));
            }

            return result;
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
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_METHOD)
            .with_help("check that the method exists and is spelled correctly");
        return Err(CompileError::semantic_with_context(msg, ctx));
    }
    // Collect available classes for suggestion
    let available: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
    let mut msg = format!("unknown class {class_name}");
    if let Some(suggestion) = crate::error::typo::format_suggestion(class_name, available) {
        msg.push_str(&format!("; {}", suggestion));
    }
    let ctx = ErrorContext::new()
        .with_code(codes::UNKNOWN_CLASS)
        .with_help("check that the class exists and is spelled correctly");
    Err(CompileError::semantic_with_context(msg, ctx))
}
