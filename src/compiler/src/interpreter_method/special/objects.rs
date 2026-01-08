//! Trait object and constructor methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{exec_block_fn, evaluate_expr, find_and_exec_method, Control, Enums, ImplMethods};
use crate::value::{Value, Env, SpecialEnumType, OptionVariant, ResultVariant};
use simple_parser::ast::{Argument, FunctionDef, ClassDef};
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;

// Import IN_NEW_METHOD from interpreter_call module
use crate::interpreter::IN_NEW_METHOD;

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
    use crate::interpreter::INTERFACE_BINDINGS;

    // Check if there's an interface binding for static polymorphism
    let bound_impl = INTERFACE_BINDINGS.with(|bindings| {
        bindings.borrow().get(trait_name).cloned()
    });

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
            if let Some(result) = find_and_exec_method(method, args, bound_type, fields, env, functions, classes, enums, impl_methods)? {
                return Ok(Some(result));
            }
        }

        // Dynamic dispatch: method lookup on the actual inner object type
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

            // If this is the `new` method, mark it to prevent recursion when the body
            // calls the class constructor (e.g., `ClassName(args)` inside `new()`)
            let is_new_method = method == "new";
            if is_new_method {
                IN_NEW_METHOD.with(|set| set.borrow_mut().insert(class_name.to_string()));
            }

            // Use exec_block_fn to properly capture implicit returns
            let result = match exec_block_fn(&method_def.body, &mut local_env, functions, classes, enums, impl_methods) {
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
