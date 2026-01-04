// Method call dispatcher - delegates to type-specific handlers

mod primitives;
mod collections;
mod special;

use crate::error::CompileError;
use crate::value::{Value, Env};
use simple_parser::ast::{Argument, FunctionDef, ClassDef, Expr};
use std::collections::HashMap;
use super::{
    evaluate_expr,
    eval_arg, eval_arg_usize,
    instantiate_class,
    exec_function, exec_function_with_captured_env,
    find_and_exec_method, try_method_missing,
    Enums, ImplMethods,
};

// Re-export the with-self-update functions
pub use special::{find_and_exec_method_with_self, exec_function_with_self_return};

/// Main entry point for method call evaluation
pub(crate) fn evaluate_method_call(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Support module-style dot calls (lib.func()) by resolving directly to imported functions/classes.
    if let Expr::Identifier(module_name) = receiver.as_ref() {
        if env.get(module_name).is_none() {
            if let Some(func) = functions.get(method).cloned() {
                return exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            }
            if classes.contains_key(method) {
                return instantiate_class(method, args, env, functions, classes, enums, impl_methods);
            }
        }
    }

    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Handle module (Dict) method calls - look up function in module and use its captured_env
    if let Value::Dict(module_dict) = &recv_val {
        if let Some(func_val) = module_dict.get(method) {
            if let Value::Function { def, captured_env, .. } = func_val {
                return exec_function_with_captured_env(def, args, env, captured_env, functions, classes, enums, impl_methods);
            }
            if let Value::Constructor { class_name } = func_val {
                return instantiate_class(class_name, args, env, functions, classes, enums, impl_methods);
            }
        }
    }

    // BDD assertion methods: to(matcher) and not_to(matcher)
    // These work on any value type and are used with matchers like eq(5), gt(3), etc.
    match method {
        "to" | "not_to" => {
            let matcher = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let matched = match &matcher {
                Value::Matcher(m) => m.matches(&recv_val),
                // If the argument isn't a Matcher, treat it as an equality check
                other => recv_val == *other,
            };
            let passed = if method == "not_to" { !matched } else { matched };
            return Ok(Value::Bool(passed));
        }
        _ => {}
    }

    // Dispatch to type-specific handlers
    match &recv_val {
        Value::Int(n) => {
            if let Some(result) = primitives::handle_int_methods(*n, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Float(f) => {
            if let Some(result) = primitives::handle_float_methods(*f, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Bool(b) => {
            if let Some(result) = primitives::handle_bool_methods(*b, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Unit { value, suffix, family } => {
            if let Some(result) = special::handle_unit_methods(value, suffix, family, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Array(arr) => {
            if let Some(result) = collections::handle_array_methods(arr, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Tuple(tup) => {
            if let Some(result) = collections::handle_tuple_methods(tup, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Dict(map) => {
            if let Some(result) = collections::handle_dict_methods(map, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
        }
        Value::Str(_) => {
            // String methods are included from a separate file
            include!("string.rs");
        }
        Value::Enum { enum_name, variant, payload } => {
            // Try Option methods
            if let Some(result) = special::handle_option_methods(&recv_val, enum_name, variant, payload, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
            // Try Result methods
            if let Some(result) = special::handle_result_methods(&recv_val, enum_name, variant, payload, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }

            // User-defined methods on enums via impl blocks
            if let Some(methods) = impl_methods.get(enum_name) {
                for m in methods {
                    if m.name == method {
                        // For enum methods, we pass self as a special context
                        // Create a fields map with just "self" for the enum value
                        let mut enum_fields = HashMap::new();
                        enum_fields.insert("self".to_string(), recv_val.clone());
                        return exec_function(m, args, env, functions, classes, enums, impl_methods, Some((enum_name, &enum_fields)));
                    }
                }
            }

            // Methods defined directly in the enum body
            if let Some(enum_def) = enums.get(enum_name) {
                for m in &enum_def.methods {
                    if m.name == method {
                        // For enum methods, we pass self as a special context
                        let mut enum_fields = HashMap::new();
                        enum_fields.insert("self".to_string(), recv_val.clone());
                        return exec_function(m, args, env, functions, classes, enums, impl_methods, Some((enum_name, &enum_fields)));
                    }
                }
            }
        }
        // EnumType method call = variant constructor call
        // EnumName.VariantName(args) -> create enum with payload
        Value::EnumType { enum_name } => {
            if let Some(enum_def) = enums.get(enum_name).cloned() {
                // Check if the method name is a variant name
                let variant_opt = enum_def.variants.iter().find(|v| v.name == method);
                if let Some(variant) = variant_opt {
                    // Construct enum variant with payload
                    let has_fields = variant.fields.as_ref().map_or(false, |f| !f.is_empty());
                    if !has_fields && args.is_empty() {
                        // Unit variant
                        return Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: method.to_string(),
                            payload: None,
                        });
                    } else {
                        // Variant with payload
                        let payload = if args.is_empty() {
                            None
                        } else if args.len() == 1 {
                            let val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                            Some(Box::new(val))
                        } else {
                            // Multiple args - wrap in tuple
                            let vals: Result<Vec<Value>, _> = args
                                .iter()
                                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                                .collect();
                            Some(Box::new(Value::Tuple(vals?)))
                        };
                        return Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: method.to_string(),
                            payload,
                        });
                    }
                }

                // Check if it's a static method on the enum
                for m in &enum_def.methods {
                    if m.name == method && m.params.first().map_or(true, |p| p.name != "self") {
                        return exec_function(m, args, env, functions, classes, enums, impl_methods, None);
                    }
                }

                return Err(CompileError::Semantic(format!(
                    "unknown variant or method '{}' on enum {}",
                    method, enum_name
                )));
            } else {
                return Err(CompileError::Semantic(format!("unknown enum {}", enum_name)));
            }
        }
        Value::TraitObject { trait_name, inner } => {
            if let Some(result) = special::handle_trait_object_methods(trait_name, inner, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            } else {
                return Err(CompileError::Semantic(format!(
                    "Method '{}' not found on dyn {}",
                    method, trait_name
                )));
            }
        }
        Value::Object { class, fields } => {
            // Try to find and execute the method
            if let Some(result) = find_and_exec_method(method, args, class, fields, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
            // Try method_missing hook
            if let Some(result) = try_method_missing(method, args, class, fields, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
            // Collect available methods for typo suggestion
            let mut available_methods: Vec<&str> = Vec::new();
            if let Some(methods) = impl_methods.get(class) {
                available_methods.extend(methods.iter().map(|m| m.name.as_str()));
            }
            // Add built-in methods for common types
            available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
            bail_unknown_method!(method, class, available_methods);
        }
        Value::Future(future) => {
            if let Some(result) = special::handle_future_methods(future, method)? {
                return Ok(result);
            } else {
                let available = ["join", "await", "get", "is_ready"];
                bail_unknown_method!(method, "Future", available);
            }
        }
        Value::Channel(channel) => {
            if let Some(result) = special::handle_channel_methods(channel, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            } else {
                let available = ["send", "recv", "try_recv"];
                bail_unknown_method!(method, "Channel", available);
            }
        }
        Value::ThreadPool(pool) => {
            if let Some(result) = special::handle_threadpool_methods(pool, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            } else {
                let available = ["submit"];
                bail_unknown_method!(method, "ThreadPool", available);
            }
        }
        Value::Constructor { class_name } => {
            if let Some(result) = special::handle_constructor_methods(class_name, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            } else {
                return Err(CompileError::Semantic(format!("unknown class {}", class_name)));
            }
        }
        Value::Mock(mock) => {
            if let Some(result) = special::handle_mock_methods(mock, method, args, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
            // Mock methods handler handles all cases including fallback
            unreachable!("Mock methods handler should have handled all cases");
        }
        _ => {}
    }

    Err(CompileError::Semantic(format!("method call on unsupported type: {method}")))
}

/// Evaluate a method call and return both the result and the potentially modified self.
/// This is used when we need to persist mutations to self back to the calling environment.
pub(crate) fn evaluate_method_call_with_self_update(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<Value>), CompileError> {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Only handle Object methods with self mutation
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some((result, updated_self)) = special::find_and_exec_method_with_self(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok((result, Some(updated_self)));
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            // method_missing returns just a result, self is not mutated
            return Ok((result, None));
        }
        // Collect available methods for typo suggestion
        let mut available_methods: Vec<&str> = Vec::new();
        if let Some(methods) = impl_methods.get(&class) {
            available_methods.extend(methods.iter().map(|m| m.name.as_str()));
        }
        available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
        bail_unknown_method!(method, class, available_methods);
    }

    // For non-objects, just use regular method call
    let result = evaluate_method_call(receiver, method, args, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}
