// Method call dispatcher - delegates to type-specific handlers

mod collections;
mod primitives;
mod special;

use super::{
    eval_arg, eval_arg_usize, evaluate_expr, exec_function, exec_function_with_captured_env,
    exec_function_with_values, find_and_exec_method, instantiate_class, try_method_missing, Enums,
    ImplMethods, BLOCK_SCOPED_ENUMS,
};
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, Expr, FunctionDef};
use std::collections::HashMap;

// Re-export the with-self-update functions
pub use special::{exec_function_with_self_return, find_and_exec_method_with_self};

/// Main entry point for method call evaluation
pub(crate) fn evaluate_method_call(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
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
                let mut captured_env_clone = captured_env.clone();
                return exec_function_with_captured_env(
                    def,
                    args,
                    env,
                    &mut captured_env_clone,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                );
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

            // Report to BDD framework
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !passed {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {:?} {} {:?}",
                    recv_val,
                    if method == "not_to" { "not to match" } else { "to match" },
                    matcher
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }

            return Ok(Value::Bool(passed));
        }
        _ => {}
    }

    // Dispatch to type-specific handlers
    match &recv_val {
        Value::Int(n) => {
            if let Some(result) =
                primitives::handle_int_methods(*n, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Float(f) => {
            if let Some(result) =
                primitives::handle_float_methods(*f, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Bool(b) => {
            if let Some(result) =
                primitives::handle_bool_methods(*b, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Unit { value, suffix, family } => {
            if let Some(result) = special::handle_unit_methods(
                value,
                suffix,
                family,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::Array(arr) => {
            if let Some(result) =
                collections::handle_array_methods(arr, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Tuple(tup) => {
            if let Some(result) =
                collections::handle_tuple_methods(tup, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Dict(map) => {
            if let Some(result) =
                collections::handle_dict_methods(map, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Str(_) => {
            // String methods are included from a separate file
            include!("string.rs");
        }
        Value::Enum {
            enum_name,
            variant,
            payload,
        } => {
            // Try Option methods
            if let Some(result) = special::handle_option_methods(
                &recv_val,
                enum_name,
                variant,
                payload,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
            // Try Result methods
            if let Some(result) = special::handle_result_methods(
                &recv_val,
                enum_name,
                variant,
                payload,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
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
                        let result = exec_function(
                            m,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((enum_name, &enum_fields)),
                        )?;
                        return Ok(result);
                    }
                }
            }

            // Methods defined directly in the enum body (or merged from impl blocks)
            if let Some(enum_def) = enums.get(enum_name) {
                for m in &enum_def.methods {
                    if m.name == method {
                        // For enum methods, we pass self as a special context
                        let mut enum_fields = HashMap::new();
                        enum_fields.insert("self".to_string(), recv_val.clone());
                        return exec_function(
                            m,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((enum_name, &enum_fields)),
                        );
                    }
                }
            }
        }
        // EnumType method call = variant constructor call
        // EnumName.VariantName(args) -> create enum with payload
        Value::EnumType { enum_name } => {
            // Check both module-level enums and block-scoped enums
            let enum_def = enums.get(enum_name).cloned()
                .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()));
            if let Some(enum_def) = enum_def {
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

                return Err(crate::error::factory::unknown_enum_variant_or_method(method, enum_name));
            } else {
                // E1015 - Unknown Enum
                let available_enums: Vec<&str> = enums.keys().map(|s| s.as_str()).collect();
                let suggestion = if !available_enums.is_empty() {
                    typo::suggest_name(enum_name, available_enums.clone())
                } else {
                    None
                };

                let mut ctx = ErrorContext::new()
                    .with_code(codes::UNKNOWN_ENUM)
                    .with_help("check that the enum is defined or imported in this scope");

                if let Some(best_match) = suggestion {
                    ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                }

                return Err(CompileError::semantic_with_context(
                    format!("enum `{}` not found in this scope", enum_name),
                    ctx,
                ));
            }
        }
        Value::TraitObject { trait_name, inner } => {
            if let Some(result) = special::handle_trait_object_methods(
                trait_name,
                inner,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            } else {
                // E1013 - Unknown Method (for dyn trait)
                let ctx = ErrorContext::new()
                    .with_code(codes::UNKNOWN_METHOD)
                    .with_help("check that the method is defined in the trait");

                return Err(CompileError::semantic_with_context(
                    format!("method `{}` not found on type `dyn {}`", method, trait_name),
                    ctx,
                ));
            }
        }
        Value::Object { class, fields } => {
            // Try to find and execute the method
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
                return Ok(result);
            }
            // Check if the method name corresponds to a callable field (Lambda/Function)
            // This allows patterns like: self.callback(arg) where callback is a lambda field
            if let Some(field_value) = fields.get(method) {
                match field_value {
                    Value::Lambda { params, body, env: captured_env } => {
                        // Call the lambda stored in the field
                        let mut arg_vals = Vec::new();
                        for arg in args {
                            arg_vals.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        // Create local env from captured env and bind params
                        let mut local_env = captured_env.clone();
                        for (i, param) in params.iter().enumerate() {
                            if let Some(val) = arg_vals.get(i) {
                                local_env.insert(param.clone(), val.clone());
                            }
                        }
                        // Evaluate the body expression
                        let result = evaluate_expr(body.as_ref(), &mut local_env, functions, classes, enums, impl_methods)?;
                        return Ok(result);
                    }
                    Value::Function { def, captured_env, .. } => {
                        // Call the function stored in the field
                        return exec_function_with_captured_env(
                            def,
                            args,
                            env,
                            &mut captured_env.clone(),
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        );
                    }
                    _ => {}
                }
            }
            // Try method_missing hook
            if let Some(result) = try_method_missing(
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
            if let Some(result) =
                special::handle_channel_methods(channel, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            } else {
                let available = ["send", "recv", "try_recv"];
                bail_unknown_method!(method, "Channel", available);
            }
        }
        Value::ThreadPool(pool) => {
            if let Some(result) =
                special::handle_threadpool_methods(pool, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            } else {
                let available = ["submit"];
                bail_unknown_method!(method, "ThreadPool", available);
            }
        }
        Value::Constructor { class_name } => {
            if let Some(result) = special::handle_constructor_methods(
                class_name,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            } else {
                return Err(crate::error::factory::class_not_found(class_name));
            }
        }
        Value::Mock(mock) => {
            if let Some(result) =
                special::handle_mock_methods(mock, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
            // Mock methods handler handles all cases including fallback
            unreachable!("Mock methods handler should have handled all cases");
        }
        Value::Nil => {
            // Treat nil as Option::None for Option-like methods
            match method {
                "map" | "and_then" | "flat_map" => {
                    // map/and_then on None returns None
                    return Ok(Value::Nil);
                }
                "or_else" => {
                    // or_else on None calls the closure
                    let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda { params, body, env: captured } = func {
                        let mut local_env = captured.clone();
                        // No args to bind for or_else
                        return evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods);
                    }
                    return Ok(Value::Nil);
                }
                "unwrap" => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("use unwrap_or(default) or check with is_some() first");
                    return Err(CompileError::semantic_with_context(
                        "called unwrap() on None/nil value".to_string(),
                        ctx,
                    ));
                }
                "unwrap_or" => {
                    // Return the default value
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "unwrap_or_else" => {
                    // Call the closure and return its result
                    let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda { params, body, env: captured } = func {
                        let mut local_env = captured.clone();
                        return evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods);
                    }
                    return Ok(Value::Nil);
                }
                "is_some" | "is_present" => return Ok(Value::Bool(false)),
                "is_none" | "is_nil" | "is_null" => return Ok(Value::Bool(true)),
                "ok_or" => {
                    // Convert None to Err(default)
                    let err_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    return Ok(Value::err(err_val));
                }
                "expect" => {
                    let msg = eval_arg(args, 0, Value::Str("expected Some value".to_string()), env, functions, classes, enums, impl_methods)?;
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION);
                    return Err(CompileError::semantic_with_context(
                        format!("expect() failed: {}", msg.to_display_string()),
                        ctx,
                    ));
                }
                _ => {} // Fall through to default error handling
            }
        }
        _ => {}
    }

    // UFCS Fallback: Try to find a free function with the method name
    // This allows both len(x) and x.len() syntax to work
    if let Some(func) = functions.get(method).cloned() {
        // Evaluate all arguments to values
        let mut arg_values = vec![recv_val.clone()]; // Receiver becomes first argument
        for arg in args {
            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
            arg_values.push(val);
        }
        // Call the function with receiver as first argument
        return exec_function_with_values(
            &func,
            &arg_values,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        );
    }

    // E1013 - Unknown Method (with helpful hints for common conversions)
    let mut ctx = ErrorContext::new().with_code(codes::UNKNOWN_METHOD);

    // Handle special case: method on function value (user probably forgot to call the function)
    if recv_val.type_name() == "function" {
        let func_name = match &recv_val {
            Value::Function { name, .. } => name.clone(),
            Value::Lambda { .. } => "<lambda>".to_string(),
            Value::BlockClosure { .. } => "<block>".to_string(),
            Value::NativeFunction(nf) => format!("<native:{}>", nf.name),
            _ => "<unknown>".to_string(),
        };
        ctx = ctx.with_help(format!(
            "you have a function value, not its result. Did you mean to call it? Try: {}().{}()",
            func_name, method
        ));
        return Err(CompileError::semantic_with_context(
            format!("method `{}` not found on type `function` (function '{}' was not called)", method, func_name),
            ctx,
        ));
    }

    let hint = match method {
        "to_f64" | "to_f32" | "to_float" => {
            Some("use implicit conversion (e.g., `float_val / int_val` auto-converts) or explicit cast: `val as f64`")
        }
        "to_i64" | "to_i32" | "to_int" => Some("use explicit cast: `val as i64` or `val as i32`"),
        "to_str" | "to_string" | "toString" => Some("use `str(val)` function or f-string: `f\"{val}\"`"),
        _ => None,
    };

    if let Some(hint_text) = hint {
        ctx = ctx.with_help(hint_text);
        Err(CompileError::semantic_with_context(
            format!("method `{}` not found on type `{}`", method, recv_val.type_name()),
            ctx,
        ))
    } else {
        ctx = ctx.with_help("check that the method is defined for this type");
        Err(CompileError::semantic_with_context(
            format!("method `{}` not found on type `{}`", method, recv_val.type_name()),
            ctx,
        ))
    }
}

/// Evaluate a method call and return both the result and the potentially modified self.
/// This is used when we need to persist mutations to self back to the calling environment.
pub(crate) fn evaluate_method_call_with_self_update(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<Value>), CompileError> {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Only handle Object methods with self mutation
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some((result, updated_self)) = special::find_and_exec_method_with_self(
            method,
            args,
            &class,
            &fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            return Ok((result, Some(updated_self)));
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(
            method,
            args,
            &class,
            &fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            // method_missing returns just a result, self is not mutated
            return Ok((result, None));
        }
        // UFCS Fallback: Try to find a free function with the method name
        if let Some(func) = functions.get(method).cloned() {
            // Evaluate all arguments to values
            let mut arg_values = vec![recv_val.clone()]; // Receiver becomes first argument
            for arg in args {
                let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                arg_values.push(val);
            }
            // Call the function with receiver as first argument
            let result = exec_function_with_values(
                &func,
                &arg_values,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            return Ok((result, None)); // UFCS calls don't mutate self
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
