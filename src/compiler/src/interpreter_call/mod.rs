// Call expression evaluation (main dispatcher)

mod bdd;
mod block_execution;
mod builtins;
mod core;
mod mock;

// Re-export public items
pub(crate) use bdd::{
    exec_block_value, BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_EXPECT_FAILED,
    BDD_FAILURE_MSG, BDD_INDENT, BDD_LAZY_VALUES, BDD_SHARED_EXAMPLES,
};
pub(crate) use core::{
    bind_args, bind_args_with_injected, exec_function, exec_function_with_captured_env, exec_function_with_values,
    exec_function_with_values_and_self, exec_lambda, instantiate_class, ProceedContext, IN_NEW_METHOD,
};

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    call_extern_function, dispatch_context_method, evaluate_expr, BUILTIN_CHANNEL, CONTEXT_OBJECT, EXTERN_FUNCTIONS,
};
use crate::value::*;
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef};
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

const METHOD_SELF: &str = "self";

pub(crate) fn evaluate_call(
    callee: &Box<Expr>,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Try built-in functions first
    if let Expr::Identifier(name) = callee.as_ref() {
        // Try built-ins
        if let Some(result) = builtins::eval_builtin(name, args, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }

        // Try BDD framework
        if let Some(result) = bdd::eval_bdd_builtin(name, args, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }

        // Try mock library
        if let Some(result) = mock::eval_mock_builtin(name, args, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }

        // Check env for decorated functions and closures
        if let Some(val) = env.get(name).cloned() {
            match val {
                Value::Function { def, captured_env, .. } => {
                    let mut captured_env_clone = captured_env.clone();
                    return core::exec_function_with_captured_env(
                        &def,
                        args,
                        env,
                        &mut captured_env_clone,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
                Value::Lambda {
                    params,
                    body,
                    env: captured,
                } => {
                    let mut captured_clone = captured.clone();
                    return core::exec_lambda(
                        &params,
                        &body,
                        args,
                        env,
                        &mut captured_clone,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
                Value::Constructor { class_name } => {
                    return core::instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods);
                }
                Value::NativeFunction(native) => {
                    let evaluated: Vec<Value> = args
                        .iter()
                        .map(|a| {
                            if a.name.is_some() {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                                    .with_help("native functions do not support named arguments");
                                return Err(CompileError::semantic_with_context(
                                    "native function does not support named arguments".to_string(),
                                    ctx,
                                ));
                            }
                            evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    return (native.func)(&evaluated);
                }
                _ => {}
            }
        }

        // Check regular functions
        if let Some(func) = functions.get(name).cloned() {
            return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
        }

        // Check extern functions
        let is_extern = EXTERN_FUNCTIONS.with(|cell| cell.borrow().contains(name));
        if is_extern {
            return call_extern_function(name, args, env, functions, classes, enums, impl_methods);
        }

        // Check class constructors (e.g., MyClass() instantiation)
        if classes.contains_key(name) {
            return core::instantiate_class(name, args, env, functions, classes, enums, impl_methods);
        }

        // Check context object
        let context_obj = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
        if let Some(ctx) = context_obj {
            return dispatch_context_method(&ctx, name, args, env, functions, classes, enums, impl_methods);
        }

        // If we reach here with an identifier name, the function is not found
        // E1002 - Undefined Function
        let known_names: Vec<&str> = functions.keys().map(|s| s.as_str()).collect();

        let suggestion = crate::error::typo::suggest_name(name, known_names.clone());
        let mut ctx = ErrorContext::new()
            .with_code(codes::UNDEFINED_FUNCTION)
            .with_help("check that the function is defined and in scope");

        if let Some(best_match) = suggestion {
            ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
        }

        if !known_names.is_empty() && known_names.len() <= 5 {
            let names_list = known_names.join(", ");
            ctx = ctx.with_note(format!("available functions: {}", names_list));
        }

        return Err(CompileError::semantic_with_context(
            format!("function `{}` not found", name),
            ctx,
        ));
    }

    // Handle module-style calls: module.function()
    if let Expr::FieldAccess { receiver, field } = callee.as_ref() {
        if let Expr::Identifier(module_name) = receiver.as_ref() {
            // First, check if the receiver is a module dict in env
            if let Some(module_val) = env.get(module_name).cloned() {
                if let Value::Dict(module_dict) = module_val {
                    // Look up function in the module's exports
                    if let Some(func_val) = module_dict.get(field).cloned() {
                        if let Value::Function { def, captured_env, .. } = func_val {
                            let mut captured_env_clone = captured_env.clone();
                            return core::exec_function_with_captured_env(
                                &def,
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
                            return core::instantiate_class(
                                &class_name,
                                args,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            );
                        }
                    }
                }
            }
            // Check for static method call on a type: Type.method()
            // This handles calls like Set.new() or Set.from_array()
            if let Some(methods) = impl_methods.get(module_name) {
                if let Some(func) = methods.iter().find(|m| &m.name == field) {
                    return core::exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                }
            }
            // Check for class static methods
            if let Some(class_def) = classes.get(module_name).cloned() {
                if let Some(func) = class_def.methods.iter().find(|m| &m.name == field) {
                    return core::exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                }
            }

            // Fall back to global functions if module lookup failed
            if let Some(func) = functions.get(field).cloned() {
                return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(field) {
                return core::instantiate_class(field, args, env, functions, classes, enums, impl_methods);
            } else if let Some(func) = env.get(field).cloned() {
                if let Value::Function { def, captured_env, .. } = func {
                    let mut captured_env_clone = captured_env.clone();
                    return core::exec_function_with_captured_env(
                        &def,
                        args,
                        env,
                        &mut captured_env_clone,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    );
                }
            }
            let ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_VARIABLE)
                .with_help("check that the symbol exists in the module");
            return Err(CompileError::semantic_with_context(
                format!("unknown symbol {}.{}", module_name, field),
                ctx,
            ));
        }
    }

    // Handle path calls: Type::method(args) or Type::Variant(args)
    if let Expr::Path(segments) = callee.as_ref() {
        if segments.len() == 2 {
            let type_name = &segments[0];
            let method_name = &segments[1];

            // Check if it's an enum variant constructor
            if let Some(enum_def) = enums.get(type_name) {
                if enum_def.variants.iter().any(|v| &v.name == method_name) {
                    let payload = if args.is_empty() {
                        None
                    } else if args.len() == 1 {
                        Some(Box::new(evaluate_expr(
                            &args[0].value,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?))
                    } else {
                        let mut values = Vec::new();
                        for arg in args {
                            values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        Some(Box::new(Value::Tuple(values)))
                    };
                    return Ok(Value::Enum {
                        enum_name: type_name.clone(),
                        variant: method_name.clone(),
                        payload,
                    });
                }
            }

            // Check for associated function call
            if let Some(methods) = impl_methods.get(type_name) {
                if let Some(func) = methods.iter().find(|m| m.name == *method_name) {
                    return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                }
            }

            // Check for class associated function (static method)
            if let Some(class_def) = classes.get(type_name).cloned() {
                if let Some(func) = class_def.methods.iter().find(|m| m.name == *method_name) {
                    return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
                }
            }

            // Legacy fallbacks
            if let Some(func) = functions.get(method_name).cloned() {
                return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            } else if classes.contains_key(method_name) {
                return core::instantiate_class(method_name, args, env, functions, classes, enums, impl_methods);
            }
        }
        bail_semantic!("unsupported path call: {:?}", segments);
    }

    // Handle generic type constructors like Channel[int]()
    if let Expr::Index { receiver, .. } = callee.as_ref() {
        if let Expr::Identifier(name) = receiver.as_ref() {
            if name == BUILTIN_CHANNEL {
                let buffer_size = args.iter().find_map(|arg| {
                    if arg.name.as_deref() == Some("buffer") {
                        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                            .ok()
                            .and_then(|v| v.as_int().ok())
                            .map(|n| n as usize)
                    } else {
                        None
                    }
                });

                let channel = if let Some(size) = buffer_size {
                    ChannelValue::with_buffer(size)
                } else {
                    ChannelValue::new()
                };
                return Ok(Value::Channel(channel));
            }
        }
    }

    // Evaluate callee and dispatch based on value type
    let callee_val = evaluate_expr(callee, env, functions, classes, enums, impl_methods)?;
    match callee_val {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            let mut captured_clone = captured.clone();
            core::exec_lambda(
                &params,
                &body,
                args,
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::BlockClosure { nodes, env: captured } => {
            let mut captured_clone = captured.clone();
            block_execution::exec_block_closure(&nodes, &mut captured_clone, functions, classes, enums, impl_methods)
        }
        Value::Function { def, captured_env, .. } => {
            let mut captured_env_clone = captured_env.clone();
            core::exec_function_with_captured_env(
                &def,
                args,
                env,
                &mut captured_env_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::NativeFunction(native) => {
            let evaluated: Vec<Value> = args
                .iter()
                .map(|a| {
                    if a.name.is_some() {
                        let ctx = ErrorContext::new()
                            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                            .with_help("native functions do not support named arguments");
                        return Err(CompileError::semantic_with_context(
                            "native function does not support named arguments".to_string(),
                            ctx,
                        ));
                    }
                    evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)
                })
                .collect::<Result<Vec<_>, _>>()?;
            (native.func)(&evaluated)
        }
        Value::Constructor { class_name } => {
            core::instantiate_class(&class_name, args, env, functions, classes, enums, impl_methods)
        }
        Value::EnumVariantConstructor {
            enum_name,
            variant_name,
        } => {
            // Construct enum variant with payload
            // Currently supports single payload value
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
            Ok(Value::Enum {
                enum_name,
                variant: variant_name,
                payload,
            })
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::NOT_CALLABLE)
                .with_help("value must be a function, lambda, constructor, or other callable type");
            Err(CompileError::semantic_with_context(
                "value is not callable".to_string(),
                ctx,
            ))
        }
    }
}
