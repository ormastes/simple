//! Method dispatch and method_missing hooks

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, OptionVariant, ResultVariant, Value, METHOD_MISSING};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef};
use std::collections::HashMap;

use super::super::{evaluate_expr, evaluate_method_call_with_self_update, exec_function, Control, Enums, ImplMethods, BLANKET_IMPL_METHODS};
use crate::interpreter::interpreter_call::{exec_function_with_values, exec_function_with_values_and_self};

pub(crate) fn call_method_on_value(
    recv_val: Value,
    method: &str,
    _args: &[Value],
    _env: &mut Env,
    _functions: &mut HashMap<String, FunctionDef>,
    _classes: &mut HashMap<String, ClassDef>,
    _enums: &Enums,
    _impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let recv_val = recv_val.deref_pointer();

    // Handle common methods for chained calls
    match &recv_val {
        // String methods
        Value::Str(s) => match method {
            "len" | "length" => return Ok(Value::Int(s.chars().count() as i64)),
            "is_empty" => return Ok(Value::Bool(s.is_empty())),
            "to_string" => return Ok(Value::Str(s.clone())),
            "chars" => return Ok(Value::Array(s.chars().map(|c| Value::Str(c.to_string())).collect())),
            "trim" | "strip" => return Ok(Value::Str(s.trim().to_string())),
            "to_upper" | "upper" | "uppercase" => return Ok(Value::Str(s.to_uppercase())),
            "to_lower" | "lower" | "lowercase" => return Ok(Value::Str(s.to_lowercase())),
            _ => {}
        },

        // Option methods (most common in chained calls)
        Value::Enum {
            enum_name,
            variant,
            payload,
        } if enum_name == "Option" => {
            let opt_variant = OptionVariant::from_name(variant);
            match method {
                "is_some" => return Ok(Value::Bool(opt_variant == Some(OptionVariant::Some))),
                "is_none" => return Ok(Value::Bool(opt_variant == Some(OptionVariant::None))),
                "unwrap" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    let ctx = ErrorContext::new()
                        .with_code(codes::INDEX_OUT_OF_BOUNDS)
                        .with_help("check that the Option contains Some before calling unwrap");
                    return Err(CompileError::semantic_with_context(
                        "called unwrap on None".to_string(),
                        ctx,
                    ));
                }
                "unwrap_or" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    // Return the default value from args if provided
                    if let Some(default) = _args.first() {
                        return Ok(default.clone());
                    }
                    return Ok(Value::Nil);
                }
                _ => {}
            }
        }

        // Result methods
        Value::Enum {
            enum_name,
            variant,
            payload,
        } if enum_name == "Result" => {
            let res_variant = ResultVariant::from_name(variant);
            match method {
                "is_ok" => return Ok(Value::Bool(res_variant == Some(ResultVariant::Ok))),
                "is_err" => return Ok(Value::Bool(res_variant == Some(ResultVariant::Err))),
                "unwrap" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    if let Some(err_val) = payload {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help("check that the Result is Ok before calling unwrap");
                        return Err(CompileError::semantic_with_context(
                            format!("called unwrap on Err: {}", err_val.to_display_string()),
                            ctx,
                        ));
                    }
                    let ctx = ErrorContext::new()
                        .with_code(codes::INDEX_OUT_OF_BOUNDS)
                        .with_help("check that the Result is Ok before calling unwrap");
                    return Err(CompileError::semantic_with_context(
                        "called unwrap on Err".to_string(),
                        ctx,
                    ));
                }
                "unwrap_err" => {
                    if res_variant == Some(ResultVariant::Err) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    let ctx = ErrorContext::new()
                        .with_code(codes::INDEX_OUT_OF_BOUNDS)
                        .with_help("check that the Result is Err before calling unwrap_err");
                    return Err(CompileError::semantic_with_context(
                        "called unwrap_err on Ok".to_string(),
                        ctx,
                    ));
                }
                _ => {}
            }
        }

        // Array methods
        Value::Array(arr) => match method {
            "len" | "length" => return Ok(Value::Int(arr.len() as i64)),
            "is_empty" => return Ok(Value::Bool(arr.is_empty())),
            "first" => {
                return Ok(arr.first().map(|v| Value::some(v.clone())).unwrap_or_else(Value::none));
            }
            "last" => {
                return Ok(arr.last().map(|v| Value::some(v.clone())).unwrap_or_else(Value::none));
            }
            _ => {}
        },

        // Int methods
        Value::Int(n) => match method {
            "abs" => return Ok(Value::Int(n.abs())),
            "to_string" => return Ok(Value::Str(n.to_string())),
            _ => {}
        },

        // Float methods
        Value::Float(f) => match method {
            "abs" => return Ok(Value::Float(f.abs())),
            "floor" => return Ok(Value::Float(f.floor())),
            "ceil" => return Ok(Value::Float(f.ceil())),
            "round" => return Ok(Value::Float(f.round())),
            "to_string" => return Ok(Value::Str(f.to_string())),
            _ => {}
        },

        // Custom class methods - enable method chaining on user-defined classes
        Value::Object { class, fields } => {
            // Search for method in class definition
            if let Some(class_def) = _classes.get(class).cloned() {
                if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
                    // Call method with self context
                    return exec_function_with_values_and_self(
                        func,
                        _args,
                        _env,
                        _functions,
                        _classes,
                        _enums,
                        _impl_methods,
                        Some((class, fields)),
                    );
                }
            }

            // Search for method in impl blocks
            if let Some(methods) = _impl_methods.get(class) {
                if let Some(func) = methods.iter().find(|m| m.name == method) {
                    return exec_function_with_values_and_self(
                        func,
                        _args,
                        _env,
                        _functions,
                        _classes,
                        _enums,
                        _impl_methods,
                        Some((class, fields)),
                    );
                }
            }

            // Method not found, fall through to error
        }

        _ => {}
    }

    // UFCS Fallback: Try to find a free function with the method name
    // This allows both len(x) and x.len() syntax to work in chained calls
    if let Some(func) = _functions.get(method).cloned() {
        // Prepend receiver to the arguments
        let mut arg_values = vec![recv_val.clone()];
        arg_values.extend(_args.iter().cloned());
        // Call the function with receiver as first argument
        return exec_function_with_values(
            &func,
            &arg_values,
            _env,
            _functions,
            _classes,
            _enums,
            _impl_methods,
        );
    }

    let ctx = ErrorContext::new()
        .with_code(codes::METHOD_NOT_FOUND)
        .with_help("check that the method is defined on this type");
    Err(CompileError::semantic_with_context(
        format!(
            "method '{}' not found on value of type {} in nested call context",
            method,
            recv_val.type_name()
        ),
        ctx,
    ))
}

/// Build method_missing arguments from method name and original args
pub(crate) fn build_method_missing_args(
    method: &str,
    args: &[simple_parser::ast::Argument],
) -> Vec<simple_parser::ast::Argument> {
    vec![
        simple_parser::ast::Argument::new(None, Expr::Symbol(method.to_string())),
        simple_parser::ast::Argument::new(None, Expr::Array(args.iter().map(|a| a.value.clone()).collect())),
        simple_parser::ast::Argument::new(None, Expr::Nil),
    ]
}

/// Internal helper: find and execute a method by name on a class/struct object.
/// Searches in class_def methods first, then impl_methods, then blanket impls.
/// Returns Ok(Some(value)) if method found, Ok(None) if not found.
fn find_method_and_exec(
    method_name: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class).cloned() {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method_name) {
            return Ok(Some(exec_function(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                Some((class, fields)),
            )?));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method_name) {
            return Ok(Some(exec_function(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                Some((class, fields)),
            )?));
        }
    }

    // Check blanket impls - search all registered blanket impls for the method
    // Blanket impls apply to any type that doesn't have a concrete impl
    let blanket_method: Option<FunctionDef> = BLANKET_IMPL_METHODS.with(|cell| {
        let blanket_impls = cell.borrow();
        // Search through all blanket impls (keyed by trait name)
        for (_trait_name, methods) in blanket_impls.iter() {
            if let Some(func) = methods.iter().find(|m| m.name == method_name) {
                return Some(func.clone());
            }
        }
        None
    });

    if let Some(func) = blanket_method {
        return Ok(Some(exec_function(
            &func,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            Some((class, fields)),
        )?));
    }

    Ok(None)
}

/// Find and execute a method on a class/struct object.
/// Searches in class_def methods first, then impl_methods.
/// Returns Ok(Some(value)) if method found, Ok(None) if not found.
pub(crate) fn find_and_exec_method<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    find_method_and_exec(
        method,
        args,
        class,
        fields,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )
}

/// Try to call method_missing hook on a class/struct object.
/// Returns Ok(Some(value)) if method_missing found, Ok(None) if not found.
pub(crate) fn try_method_missing<'a>(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let mm_args = build_method_missing_args(method, args);
    find_method_and_exec(
        METHOD_MISSING,
        &mm_args,
        class,
        fields,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )
}
