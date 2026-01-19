use std::collections::HashMap;

use simple_parser::ast::Expr;

use super::evaluate_expr;
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::value::Value;

use super::super::{
    evaluate_call, evaluate_method_call, exec_method_function, ClassDef, Enums, Env, FunctionDef, ImplMethods,
};

pub(super) fn eval_call_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::Call { callee, args } => Ok(Some(evaluate_call(
            callee,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?)),
        Expr::MethodCall { receiver, method, args } => Ok(Some(evaluate_method_call(
            receiver,
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?)),
        Expr::FieldAccess { receiver, field } => {
            // Support module-style access (lib.foo) by resolving directly to functions/classes
            if let Expr::Identifier(module_name) = receiver.as_ref() {
                if env.get(module_name).is_none() {
                    if let Some(func) = functions.get(field).cloned() {
                        return Ok(Some(Value::Function {
                            name: field.clone(),
                            def: Box::new(func.clone()),
                            captured_env: Env::new(),
                        }));
                    }
                    if classes.contains_key(field) {
                        return Ok(Some(Value::Constructor {
                            class_name: field.clone(),
                        }));
                    }
                }
            }

            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let result = match recv_val {
                Value::Object {
                    ref fields, ref class, ..
                } => {
                    // First, try direct field access
                    if let Some(val) = fields.get(field) {
                        return Ok(Some(val.clone()));
                    }
                    // Auto-initializing internal fields: fields starting with '_' default to 0
                    if field.starts_with('_') {
                        return Ok(Some(Value::Int(0)));
                    }
                    // Auto-forwarding: try get_<field>() or is_<field>() methods
                    let getter_name = format!("get_{}", field);
                    let is_getter_name = format!("is_{}", field);

                    if let Some(class_def) = classes.get(class).cloned() {
                        // Try get_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == getter_name) {
                            // Call the getter method with self
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return Ok(Some(exec_method_function(
                                method,
                                &[],
                                &self_val,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?));
                        }
                        // Try is_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == is_getter_name) {
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return Ok(Some(exec_method_function(
                                method,
                                &[],
                                &self_val,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?));
                        }
                    }

                    // E1012 - Undefined Field
                    let available_fields: Vec<&str> = fields.keys().map(|s| s.as_str()).collect();
                    let suggestion = if !available_fields.is_empty() {
                        typo::suggest_name(field, available_fields.clone())
                    } else {
                        None
                    };

                    let mut ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_FIELD)
                        .with_help("check the field name and class definition");

                    if let Some(best_match) = suggestion {
                        ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                    }

                    if !available_fields.is_empty() && available_fields.len() <= 5 {
                        let fields_list = available_fields.join(", ");
                        ctx = ctx.with_note(format!("available fields: {}", fields_list));
                    }

                    Err(CompileError::semantic_with_context(
                        format!("class `{}` has no field named `{}`", class, field),
                        ctx,
                    ))
                }
                Value::Constructor { ref class_name } => {
                    // Look up static method on class
                    if let Some(class_def) = classes.get(class_name).cloned() {
                        if let Some(method) = class_def.methods.iter().find(|m| &m.name == field) {
                            // Return as a function value for call
                            Ok(Value::Function {
                                name: method.name.clone(),
                                def: Box::new(method.clone()),
                                captured_env: Env::new(),
                            })
                        } else {
                            // E1013 - Unknown Method (static method on class)
                            let available_methods: Vec<&str> = class_def
                                .methods
                                .iter()
                                .map(|m| m.name.as_str())
                                .collect();
                            let suggestion = if !available_methods.is_empty() {
                                typo::suggest_name(field, available_methods.clone())
                            } else {
                                None
                            };

                            let mut ctx = ErrorContext::new()
                                .with_code(codes::UNKNOWN_METHOD)
                                .with_help("check that the method is defined in the class");

                            if let Some(best_match) = suggestion {
                                ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                            }

                            if !available_methods.is_empty() && available_methods.len() <= 5 {
                                let methods_list = available_methods.join(", ");
                                ctx = ctx.with_note(format!("available methods: {}", methods_list));
                            }

                            Err(CompileError::semantic_with_context(
                                format!("method `{}` not found on type `{}`", field, class_name),
                                ctx,
                            ))
                        }
                    } else {
                        // E1014 - Unknown Class
                        let available_classes: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
                        let suggestion = if !available_classes.is_empty() {
                            typo::suggest_name(class_name, available_classes.clone())
                        } else {
                            None
                        };

                        let mut ctx = ErrorContext::new()
                            .with_code(codes::UNKNOWN_CLASS)
                            .with_help("check that the class is defined or imported in this scope");

                        if let Some(best_match) = suggestion {
                            ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                        }

                        Err(CompileError::semantic_with_context(
                            format!("class `{}` not found in this scope", class_name),
                            ctx,
                        ))
                    }
                }
                // Enum type field access - construct enum variants
                // EnumName.VariantName syntax
                Value::EnumType { ref enum_name } => {
                    if let Some(enum_def) = enums.get(enum_name).cloned() {
                        // Check if the field is a valid variant name
                        let variant_opt = enum_def.variants.iter().find(|v| v.name == *field);
                        if let Some(variant) = variant_opt {
                            // For unit variants (no fields), return the enum value directly
                            // For variants with data, we'd need to return a constructor function
                            let has_fields = variant.fields.as_ref().map_or(false, |f| !f.is_empty());
                            if !has_fields {
                                Ok(Value::Enum {
                                    enum_name: enum_name.clone(),
                                    variant: field.clone(),
                                    payload: None,
                                })
                            } else {
                                // Return a constructor-like callable for variants with data
                                Ok(Value::EnumVariantConstructor {
                                    enum_name: enum_name.clone(),
                                    variant_name: field.clone(),
                                })
                            }
                        } else {
                            // Check for enum methods
                            if let Some(method) = enum_def.methods.iter().find(|m| m.name == *field) {
                                Ok(Value::Function {
                                    name: method.name.clone(),
                                    def: Box::new(method.clone()),
                                    captured_env: Env::new(),
                                })
                            } else {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::METHOD_NOT_FOUND)
                                    .with_help("check that this variant or method is defined on this enum");
                                Err(CompileError::semantic_with_context(
                                    format!(
                                        "unknown variant or method '{}' on enum {}",
                                        field, enum_name
                                    ),
                                    ctx,
                                ))
                            }
                        }
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

                        Err(CompileError::semantic_with_context(
                            format!("enum `{}` not found in this scope", enum_name),
                            ctx,
                        ))
                    }
                }
                // String property access (e.g., str.len, str.is_empty)
                Value::Str(ref s) => match field.as_str() {
                    "len" => Ok(Value::Int(s.len() as i64)),
                    "byte_len" => Ok(Value::Int(s.len() as i64)),
                    "char_count" => Ok(Value::Int(s.chars().count() as i64)),
                    "is_empty" => Ok(Value::Bool(s.is_empty())),
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::UNDEFINED_FIELD)
                            .with_help("available properties on String: len, byte_len, char_count, is_empty");
                        Err(CompileError::semantic_with_context(
                            format!("undefined field: unknown property '{field}' on String"),
                            ctx,
                        ))
                    },
                },
                // Array property access (e.g., arr.len, arr.is_empty)
                Value::Array(ref arr) => match field.as_str() {
                    "len" => Ok(Value::Int(arr.len() as i64)),
                    "is_empty" => Ok(Value::Bool(arr.is_empty())),
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::UNDEFINED_FIELD)
                            .with_help("available properties on Array: len, is_empty");
                        Err(CompileError::semantic_with_context(
                            format!("undefined field: unknown property '{field}' on Array"),
                            ctx,
                        ))
                    },
                },
                // Tuple property access (e.g., tup.len)
                Value::Tuple(ref tup) => match field.as_str() {
                    "len" => Ok(Value::Int(tup.len() as i64)),
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::UNDEFINED_FIELD)
                            .with_help("available properties on Tuple: len");
                        Err(CompileError::semantic_with_context(
                            format!("undefined field: unknown property '{field}' on Tuple"),
                            ctx,
                        ))
                    },
                },
                // Dict property access (e.g., dict.len, dict.is_empty)
                // Also supports module namespace access (e.g., physics.World)
                Value::Dict(ref map) => match field.as_str() {
                    "len" => Ok(Value::Int(map.len() as i64)),
                    "is_empty" => Ok(Value::Bool(map.is_empty())),
                    _ => {
                        // Check if this is a key in the dict (module namespace access)
                        if let Some(value) = map.get(field) {
                            Ok(value.clone())
                        } else {
                            let ctx = ErrorContext::new()
                                .with_code(codes::UNDEFINED_FIELD)
                                .with_help("available properties on Dict: len, is_empty");
                            Err(CompileError::semantic_with_context(
                                format!("undefined field: unknown property or key '{field}' on Dict"),
                                ctx,
                            ))
                        }
                    }
                },
                // Enum property access (Option/Result properties)
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ..
                } => {
                    if enum_name == "Option" {
                        match field.as_str() {
                            "is_some" => Ok(Value::Bool(variant == "Some")),
                            "is_none" => Ok(Value::Bool(variant == "None")),
                            _ => {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("available properties on Option: is_some, is_none");
                                Err(CompileError::semantic_with_context(
                                    format!("undefined field: unknown property '{field}' on Option"),
                                    ctx,
                                ))
                            },
                        }
                    } else if enum_name == "Result" {
                        match field.as_str() {
                            "is_ok" => Ok(Value::Bool(variant == "Ok")),
                            "is_err" => Ok(Value::Bool(variant == "Err")),
                            _ => {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("available properties on Result: is_ok, is_err");
                                Err(CompileError::semantic_with_context(
                                    format!("undefined field: unknown property '{field}' on Result"),
                                    ctx,
                                ))
                            },
                        }
                    } else {
                        let ctx = ErrorContext::new()
                            .with_code(codes::UNDEFINED_FIELD)
                            .with_help(format!("check that the property '{field}' exists on enum {enum_name}"));
                        Err(CompileError::semantic_with_context(
                            format!("undefined field: unknown property '{field}' on enum {enum_name}"),
                            ctx,
                        ))
                    }
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_FIELD)
                        .with_help("field access requires an object, array, dict, or enum value");
                    Err(CompileError::semantic_with_context(
                        "undefined field: cannot access field on this value type",
                        ctx,
                    ))
                },
            };
            Ok(Some(result?))
        }
        Expr::FunctionalUpdate { target, method, args } => {
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            Ok(Some(evaluate_expr(
                &method_call,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?))
        }
        _ => Ok(None),
    }
}
