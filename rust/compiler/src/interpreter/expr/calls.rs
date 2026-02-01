use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{Argument, Expr};

use super::evaluate_expr;
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::value::Value;

use super::super::{
    evaluate_call, evaluate_method_call, exec_method_function, find_and_exec_method_with_self, ClassDef, Enums, Env,
    FunctionDef, ImplMethods, BLOCK_SCOPED_ENUMS,
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
        Expr::MethodCall { receiver, method, args } => {
            // Check if receiver is an identifier - if so, we may need to update it
            // after calling a mutating (me) method
            if let Expr::Identifier(var_name) = receiver.as_ref() {
                // Use the self-update variant to get both result and updated self
                let (result, updated_self) = super::super::evaluate_method_call_with_self_update(
                    receiver,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?;
                // If self was updated (from a me method), update the variable in env
                if let Some(new_self) = updated_self {
                    env.insert(var_name.clone(), new_self);
                }
                Ok(Some(result))
            } else if let Expr::FieldAccess {
                receiver: outer_receiver,
                field,
            } = receiver.as_ref()
            {
                // Handle nested field access like self.instructions.push()
                // where self.instructions needs to be updated after a mutating method call
                if let Expr::Identifier(var_name) = outer_receiver.as_ref() {
                    // Evaluate the outer receiver to get its current value
                    let outer_val = evaluate_expr(outer_receiver, env, functions, classes, enums, impl_methods)?;
                    if let Value::Object { class, fields } = outer_val {
                        let mut fields = fields;
                        // Get the field value (can be Object, Array, Dict, String, etc.)
                        if let Some(field_val) = fields.get(field).cloned() {
                            // Store field value in a temporary variable so we can call method on it
                            let temp_var = format!("__nested_field_{}__", field);
                            env.insert(temp_var.clone(), field_val.clone());

                            // Call method with self-update tracking
                            let temp_receiver = Box::new(Expr::Identifier(temp_var.clone()));
                            let (result, updated_field) = super::super::evaluate_method_call_with_self_update(
                                &temp_receiver,
                                method,
                                args,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?;

                            // Clean up temporary variable
                            env.remove(&temp_var);

                            // If the field was updated by a mutating method, update it in the outer object
                            if let Some(new_field_val) = updated_field {
                                Arc::make_mut(&mut fields).insert(field.clone(), new_field_val);
                                env.insert(var_name.clone(), Value::Object { class, fields });
                            }

                            return Ok(Some(result));
                        }
                    }
                }
                // Fall through to regular method call if nested update doesn't apply
                Ok(Some(evaluate_method_call(
                    receiver,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?))
            } else {
                // For other expressions (like temporaries), use regular method call
                Ok(Some(evaluate_method_call(
                    receiver,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?))
            }
        }
        Expr::FieldAccess { receiver, field } => {
            // Support module-style access (lib.foo) by resolving directly to functions/classes
            if let Expr::Identifier(module_name) = receiver.as_ref() {
                if env.get(module_name).is_none() {
                    // Special handling for built-in Option and Result enum variants
                    if module_name == "Option" && (field == "Some" || field == "None") {
                        // Return a constructor function for the variant
                        // When called, it will create the enum value
                        // For None, just return the enum value directly since it has no payload
                        if field == "None" {
                            return Ok(Some(Value::Enum {
                                enum_name: "Option".to_string(),
                                variant: "None".to_string(),
                                payload: None,
                            }));
                        }
                        // For Some, we can't return a constructor here because field access
                        // doesn't create functions. The user should use Option.Some(x) with parens.
                        // But to match Rust/Scala style, let's return a special marker.
                        // Actually, this won't work well. Let me reconsider.
                    }
                    if module_name == "Result" && (field == "Ok" || field == "Err") {
                        // Similar issue - Result variants need arguments, so field access doesn't work
                    }

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
                    // Look up static method on class - check both class_def.methods and impl_methods
                    if let Some(class_def) = classes.get(class_name).cloned() {
                        // First check methods defined in class body
                        if let Some(method) = class_def.methods.iter().find(|m| &m.name == field) {
                            // Warn if using deprecated .new() pattern
                            if field == "new" {
                                eprintln!("[WARN] Deprecated: {}.new() should be replaced with {}(). Use direct construction instead.", class_name, class_name);
                            }
                            // Return as a function value for call
                            return Ok(Some(Value::Function {
                                name: method.name.clone(),
                                def: Box::new(method.clone()),
                                captured_env: Env::new(),
                            }));
                        }
                        // Then check methods defined in impl blocks
                        if let Some(methods) = impl_methods.get(class_name) {
                            if let Some(method) = methods.iter().find(|m| &m.name == field) {
                                // Warn if using deprecated .new() pattern
                                if field == "new" {
                                    eprintln!("[WARN] Deprecated: {}.new() should be replaced with {}(). Use direct construction instead.", class_name, class_name);
                                }
                                return Ok(Some(Value::Function {
                                    name: method.name.clone(),
                                    def: Box::new(method.clone()),
                                    captured_env: Env::new(),
                                }));
                            }
                        }
                        {
                            // E1013 - Unknown Method (static method on class)
                            // Collect methods from both class body and impl blocks
                            let mut available_methods: Vec<&str> =
                                class_def.methods.iter().map(|m| m.name.as_str()).collect();
                            if let Some(impl_meths) = impl_methods.get(class_name) {
                                available_methods.extend(impl_meths.iter().map(|m| m.name.as_str()));
                            }
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
                    // Check both module-level enums and block-scoped enums
                    let enum_def = enums
                        .get(enum_name)
                        .cloned()
                        .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()));
                    if let Some(enum_def) = enum_def {
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
                                    format!("unknown variant or method '{}' on enum {}", field, enum_name),
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
                // Also supports no-paren method calls (e.g., str.upper, str.trim)
                Value::Str(ref s) => match field.as_str() {
                    "len" => Ok(Value::Int(s.len() as i64)),
                    "byte_len" => Ok(Value::Int(s.len() as i64)),
                    "char_count" => Ok(Value::Int(s.chars().count() as i64)),
                    "is_empty" => Ok(Value::Bool(s.is_empty())),
                    _ => {
                        // Try calling as a no-arg method (e.g., str.upper, str.trim)
                        let empty_args: Vec<Argument> = vec![];
                        match evaluate_method_call(
                            receiver,
                            field,
                            &empty_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok(result) => Ok(result),
                            Err(_) => {
                                let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FIELD).with_help(
                                    "available properties: len, byte_len, char_count, is_empty; or use method() syntax",
                                );
                                Err(CompileError::semantic_with_context(
                                    format!("undefined field: unknown property or method '{field}' on String"),
                                    ctx,
                                ))
                            }
                        }
                    }
                },
                // Array property access (e.g., arr.len, arr.is_empty)
                // Also supports no-paren method calls (e.g., arr.first, arr.last, arr.reverse)
                Value::Array(ref arr) => match field.as_str() {
                    "len" => Ok(Value::Int(arr.len() as i64)),
                    "is_empty" => Ok(Value::Bool(arr.is_empty())),
                    _ => {
                        // Try calling as a no-arg method (e.g., arr.first, arr.last, arr.reverse)
                        let empty_args: Vec<Argument> = vec![];
                        match evaluate_method_call(
                            receiver,
                            field,
                            &empty_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok(result) => Ok(result),
                            Err(_) => {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("available properties: len, is_empty; or use method() syntax");
                                Err(CompileError::semantic_with_context(
                                    format!("undefined field: unknown property or method '{field}' on Array"),
                                    ctx,
                                ))
                            }
                        }
                    }
                },
                // Tuple property access (e.g., tup.len)
                // Also supports no-paren method calls
                Value::Tuple(ref _tup) => match field.as_str() {
                    "len" => Ok(Value::Int(_tup.len() as i64)),
                    _ => {
                        // Try calling as a no-arg method
                        let empty_args: Vec<Argument> = vec![];
                        match evaluate_method_call(
                            receiver,
                            field,
                            &empty_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok(result) => Ok(result),
                            Err(_) => {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNDEFINED_FIELD)
                                    .with_help("available properties: len; or use method() syntax");
                                Err(CompileError::semantic_with_context(
                                    format!("undefined field: unknown property or method '{field}' on Tuple"),
                                    ctx,
                                ))
                            }
                        }
                    }
                },
                // Dict property access (e.g., dict.len, dict.is_empty)
                // Also supports module namespace access and no-paren method calls
                Value::Dict(ref map) => match field.as_str() {
                    "len" => Ok(Value::Int(map.len() as i64)),
                    "is_empty" => Ok(Value::Bool(map.is_empty())),
                    _ => {
                        // Check if this is a key in the dict (module namespace access)
                        if let Some(value) = map.get(field) {
                            Ok(value.clone())
                        } else {
                            // Try calling as a no-arg method (e.g., dict.keys, dict.values)
                            let empty_args: Vec<Argument> = vec![];
                            match evaluate_method_call(
                                receiver,
                                field,
                                &empty_args,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            ) {
                                Ok(result) => Ok(result),
                                Err(_) => {
                                    let ctx = ErrorContext::new()
                                        .with_code(codes::UNDEFINED_FIELD)
                                        .with_help("available properties: len, is_empty; or use method() syntax");
                                    Err(CompileError::semantic_with_context(
                                        format!("undefined field: unknown property, key, or method '{field}' on Dict"),
                                        ctx,
                                    ))
                                }
                            }
                        }
                    }
                },
                // Enum property access (Option/Result properties)
                // Also supports no-paren method calls
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
                                // Try calling as a no-arg method
                                let empty_args: Vec<Argument> = vec![];
                                match evaluate_method_call(
                                    receiver,
                                    field,
                                    &empty_args,
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                ) {
                                    Ok(result) => Ok(result),
                                    Err(_) => {
                                        let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FIELD).with_help(
                                            "available properties: is_some, is_none; or use method() syntax",
                                        );
                                        Err(CompileError::semantic_with_context(
                                            format!("undefined field: unknown property or method '{field}' on Option"),
                                            ctx,
                                        ))
                                    }
                                }
                            }
                        }
                    } else if enum_name == "Result" {
                        match field.as_str() {
                            "is_ok" => Ok(Value::Bool(variant == "Ok")),
                            "is_err" => Ok(Value::Bool(variant == "Err")),
                            _ => {
                                // Try calling as a no-arg method
                                let empty_args: Vec<Argument> = vec![];
                                match evaluate_method_call(
                                    receiver,
                                    field,
                                    &empty_args,
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                ) {
                                    Ok(result) => Ok(result),
                                    Err(_) => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::UNDEFINED_FIELD)
                                            .with_help("available properties: is_ok, is_err; or use method() syntax");
                                        Err(CompileError::semantic_with_context(
                                            format!("undefined field: unknown property or method '{field}' on Result"),
                                            ctx,
                                        ))
                                    }
                                }
                            }
                        }
                    } else {
                        // Try calling as a no-arg method for other enums
                        let empty_args: Vec<Argument> = vec![];
                        match evaluate_method_call(
                            receiver,
                            field,
                            &empty_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok(result) => Ok(result),
                            Err(_) => {
                                let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FIELD).with_help(format!(
                                    "check that the property or method '{field}' exists on enum {enum_name}"
                                ));
                                Err(CompileError::semantic_with_context(
                                    format!(
                                        "undefined field: unknown property or method '{field}' on enum {enum_name}"
                                    ),
                                    ctx,
                                ))
                            }
                        }
                    }
                }
                _ => {
                    // Debug: show what value type we're trying to access
                    eprintln!(
                        "[DEBUG FIELD ACCESS] Trying to access field '{}' on value type: {:?}",
                        field,
                        recv_val.type_name()
                    );
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_FIELD)
                        .with_help("field access requires an object, array, dict, or enum value");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "undefined field '{}': cannot access field on value of type '{}'",
                            field,
                            recv_val.type_name()
                        ),
                        ctx,
                    ))
                }
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
