use std::collections::HashMap;

use simple_parser::ast::Expr;

use super::evaluate_expr;
use crate::error::CompileError;
use crate::value::Value;

use super::super::{
    evaluate_call, evaluate_method_call, evaluate_method_call_with_self_update, exec_method_function, ClassDef, Enums, Env, FunctionDef, ImplMethods,
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
            // For objects, use evaluate_method_call_with_self_update to handle `me` methods
            // that mutate self and need to persist the changes
            if let Expr::Identifier(obj_name) = receiver.as_ref() {
                if let Some(Value::Object { .. }) = env.get(obj_name) {
                    let (result, updated_self) = evaluate_method_call_with_self_update(
                        receiver,
                        method,
                        args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    // Update the variable with the potentially modified self
                    if let Some(new_self) = updated_self {
                        env.insert(obj_name.clone(), new_self);
                    }
                    return Ok(Some(result));
                }
            }
            // For non-objects or complex receivers, use regular method call
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
                    Err(CompileError::Semantic(format!("unknown field {field}")))
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
                            Err(CompileError::Semantic(format!(
                                "unknown method {field} on class {class_name}"
                            )))
                        }
                    } else {
                        Err(CompileError::Semantic(format!("unknown class {class_name}")))
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
                                Err(CompileError::Semantic(format!(
                                    "unknown variant or method '{field}' on enum {enum_name}"
                                )))
                            }
                        }
                    } else {
                        Err(CompileError::Semantic(format!("unknown enum {enum_name}")))
                    }
                }
                // String property access (e.g., str.len, str.is_empty)
                Value::Str(ref s) => match field.as_str() {
                    "len" => Ok(Value::Int(s.len() as i64)),
                    "byte_len" => Ok(Value::Int(s.len() as i64)),
                    "char_count" => Ok(Value::Int(s.chars().count() as i64)),
                    "is_empty" => Ok(Value::Bool(s.is_empty())),
                    _ => Err(CompileError::Semantic(format!("unknown property '{field}' on String"))),
                },
                // Array property access (e.g., arr.len, arr.is_empty)
                Value::Array(ref arr) => match field.as_str() {
                    "len" => Ok(Value::Int(arr.len() as i64)),
                    "is_empty" => Ok(Value::Bool(arr.is_empty())),
                    _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Array"))),
                },
                // Tuple property access (e.g., tup.len)
                Value::Tuple(ref tup) => match field.as_str() {
                    "len" => Ok(Value::Int(tup.len() as i64)),
                    _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Tuple"))),
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
                            Err(CompileError::Semantic(format!(
                                "unknown property or key '{field}' on Dict"
                            )))
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
                            _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Option"))),
                        }
                    } else if enum_name == "Result" {
                        match field.as_str() {
                            "is_ok" => Ok(Value::Bool(variant == "Ok")),
                            "is_err" => Ok(Value::Bool(variant == "Err")),
                            _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Result"))),
                        }
                    } else {
                        Err(CompileError::Semantic(format!(
                            "unknown property '{field}' on enum {enum_name}"
                        )))
                    }
                }
                _ => Err(CompileError::Semantic("field access on non-object".into())),
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
