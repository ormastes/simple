//! Function execution (lambdas, functions, class instantiation)

use std::collections::HashMap;
use simple_parser::ast::{Argument, Expr, Type};
use crate::value::Value;
use crate::{ClassDef, CompileError, Enums, FunctionDef, ImplMethods};
use crate::interpreter::env::Env;
use crate::interpreter::expressions::evaluate_expr;
use crate::interpreter::control::Control;
use crate::interpreter::exec_block_closure;
use crate::interpreter::exec_block;
use crate::interpreter::exec_block_fn;
use crate::interpreter::effects::with_effect_context;
use crate::interpreter::METHOD_SELF;
use crate::interpreter::METHOD_NEW;
use crate::interpreter::unit_types::{is_unit_type, validate_unit_type};
use crate::{bail_semantic, semantic_err};

use super::binding::*;
use super::injection::*;

pub(super) fn exec_lambda(
    params: &[String],
    body: &Expr,
    args: &[Argument],
    call_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                bail_semantic!("too many arguments to lambda");
            }
            local_env.insert(params[positional_idx].clone(), val);
            positional_idx += 1;
        }
    }

    for param in params {
        if !local_env.contains_key(param) {
            local_env.insert(param.clone(), Value::Nil);
        }
    }

    // If body is a DoBlock, execute its statements directly instead of
    // returning a BlockClosure value
    if let Expr::DoBlock(nodes) = body {
        return exec_block_closure(nodes, &local_env, functions, classes, enums, impl_methods);
    }

    evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
}

/// Helper to get iterator values from various iterable types
include!("interpreter_call_block_execution.rs");

pub(crate) fn exec_function(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    with_effect_context(&func.effects, || {
        exec_function_inner(func, args, outer_env, functions, classes, enums, impl_methods, self_ctx)
    })
}

pub(super) fn exec_function_with_values(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_context(&func.effects, || {
        exec_function_with_values_inner(func, args, outer_env, functions, classes, enums, impl_methods)
    })
}

/// Execute a function with a captured environment for closure semantics
pub(super) fn exec_function_with_captured_env(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    with_effect_context(&func.effects, || {
        // Start with the captured environment (for closure variables)
        let mut local_env = captured_env.clone();

        // Bind arguments
        let self_mode = simple_parser::ast::SelfMode::IncludeSelf;
        let bound_args = bind_args(&func.params, args, outer_env, functions, classes, enums, impl_methods, self_mode)?;
        for (name, value) in bound_args {
            local_env.insert(name, value);
        }

        // Execute the function body with implicit return support
        let result_value = exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods);
        let result = match result_value {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v, // Implicit return from last expression
            Ok((_, None)) => Value::Nil,
            Err(e) => return Err(e),
        };

        // Validate return type against unit type annotation if present
        if let Some(Type::Simple(type_name)) = &func.return_type {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type(&result, type_name) {
                    bail_semantic!("return type mismatch in '{}': {}", func.name, e);
                }
            }
        }

        Ok(result)
    })
}

fn exec_function_inner(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    // Record function call for coverage tracking
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

    let mut local_env = Env::new();

    // TODO(contracts): Add interpreter contract support
    // For now, contracts are only checked in compiled code.
    // Future work:
    // 1. Evaluate preconditions before function execution
    // 2. Capture old() values at entry
    // 3. Evaluate entry invariants
    // 4. Execute function body
    // 5. Evaluate exit invariants and postconditions
    // See interpreter_contract.rs module for helper functions
    if let Some((class_name, fields)) = self_ctx {
        local_env.insert(
            "self".into(),
            Value::Object {
                class: class_name.to_string(),
                fields: fields.clone(),
            },
        );
    }
    let self_mode = if self_ctx.is_some() {
        simple_parser::ast::SelfMode::SkipSelf
    } else {
        simple_parser::ast::SelfMode::IncludeSelf
    };
    let bound = bind_args(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v, // Implicit return from last expression
        Ok((_, None)) => Value::Nil,
        // TryError from ? operator - propagate as return value
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    // Validate return type against unit type annotation if present
    if let Some(Type::Simple(type_name)) = &func.return_type {
        if is_unit_type(type_name) {
            if let Err(e) = validate_unit_type(&result, type_name) {
                bail_semantic!("return type mismatch in '{}': {}", func.name, e);
            }
        }
    }

    Ok(result)
}

fn exec_function_with_values_inner(
    func: &FunctionDef,
    args: &[Value],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Record function call for coverage tracking
    if let Some(cov) = crate::coverage::get_global_coverage() {
        cov.lock().unwrap().record_function_call(&func.name);
    }

    let mut local_env = Env::new();
    let self_mode = simple_parser::ast::SelfMode::IncludeSelf;
    let bound = bind_args_with_values(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    let result = match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    if let Some(Type::Simple(type_name)) = &func.return_type {
        if is_unit_type(type_name) {
            if let Err(e) = validate_unit_type(&result, type_name) {
                bail_semantic!("return type mismatch in '{}': {}", func.name, e);
            }
        }
    }

    Ok(result)
}

/// Instantiate a class by calling its constructor (the 'new' method if present)
/// or by creating an object with default field values.
pub(crate) fn instantiate_class(
    class_name: &str,
    args: &[Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let class_def = classes.get(class_name).ok_or_else(|| {
        semantic_err!("unknown class: {}", class_name)
    })?;

    // Initialize fields with defaults
    let mut fields: HashMap<String, Value> = HashMap::new();
    for field in &class_def.fields {
        let val = if let Some(default_expr) = &field.default {
            evaluate_expr(default_expr, env, functions, classes, enums, impl_methods)?
        } else {
            Value::Nil
        };
        fields.insert(field.name.clone(), val);
    }

    // Look for 'new' constructor method
    if let Some(new_method) = class_def.methods.iter().find(|m| m.name == METHOD_NEW) {
        // Call the constructor with self
        let self_val = Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        };

        let mut local_env = env.clone();
        local_env.insert(METHOD_SELF.to_string(), self_val);

        // Add fields to environment so constructor can access them
        for (k, v) in &fields {
            local_env.insert(k.clone(), v.clone());
        }

        let self_mode = simple_parser::ast::SelfMode::SkipSelf;
        let injected = if has_inject_attr(new_method) {
            resolve_injected_args(
                &new_method.params,
                args,
                class_name,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                self_mode,
            )?
        } else {
            HashMap::new()
        };
        let bound = bind_args_with_injected(
            &new_method.params,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            self_mode,
            &injected,
        )?;
        for (name, val) in bound {
            local_env.insert(name, val);
        }

        match exec_block(&new_method.body, &mut local_env, functions, classes, enums, impl_methods) {
            Ok(Control::Return(v)) => Ok(v),
            Ok(_) => {
                // Return the self object (possibly modified by constructor)
                Ok(local_env.get("self").cloned().unwrap_or(Value::Object {
                    class: class_name.to_string(),
                    fields,
                }))
            }
            Err(CompileError::TryError(val)) => Ok(val),
            Err(e) => Err(e),
        }
    } else {
        // No constructor - just return object with field values from args
        // Match arguments to fields positionally or by name
        let mut positional_idx = 0;
        for arg in args {
            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
            if let Some(name) = &arg.name {
                if !fields.contains_key(name) {
                    bail_semantic!("unknown field {} for class {}", name, class_name);
                }
                fields.insert(name.clone(), val);
            } else {
                // Positional argument - match to field in declaration order
                if positional_idx < class_def.fields.len() {
                    let field_name = &class_def.fields[positional_idx].name;
                    fields.insert(field_name.clone(), val);
                    positional_idx += 1;
                } else {
                    bail_semantic!("too many arguments for class {}", class_name);
                }
            }
        }

        Ok(Value::Object {
            class: class_name.to_string(),
            fields,
        })
    }
}
