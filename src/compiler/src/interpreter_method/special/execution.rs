//! Method execution helpers

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{bind_args, exec_block_fn, Control, Enums, ImplMethods};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;

/// Extract result from exec_block_fn return value
macro_rules! extract_block_result {
    ($block_exec:expr) => {
        match $block_exec {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(CompileError::TryError(val)) => val,
            Err(e) => return Err(e),
        }
    };
}

pub fn find_and_exec_method_with_self(
    method: &str,
    args: &[Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class).cloned() {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                class,
                fields,
            )?;
            return Ok(Some((result, updated_self)));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                class,
                fields,
            )?;
            return Ok(Some((result, updated_self)));
        }
    }
    Ok(None)
}

/// Execute a function and return both result and modified self
pub fn exec_function_with_self_return(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: &HashMap<String, Value>,
) -> Result<(Value, Value), CompileError> {
    let mut local_env = Env::new();

    // Set up self
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
        },
    );

    // Bind arguments (skip self parameter)
    let self_mode = simple_parser::ast::SelfMode::SkipSelf;
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

    // Execute the function body with implicit return support
    let result = extract_block_result!(exec_block_fn(
        &func.body,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods
    ));

    // Get the potentially modified self
    let updated_self = local_env.get("self").cloned().unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: fields.clone(),
    });

    Ok((result, updated_self))
}
