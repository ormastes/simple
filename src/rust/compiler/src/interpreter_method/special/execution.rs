//! Method execution helpers

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{bind_args, exec_block_fn, Control, Enums, ImplMethods, CONST_NAMES, IN_IMMUTABLE_FN_METHOD};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;
use std::sync::Arc;

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
    fields: &Arc<HashMap<String, Value>>,
    env: &mut Env,
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
    outer_env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: &Arc<HashMap<String, Value>>,
) -> Result<(Value, Value), CompileError> {
    let mut local_env = Env::new();

    // Set up self — Arc::clone is O(1), no deep copy
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields: Arc::clone(fields),
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

    // Save current CONST_NAMES and clear for function scope
    let saved_const_names = CONST_NAMES.with(|cell| cell.borrow().clone());
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());

    // Save and set IN_IMMUTABLE_FN_METHOD flag
    // Methods always have self here, so check if this is a me method
    let saved_in_immutable_fn = IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow());
    let is_immutable_fn_method = !func.is_me_method;

    IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow_mut() = is_immutable_fn_method);

    // Execute the function body - handle result manually to ensure flag restoration
    let exec_result = exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods);

    // ALWAYS restore flags before handling the result to avoid flag leaking on error
    IN_IMMUTABLE_FN_METHOD.with(|cell| *cell.borrow_mut() = saved_in_immutable_fn);
    CONST_NAMES.with(|cell| *cell.borrow_mut() = saved_const_names);

    // Now extract result, potentially returning error
    let result = match exec_result {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    // Get the potentially modified self
    let updated_self = local_env.get("self").cloned().unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: Arc::clone(fields),
    });

    // DEBUG: Check if updated_self is correct type
    if let Value::Object { class: self_class, .. } = &updated_self {
        if self_class != class_name {
            eprintln!(
                "[DEBUG EXEC_FN_SELF] WARNING: self class changed from '{}' to '{}'",
                class_name, self_class
            );
        }
    } else {
        eprintln!(
            "[DEBUG EXEC_FN_SELF] WARNING: self is not an Object! type={}, class_name was '{}'",
            updated_self.type_name(),
            class_name
        );
    }

    Ok((result, updated_self))
}
