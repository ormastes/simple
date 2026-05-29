//! Method execution helpers

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{
    bind_args, exec_block_fn, Control, Enums, ImplMethods, CONST_NAMES, IMMUTABLE_VARS, IN_IMMUTABLE_FN_METHOD,
};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

thread_local! {
    static METHOD_INDEX_CLASS: RefCell<HashMap<String, HashMap<String, usize>>> =
        RefCell::new(HashMap::new());
    static METHOD_INDEX_IMPL: RefCell<HashMap<String, HashMap<String, usize>>> =
        RefCell::new(HashMap::new());
}

pub fn lookup_class_method_index(class_def: &ClassDef, class_name: &str, method_name: &str) -> Option<usize> {
    METHOD_INDEX_CLASS.with(|cache| {
        // Fast path: probe with &str — avoids String allocation when entry exists (common case)
        {
            let cache_ref = cache.borrow();
            if let Some(class_cache) = cache_ref.get(class_name) {
                return class_cache.get(method_name).copied();
            }
        }
        // Cold path: first lookup for this class — allocate key and populate index
        let mut cache_mut = cache.borrow_mut();
        let class_cache = cache_mut.entry(class_name.to_string()).or_insert_with(|| {
            class_def
                .methods
                .iter()
                .enumerate()
                .map(|(i, m)| (m.name.clone(), i))
                .collect()
        });
        class_cache.get(method_name).copied()
    })
}

pub fn lookup_impl_method_index(methods: &[Arc<FunctionDef>], class_name: &str, method_name: &str) -> Option<usize> {
    METHOD_INDEX_IMPL.with(|cache| {
        // Fast path: probe with &str — avoids String allocation when entry exists (common case)
        {
            let cache_ref = cache.borrow();
            if let Some(class_cache) = cache_ref.get(class_name) {
                return class_cache.get(method_name).copied();
            }
        }
        // Cold path: first lookup for this class — allocate key and populate index
        let mut cache_mut = cache.borrow_mut();
        let class_cache = cache_mut
            .entry(class_name.to_string())
            .or_insert_with(|| methods.iter().enumerate().map(|(i, m)| (m.name.clone(), i)).collect());
        class_cache.get(method_name).copied()
    })
}

/// Extract result from exec_block_fn return value
macro_rules! extract_block_result {
    ($block_exec:expr) => {
        match $block_exec {
            Ok((Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(CompileError::TryError(val)) => *val,
            Err(e) => return Err(e),
        }
    };
}

#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn find_and_exec_method_with_self(
    method: &str,
    args: &[Argument],
    class: &str,
    fields: &Arc<HashMap<String, Value>>,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    // Check class methods (cached O(1) lookup)
    if let Some(class_def) = classes.get(class).cloned() {
        if let Some(idx) = lookup_class_method_index(&class_def, class, method) {
            let func = &class_def.methods[idx];
            let (result, updated_self) = exec_function_with_self_return(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                class,
                Arc::clone(fields),
            )?;
            return Ok(Some((result, updated_self)));
        }
    }
    // Check impl methods (cached O(1) lookup)
    if let Some(methods) = impl_methods.get(class) {
        if let Some(idx) = lookup_impl_method_index(methods, class, method) {
            let func = &methods[idx];
            let (result, updated_self) = exec_function_with_self_return(
                func,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
                class,
                Arc::clone(fields),
            )?;
            return Ok(Some((result, updated_self)));
        }
    }
    Ok(None)
}

/// Like find_and_exec_method_with_self but takes owned Arc for zero-copy field mutations.
/// When the caller can pass an Arc with refcount 1, ALL self.field mutations
/// inside the method body become zero-copy (no HashMap deep-clone).
#[allow(clippy::too_many_arguments)]
pub fn find_and_exec_method_with_self_owned(
    method: &str,
    args: &[Argument],
    class: &str,
    fields: Arc<HashMap<String, Value>>,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    if let Some(class_def) = classes.get(class).cloned() {
        if let Some(idx) = lookup_class_method_index(&class_def, class, method) {
            let func = &class_def.methods[idx];
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
    if let Some(methods) = impl_methods.get(class) {
        if let Some(idx) = lookup_impl_method_index(methods, class, method) {
            let func = &methods[idx];
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
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn exec_function_with_self_return(
    func: &FunctionDef,
    args: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: Arc<HashMap<String, Value>>,
) -> Result<(Value, Value), CompileError> {
    let mut local_env = Env::new();

    // Move fields directly — callers that own the Arc pass refcount 1 (zero-copy mutations)
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields,
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

    // Save current CONST_NAMES and IMMUTABLE_VARS, clear for function scope
    let saved_const_names = CONST_NAMES.with(|cell| std::mem::take(&mut *cell.borrow_mut()));
    let saved_immutable_vars = IMMUTABLE_VARS.with(|cell| std::mem::take(&mut *cell.borrow_mut()));

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
    IMMUTABLE_VARS.with(|cell| *cell.borrow_mut() = saved_immutable_vars);

    // Now extract result, potentially returning error
    let result = match exec_result {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v,
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => *val,
        Err(e) => return Err(e),
    };

    // Write back mutated container arguments passed by identifier.
    // This mirrors normal function-call behavior for arrays, dicts, tuples,
    // and objects that are mutated inside methods.
    let non_self_params: Vec<_> = func.params.iter().filter(|p| p.name != "self").collect();
    for (param, arg) in non_self_params.into_iter().zip(args.iter()) {
        if let simple_parser::ast::Expr::Identifier(var_name) = &arg.value {
            if let Some(updated_arg) = local_env.get(&param.name).cloned() {
                if matches!(
                    updated_arg,
                    Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                ) {
                    outer_env.insert(var_name.clone(), updated_arg);
                }
            }
        }
    }

    // Extract the potentially modified self (remove avoids an extra Arc clone)
    let updated_self = local_env.remove("self").unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: Arc::new(HashMap::new()),
    });

    // DEBUG: Check if updated_self is correct type (debug builds only — avoids
    // format!+eprintln overhead on every method return in release builds)
    #[cfg(debug_assertions)]
    {
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
    }

    Ok((result, updated_self))
}
