//! Method execution helpers

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{
    bind_args, captured_env_with_live_globals, execute_function_body, publish_and_repoint,
    sync_owned_captured_globals, Enums, ImplMethods,
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
                if let Some(idx) = class_cache.get(method_name).copied() {
                    if class_def.methods.get(idx).is_some_and(|method| method.name == method_name) {
                        return Some(idx);
                    }
                }
            }
        }
        // Cold or stale path: rebuild from the current class definition.
        let mut cache_mut = cache.borrow_mut();
        let class_cache: HashMap<_, _> = class_def
            .methods
            .iter()
            .enumerate()
            .map(|(i, method)| (method.name.clone(), i))
            .collect();
        let result = class_cache.get(method_name).copied();
        cache_mut.insert(class_name.to_string(), class_cache);
        result
    })
}

pub fn lookup_impl_method_index(methods: &[Arc<FunctionDef>], class_name: &str, method_name: &str) -> Option<usize> {
    METHOD_INDEX_IMPL.with(|cache| {
        // Fast path: probe with &str — avoids String allocation when entry exists (common case)
        {
            let cache_ref = cache.borrow();
            if let Some(class_cache) = cache_ref.get(class_name) {
                if let Some(idx) = class_cache.get(method_name).copied() {
                    if methods.get(idx).is_some_and(|method| method.name == method_name) {
                        return Some(idx);
                    }
                }
            }
        }
        // Cold or stale path: rebuild from the current impl registry.
        let mut cache_mut = cache.borrow_mut();
        let class_cache: HashMap<_, _> = methods.iter().enumerate().map(|(i, m)| (m.name.clone(), i)).collect();
        let result = class_cache.get(method_name).copied();
        cache_mut.insert(class_name.to_string(), class_cache);
        result
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
/// Mirror a method-argument write-back into `MODULE_GLOBALS`.
///
/// Identifier evaluation prefers `MODULE_GLOBALS` for non-local names
/// (`interpreter/expr/literals.rs`), so writing only `outer_env` left a
/// module-level `let out = []` still empty after `obj.m(out)` pushed into it.
fn sync_module_global_writeback(name: &str, value: &Value) {
    crate::interpreter::MODULE_GLOBALS.with(|cell| {
        // Peek before taking the write borrow: borrow_mut() on this
        // generation-tracked cell invalidates owned-env templates.
        if !cell.borrow().contains_key(name) {
            return;
        }
        cell.borrow_mut().insert(name.to_string(), value.clone());
    });
}

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
    publish_and_repoint(outer_env);
    let mut local_env = captured_env_with_live_globals(func, &Env::new());

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
    outer_env.release_scope();
    let result = execute_function_body(
        func,
        bound,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
        true,
    );
    local_env.release_scope();
    sync_owned_captured_globals(func, &local_env, outer_env);
    let result = result?;

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
                    sync_module_global_writeback(var_name, &updated_arg);
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

/// True when `class` has a class-body or impl-block method named `method`.
/// Used by the owned-receiver fast paths to decide BEFORE taking a receiver
/// out of its slot that the call will dispatch here (and not to a lambda
/// field, `method_missing`, or UFCS).
pub fn object_method_exists(
    classes: &HashMap<String, Arc<ClassDef>>,
    impl_methods: &ImplMethods,
    class: &str,
    method: &str,
) -> bool {
    classes
        .get(class)
        .map(|cd| lookup_class_method_index(cd, class, method).is_some())
        .unwrap_or(false)
        || impl_methods
            .get(class)
            .map(|ms| lookup_impl_method_index(ms, class, method).is_some())
            .unwrap_or(false)
}

/// MECALL-OWNED (2026-08-22): zero-copy `me` call with PRE-EVALUATED args.
///
/// `find_and_exec_method_with_self_owned` promised "refcount 1 => zero-copy",
/// but every caller had to leave a clone of the receiver in `env` so that arg
/// expressions such as `me.field` could still resolve while `bind_args` ran
/// inside the callee -- and that clone put the refcount back to 2, so the first
/// `self.dict[k] = v` in EVERY `me` method body deep-copied the dict. Measured
/// on the deployed seed: a 3000-entry `Dict` field costs 0.18 ms per `me` call
/// that writes it (linear in the dict), while the same write inside one call is
/// free. `SymbolTable.define` writes three such dicts per call, which is the
/// 2.4 ms -> 8 ms per-define growth behind 136 ms enum lowerings on the real
/// closure (doc/08_tracking/bug/interpreter_me_call_dict_clone_2026-08-22.md).
///
/// Here the args arrive already evaluated (the caller evaluates them while the
/// receiver is still in place), so the receiver's field Arc can be MOVED in
/// with no other owner. Identifier-passed container args are still written
/// back exactly as `exec_function_with_self_return` does.
#[allow(clippy::too_many_arguments)]
pub fn exec_function_with_self_return_values(
    func: &FunctionDef,
    arg_vals: &[Value],
    arg_exprs: &[Argument],
    outer_env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: Arc<HashMap<String, Value>>,
) -> Result<(Value, Value), CompileError> {
    publish_and_repoint(outer_env);
    let mut local_env = captured_env_with_live_globals(func, &Env::new());
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields,
        },
    );
    let self_mode = simple_parser::ast::SelfMode::SkipSelf;
    // Named arguments must be permuted into parameter order BEFORE binding:
    // bind_args_with_values takes bare values and binds positionally, so
    // without this `m.subtract(subtrahend=15, minuend=50)` computed 15 - 50.
    let reordered = crate::interpreter::interpreter_call::reorder_named_arg_values(
        &func.params,
        arg_vals,
        arg_exprs,
        self_mode,
    );
    let arg_vals: &[Value] = reordered.as_deref().unwrap_or(arg_vals);
    let bound = crate::interpreter::interpreter_call::bind_args_with_values(
        &func.params,
        arg_vals,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_mode,
    )?;
    outer_env.release_scope();
    let result = execute_function_body(
        func,
        bound,
        &mut local_env,
        functions,
        classes,
        enums,
        impl_methods,
        true,
    );
    local_env.release_scope();
    sync_owned_captured_globals(func, &local_env, outer_env);
    let result = result?;

    let non_self_params: Vec<_> = func.params.iter().filter(|p| p.name != "self").collect();
    for (param, arg) in non_self_params.into_iter().zip(arg_exprs.iter()) {
        if let simple_parser::ast::Expr::Identifier(var_name) = &arg.value {
            if let Some(updated_arg) = local_env.get(&param.name).cloned() {
                if matches!(
                    updated_arg,
                    Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_)
                ) {
                    sync_module_global_writeback(var_name, &updated_arg);
                    outer_env.insert(var_name.clone(), updated_arg);
                }
            }
        }
    }

    let updated_self = local_env.remove("self").unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: Arc::new(HashMap::new()),
    });
    Ok((result, updated_self))
}

/// Owned-receiver dispatch with pre-evaluated args; see
/// `exec_function_with_self_return_values`. Returns `Ok(None)` when the class
/// has no such method, in which case the caller still owns nothing (it must
/// check `object_method_exists` BEFORE moving the receiver out of its slot).
#[allow(clippy::too_many_arguments)]
pub fn find_and_exec_method_with_self_owned_values(
    method: &str,
    arg_vals: &[Value],
    arg_exprs: &[Argument],
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
            return exec_function_with_self_return_values(
                func, arg_vals, arg_exprs, env, functions, classes, enums, impl_methods, class, fields,
            )
            .map(Some);
        }
    }
    if let Some(methods) = impl_methods.get(class) {
        if let Some(idx) = lookup_impl_method_index(methods, class, method) {
            let func = &methods[idx];
            return exec_function_with_self_return_values(
                func, arg_vals, arg_exprs, env, functions, classes, enums, impl_methods, class, fields,
            )
            .map(Some);
        }
    }
    Ok(None)
}

/// Evaluate a call's arguments in `env` (receiver still in place).
pub fn evaluate_call_args(
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Vec<Value>, CompileError> {
    let mut vals = Vec::with_capacity(args.len());
    for arg in args {
        vals.push(crate::interpreter::evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
    }
    Ok(vals)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::Node;
    use simple_parser::Parser;

    #[test]
    fn impl_method_index_rebuilds_when_registry_order_changes() {
        let module = Parser::new("fn alpha():\n    1\n\nfn beta():\n    2\n")
            .parse()
            .expect("parse method-index fixture");
        let mut methods: Vec<_> = module
            .items
            .into_iter()
            .filter_map(|node| match node {
                Node::Function(function) => Some(Arc::new(function)),
                _ => None,
            })
            .collect();

        assert_eq!(
            lookup_impl_method_index(&methods, "MethodIndexFixture", "alpha"),
            Some(0)
        );
        methods.reverse();
        assert_eq!(
            lookup_impl_method_index(&methods, "MethodIndexFixture", "alpha"),
            Some(1)
        );
    }

    #[test]
    fn class_method_index_rebuilds_when_methods_reorder_or_shrink() {
        let module = Parser::new("class MethodIndexClassFixture:\n    fn alpha():\n        1\n\n    fn beta():\n        2\n")
            .parse()
            .expect("parse method-index fixture");
        let mut class_def = module
            .items
            .into_iter()
            .find_map(|node| match node {
                Node::Class(class_def) => Some(class_def),
                _ => None,
            })
            .expect("class method-index fixture");

        assert_eq!(
            lookup_class_method_index(&class_def, "MethodIndexClassFixture", "alpha"),
            Some(0)
        );
        class_def.methods.reverse();
        assert_eq!(
            lookup_class_method_index(&class_def, "MethodIndexClassFixture", "alpha"),
            Some(1)
        );
        class_def.methods.retain(|method| method.name == "alpha");
        assert_eq!(
            lookup_class_method_index(&class_def, "MethodIndexClassFixture", "alpha"),
            Some(0)
        );
    }
}
