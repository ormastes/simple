//! Method execution helpers

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use crate::error::CompileError;
use crate::interpreter::{
    bind_args, captured_env_with_live_globals, execute_function_body, publish_and_repoint, sync_owned_captured_globals,
    Enums, ImplMethods,
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
    crate::perf_counters::bump(&crate::perf_counters::MECALL_METHOD_LOOKUPS, 1);
    METHOD_INDEX_CLASS.with(|cache| {
        // Fast path: probe with &str — avoids String allocation when entry exists (common case)
        {
            let cache_ref = cache.borrow();
            if let Some(class_cache) = cache_ref.get(class_name) {
                if let Some(idx) = class_cache.get(method_name).copied() {
                    if class_def
                        .methods
                        .get(idx)
                        .is_some_and(|method| method.name == method_name)
                    {
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
    crate::perf_counters::bump(&crate::perf_counters::MECALL_METHOD_LOOKUPS, 1);
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

/// The class-body or impl-block method `class` dispatches `method` to, resolved
/// ONCE.
///
/// The owned-receiver fast paths have to know, BEFORE the receiver can be taken
/// out of its slot, that the call will dispatch here and not to a lambda field,
/// `method_missing`, or UFCS. They used to answer that with a bool
/// (`object_method_exists`) and then resolve the very same name AGAIN inside the
/// executor — two probes of the thread-local method-index cache per call, each
/// one a `HashMap<String, _>` lookup plus a `RefCell` borrow plus a second
/// `HashMap<String, usize>` lookup inside it, on the single most frequent
/// interpreted shape in `src/lib/common` (21,601 call sites). Returning the
/// resolution collapses both probes into one.
///
/// The result borrows nothing: `Class` holds an `Arc<ClassDef>` (the same clone
/// the executor already made) and `Impl` an `Arc<FunctionDef>`, so the caller
/// can drop every borrow of `env`, `classes` and `impl_methods` — which is what
/// lets the receiver be MOVED out of its slot afterwards — and the class name no
/// longer has to be copied into an owned `String` to survive that move.
pub enum ResolvedMethod {
    Class(Arc<ClassDef>, usize),
    Impl(Arc<FunctionDef>),
}

impl ResolvedMethod {
    pub fn def(&self) -> &FunctionDef {
        match self {
            // The index was validated against `methods[idx].name` by
            // `lookup_class_method_index` while the Arc was cloned, and an
            // `Arc<ClassDef>` is immutable, so it cannot have gone stale here.
            ResolvedMethod::Class(class_def, idx) => &class_def.methods[*idx],
            ResolvedMethod::Impl(func) => func.as_ref(),
        }
    }
}

pub fn resolve_object_method(
    classes: &HashMap<String, Arc<ClassDef>>,
    impl_methods: &ImplMethods,
    class: &str,
    method: &str,
) -> Option<ResolvedMethod> {
    if let Some(class_def) = classes.get(class) {
        if let Some(idx) = lookup_class_method_index(class_def, class, method) {
            return Some(ResolvedMethod::Class(Arc::clone(class_def), idx));
        }
    }
    if let Some(methods) = impl_methods.get(class) {
        if let Some(idx) = lookup_impl_method_index(methods, class, method) {
            return Some(ResolvedMethod::Impl(Arc::clone(&methods[idx])));
        }
    }
    None
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
    crate::perf_counters::bump(&crate::perf_counters::MECALL_CALLS, 1);
    // Two owned `String`s: the frame's `"self"` key and the self object's class
    // name. Both are irreducible while `Env` is keyed by `String` and
    // `Value::Object` owns its class name; the third is the receiver's own name
    // at the call site, counted there.
    crate::perf_counters::bump(&crate::perf_counters::MECALL_STRING_ALLOCS, 2);
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
    let bound = crate::interpreter::interpreter_call::bind_args_with_values_named(
        &func.params,
        arg_vals,
        arg_exprs,
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

    // Container write-back. Only an argument spelled as a bare identifier can be
    // written back at all, so a call with none — the common case — needs no
    // parameter list built for it. The list itself is an iterator now rather
    // than a `Vec`: `zip` consumes the parameters positionally exactly as the
    // collected vector did, and the labelled case still re-resolves the
    // parameter by name below (a labelled argument does not sit at its
    // positional slot, so zipping alone would write the container back into the
    // wrong variable).
    if arg_exprs
        .iter()
        .any(|arg| matches!(&arg.value, simple_parser::ast::Expr::Identifier(_)))
    {
        let non_self_params = func.params.iter().filter(|p| p.name != "self");
        for (param, arg) in non_self_params.zip(arg_exprs.iter()) {
            let param = match &arg.name {
                Some(name) => match func.params.iter().find(|p| &p.name == name) {
                    Some(p) => p,
                    None => continue,
                },
                None => param,
            };
            if let simple_parser::ast::Expr::Identifier(var_name) = &arg.value {
                // Decide on a BORROW, then clone only the value that is
                // actually written back: the pre-change shape cloned every
                // identifier argument's value just to ask what kind it was, and
                // threw the clone away for every scalar.
                let is_container = matches!(
                    local_env.get(&param.name),
                    Some(Value::Array(_) | Value::Dict(_) | Value::Object { .. } | Value::Tuple(_))
                );
                if is_container {
                    if let Some(updated_arg) = local_env.get(&param.name).cloned() {
                        crate::perf_counters::bump(&crate::perf_counters::MECALL_STRING_ALLOCS, 1);
                        outer_env.insert(var_name.clone(), updated_arg);
                    }
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

/// Owned-receiver dispatch with pre-evaluated args against an ALREADY resolved
/// method; see `resolve_object_method` and `exec_function_with_self_return_values`.
///
/// This replaces `find_and_exec_method_with_self_owned_values`, which re-resolved
/// the method name it had just been told exists and therefore returned an
/// `Option` its callers all had to treat as `unreachable!()`. Taking the
/// resolution as an argument removes both the second probe and the impossible
/// arm.
#[allow(clippy::too_many_arguments)]
pub fn exec_resolved_method_with_self_owned_values(
    resolved: &ResolvedMethod,
    arg_vals: &[Value],
    arg_exprs: &[Argument],
    class: &str,
    fields: Arc<HashMap<String, Value>>,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Value), CompileError> {
    exec_function_with_self_return_values(
        resolved.def(),
        arg_vals,
        arg_exprs,
        env,
        functions,
        classes,
        enums,
        impl_methods,
        class,
        fields,
    )
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
        vals.push(crate::interpreter::evaluate_expr(
            &arg.value,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?);
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
        let module =
            Parser::new("class MethodIndexClassFixture:\n    fn alpha():\n        1\n\n    fn beta():\n        2\n")
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
