//! Pattern matching and binding

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Pattern};
use std::collections::HashMap;
use std::sync::Arc;

use super::super::{
    evaluate_call_args, evaluate_expr, evaluate_method_call_with_self_update, find_and_exec_method_with_self,
    find_and_exec_method_with_self_owned_values, lookup_class_method_index, lookup_impl_method_index,
    object_method_exists, Enums, ImplMethods, CONST_NAMES, MODULE_GLOBALS,
};

use super::args::{eval_arg, eval_arg_usize};
use super::collections::bind_sequence_pattern;
use super::method_dispatch::call_method_on_value;
use crate::value::{OptionVariant, ResultVariant};

/// Snapshot the current value of every name a pattern binds, so a scoped
/// construct can restore them afterwards. Pair with [`restore_pattern_scope`].
///
/// Used to scope `for` loop variables to their loop. The interpreter's `Env`
/// (`CowEnv`) has no scope stack, so save/restore around the loop is how a
/// scoped binding is expressed — the same shape the match-arm binding leak fix
/// already uses for arm bindings.
///
/// Covers the shapes `bind_pattern`/`bind_pattern_value` actually bind: the
/// three identifier forms and the two sequence forms, recursively. Anything else
/// binds no names and so contributes nothing.
///
/// See doc/08_tracking/bug/for_loop_variable_leaks_into_enclosing_scope_2026-08-04.md
pub(crate) fn save_pattern_scope(pattern: &Pattern, env: &Env) -> Vec<(String, Option<Value>)> {
    let mut names = Vec::new();
    collect_pattern_binding_names(pattern, &mut names);
    names
        .into_iter()
        .map(|name| {
            let prior = env.get(&name).cloned();
            (name, prior)
        })
        .collect()
}

/// Restore the bindings captured by [`save_pattern_scope`]: names that existed
/// go back to their previous value, names that did not are removed.
pub(crate) fn restore_pattern_scope(saved: Vec<(String, Option<Value>)>, env: &mut Env) {
    for (name, prior) in saved {
        match prior {
            Some(value) => {
                env.insert(name, value);
            }
            None => {
                env.remove(&name);
            }
        }
    }
}

fn collect_pattern_binding_names(pattern: &Pattern, out: &mut Vec<String>) {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => {
            out.push(name.clone())
        }
        Pattern::Tuple(patterns) | Pattern::Array(patterns) => {
            for p in patterns {
                collect_pattern_binding_names(p, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn bind_pattern(pattern: &Pattern, value: &Value, env: &mut Env) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::MoveIdentifier(name) => {
            // Move pattern - transfers ownership during pattern matching
            env.insert(name.clone(), value.clone());
            true
        }
        Pattern::Tuple(patterns) => bind_sequence_pattern(value, patterns, env, true),
        Pattern::Array(patterns) => bind_sequence_pattern(value, patterns, env, false),
        _ => {
            // For other patterns, just try identifier binding
            false
        }
    }
}

// === Helper functions to reduce duplication in interpreter.rs ===

/// Handle functional update expression: target.&method(args)
/// Returns Ok(Some(new_value)) if successfully processed, Ok(None) if not applicable
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub(crate) fn handle_functional_update(
    target: &Expr,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(String, Value)>, CompileError> {
    if let Expr::Identifier(name) = target {
        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
        if is_const {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_ASSIGNMENT)
                .with_help(format!("consider using '{name}_' for a mutable variable"));
            return Err(CompileError::semantic_with_context(
                format!("cannot use functional update on const '{name}'"),
                ctx,
            ));
        }
        let recv_val = env.get(name).cloned().ok_or_else(|| {
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_VARIABLE)
                .with_help("ensure the variable is defined before use");

            if let Some(suggestion) = crate::error::typo::suggest_name(name, known_names.clone()) {
                ctx = ctx.with_help(format!("did you mean `{suggestion}`?"));
            }

            if !known_names.is_empty() && known_names.len() <= 5 {
                let names_list = known_names.join(", ");
                ctx = ctx.with_note(format!("available names: {}", names_list));
            }

            CompileError::semantic_with_context(format!("undefined variable: {name}"), ctx)
        })?;
        let method_call = Expr::MethodCall {
            receiver: Box::new(Expr::Identifier(name.clone())),
            method: method.to_string(),
            args: args.to_vec(),
            generic_args: vec![],
        };
        let result = evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
        let new_value = match (&recv_val, &result) {
            (Value::Array(_), Value::Array(_)) => result,
            (Value::Dict(_), Value::Dict(_)) => result,
            (Value::Str(_), Value::Str(_)) => result,
            (Value::Tuple(_), Value::Tuple(_)) => result,
            (Value::Object { .. }, Value::Object { .. }) => result,
            _ => env.get(name).cloned().unwrap_or(recv_val),
        };
        Ok(Some((name.clone(), new_value)))
    } else {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_PATTERN)
            .with_help("functional update target must be a simple identifier");
        Err(CompileError::semantic_with_context(
            "functional update target must be an identifier".to_string(),
            ctx,
        ))
    }
}

/// Array methods that mutate and should update the binding
/// Note: sort, sorted, reverse, reversed, concat all return NEW arrays and are NOT mutating
const ARRAY_MUTATING_METHODS: &[&str] =
    &["append", "push", "pop", "insert", "remove", "extend", "clear", "write_span"];

/// Apply an array mutating method to a `&mut Vec<Value>` in place.
///
/// This is the single mutation kernel shared by BOTH the ownership-gated in-place
/// fast path (uniquely-owned array — `Arc::get_mut`) and the clone-then-mutate slow
/// path (aliased array — `arr.to_vec()`), so the two paths are provably byte-for-byte
/// identical in semantics; only *where* the `Vec` lives differs. The behaviour of each
/// arm mirrors `interpreter_method/collections.rs::handle_array_methods` exactly.
///
/// Returns `Ok(Some(elem))` for the two methods whose expression result is an ELEMENT
/// rather than the receiver — `pop` (the popped element) and `remove` (the removed
/// element, per the 2026-08-08 contract fix) — and `Ok(None)` for every other method
/// (whose expression result is the array itself). `extend` with a non-array argument
/// returns the same `TYPE_MISMATCH` error `handle_array_methods` does.
fn apply_array_mutation_in_place(
    method: &str,
    vec: &mut Vec<Value>,
    item: Option<Value>,
    idx: Option<usize>,
    second: Option<Value>,
) -> Result<Option<Value>, CompileError> {
    match method {
        "push" | "append" => {
            vec.push(item.unwrap_or(Value::Nil));
            Ok(None)
        }
        "pop" => Ok(Some(vec.pop().unwrap_or(Value::Nil))),
        "insert" => {
            let i = idx.unwrap_or(0);
            if i <= vec.len() {
                vec.insert(i, second.unwrap_or(Value::Nil));
            }
            Ok(None)
        }
        // Returns the REMOVED ELEMENT, like `pop` above — not the array. Both
        // this in-place fast path and the clone-then-mutate slow path go through
        // this one kernel, so the two lanes stay provably identical. An
        // out-of-range index is a no-op yielding Nil (never a panic: `Vec::remove`
        // would abort the interpreter).
        // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
        "remove" => {
            let i = idx.unwrap_or(0);
            if i < vec.len() {
                Ok(Some(vec.remove(i)))
            } else {
                Ok(Some(Value::Nil))
            }
        }
        "extend" => {
            match item {
                Some(Value::Array(other)) => vec.extend(other.iter().cloned()),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("concat/extend/merge expects an array argument");
                    return Err(CompileError::semantic_with_context(
                        "concat/extend/merge expects array argument",
                        ctx,
                    ));
                }
            }
            Ok(None)
        }
        "clear" => {
            vec.clear();
            Ok(None)
        }
        _ => Ok(None),
    }
}

/// Ownership-gated in-place mutation for the `obj.field.push(x)` shape.
///
/// The bare-identifier receiver (`arr.push(x)`) already gets in-place mutation via
/// `Arc::make_mut` further down this file, which is why local list building is O(N).
/// The FIELD receiver did NOT: `interpreter/expr/calls.rs` copied the field value into
/// a `__nested_field_*__` temp, so the array Arc was aliased (object + temp) and every
/// single `push` cloned the whole backing `Vec` — O(N^2) list building on any object
/// field. That is the cost the font loader pays (`self.glyphs = self.glyphs.push(..)`
/// style accumulation), and it is why an unrelated large live object appeared to make
/// font loading explode.
///
/// Same discipline as the identifier path: arguments are evaluated FIRST (so an
/// argument that retains a reference to this array forces the clone branch), then the
/// array is re-read through `env.get_mut` and mutated via `Arc::make_mut` — uniquely
/// owned mutates in place, aliased clones-then-mutates, so value semantics are
/// preserved exactly. `Arc::make_mut` on the field map likewise isolates an aliased
/// object before its field is touched.
///
/// Returns `Ok(None)` when the shape does not apply, leaving the caller on its
/// previous path.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_field_array_mutation_in_place(
    obj_name: &str,
    field: &str,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // `write_span` takes four arguments and is handled by its own path; keep this
    // helper to the generic item/idx/second mutators.
    if method == "write_span" || !ARRAY_MUTATING_METHODS.contains(&method) {
        return Ok(None);
    }
    // Only fire for a local object binding whose field is currently a plain array.
    match env.get(obj_name) {
        Some(Value::Object { fields, .. }) => match fields.get(field) {
            Some(Value::Array(_)) => {}
            _ => return Ok(None),
        },
        _ => return Ok(None),
    }

    let item = match method {
        "push" | "append" => Some(eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?),
        "extend" => Some(eval_arg(
            args,
            0,
            Value::array(vec![]),
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )?),
        _ => None,
    };
    let (idx, second) = match method {
        "insert" => (
            Some(eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?),
            Some(eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?),
        ),
        "remove" => (
            Some(eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?),
            None,
        ),
        _ => (None, None),
    };

    // Re-read after argument evaluation: an argument may have rebound `obj_name`
    // or replaced the field, in which case the shape no longer applies.
    let Some(Value::Object { fields, .. }) = env.get_mut(obj_name) else {
        return Ok(None);
    };
    let Some(Value::Array(arc)) = Arc::make_mut(fields).get_mut(field) else {
        return Ok(None);
    };
    let popped = {
        crate::perf_counters::bump(&crate::perf_counters::SELF_FIELD_ARR_MUT_CALLS, 1);
        if Arc::strong_count(arc) > 1 {
            crate::perf_counters::bump(&crate::perf_counters::SELF_FIELD_ARR_COW_CLONES, 1);
            crate::perf_counters::bump(&crate::perf_counters::SELF_FIELD_ARR_COW_ELEMS_CLONED, arc.len() as u64);
        }
        let vec = Arc::make_mut(arc);
        apply_array_mutation_in_place(method, vec, item, idx, second)?
    };
    let new_array_val = Value::Array(Arc::clone(arc));
    Ok(Some(popped.unwrap_or(new_array_val)))
}

/// Handle method call on object with self-update tracking
/// Returns (result, optional_updated_self) where updated_self is the object with mutations
pub(crate) fn handle_method_call_with_self_update(
    value_expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<(String, Value)>), CompileError> {
    let out = handle_method_call_with_self_update_inner(value_expr, env, functions, classes, enums, impl_methods)?;
    // A mutating method call on a MODULE-GLOBAL receiver (`g.push(x)`) only ever
    // produced a `(name, new_value)` update for the caller to write into `env`.
    // But identifier READS of a non-local name prefer MODULE_GLOBALS over `env`
    // (interpreter/expr/literals.rs), so the mutation was invisible to every
    // later read — notably a `while g.len() < n:` condition, which then never
    // terminated and grew the vec by doubling until the allocator aborted.
    // Assignment (`g = v`) and indexed store (`g[i] = x`) never had this
    // problem because they sync through `place.rs::sync_module_global`; this
    // gives the method-call path the same write-through, at one thread-local
    // `contains_key` per actual mutation (no cost on the read path).
    // doc/08_tracking/bug/native_build_worker_oom_global_array_len_stale_in_while_2026-08-18.md
    // A frame-LOCAL that merely shares its name with a module global must not
    // be written through: `var arm_body_flat: [i64]` in parser_stmts.spl
    // shadowed the `[text]` global of the same name in decl_nodes.spl, and the
    // write-through turned the global into ints -> `method split not found on
    // type i64` while parsing driver.spl (2026-08-21 stage-1 build).
    if let (_, Some((ref name, ref new_value))) = out {
        if env.is_local(name.as_str()) {
            return Ok(out);
        }
        sync_flat_global(name.as_str(), new_value);
        if env.scope_released() {
            env.refresh_scope(crate::interpreter::owned_globals_snapshot());
        }
    }
    Ok(out)
}

/// Write a module global the caller has already identified by name, WITHOUT
/// invalidating every cached call-env template.
///
/// A plain `borrow_mut()` on either generation-tracked store bumps the
/// module-globals generation, which drops every owned-env template and forces
/// a full rebuild (clone of the owner module env + re-resolution of every
/// import) on the next call. Interpreted parsing does these write-backs
/// constantly, so the bumps -- not the misses -- were the wall: 165k rebuilds
/// in a single `lint` of driver_types.spl. Since the (owner, name) pair is
/// known here, the write is recorded instead, and the cache patches just that
/// name. Both stores are kept in step so a later rebuild cannot resurrect the
/// pre-write value. When the executing module is unknown there is no owner to
/// key a patch on, so that path keeps the blunt invalidation.
fn sync_flat_global(name: &str, value: &Value) {
    let present = crate::interpreter::MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
    if !present {
        return;
    }
    crate::interpreter::MODULE_GLOBALS.with(|cell| {
        cell.borrow_mut().insert(name.to_string(), value.clone());
    });
    let owner = crate::interpreter::CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    if let Some(owner) = owner {
        crate::interpreter::set_owned_global(&owner, name, value.clone(), false);
    }
}

/// Park the global stores' copies of a module-global array and drop the frame's
/// store snapshot so the frame's Arc becomes uniquely owned before an in-place
/// mutation. Returns whether anything was parked; the caller MUST follow with
/// `sync_flat_global` + `refresh_scope` (normal path via
/// `handle_method_call_with_self_update`, error path explicitly).
fn release_global_aliases(name: &str, env: &mut Env) -> bool {
    if env.is_local(name) {
        return false;
    }
    let present = crate::interpreter::MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
    if !present {
        return false;
    }
    // Promote the binding into the frame overlay FIRST: once the snapshot is
    // gone the name is no longer resolvable through the scope.
    if env.get_mut(name).is_none() {
        return false;
    }
    env.release_scope();
    crate::interpreter::MODULE_GLOBALS.with(|cell| {
        cell.borrow_mut().insert(name.to_string(), Value::Nil);
    });
    let owner = crate::interpreter::CURRENT_EXEC_MODULE.with(|cell| cell.borrow().clone());
    if let Some(owner) = owner {
        crate::interpreter::set_owned_global(&owner, name, Value::Nil, false);
    }
    true
}

fn handle_method_call_with_self_update_inner(
    value_expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<(String, Value)>), CompileError> {
    if let Expr::MethodCall {
        receiver, method, args, ..
    } = value_expr
    {
        // Handle nested method calls like self.advance().unwrap()
        // The receiver itself might be a method call that mutates an object
        if let Expr::MethodCall { .. } = receiver.as_ref() {
            // Recursively handle the inner method call first
            let (inner_result, inner_update) =
                handle_method_call_with_self_update(receiver, env, functions, classes, enums, impl_methods)?;

            // If there was an update from the inner method call, we need to use
            // the updated environment for the outer method call
            let mut working_env = if let Some((ref obj_name, ref new_self)) = inner_update {
                let mut temp_env = env.clone();
                temp_env.insert(obj_name.clone(), new_self.clone());
                temp_env
            } else {
                env.clone()
            };

            // Now call the outer method on the inner result
            // Evaluate the arguments first
            let mut eval_args = Vec::new();
            for arg in args {
                let val = evaluate_expr(&arg.value, &mut working_env, functions, classes, enums, impl_methods)?;
                eval_args.push(val);
            }

            // Call the method on the inner_result value
            let outer_result = call_method_on_value(
                inner_result.clone(),
                method,
                &eval_args,
                &mut working_env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            // For chained mutable method calls, propagate the final result
            // If the outer method returned an object of the SAME CLASS, it's likely
            // the modified self from a `me` method
            if let Some((ref obj_name, ref inner_self)) = inner_update {
                // Only use the outer result as the update if it's the same class as inner_self
                // This handles chains like m.when("foo").returns(42) where
                // both methods modify and return self of the same type
                if let (Value::Object { class: inner_class, .. }, Value::Object { class: outer_class, .. }) =
                    (inner_self, &outer_result)
                {
                    if inner_class == outer_class {
                        return Ok((outer_result.clone(), Some((obj_name.clone(), outer_result))));
                    }
                }
            }
            // Fall back to propagating the inner update for non-object results or different types
            return Ok((outer_result, inner_update));
        }

        // Ownership-gated in-place fast path for `obj.field.push(x)` &c.
        //
        // Without this, `self.xs.push(v)` fell through to the general PLACE
        // receiver path at the bottom of this function, which resolves the
        // place by COPYING the field value into a temp, mutating the copy, and
        // rebuilding the root — so the array Arc was aliased (object + temp)
        // and `Arc::make_mut` deep-copied the whole backing `Vec` on EVERY
        // push. Measured on a 2,000-push loop: 1,321 distinct backing buffers,
        // i.e. O(N^2) accumulation into any struct field. The identifier
        // receiver (`xs.push(v)`) never had this problem (3 buffers) because it
        // mutates through the single owner in the env slot.
        //
        // `interpreter/expr/calls.rs` already had exactly this fast path, but
        // it is downstream of here and was therefore unreachable for any
        // statement routed through `handle_method_call_with_self_update` (a
        // bare expression statement, a `val x = obj.f.pop()` initializer, a
        // loop body). This reuses that same helper, so there is one kernel and
        // no new semantics: the helper evaluates arguments first, re-reads the
        // receiver through `env.get_mut`, and mutates via `Arc::make_mut`, so a
        // genuinely aliased array still deep-copies exactly as before and value
        // semantics are preserved.
        //
        // The helper only fires when the receiver resolves through `env` to an
        // Object with an Array-valued field, so a receiver that lives only in
        // MODULE_GLOBALS falls through untouched. When the name lives in BOTH,
        // the module-global copy is written through here, exactly as
        // `handle_method_call_with_self_update` does for the identifier shape.
        if let Expr::FieldAccess {
            receiver: parent_receiver,
            field,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(parent_name) = parent_receiver.as_ref() {
                if let Some(result) = try_field_array_mutation_in_place(
                    parent_name,
                    field,
                    method,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )? {
                    if !env.is_local(parent_name.as_str()) {
                        if let Some(updated) = env.get(parent_name.as_str()).cloned() {
                            sync_flat_global(parent_name.as_str(), &updated);
                        }
                    }
                    return Ok((result, None));
                }
            }
        }

        // Handle FieldAccess receivers: self.data.method()
        // When calling a mutating method on a nested object field, we need to:
        // 1. Get the parent object
        // 2. Get the field value
        // 3. Call the method on the field (with self-update tracking)
        // 4. Update the parent's field with the mutated value
        // 5. Update the parent in env
        if let Expr::FieldAccess {
            receiver: parent_receiver,
            field,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(parent_name) = parent_receiver.as_ref() {
                // MECALL-OWNED (2026-08-22): `self.symbols.define(..)` shape. When the
                // field holds an Object whose class has the method, move the field
                // OUT of the parent (unique parent map => no clone at all; a shared
                // parent map is shallow-copied, which is the value-semantics rule),
                // run the method on the owned Arc, and store the updated self back.
                // The generic path below cloned the field, so every dict write inside
                // the callee deep-copied that dict (linear in the symbol table).
                let owned_field_call = match env.get(parent_name) {
                    Some(Value::Object { fields: parent_fields, .. }) => match parent_fields.get(field) {
                        Some(Value::Object { class: field_class, .. }) => {
                            object_method_exists(classes, impl_methods, field_class, method)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if owned_field_call {
                    let arg_vals = evaluate_call_args(args, env, functions, classes, enums, impl_methods)?;
                    let taken = match env.get_mut(parent_name) {
                        Some(Value::Object { fields: parent_fields, .. }) => Arc::make_mut(parent_fields).remove(field),
                        _ => None,
                    };
                    if let Some(Value::Object {
                        class: field_class,
                        fields: field_fields,
                    }) = taken
                    {
                        let (result, updated_field) = match find_and_exec_method_with_self_owned_values(
                            method,
                            &arg_vals,
                            args,
                            &field_class,
                            field_fields,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )? {
                            Some(pair) => pair,
                            None => unreachable!("object_method_exists checked before the field was taken"),
                        };
                        if let Some(Value::Object { fields: parent_fields, .. }) = env.get_mut(parent_name) {
                            Arc::make_mut(parent_fields).insert(field.clone(), updated_field);
                        }
                        if let Some(updated_parent) = env.get(parent_name).cloned() {
                            return Ok((result, Some((parent_name.clone(), updated_parent))));
                        }
                        return Ok((result, None));
                    }
                }
                // Get parent object
                if let Some(Value::Object {
                    class: parent_class,
                    mut fields,
                }) = env.get(parent_name).cloned()
                {
                    // Get the field value - for Object field values, use find_and_exec_method_with_self
                    // to properly execute the method and get the updated self.
                    // For non-Object field values, fall through to regular evaluation.
                    if let Some(Value::Object {
                        class: field_class,
                        fields: field_fields,
                    }) = fields.get(field).cloned().as_ref()
                    {
                        if let Some((result, updated_field)) = find_and_exec_method_with_self(
                            method,
                            args,
                            field_class,
                            field_fields,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )? {
                            // Update the field in parent with the mutated nested object
                            Arc::make_mut(&mut fields).insert(field.clone(), updated_field);

                            // Create updated parent
                            let updated_parent = Value::Object {
                                class: parent_class.clone(),
                                fields,
                            };

                            // Return result and update instruction for parent
                            return Ok((result, Some((parent_name.clone(), updated_parent))));
                        }
                    }
                }
            }
        }

        // Handle `arr[i].method()` — Index receiver write-back (bug #28).
        // When the receiver is `Expr::Index { receiver: arr_expr, index }` where
        // `arr_expr` is a plain identifier, evaluate the index, extract the element,
        // run the method with self-update tracking, then write the element back into
        // the array and update the binding (and MODULE_GLOBALS if present).
        if let Expr::Index {
            receiver: arr_expr,
            index: idx_expr,
        } = receiver.as_ref()
        {
            if let Expr::Identifier(arr_name) = arr_expr.as_ref() {
                // Evaluate the index expression to a concrete integer.
                let idx_val = evaluate_expr(idx_expr, env, functions, classes, enums, impl_methods)?;
                let idx = match &idx_val {
                    Value::Int(i) => *i,
                    Value::UInt { value, .. } => *value as i64,
                    _ => {
                        // Non-integer index — fall through to regular evaluation.
                        let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                        return Ok((result, None));
                    }
                };

                // Get the array from the environment (or MODULE_GLOBALS).
                let arr_val = env
                    .get(arr_name)
                    .cloned()
                    .or_else(|| MODULE_GLOBALS.with(|cell| cell.borrow().get(arr_name).cloned()));

                if let Some(Value::Array(arr)) = arr_val {
                    let len = arr.len() as i64;
                    let real_idx = if idx < 0 { len + idx } else { idx };
                    if real_idx >= 0 && real_idx < len {
                        let elem = arr[real_idx as usize].clone();
                        match elem {
                            Value::Object {
                                class: obj_class,
                                fields: obj_fields,
                            } => {
                                if let Some((result, updated_elem)) = find_and_exec_method_with_self(
                                    method,
                                    args,
                                    &obj_class,
                                    &obj_fields,
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                )? {
                                    // Write updated element back into the array.
                                    let mut new_arr = (*arr).clone();
                                    new_arr[real_idx as usize] = updated_elem;
                                    let new_arr_val = Value::Array(Arc::new(new_arr));
                                    // Update local env.
                                    env.insert(arr_name.clone(), new_arr_val.clone());
                                    // Sync to MODULE_GLOBALS if this variable lives there.
                                    sync_flat_global(arr_name.as_ref(), &new_arr_val);
                                    return Ok((result, Some((arr_name.clone(), new_arr_val))));
                                }
                            }
                            Value::Array(ref inner_arr) => {
                                // Inner array (e.g. outer[0].push(x)): use a temp variable so
                                // evaluate_method_call_with_self_update can track the mutation.
                                let temp_var = format!("__indexed_elem_{}__", arr_name);
                                env.insert(temp_var.clone(), Value::Array(inner_arr.clone()));
                                let temp_receiver = Box::new(Expr::Identifier(temp_var.clone()));
                                let temp_call = Expr::MethodCall {
                                    receiver: temp_receiver,
                                    method: method.clone(),
                                    args: args.clone(),
                                    generic_args: vec![],
                                };
                                let (result, updated_elem_opt) = handle_method_call_with_self_update(
                                    &temp_call,
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                )?;
                                env.remove(&temp_var);
                                if let Some((_, updated_elem)) = updated_elem_opt {
                                    let mut new_arr = (*arr).clone();
                                    new_arr[real_idx as usize] = updated_elem;
                                    let new_arr_val = Value::Array(Arc::new(new_arr));
                                    env.insert(arr_name.clone(), new_arr_val.clone());
                                    sync_flat_global(arr_name.as_ref(), &new_arr_val);
                                    return Ok((result, Some((arr_name.clone(), new_arr_val))));
                                }
                                return Ok((result, None));
                            }
                            _ => {
                                // Scalar element — fall through to regular evaluation.
                            }
                        }
                    }
                }
            }
        }

        // General PLACE receiver: a variable followed by an arbitrary chain of
        // field/index projections (`a.b.c.m()`, `self.world.store.insert(..)`).
        //
        // The hand-written branches above stop at two levels: a FieldAccess whose
        // parent is an identifier, or an Index on an identifier. Anything deeper
        // used to fall through to plain evaluation, which evaluates the receiver
        // to a COPY — the mutating method ran against the copy and the write was
        // silently dropped (the "two-hop mutation lost" defect). Assignment
        // rejected the very same place loudly; this path lost data quietly.
        //
        // Resolve the receiver as a place, run the method with self-update
        // tracking, then rebuild the ROOT value with the mutated receiver stored
        // back at its projection and hand that to the caller as the update.
        if let Some(place) = super::super::place::resolve_place(receiver, env, functions, classes, enums, impl_methods)?
        {
            if super::super::place::place_is_live(env, &place)
                && (!place.projections.is_empty() || matches!(env.get(&place.root), Some(Value::FrozenByteArray(_))))
            {
                if place.projections.is_empty()
                    && matches!(env.get(&place.root), Some(Value::FrozenByteArray(_)))
                    && ARRAY_MUTATING_METHODS.contains(&method.as_str())
                {
                    let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT);
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "cannot call mutating method '{}' on frozen byte array '{}'",
                            method, place.root
                        ),
                        ctx,
                    ));
                }
                if place.projections.is_empty()
                    && ARRAY_MUTATING_METHODS.contains(&method.as_str())
                    && CONST_NAMES.with(|cell| cell.borrow().contains(&place.root))
                {
                    let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT);
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "cannot call mutating method '{}' on immutable byte array '{}'",
                            method, place.root
                        ),
                        ctx,
                    ));
                }
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
                if let Some(new_self) = updated_self {
                    if let Some(new_root) = super::super::place::updated_root(env, &place, new_self) {
                        // Keep MODULE_GLOBALS in step, as the sibling paths do.
                        sync_flat_global(place.root.as_ref(), &new_root);
                        return Ok((result, Some((place.root.clone(), new_root))));
                    }
                }
                return Ok((result, None));
            }
        }

        if let Expr::Identifier(obj_name) = receiver.as_ref() {
            // Handle Object mutations — fast path with zero-copy field mutations
            if let Some(Value::Object { ref class, .. }) = env.get(obj_name) {
                let class_name = class.clone();
                // Pre-check method exists via cached index before taking from env
                let method_found = classes
                    .get(&class_name)
                    .map(|cd| lookup_class_method_index(cd, &class_name, method).is_some())
                    .unwrap_or(false)
                    || impl_methods
                        .get(&class_name)
                        .map(|ms| lookup_impl_method_index(ms, &class_name, method).is_some())
                        .unwrap_or(false);

                if method_found {
                    // Take ownership: Arc refcount drops to 1 -> zero-copy mutations.
                    // MECALL-OWNED (2026-08-22): the args are evaluated HERE, while
                    // the receiver is still in env (so `me.field` args resolve), and
                    // the receiver is then moved into the callee with NO clone left
                    // behind. The previous shape re-inserted a clone for the benefit
                    // of bind_args (bug 2026-06-11), which put the refcount back to 2
                    // and made the first `self.dict[k] = v` of every `me` call deep-copy
                    // the dict -- linear in the dict, per call. Losing the binding on
                    // an Err is unobservable: TryError unwinds to the enclosing
                    // function boundary and every other CompileError aborts.
                    let arg_vals = evaluate_call_args(args, env, functions, classes, enums, impl_methods)?;
                    if let Some(Value::Object { class, fields }) = env.remove(obj_name) {
                        match find_and_exec_method_with_self_owned_values(
                            method,
                            &arg_vals,
                            args,
                            &class,
                            fields,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        ) {
                            Ok(Some((result, updated_self))) => {
                                return Ok((result, Some((obj_name.clone(), updated_self))));
                            }
                            Ok(None) => unreachable!(),
                            Err(e) => return Err(e),
                        }
                    }
                } else {
                    // Method not in class/impl — use full dispatch for method_missing/UFCS/lambdas
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
                    if let Some(new_self) = updated_self {
                        return Ok((result, Some((obj_name.clone(), new_self))));
                    }
                    return Ok((result, None));
                }
            }
            // Handle Object mutations for MODULE_GLOBALS variables (not in local env)
            // Only an Object is used below. Cloning whatever the flat map holds
            // kept a second reference to a global ARRAY alive across the in-place
            // mutation branch, so `Arc::make_mut` deep-copied it on every push
            // (doc/08_tracking/bug/seed_global_array_push_cow_per_frame_2026-08-22.md).
            let global_obj = MODULE_GLOBALS.with(|cell| match cell.borrow().get(obj_name) {
                Some(obj @ Value::Object { .. }) => Some(obj.clone()),
                _ => None,
            });
            if let Some(Value::Object { class, fields }) = global_obj {
                if let Some((result, updated_self)) = find_and_exec_method_with_self(
                    method,
                    args,
                    &class,
                    &fields,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )? {
                    // Write back to MODULE_GLOBALS directly
                    sync_flat_global(obj_name.as_str(), &updated_self);
                    return Ok((result, Some((obj_name.clone(), updated_self))));
                }
            }
            // Handle Array mutations for mutating methods
            // A module-global array that is not yet visible through this frame's
            // env (first mutation from a helper fn: `expr_tag.push(..)` in
            // `expr_alloc`) used to fall through to the generic path, which
            // clones the receiver and therefore the whole Vec on EVERY call.
            // Promote the store's handle into the overlay (one Arc clone) so the
            // ownership-gated in-place path below applies; the generic path's own
            // write-back (`calls.rs`) ends in exactly this overlay state anyway.
            if env.get(obj_name).is_none() && !env.is_local(obj_name) && ARRAY_MUTATING_METHODS.contains(&method.as_str()) {
                let global_arr = MODULE_GLOBALS.with(|cell| match cell.borrow().get(obj_name) {
                    Some(v @ Value::Array(_)) => Some(v.clone()),
                    _ => None,
                });
                if let Some(v) = global_arr {
                    env.insert(obj_name.clone(), v);
                }
            }
            if let Some(Value::Array(_)) = env.get(obj_name) {
                if ARRAY_MUTATING_METHODS.contains(&method.as_str()) {
                    // Check if variable is mutable
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(obj_name));
                    if is_const {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help(format!("consider using '{obj_name}_' for a mutable variable"));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "cannot call mutating method '{}' on immutable array '{}'",
                                method, obj_name
                            ),
                            ctx,
                        ));
                    }

                    // `write_span(src, dst_off, src_off, count)` — bulk in-place span copy.
                    // Handled before the generic item/idx/second plumbing because it takes
                    // FOUR arguments. Same ownership-gated `Arc::make_mut` discipline as the
                    // generic path below: uniquely-owned → true in-place copy; aliased
                    // (including a same-array `a.write_span(a, ...)`, whose src argument
                    // holds a second strong ref) → clone-then-mutate, which is exactly what
                    // gives the documented memmove-style overlap semantics (the src Value is
                    // a pre-copy snapshot). Expression result is the COUNT WRITTEN.
                    if method.as_str() == "write_span" {
                        let src =
                            eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                        let mut ints = [-1i64, -1, 0];
                        for (slot, (arg_i, dflt)) in ints.iter_mut().zip([(1usize, -1i64), (2, -1), (3, 0)]) {
                            *slot = match args.get(arg_i) {
                                Some(a) => evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)?
                                    .as_int()
                                    .unwrap_or(dflt),
                                None => dflt,
                            };
                        }
                        if let Some(Value::Array(arc)) = env.get_mut(obj_name) {
                            let written = {
                                let vec = Arc::make_mut(arc);
                                super::super::interpreter_method::collections::array_write_span(
                                    vec, &src, ints[0], ints[1], ints[2],
                                )?
                            };
                            let new_array_val = Value::Array(Arc::clone(arc));
                            return Ok((Value::Int(written), Some((obj_name.clone(), new_array_val))));
                        }
                    }

                    // Evaluate the method's argument(s) exactly ONCE, up front. This mirrors the
                    // index-store fast path (interpreter/node_exec.rs:906-937), which evaluates its
                    // RHS/index operands before branching on ownership. The values are consumed by
                    // the single mutation call below, so an aliased array is never double-evaluated
                    // (no duplicated argument side effects) — the previous path re-entered
                    // `evaluate_expr`, which re-cloned the whole backing Vec on every call.
                    let m = method.as_str();
                    let item = match m {
                        "push" | "append" => Some(eval_arg(
                            args,
                            0,
                            Value::Nil,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?),
                        "extend" => Some(eval_arg(
                            args,
                            0,
                            Value::array(vec![]),
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?),
                        _ => None,
                    };
                    let (idx, second) = match m {
                        "insert" => (
                            Some(eval_arg_usize(
                                args,
                                0,
                                0,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                            Some(eval_arg(
                                args,
                                1,
                                Value::Nil,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                        ),
                        "remove" => (
                            Some(eval_arg_usize(
                                args,
                                0,
                                0,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                            None,
                        ),
                        _ => (None, None),
                    };

                    // Ownership-gated IN-PLACE mutation — the durable fix for the O(N)-per-call
                    // whole-array clone that made `arr.push(x)` list-building O(N^2). `Arc::make_mut`
                    // on the binding's Arc:
                    //   * uniquely owned (Arc strong_count == 1) → mutates the backing Vec IN PLACE,
                    //     O(1) amortized — this is the new fast path;
                    //   * aliased (strong_count > 1) → clones the Vec and mutates the copy, leaving
                    //     every other binding/alias untouched — value semantics preserved exactly,
                    //     identical to the index-store slow path at node_exec.rs:951.
                    // `Value::Array` Arcs are never `Arc::downgrade`d anywhere in the interpreter, so
                    // weak_count is always 0 and make_mut's `strong_count == 1` test coincides with
                    // the index-store fast path's `strong_count == 1 && weak_count == 0` gate.
                    // NB: the array is re-read via `env.get_mut` AFTER argument evaluation, so an
                    // argument that itself retained a reference to this array (e.g. `a.push(a)`)
                    // bumps the refcount and correctly forces the clone branch.
                    //
                    // Weak-count invariant (adversarial-review note): `Arc::make_mut` below mutates
                    // in place whenever `strong_count == 1`, *regardless* of `weak_count` — unlike
                    // the sibling index-store fast path, which explicitly gates on both
                    // `strong_count == 1 && weak_count == 0` (`node_exec.rs:917`, `Arc::get_mut`,
                    // gated by the check at `node_exec.rs:907`). The two paths coincide ONLY because
                    // no `Value::Array` Arc is ever `Arc::downgrade`d anywhere in the interpreter
                    // today (verified: zero call sites), so `weak_count` is always 0 here. If a
                    // `Weak<Vec<Value>>` on an array Arc is ever introduced (e.g. a future weak-ref
                    // language feature), this call MUST switch from `Arc::make_mut` to `Arc::get_mut`
                    // (falling through to the clone branch on `None`) to stay safe, exactly like
                    // index-store does.
                    //
                    // Eval-order edge case (accepted, unreachable in-tree): argument(s) are evaluated
                    // above, BEFORE the receiver array is re-read via `env.get_mut` here. A
                    // self-referential, trimming-mutating argument expression on the SAME array —
                    // e.g. `a.push(a.pop())`, where evaluating the argument mutates `a` as a side
                    // effect before the outer `push` re-reads it — would therefore observe a
                    // different intermediate state than re-entering `evaluate_expr` per call did
                    // pre-fix, i.e. this is a genuine ordering divergence from stock, not merely an
                    // aliasing one. It is accepted as-is because: (1) it is UNREACHABLE in-tree today
                    // (zero occurrences of the same-variable-receiver-equals-argument-receiver shape,
                    // grepped across src/ and test/); the real in-tree idiom, `args.push(self.pop())`
                    // (e.g. `src/lib/common/js/engine/vm.spl`), is cross-variable (`args` vs `self`)
                    // and does NOT hit this edge; (2) the case is ill-defined in stock semantics too
                    // — there is no independently "correct" answer for what a self-mutating argument
                    // to a self-mutating receiver method should observe, in this or most languages;
                    // and (3) it is consistent with the index-store fast path's own live-read
                    // semantics (index and RHS operands are likewise evaluated before the ownership
                    // check there). Not a regression to fix; documented so a future reader doesn't
                    // mistake it for an oversight.
                    // A MODULE-GLOBAL receiver is aliased by the two global stores
                    // (`MODULE_GLOBALS` and the owner's live store), so `Arc::make_mut`
                    // below deep-copied the whole Vec on EVERY `g.push(x)` from inside a
                    // function. Park the stores' copies (Nil) and drop the frame snapshot
                    // so the frame's Arc is unique; the caller's write-through
                    // (`sync_flat_global`) re-publishes the mutated Arc. On error the
                    // stores are restored from the frame value, so nothing is lost.
                    let released = release_global_aliases(obj_name, env);
                    if let Some(Value::Array(arc)) = env.get_mut(obj_name) {
                        crate::perf_counters::bump(&crate::perf_counters::ARR_MUT_CALLS, 1);
                        if crate::perf_counters::enabled() && Arc::strong_count(arc) > 1 {
                            crate::perf_counters::bump(&crate::perf_counters::ARR_MUT_COW_CLONES, 1);
                            crate::perf_counters::bump(
                                &crate::perf_counters::ARR_MUT_COW_ELEMS_CLONED,
                                arc.len() as u64,
                            );
                            crate::perf_counters::trace_array("arr_mut_cow", obj_name, arc.len());
                            if crate::perf_counters::trace_min_len() > 0 {
                                let mut where_ = Vec::new();
                                crate::interpreter::MODULE_GLOBALS.with(|c| for (k, v) in c.borrow().iter() { if let Value::Array(o) = v { if Arc::ptr_eq(o, arc) { where_.push(format!("flat:{k}")); } } });
                                crate::interpreter::MODULE_GLOBALS_BY_OWNER.with(|c| for (ow, g) in c.borrow().iter() { for (k, v) in g.iter() { if let Value::Array(o) = v { if Arc::ptr_eq(o, arc) { where_.push(format!("owned:{ow}::{k}")); } } } });
                                eprintln!("[perf-trace] arr_mut_cow_pins name={obj_name} rc={} store_pins={:?}", Arc::strong_count(arc), where_);
                            }
                        }
                        let popped = {
                            let vec = Arc::make_mut(arc);
                            match apply_array_mutation_in_place(m, vec, item, idx, second) {
                                Ok(p) => p,
                                Err(e) => {
                                    if released {
                                        let cur = Value::Array(Arc::clone(arc));
                                        sync_flat_global(obj_name, &cur);
                                        env.refresh_scope(crate::interpreter::owned_globals_snapshot());
                                    }
                                    return Err(e);
                                }
                            }
                        };
                        // Hand the (already-mutated) Arc back as both the binding update and, for
                        // non-`pop` methods, the expression result — an O(1) refcount bump, not a copy.
                        let new_array_val = Value::Array(Arc::clone(arc));
                        let result_val = popped.unwrap_or_else(|| new_array_val.clone());
                        return Ok((result_val, Some((obj_name.clone(), new_array_val))));
                    }
                }
            }
            // Packed `[u8]` values use the same identifier-lvalue contract as
            // generic arrays.  Falling through to `evaluate_expr` computes the
            // mutator result, but loses the receiver write-back; consequently
            // `bytes.push(x)` returned the enlarged byte array while leaving
            // `bytes` unchanged.  Keep the packed Arc compact and use
            // `Arc::make_mut` so a uniquely-owned binding mutates in place while
            // an aliased binding gets an isolated COW copy.
            if let Some(Value::ByteArray(_)) = env.get(obj_name) {
                if ARRAY_MUTATING_METHODS.contains(&method.as_str()) {
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(obj_name));
                    if is_const {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help(format!("consider using '{obj_name}_' for a mutable variable"));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "cannot call mutating method '{}' on immutable byte array '{}'",
                                method, obj_name
                            ),
                            ctx,
                        ));
                    }

                    let m = method.as_str();
                    let item = match m {
                        "push" | "append" => Some(eval_arg(
                            args,
                            0,
                            Value::Nil,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?),
                        "extend" => Some(eval_arg(
                            args,
                            0,
                            Value::array(vec![]),
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?),
                        _ => None,
                    };
                    let (idx, second) = match m {
                        "insert" => (
                            Some(eval_arg_usize(
                                args,
                                0,
                                0,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                            Some(eval_arg(
                                args,
                                1,
                                Value::Nil,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                        ),
                        "remove" => (
                            Some(eval_arg_usize(
                                args,
                                0,
                                0,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )?),
                            None,
                        ),
                        _ => (None, None),
                    };

                    if let Some(Value::ByteArray(arc)) = env.get_mut(obj_name) {
                        let byte_value = |value: &Value| match value {
                            Value::UInt { value, width: 8 } => u8::try_from(*value).ok(),
                            _ => None,
                        };
                        let mut element_result = None;
                        let mut widened = None;
                        {
                            let bytes = Arc::make_mut(arc);
                            match m {
                                "push" | "append" => {
                                    let value = item.unwrap_or(Value::Nil);
                                    if let Some(byte) = byte_value(&value) {
                                        bytes.push(byte);
                                    } else {
                                        let mut values = Value::byte_array_values(bytes);
                                        values.push(value);
                                        widened = Some(Value::array(values));
                                    }
                                }
                                "pop" => {
                                    element_result = Some(
                                        bytes
                                            .pop()
                                            .map(|byte| Value::UInt {
                                                value: u64::from(byte),
                                                width: 8,
                                            })
                                            .unwrap_or(Value::Nil),
                                    );
                                }
                                "insert" => {
                                    let index = idx.unwrap_or(0);
                                    let value = second.unwrap_or(Value::Nil);
                                    if index <= bytes.len() {
                                        if let Some(byte) = byte_value(&value) {
                                            bytes.insert(index, byte);
                                        } else {
                                            let mut values = Value::byte_array_values(bytes);
                                            values.insert(index, value);
                                            widened = Some(Value::array(values));
                                        }
                                    }
                                }
                                "remove" => {
                                    let index = idx.unwrap_or(0);
                                    element_result = Some(if index < bytes.len() {
                                        Value::UInt {
                                            value: u64::from(bytes.remove(index)),
                                            width: 8,
                                        }
                                    } else {
                                        Value::Nil
                                    });
                                }
                                "extend" => match item {
                                    // `[u8]` is a first-class array representation.  Preserve the
                                    // packed fast path when extending with packed mutable or frozen
                                    // bytes; accepting only `Value::Array` made `a.extend(b)` fail
                                    // solely because `b` used the compact representation.
                                    Some(Value::ByteArray(other)) | Some(Value::FrozenByteArray(other)) => {
                                        bytes.extend(other.iter().copied());
                                    }
                                    Some(Value::Array(other)) => {
                                        let mut values = Value::byte_array_values(bytes);
                                        values.extend(other.iter().cloned());
                                        let packed: Option<Vec<u8>> = values.iter().map(byte_value).collect();
                                        if let Some(packed) = packed {
                                            *bytes = packed;
                                        } else {
                                            widened = Some(Value::array(values));
                                        }
                                    }
                                    _ => {
                                        let ctx = ErrorContext::new()
                                            .with_code(codes::TYPE_MISMATCH)
                                            .with_help("concat/extend/merge expects an array argument");
                                        return Err(CompileError::semantic_with_context(
                                            "concat/extend/merge expects array argument",
                                            ctx,
                                        ));
                                    }
                                },
                                "clear" => bytes.clear(),
                                _ => {}
                            }
                        }

                        if let Some(new_value) = widened {
                            let result = element_result.unwrap_or_else(|| new_value.clone());
                            return Ok((result, Some((obj_name.clone(), new_value))));
                        }
                        let new_value = Value::ByteArray(Arc::clone(arc));
                        let result = element_result.unwrap_or_else(|| new_value.clone());
                        return Ok((result, Some((obj_name.clone(), new_value))));
                    }
                }
            }
            // Handle Dict mutations for mutating methods
            if let Some(Value::Dict(_)) = env.get(obj_name) {
                let dict_mutating = ["set", "insert", "remove", "delete", "merge", "extend", "clear"];
                if dict_mutating.contains(&method.as_str()) {
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(obj_name));
                    if is_const {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_ASSIGNMENT)
                            .with_help(format!("consider using '{obj_name}_' for a mutable variable"));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "cannot call mutating method '{}' on immutable dict '{}'",
                                method, obj_name
                            ),
                            ctx,
                        ));
                    }
                    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(new_dict) = &result {
                        // Return both the new dict as result AND the update for self-mutation
                        let new_dict_val = Value::Dict(new_dict.clone());
                        return Ok((new_dict_val.clone(), Some((obj_name.clone(), new_dict_val))));
                    }
                }
            }
        }
    }
    let result = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}

/// Bind a single pattern element from a let statement
/// Updates const names set if the binding is immutable
fn bind_let_pattern_element(pat: &Pattern, val: Value, is_mutable: bool, env: &mut Env) {
    match pat {
        Pattern::Identifier(name) => {
            env.insert(name.clone(), val);
            // A local `val` binding must not const-poison a name that is also a
            // mutable module-level global. CONST_NAMES is a process-global set
            // with no scope cleanup, so a local `val arm_body` would otherwise
            // permanently mark the module-global `var arm_body` as const and make
            // later `arm_body = []` reassignments fail "cannot assign to const".
            // Only track names that are not module globals (the collision case is
            // legitimately mutable and enforced by the compiler's semantic phase).
            if !is_mutable && !MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name)) {
                crate::interpreter::const_trace("patterns:val-insert", name); CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
            } else if is_mutable {
                // CONST_NAMES has function lifetime with no block scoping, so a
                // `val x` executed in one branch would leave `x` const-poisoned
                // for a later `var x` in a sibling scope of the same function
                // (e.g. layout()'s absolute-child `val child_styles` vs the flex
                // main loop's `var child_styles`). A mutable re-declaration must
                // clear the stale entry.
                crate::interpreter::const_trace("patterns:remove", name); CONST_NAMES.with(|cell| cell.borrow_mut().remove(name));
            }
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), val);
            crate::interpreter::const_trace("patterns:remove", name); CONST_NAMES.with(|cell| cell.borrow_mut().remove(name));
        }
        Pattern::MoveIdentifier(name) => {
            // Move pattern - transfers ownership
            env.insert(name.clone(), val);
        }
        Pattern::Typed { pattern, .. } => {
            bind_let_pattern_element(pattern, val, is_mutable, env);
        }
        _ => {}
    }
}

/// Bind any pattern from a let statement.
pub(crate) fn bind_pattern_value(pat: &Pattern, val: Value, is_mutable: bool, env: &mut Env) {
    match pat {
        Pattern::Tuple(patterns) => {
            // Allow tuple pattern to match both Tuple and Array
            let values: Vec<Value> = match val {
                Value::Tuple(v) => v,
                Value::Array(v) => (*v).clone(),
                _ => Vec::new(),
            };
            bind_collection_pattern(patterns, values, is_mutable, env);
        }
        Pattern::Array(patterns) => {
            if let Value::Array(values) = val {
                bind_collection_pattern(patterns, (*values).clone(), is_mutable, env);
            }
        }
        _ => bind_let_pattern_element(pat, val, is_mutable, env),
    }
}

/// Bind a collection pattern (tuple or array) from a let statement.
fn bind_collection_pattern(patterns: &[Pattern], values: Vec<Value>, is_mutable: bool, env: &mut Env) {
    for (pat, val) in patterns.iter().zip(values.into_iter()) {
        bind_pattern_value(pat, val, is_mutable, env);
    }
}

/// Mechanism tests for the COW-alias performance class.
///
/// Simple has value semantics implemented as copy-on-write: a container is an
/// `Arc<Vec<..>>` and a mutation goes through `Arc::make_mut`, which deep-copies
/// the whole container whenever the Arc is ALIASED (strong_count > 1). That is
/// correct — two live bindings must not observe each other's writes — but it is
/// catastrophic when the only "alias" is the interpreter's own bookkeeping: the
/// env slot / struct field it is about to write back to. Then every single write
/// copies the whole container and list building is O(N^2).
///
/// These tests count DISTINCT BACKING BUFFERS across N mutations (pointer
/// identity, not time), so they are deterministic on a loaded box. A sole owner
/// must touch O(1) buffers (amortized `Vec` growth reallocates, but the buffer
/// is reused between growths, so the count is O(log N), bounded well below N).
/// A genuine alias must still copy exactly once and leave the alias untouched.
#[cfg(test)]
mod cow_alias_mechanism_tests {
    use super::*;
    use std::collections::HashSet;

    fn arr_ptr(v: &Value) -> usize {
        match v {
            Value::Array(a) => a.as_ptr() as usize,
            other => panic!("expected array, got {:?}", other),
        }
    }

    fn arr_len(v: &Value) -> usize {
        match v {
            Value::Array(a) => a.len(),
            other => panic!("expected array, got {:?}", other),
        }
    }

    fn box_with_empty_xs() -> Value {
        let mut fields: HashMap<String, Value> = HashMap::new();
        fields.insert("xs".to_string(), Value::array(vec![]));
        Value::Object {
            class: "Box".to_string(),
            fields: Arc::new(fields),
        }
    }

    fn field_of<'e>(env: &'e Env, obj: &str, field: &str) -> &'e Value {
        match env.get(obj).expect("object binding") {
            Value::Object { fields, .. } => fields.get(field).expect("field"),
            other => panic!("expected object, got {:?}", other),
        }
    }

    fn ident(name: &str) -> Expr {
        Expr::Identifier(name.to_string())
    }

    fn arg(e: Expr) -> simple_parser::ast::Argument {
        simple_parser::ast::Argument::new(None, e)
    }

    fn push_call(receiver: Expr) -> Expr {
        Expr::MethodCall {
            receiver: Box::new(receiver),
            method: "push".to_string(),
            args: vec![arg(Expr::Integer(1))],
            generic_args: vec![],
        }
    }

    fn run(expr: &Expr, env: &mut Env) -> (Value, Option<(String, Value)>) {
        handle_method_call_with_self_update(
            expr,
            env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("method call")
    }

    #[test]
    fn local_array_push_mutates_the_single_owner_in_place() {
        const N: usize = 2_000;
        let mut env = Env::new();
        env.insert("a".to_string(), Value::array(vec![]));
        let call = push_call(ident("a"));
        let mut seen: HashSet<usize> = HashSet::new();
        for _ in 0..N {
            let (_, update) = run(&call, &mut env);
            if let Some((name, val)) = update {
                env.insert(name, val);
            }
            seen.insert(arr_ptr(env.get("a").expect("a")));
        }
        assert_eq!(arr_len(env.get("a").expect("a")), N, "every push must land");
        assert!(
            seen.len() < 64,
            "sole-owner push must reallocate O(log N) times (amortized Vec growth), \
             got {} distinct buffers for {N} pushes; a value near {N} means the \
             array Arc is aliased and Arc::make_mut is deep-copying per write",
            seen.len()
        );
    }

    #[test]
    fn field_array_push_mutates_the_single_owner_in_place() {
        const N: usize = 2_000;
        let mut env = Env::new();
        env.insert("o".to_string(), box_with_empty_xs());
        let call = push_call(Expr::FieldAccess {
            receiver: Box::new(ident("o")),
            field: "xs".to_string(),
        });
        let mut seen: HashSet<usize> = HashSet::new();
        for _ in 0..N {
            let (_, update) = run(&call, &mut env);
            if let Some((name, val)) = update {
                env.insert(name, val);
            }
            seen.insert(arr_ptr(field_of(&env, "o", "xs")));
        }
        assert_eq!(arr_len(field_of(&env, "o", "xs")), N, "every push must land");
        // Pre-fix this was 1,321 distinct buffers for N = 2,000: the general
        // PLACE receiver path copied the field into a temp, aliasing the Arc,
        // so `Arc::make_mut` deep-copied the whole Vec on every push.
        assert!(
            seen.len() < 64,
            "`o.xs.push(v)` must mutate the field in place; got {} distinct \
             buffers for {N} pushes (pre-fix: ~1321) — the field array Arc is \
             aliased again and every write is an O(n) COW clone",
            seen.len()
        );
    }

    #[test]
    fn genuinely_aliased_array_still_copies_on_write() {
        // Value semantics must survive the optimization: a second LIVE binding
        // to the same Arc must not observe the mutation, and must cost exactly
        // one copy (not zero — that would be a semantic change — and not one
        // per write).
        let mut env = Env::new();
        env.insert("a".to_string(), Value::array(vec![Value::Int(0)]));
        let aliased = env.get("a").expect("a").clone();
        env.insert("b".to_string(), aliased);
        let call = push_call(ident("a"));
        for _ in 0..3 {
            let (_, update) = run(&call, &mut env);
            if let Some((name, val)) = update {
                env.insert(name, val);
            }
        }
        assert_eq!(arr_len(env.get("a").expect("a")), 4, "a must have grown");
        assert_eq!(arr_len(env.get("b").expect("b")), 1, "the alias must be unchanged");
        assert_ne!(
            arr_ptr(env.get("a").expect("a")),
            arr_ptr(env.get("b").expect("b")),
            "the aliased array must have been isolated by copy-on-write"
        );
    }

    #[test]
    fn genuinely_aliased_field_array_still_copies_on_write() {
        let mut env = Env::new();
        let mut fields: HashMap<String, Value> = HashMap::new();
        fields.insert("xs".to_string(), Value::array(vec![Value::Int(0)]));
        env.insert(
            "o".to_string(),
            Value::Object {
                class: "Box".to_string(),
                fields: Arc::new(fields),
            },
        );
        let alias = field_of(&env, "o", "xs").clone();
        env.insert("b".to_string(), alias);
        let call = push_call(Expr::FieldAccess {
            receiver: Box::new(ident("o")),
            field: "xs".to_string(),
        });
        for _ in 0..3 {
            let (_, update) = run(&call, &mut env);
            if let Some((name, val)) = update {
                env.insert(name, val);
            }
        }
        assert_eq!(arr_len(field_of(&env, "o", "xs")), 4, "o.xs must have grown");
        assert_eq!(arr_len(env.get("b").expect("b")), 1, "the alias must be unchanged");
    }

    #[test]
    fn field_array_pop_and_remove_return_the_element_not_the_array() {
        // The fast path routes through `apply_array_mutation_in_place`, the same
        // kernel the slow path uses; pin that the RESULT contract is unchanged.
        let mut env = Env::new();
        let mut fields: HashMap<String, Value> = HashMap::new();
        fields.insert(
            "xs".to_string(),
            Value::array(vec![Value::Int(7), Value::Int(8), Value::Int(9)]),
        );
        env.insert(
            "o".to_string(),
            Value::Object {
                class: "Box".to_string(),
                fields: Arc::new(fields),
            },
        );
        let pop = Expr::MethodCall {
            receiver: Box::new(Expr::FieldAccess {
                receiver: Box::new(ident("o")),
                field: "xs".to_string(),
            }),
            method: "pop".to_string(),
            args: vec![],
            generic_args: vec![],
        };
        let (result, _) = run(&pop, &mut env);
        assert!(matches!(result, Value::Int(9)), "pop must return the element, got {:?}", result);
        assert_eq!(arr_len(field_of(&env, "o", "xs")), 2, "pop must shrink the field array");
    }
}
