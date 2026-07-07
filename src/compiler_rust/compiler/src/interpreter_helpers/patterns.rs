//! Pattern matching and binding

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, Pattern};
use std::collections::HashMap;
use std::sync::Arc;

use super::super::{
    evaluate_expr, evaluate_method_call_with_self_update, find_and_exec_method_with_self,
    find_and_exec_method_with_self_owned, lookup_class_method_index, lookup_impl_method_index, Enums, ImplMethods,
    CONST_NAMES, MODULE_GLOBALS,
};

use super::args::{eval_arg, eval_arg_usize};
use super::collections::bind_sequence_pattern;
use super::method_dispatch::call_method_on_value;
use crate::value::{OptionVariant, ResultVariant};

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
const ARRAY_MUTATING_METHODS: &[&str] = &["append", "push", "pop", "insert", "remove", "extend", "clear"];

/// Apply an array mutating method to a `&mut Vec<Value>` in place.
///
/// This is the single mutation kernel shared by BOTH the ownership-gated in-place
/// fast path (uniquely-owned array — `Arc::get_mut`) and the clone-then-mutate slow
/// path (aliased array — `arr.to_vec()`), so the two paths are provably byte-for-byte
/// identical in semantics; only *where* the `Vec` lives differs. The behaviour of each
/// arm mirrors `interpreter_method/collections.rs::handle_array_methods` exactly.
///
/// Returns `Ok(Some(elem))` for `pop` (the popped element to yield as the expression
/// result; the pre-existing lvalue path already special-cased this), and `Ok(None)` for
/// every other method (whose expression result is the array itself). `extend` with a
/// non-array argument returns the same `TYPE_MISMATCH` error `handle_array_methods` does.
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
        "remove" => {
            let i = idx.unwrap_or(0);
            if i < vec.len() {
                vec.remove(i);
            }
            Ok(None)
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
                                    MODULE_GLOBALS.with(|cell| {
                                        let mut globals = cell.borrow_mut();
                                        if globals.contains_key(arr_name) {
                                            globals.insert(arr_name.clone(), new_arr_val.clone());
                                        }
                                    });
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
                                    MODULE_GLOBALS.with(|cell| {
                                        let mut globals = cell.borrow_mut();
                                        if globals.contains_key(arr_name) {
                                            globals.insert(arr_name.clone(), new_arr_val.clone());
                                        }
                                    });
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
                    // Take ownership: Arc refcount drops to 1 → zero-copy mutations.
                    // IMPORTANT: args must be evaluated in env while `self` is still
                    // present. We remove `self` for the zero-copy optimisation, but
                    // re-insert a clone so that arg expressions such as `me.field`
                    // (which lower to `self.field`) can resolve during bind_args inside
                    // exec_function_with_self_return. The clone costs one Arc refcount
                    // bump for the duration of the call, which is acceptable correctness
                    // over the alternative of "self not found" (bug 2026-06-11).
                    if let Some(Value::Object { class, fields }) = env.remove(obj_name) {
                        // Re-insert self so arg expressions that reference the caller's
                        // self (e.g. `me.field` as a direct arg to a nested `me fn`)
                        // can still resolve during argument evaluation.
                        env.insert(
                            obj_name.to_string(),
                            Value::Object {
                                class: class.clone(),
                                fields: Arc::clone(&fields),
                            },
                        );
                        match find_and_exec_method_with_self_owned(
                            method,
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
            let global_obj = MODULE_GLOBALS.with(|cell| cell.borrow().get(obj_name).cloned());
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
                    MODULE_GLOBALS.with(|cell| {
                        cell.borrow_mut().insert(obj_name.clone(), updated_self.clone());
                    });
                    return Ok((result, Some((obj_name.clone(), updated_self))));
                }
            }
            // Handle Array mutations for mutating methods
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
                    if let Some(Value::Array(arc)) = env.get_mut(obj_name) {
                        let popped = {
                            let vec = Arc::make_mut(arc);
                            apply_array_mutation_in_place(m, vec, item, idx, second)?
                        };
                        // Hand the (already-mutated) Arc back as both the binding update and, for
                        // non-`pop` methods, the expression result — an O(1) refcount bump, not a copy.
                        let new_array_val = Value::Array(Arc::clone(arc));
                        let result_val = popped.unwrap_or_else(|| new_array_val.clone());
                        return Ok((result_val, Some((obj_name.clone(), new_array_val))));
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
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
            } else if is_mutable {
                // CONST_NAMES has function lifetime with no block scoping, so a
                // `val x` executed in one branch would leave `x` const-poisoned
                // for a later `var x` in a sibling scope of the same function
                // (e.g. layout()'s absolute-child `val child_styles` vs the flex
                // main loop's `var child_styles`). A mutable re-declaration must
                // clear the stale entry.
                CONST_NAMES.with(|cell| cell.borrow_mut().remove(name));
            }
        }
        Pattern::MutIdentifier(name) => {
            env.insert(name.clone(), val);
            CONST_NAMES.with(|cell| cell.borrow_mut().remove(name));
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
