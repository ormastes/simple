// Collection type methods: Array, Tuple, Dict

use std::sync::Arc;
use super::super::{
    eval_arg, eval_arg_usize, eval_array_all, eval_array_any, eval_array_filter, eval_array_find, eval_array_map,
    eval_array_reduce, eval_dict_filter, eval_dict_for_each, eval_dict_map_values, evaluate_expr, exec_function, instantiate_class, Enums,
    ImplMethods,
};
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, Expr, FunctionDef};
use std::collections::HashMap;

#[cfg(test)]
thread_local! {
    static BYTE_ARRAY_WIDEN_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn measure_byte_array_widens<T>(f: impl FnOnce() -> T) -> (T, usize) {
    BYTE_ARRAY_WIDEN_COUNT.with(|count| {
        count.set(0);
        let result = f();
        (result, count.get())
    })
}

/// Trust `.?`'s own presence decision instead of re-testing the payload's
/// truthiness. `expr.?` (`Expr::ExistsCheck`) already evaluates to "the
/// unwrapped value if present, `Value::Nil` if absent" -- feeding that value
/// back through generic `Value::truthy()` re-decides presence a second time,
/// this time from the *payload's* truthiness, and wrongly rejects
/// `Some(0)`/`Some(false)`/etc. Mirrors N2's `is_condition_present`
/// (interpreter_control.rs, if/elif/while/match-guard sites; see
/// doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md)
/// applied here to lambda-predicate bodies (take_while/skip_while/count/partition).
fn is_condition_present(condition_expr: &Expr, val: &Value) -> bool {
    if matches!(condition_expr, Expr::ExistsCheck(_)) {
        !matches!(val, Value::Nil)
    } else {
        val.truthy()
    }
}

/// Bulk in-place span copy: `dst[dst_off..dst_off+count] = src[src_off..src_off+count]`.
///
/// Shared validation + copy kernel for every `arr.write_span(src, dst_off, src_off,
/// count)` dispatch site (the identifier fast path in interpreter_helpers/patterns.rs,
/// the place write-back path in interpreter_method/mod.rs, and the borrowed-slice
/// handler below), so bounds semantics cannot drift between lanes.
///
/// Contract (doc/08_tracking/bug/engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md):
///   * `count <= 0` is a no-op returning 0 (mirrors the span kernels' guard);
///   * any out-of-range access is a LOUD error — no silent growth, no clamp;
///   * returns the number of elements written (== count);
///   * overlap semantics are memmove-style: `src` here is always a snapshot Value
///     taken at argument-evaluation time, so a same-array copy reads the PRE-copy
///     contents even when the destination is mutated in place (the in-place path's
///     `Arc::make_mut` sees the src argument holding a second strong ref and clones).
pub(crate) fn array_write_span(
    dst: &mut Vec<Value>,
    src: &Value,
    dst_off: i64,
    src_off: i64,
    count: i64,
) -> Result<i64, CompileError> {
    if count <= 0 {
        return Ok(0);
    }
    let src_arr = match src {
        Value::Array(a) => a,
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("write_span expects an array as its first argument");
            return Err(CompileError::semantic_with_context(
                "write_span expects array source argument",
                ctx,
            ));
        }
    };
    let dst_len = dst.len() as i64;
    let src_len = src_arr.len() as i64;
    if dst_off < 0 || src_off < 0 || dst_off + count > dst_len || src_off + count > src_len {
        let ctx = ErrorContext::new()
            .with_code(codes::INDEX_OUT_OF_BOUNDS)
            .with_help("write_span never grows the destination; ensure dst_off+count <= dst.len() and src_off+count <= src.len()");
        return Err(CompileError::semantic_with_context(
            format!(
                "write_span out of range: dst_off={dst_off} src_off={src_off} count={count} dst_len={dst_len} src_len={src_len}"
            ),
            ctx,
        ));
    }
    dst[dst_off as usize..(dst_off + count) as usize]
        .clone_from_slice(&src_arr[src_off as usize..(src_off + count) as usize]);
    Ok(count)
}

fn array_ndim(arr: &[Value]) -> i64 {
    if arr.is_empty() {
        return 1;
    }
    match &arr[0] {
        Value::Array(inner) => 1 + array_ndim(inner),
        _ => 1,
    }
}

/// Read any language-level array representation through the generic array
/// method kernel.  Packed `[u8]` is deliberately widened only at this
/// polymorphic boundary; callers that can retain byte semantics repack the
/// result afterwards.
fn generic_array_values(value: &Value) -> Option<Vec<Value>> {
    match value {
        Value::Array(values) | Value::FrozenArray(values) => Some(values.as_ref().clone()),
        Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => Some(Value::byte_array_values(bytes)),
        Value::FixedSizeArray { data, .. } => Some(data.clone()),
        _ => None,
    }
}

/// Handle Array methods
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_array_methods(
    arr: &[Value],
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" | "length" => Value::Int(arr.len() as i64),
        "ndim" => Value::Int(array_ndim(arr)),
        "is_empty" => Value::Bool(arr.is_empty()),
        "first" => arr.first().cloned().unwrap_or(Value::Nil),
        "last" => arr.last().cloned().unwrap_or(Value::Nil),
        "get" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            arr.get(idx).cloned().unwrap_or(Value::Nil)
        }
        // Array `at`: bounds-checked element access returning a real
        // `Option` -- `Value::some(elem)` in range, `Value::none()` otherwise.
        //
        // Until this arm existed the seed had NO array `at` at all: the only
        // `at` binding was the *text* one (`"char_at" | "at" =>
        // rt_string_char_at`). Every `arr.at(i)` therefore fell to
        // `_ => Ok(None)` ("unhandled"). On this interpreter that surfaced
        // loudly as "method `at` not found on type `array`", but on the JIT and
        // native-LLVM lanes the same gap silently yields `nil`, which reads as
        // `None` for EVERY index -- in-range hits included, and
        // indistinguishable from a genuinely absent element. See
        // doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md.
        //
        // Note this must build an actual Option, NOT the "flat" encoding the
        // pure-Simple interpreter uses (where the bare element stands for
        // `Some`). This interpreter's pattern matcher rejects a bare `i64`
        // against `Some(v)`/`None` with "match expression exhausted", so
        // returning the element directly trades a loud missing-method error for
        // a loud missing-pattern one.
        //
        // The index is read as *signed* on purpose. The `get` arm above uses
        // `eval_arg_usize`, which cannot represent `at(-1)`; a negative index
        // must resolve to `None`, not wrap around to a huge positive one.
        "at" => {
            let idx_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            match idx_val {
                Value::Int(idx) if idx >= 0 && (idx as usize) < arr.len() => Value::some(arr[idx as usize].clone()),
                _ => Value::none(),
            }
        }
        "has" | "contains" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Value::Bool(arr.contains(&needle))
        }
        "push" | "append" => {
            let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            new_arr.push(item);
            Value::array(new_arr)
        }
        "pop" => {
            // `pop` REMOVES AND RETURNS THE LAST ELEMENT. That is the language's own
            // definition of the method, in both places that define it:
            //   * method_registry/builtins.rs — "removes and returns the last element",
            //     is_mutating: true;
            //   * hir/lower/expr/mod.rs — types `[T].pop()` as the ELEMENT type `T`
            //     (explicitly contrasted there with `push`, typed as the array).
            // The Cranelift/LLVM backends match it via `rt_array_pop`.
            //
            // Empty array yields Nil, consistent with `first`/`last`/`get` above and
            // with the identifier-lvalue path in interpreter_helpers/patterns.rs
            // (`vec.pop().unwrap_or(Value::Nil)`).
            //
            // This handler only ever sees a BORROWED slice, so it cannot write the
            // trimmed receiver back; that is each owning caller's job, and neither
            // caller reads the trimmed array off this return value:
            //   * identifier receiver — interpreter_helpers/patterns.rs mutates the
            //     binding in place via `apply_array_mutation_in_place`;
            //   * field/index/deep place — `evaluate_method_call_with_self_update`
            //     re-derives the trimmed array from the RECEIVER (it must, precisely
            //     because this result is the element, not the array).
            // A non-place receiver (`[10, 20, 30].pop()`) has nothing to write back to.
            arr.last().cloned().unwrap_or(Value::Nil)
        }
        // Bulk in-place span copy. Like `pop` above, this handler only ever sees a
        // BORROWED slice, so it cannot write the mutated receiver back: the owning
        // callers do that (identifier receiver — interpreter_helpers/patterns.rs
        // fast path; field/index/deep place — `evaluate_method_call_with_self_update`
        // re-derives the mutated array from the RECEIVER, exactly as it does for
        // `pop`). The expression result is the COUNT WRITTEN, not the array.
        // This arm still runs the copy on a clone so bounds errors surface loudly
        // even for a non-place receiver, and so the shared kernel is the single
        // source of truth for the semantics.
        "write_span" => {
            let src = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let dst_off = eval_arg(args, 1, Value::Int(-1), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(-1);
            let src_off = eval_arg(args, 2, Value::Int(-1), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(-1);
            let count = eval_arg(args, 3, Value::Int(0), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(0);
            let mut tmp = arr.to_vec();
            let written = array_write_span(&mut tmp, &src, dst_off, src_off, count)?;
            Value::Int(written)
        }
        "concat" | "extend" | "merge" => {
            let other = eval_arg(
                args,
                0,
                Value::array(vec![]),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Some(other_arr) = generic_array_values(&other) {
                let mut new_arr = arr.to_vec();
                new_arr.extend(other_arr);
                Value::array(new_arr)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("concat/extend/merge expects an array argument");
                return Err(CompileError::semantic_with_context(
                    "concat/extend/merge expects array argument",
                    ctx,
                ));
            }
        }
        "insert" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let item = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            if idx <= new_arr.len() {
                new_arr.insert(idx, item);
            }
            Value::array(new_arr)
        }
        // Returns the REMOVED ELEMENT, not the mutated array. The mutation is
        // written back to the receiver binding by the `MUTATING_METHODS` path in
        // interpreter_helpers/patterns.rs, exactly as it is for `pop`; this arm
        // only decides the EXPRESSION VALUE. Returning the post-mutation array
        // here (the previous behaviour) contradicted the sibling `pop`, the
        // sibling `Dict.remove(key)`, and mutable_by_default_spec.spl's
        // `expect removed == 2`.
        // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
        "remove" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            // Out of range is a no-op yielding Nil, mirroring `pop` on an empty
            // array. Never a panic: `remove` on an out-of-range index would
            // abort the whole interpreter.
            if idx < new_arr.len() {
                new_arr.remove(idx)
            } else {
                Value::Nil
            }
        }
        "rev" | "reverse" => {
            let mut new_arr = arr.to_vec();
            new_arr.reverse();
            Value::array(new_arr)
        }
        "slice" => {
            let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let end = args
                .get(1)
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.as_int().unwrap_or(arr.len() as i64) as usize)
                .unwrap_or(arr.len());
            let end = end.min(arr.len());
            let start = start.min(end);
            Value::array(arr[start..end].to_vec())
        }
        "map" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_map(
                arr,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "filter" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_filter(
                arr,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "merge" | "concat" => {
            let other = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            match other {
                Value::Array(other_arr) => {
                    let mut result = arr.to_vec();
                    result.extend_from_slice(&other_arr);
                    Value::array(result)
                }
                _ => {
                    return Err(CompileError::semantic("merge expects an array argument".to_string()));
                }
            }
        }
        "reduce" | "fold" => {
            let init = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let func = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_reduce(
                arr,
                init,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "find" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_find(
                arr,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "any" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_any(
                arr,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "all" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_array_all(
                arr,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "join" => {
            let sep =
                eval_arg(args, 0, Value::text(""), env, functions, classes, enums, impl_methods)?.to_display_string();
            // Byte-aware join: text-like items contribute raw bytes so
            // mid-codepoint slice fragments (Value::StrBytes) reassemble and
            // re-validate instead of being lossy-rendered to U+FFFD.
            let mut joined: Vec<u8> = Vec::new();
            for (i, v) in arr.iter().enumerate() {
                if i > 0 {
                    joined.extend_from_slice(sep.as_bytes());
                }
                match v.text_bytes_view() {
                    Some(b) => joined.extend_from_slice(b),
                    None => joined.extend_from_slice(v.to_display_string().as_bytes()),
                }
            }
            Value::text_from_bytes(joined)
        }
        "sum" => {
            let mut total: i64 = 0;
            for item in arr {
                if let Value::Int(n) = item {
                    total += n;
                }
            }
            Value::Int(total)
        }
        "index_of" => {
            let needle = args
                .first()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Nil);
            for (i, item) in arr.iter().enumerate() {
                if item == &needle {
                    return Ok(Some(Value::Int(i as i64)));
                }
            }
            Value::Int(-1)
        }
        "sort" => {
            let mut new_arr = arr.to_vec();
            new_arr.sort_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => a.cmp(b),
                (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => a.cmp(b),
                _ => std::cmp::Ordering::Equal,
            });
            Value::array(new_arr)
        }
        "sort_desc" => {
            let mut new_arr = arr.to_vec();
            new_arr.sort_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => b.cmp(a),
                (Value::Float(a), Value::Float(b)) => b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => b.cmp(a),
                _ => std::cmp::Ordering::Equal,
            });
            Value::array(new_arr)
        }
        "enumerate" => {
            let result: Vec<Value> = arr
                .iter()
                .enumerate()
                .map(|(i, v)| Value::Tuple(vec![Value::Int(i as i64), v.clone()]))
                .collect();
            Value::array(result)
        }
        "zip" => {
            let other = eval_arg(
                args,
                0,
                Value::array(vec![]),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Some(other_arr) = generic_array_values(&other) {
                let result: Vec<Value> = arr
                    .iter()
                    .zip(other_arr.iter())
                    .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()]))
                    .collect();
                Value::array(result)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("zip expects an array argument");
                return Err(CompileError::semantic_with_context("zip expects array argument", ctx));
            }
        }
        "flat_map" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mapped = eval_array_map(arr, func, functions, classes, enums, impl_methods)?;
            if let Value::Array(mapped_arr) = mapped {
                let mut result = Vec::new();
                for item in mapped_arr.iter() {
                    if let Value::Array(inner) = item {
                        result.extend(inner.iter().cloned());
                    } else {
                        result.push(item.clone());
                    }
                }
                Value::array(result)
            } else {
                Value::array(vec![])
            }
        }
        "flatten" => {
            let mut result = Vec::new();
            for item in arr {
                if let Value::Array(inner) = item {
                    result.extend(inner.iter().cloned());
                } else {
                    result.push(item.clone());
                }
            }
            Value::array(result)
        }
        "take" => {
            let n = eval_arg_usize(args, 0, arr.len(), env, functions, classes, enums, impl_methods)?;
            Value::array(arr.iter().take(n).cloned().collect())
        }
        "skip" | "drop" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Value::array(arr.iter().skip(n).cloned().collect())
        }
        "take_while" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut result = Vec::new();
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                for item in arr {
                    let mut local_env = Env::clone(&captured);
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    if !is_condition_present(&body, &pred) {
                        break;
                    }
                    result.push(item.clone());
                }
            }
            Value::array(result)
        }
        "skip_while" | "drop_while" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut result = Vec::new();
            let mut dropping = true;
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                for item in arr {
                    if dropping {
                        let mut local_env = Env::clone(&*captured);
                        if let Some(param) = params.first() {
                            local_env.insert(param.clone(), item.clone());
                        }
                        let pred = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                        if !is_condition_present(&body, &pred) {
                            dropping = false;
                            result.push(item.clone());
                        }
                    } else {
                        result.push(item.clone());
                    }
                }
            }
            Value::array(result)
        }
        "chunk" | "chunks" => {
            let size = eval_arg_usize(args, 0, 1, env, functions, classes, enums, impl_methods)?.max(1);
            let result: Vec<Value> = arr.chunks(size).map(|chunk| Value::array(chunk.to_vec())).collect();
            Value::array(result)
        }
        "uniq" | "unique" | "distinct" => {
            let mut seen = Vec::new();
            let mut result = Vec::new();
            for item in arr {
                if !seen.contains(item) {
                    seen.push(item.clone());
                    result.push(item.clone());
                }
            }
            Value::array(result)
        }
        "min" => {
            let min_val = arr.iter().min_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => a.cmp(b),
                (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => a.cmp(b),
                _ => std::cmp::Ordering::Equal,
            });
            min_val.cloned().unwrap_or(Value::Nil)
        }
        "max" => {
            let max_val = arr.iter().max_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => a.cmp(b),
                (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => a.cmp(b),
                _ => std::cmp::Ordering::Equal,
            });
            max_val.cloned().unwrap_or(Value::Nil)
        }
        "count" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                let mut count = 0i64;
                for item in arr {
                    let mut local_env = Env::clone(&captured);
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    if is_condition_present(&body, &pred) {
                        count += 1;
                    }
                }
                Value::Int(count)
            } else {
                Value::Int(arr.len() as i64)
            }
        }
        "partition" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut pass = Vec::new();
            let mut fail = Vec::new();
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                for item in arr {
                    let mut local_env = Env::clone(&captured);
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    if is_condition_present(&body, &pred) {
                        pass.push(item.clone());
                    } else {
                        fail.push(item.clone());
                    }
                }
            }
            Value::Tuple(vec![Value::array(pass), Value::array(fail)])
        }
        "group_by" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut groups: HashMap<String, Vec<Value>> = HashMap::new();
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                for item in arr {
                    let mut local_env = Env::clone(&captured);
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let key = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    let key_str = key.to_key_string();
                    groups.entry(key_str).or_default().push(item.clone());
                }
            }
            let result: HashMap<String, Value> = groups.into_iter().map(|(k, v)| (k, Value::array(v))).collect();
            Value::Dict(Arc::new(result))
        }
        "compact" => {
            // Remove nil/None values from array, unwrap Some values
            let result: Vec<Value> = arr
                .iter()
                .filter_map(|v| {
                    match v {
                        Value::Nil => None,
                        Value::Enum {
                            ref enum_name,
                            ref variant,
                            ref payload,
                        } if enum_name == "Option" => {
                            if variant == "Some" {
                                payload.as_ref().map(|p| p.as_ref().clone())
                            } else {
                                None // Option::None
                            }
                        }
                        other => Some(other.clone()),
                    }
                })
                .collect();
            Value::array(result)
        }
        "rotate" => {
            // Rotate array elements by n positions (left if positive, right if negative)
            if arr.is_empty() {
                return Ok(Some(Value::array(vec![])));
            }
            let n = eval_arg(args, 0, Value::Int(1), env, functions, classes, enums, impl_methods)?
                .as_int()
                .unwrap_or(1);
            let len = arr.len() as i64;
            let n = ((n % len) + len) % len; // Normalize to positive range
            let pivot = n as usize;
            let mut result = arr[pivot..].to_vec();
            result.extend_from_slice(&arr[..pivot]);
            Value::array(result)
        }
        "shuffle" => {
            // Randomize array order
            use rand::seq::SliceRandom;
            use rand::thread_rng;
            let mut result = arr.to_vec();
            let mut rng = thread_rng();
            result.shuffle(&mut rng);
            Value::array(result)
        }
        "sample" => {
            // Return random element(s) from array
            use rand::seq::SliceRandom;
            use rand::thread_rng;
            if arr.is_empty() {
                return Ok(Some(Value::Nil));
            }
            let n = args
                .first()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .transpose()?
                .and_then(|v| v.as_int().ok());

            let mut rng = thread_rng();
            match n {
                Some(count) if count > 0 => {
                    // Return array of n random elements
                    let sample: Vec<Value> = arr.choose_multiple(&mut rng, count as usize).cloned().collect();
                    Value::array(sample)
                }
                _ => {
                    // Return single random element
                    arr.choose(&mut rng).cloned().unwrap_or(Value::Nil)
                }
            }
        }
        "transpose" => {
            // Transpose 2D array (array of arrays)
            if arr.is_empty() {
                return Ok(Some(Value::array(vec![])));
            }

            // Check if all elements are arrays
            let inner_arrays: Vec<&[Value]> = arr
                .iter()
                .map(|v| match v {
                    Value::Array(a) => Some(a.as_slice()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("transpose requires a 2D array (array of arrays)");
                    CompileError::semantic_with_context("transpose requires array of arrays", ctx)
                })?;

            if inner_arrays.is_empty() {
                return Ok(Some(Value::array(vec![])));
            }

            // Find max length
            let max_len = inner_arrays.iter().map(|a| a.len()).max().unwrap_or(0);

            // Transpose
            let mut result = vec![vec![]; max_len];
            for inner in inner_arrays {
                for (i, val) in inner.iter().enumerate() {
                    result[i].push(val.clone());
                }
            }

            Value::array(result.into_iter().map(Value::array).collect())
        }
        "fetch" => {
            // Get element at index with default value if out of bounds
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            arr.get(idx).cloned().unwrap_or(default)
        }
        "clear" => {
            // Return empty array (functional style - original is not modified)
            Value::array(vec![])
        }
        "sorted" => {
            // Alias for sort - returns a new sorted array
            let mut new_arr = arr.to_vec();
            new_arr.sort_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => a.cmp(b),
                (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => a.cmp(b),
                _ => std::cmp::Ordering::Equal,
            });
            Value::array(new_arr)
        }
        "reversed" => {
            // Alias for reverse - returns a new reversed array
            let mut new_arr = arr.to_vec();
            new_arr.reverse();
            Value::array(new_arr)
        }
        "copy" | "clone" => {
            // Return a shallow copy of the array
            Value::array(arr.to_vec())
        }
        "all_truthy" => {
            // Check if all elements are truthy (without a predicate function)
            Value::Bool(arr.iter().all(|v| v.truthy()))
        }
        "any_truthy" => {
            // Check if any element is truthy (without a predicate function)
            Value::Bool(arr.iter().any(|v| v.truthy()))
        }
        "count_of" => {
            // Count occurrences of a specific value
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let count = arr.iter().filter(|v| *v == &needle).count();
            Value::Int(count as i64)
        }
        "fill" => {
            // Fill array with a value (returns new array of same length)
            let value = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Value::array(vec![value; arr.len()])
        }
        "ptr" | "data_ptr" => {
            // Return raw pointer to array's data as i64 (for SFFI/codegen)
            let ptr = arr.as_ptr() as i64;
            Value::Int(ptr)
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle Tuple methods
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_tuple_methods(
    tup: &[Value],
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" | "length" => Value::Int(tup.len() as i64),
        "is_empty" => Value::Bool(tup.is_empty()),
        "get" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            tup.get(idx).cloned().unwrap_or(Value::Nil)
        }
        "first" => tup.first().cloned().unwrap_or(Value::Nil),
        "last" => tup.last().cloned().unwrap_or(Value::Nil),
        "to_array" => Value::array(tup.to_vec()),
        "has" | "contains" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Value::Bool(tup.contains(&needle))
        }
        "index_of" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            for (i, item) in tup.iter().enumerate() {
                if item == &needle {
                    return Ok(Some(Value::Int(i as i64)));
                }
            }
            Value::Int(-1)
        }
        "rev" | "reverse" => {
            let mut new_tup = tup.to_vec();
            new_tup.reverse();
            Value::Tuple(new_tup)
        }
        "map" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            if let Value::Lambda {
                params,
                body,
                env: captured,
            } = func
            {
                let mut result = Vec::new();
                for item in tup {
                    let mut local_env = Env::clone(&captured);
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let mapped = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)?;
                    result.push(mapped);
                }
                Value::Tuple(result)
            } else {
                Value::Tuple(tup.to_vec())
            }
        }
        "zip" => {
            let other = eval_arg(
                args,
                0,
                Value::Tuple(vec![]),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Value::Tuple(other_tup) = other {
                let result: Vec<Value> = tup
                    .iter()
                    .zip(other_tup.iter())
                    .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()]))
                    .collect();
                Value::Tuple(result)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("zip expects a tuple argument");
                return Err(CompileError::semantic_with_context("zip expects tuple argument", ctx));
            }
        }
        "enumerate" => {
            let result: Vec<Value> = tup
                .iter()
                .enumerate()
                .map(|(i, v)| Value::Tuple(vec![Value::Int(i as i64), v.clone()]))
                .collect();
            Value::Tuple(result)
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle FrozenArray methods (read-only operations only)
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_frozen_array_methods(
    arr: &std::sync::Arc<Vec<Value>>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Reject mutation methods on frozen arrays
    match method {
        "push" | "append" | "pop" | "insert" | "remove" | "clear" | "reverse" | "sort" => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("Cannot mutate a frozen array. Use freeze() to create immutable copies.");
            return Err(CompileError::semantic_with_context(
                format!("Cannot call {}() on frozen array", method),
                ctx,
            ));
        }
        _ => {}
    }

    // Allow all read-only operations by delegating to regular array handler
    handle_array_methods(arr.as_ref(), method, args, env, functions, classes, enums, impl_methods)
}

fn repack_byte_result(value: Value, frozen: bool) -> Value {
    let Value::Array(values) = value else {
        return value;
    };
    let bytes: Option<Vec<u8>> = values
        .iter()
        .map(|value| match value {
            Value::UInt { value, .. } => u8::try_from(*value).ok(),
            Value::Int(value) => u8::try_from(*value).ok(),
            _ => None,
        })
        .collect();
    match bytes {
        Some(bytes) if frozen => Value::frozen_byte_array(bytes),
        Some(bytes) => Value::byte_array(bytes),
        None => Value::Array(values),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn handle_byte_array_methods(
    bytes: &[u8],
    frozen: bool,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if frozen
        && matches!(
            method,
            "push" | "append" | "pop" | "insert" | "remove" | "clear" | "reverse" | "sort" | "extend"
        )
    {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help("Cannot mutate a frozen byte array");
        return Err(CompileError::semantic_with_context(
            format!("Cannot call {}() on frozen byte array", method),
            ctx,
        ));
    }
    // Packed fast paths: read-only metadata ops must NOT widen the blob into
    // a Vec<Value> — one Value per byte. Font loading measures a ~1.7MB TTF
    // via per-glyph `.len()` checks; widening made each call O(n) and the
    // interpreted font path spun at 100% CPU (2.4B Value allocs in 25s —
    // see doc/08_tracking/bug/interpreter_byte_array_len_widening_spin_2026-08-13.md).
    if args.is_empty() {
        match method {
            "len" | "length" => return Ok(Some(Value::Int(bytes.len() as i64))),
            "is_empty" => return Ok(Some(Value::Bool(bytes.is_empty()))),
            _ => {}
        }
    }
    if std::env::var("SIMPLE_TRACE_BIG_BYTEARRAY").is_ok() && bytes.len() > 1_000_000 {
        eprintln!("[bigba] method={method} len={}", bytes.len());
    }
    #[cfg(test)]
    BYTE_ARRAY_WIDEN_COUNT.with(|count| count.set(count.get() + 1));
    let values = Value::byte_array_values(bytes);
    handle_array_methods(&values, method, args, env, functions, classes, enums, impl_methods)
        .map(|result| result.map(|value| repack_byte_result(value, frozen)))
}

#[cfg(test)]
mod byte_array_metadata_fast_path_tests {
    use super::super::evaluate_method_call;
    use super::*;

    fn call_value(value: Value, method: &str, args: &[Argument]) -> Result<Value, CompileError> {
        let mut env = Env::new();
        env.insert("subject".to_string(), value);
        evaluate_method_call(
            &Box::new(Expr::Identifier("subject".to_string())),
            method,
            args,
            &mut env,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &Enums::new(),
            &ImplMethods::new(),
        )
    }

    fn assert_metadata_without_widening(value: Value, expected_len: i64, expected_empty: bool) {
        for (method, expected) in [
            ("len", Value::Int(expected_len)),
            ("length", Value::Int(expected_len)),
            ("is_empty", Value::Bool(expected_empty)),
        ] {
            let (result, widen_count) = measure_byte_array_widens(|| call_value(value.clone(), method, &[]));
            assert_eq!(result.expect("metadata method"), expected);
            assert_eq!(widen_count, 0, "{method} widened packed byte storage");
        }
    }

    #[test]
    fn bytes_evidence_byte_backed_and_array_metadata_preserve_direct_semantics() {
        for bytes in [Vec::new(), vec![3, 7, 11]] {
            let expected_len = bytes.len() as i64;
            let expected_empty = bytes.is_empty();
            assert_metadata_without_widening(Value::byte_array(bytes.clone()), expected_len, expected_empty);
            assert_metadata_without_widening(Value::frozen_byte_array(bytes.clone()), expected_len, expected_empty);
            assert_metadata_without_widening(
                Value::StrBytes(std::sync::Arc::new(bytes)),
                expected_len,
                expected_empty,
            );
        }

        for values in [Vec::new(), vec![Value::Int(1), Value::Int(2)]] {
            let expected_len = values.len() as i64;
            let expected_empty = values.is_empty();
            assert_metadata_without_widening(Value::array(values.clone()), expected_len, expected_empty);
            assert_metadata_without_widening(Value::frozen_array(values), expected_len, expected_empty);
        }
    }

    #[test]
    fn bytes_evidence_byte_array_fallback_and_mutation_contracts_are_unchanged() {
        let bogus_arg = [Argument::new(None, Expr::Integer(99))];
        let (fallback, widen_count) =
            measure_byte_array_widens(|| call_value(Value::byte_array(vec![1, 2]), "len", &bogus_arg));
        assert_eq!(fallback.expect("legacy len fallback"), Value::Int(2));
        assert_eq!(
            widen_count, 1,
            "argument-bearing len incorrectly took the direct fast path"
        );

        let push = [Argument::new(None, Expr::Integer(9))];
        assert!(call_value(Value::frozen_byte_array(vec![1]), "push", &push).is_err());
        assert_eq!(
            call_value(Value::byte_array(vec![1]), "push", &push).expect("mutable push"),
            Value::byte_array(vec![1, 9])
        );
    }
}

/// Handle FixedSizeArray methods (no size-changing operations)
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_fixed_size_array_methods(
    size: usize,
    data: &[Value],
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Reject size-changing methods on fixed-size arrays
    match method {
        "push" | "append" | "pop" | "insert" | "remove" | "clear" | "extend" | "concat" => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help(format!(
                    "Fixed-size arrays have a fixed length of {}. Cannot change size with {}().",
                    size, method
                ));
            return Err(CompileError::semantic_with_context(
                format!("Cannot call {}() on fixed-size array [T; {}]", method, size),
                ctx,
            ));
        }
        _ => {}
    }

    // Allow all read-only and non-size-changing operations
    handle_array_methods(data, method, args, env, functions, classes, enums, impl_methods)
}

/// Handle FrozenDict methods (read-only operations only)
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_frozen_dict_methods(
    map: &std::sync::Arc<HashMap<String, Value>>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    // Reject mutation methods on frozen dicts
    match method {
        "insert" | "set" | "remove" | "delete" | "clear" | "update" => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("Cannot mutate a frozen dict. Use freeze() to create immutable copies.");
            return Err(CompileError::semantic_with_context(
                format!("Cannot call {}() on frozen dict", method),
                ctx,
            ));
        }
        _ => {}
    }

    // Allow all read-only operations by delegating to regular dict handler
    handle_dict_methods(map.as_ref(), method, args, env, functions, classes, enums, impl_methods)
}

/// Handle Dict methods
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_dict_methods(
    map: &HashMap<String, Value>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" | "length" => Value::Int(map.len() as i64),
        "is_empty" => Value::Bool(map.is_empty()),
        "has" | "contains_key" | "contains" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            Value::Bool(map.contains_key(&key))
        }
        "get" => {
            let key_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let key = key_val.to_key_string();
            map.get(&key)
                .cloned()
                .map(|stored| Value::unwrap_dict_entry(&key_val, stored))
                .unwrap_or(Value::Nil)
        }
        // `keys`/`values`/`entries` all iterate in the canonical sorted-by-key
        // order (`dict_entries_sorted`) so that `keys()[i]` and `values()[i]`
        // describe the SAME entry. `values` must not use `map.values()`: that
        // is raw HashMap order and would desync from the sorted `keys()`.
        "keys" => {
            let keys: Vec<Value> = crate::value::dict_entries_sorted(map)
                .into_iter()
                .map(|(k, v)| Value::dict_entry_key_for_iteration(v, k))
                .collect();
            Value::array(keys)
        }
        "values" => {
            let vals: Vec<Value> = crate::value::dict_entries_sorted(map)
                .into_iter()
                .map(|(_, v)| Value::dict_entry_value_for_iteration(v))
                .collect();
            Value::array(vals)
        }
        "set" | "insert" => {
            let key_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let key = key_val.to_key_string();
            let value = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_map = map.clone();
            new_map.insert(key, Value::wrap_dict_entry(&key_val, value));
            Value::Dict(Arc::new(new_map))
        }
        "remove" | "delete" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            let mut new_map = map.clone();
            new_map.remove(&key);
            Value::Dict(Arc::new(new_map))
        }
        "merge" | "extend" => {
            let other = eval_arg(
                args,
                0,
                Value::Dict(Arc::new(HashMap::new())),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Value::Dict(other_map) = other {
                let mut new_map = map.clone();
                new_map.extend(other_map.iter().map(|(k, v)| (k.clone(), v.clone())));
                Value::Dict(Arc::new(new_map))
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("merge expects a dict argument");
                return Err(CompileError::semantic_with_context("merge expects dict argument", ctx));
            }
        }
        "clear" => {
            // Return empty dict (functional style - original is not modified)
            Value::Dict(Arc::new(HashMap::new()))
        }
        "clone" | "copy" => {
            // Return a shallow copy of the dict
            Value::Dict(Arc::new(map.clone()))
        }
        "get_or" => {
            let key_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let key = key_val.to_key_string();
            let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            map.get(&key)
                .cloned()
                .map(|stored| Value::unwrap_dict_entry(&key_val, stored))
                .unwrap_or(default)
        }
        "entries" | "items" => {
            let entries: Vec<Value> = crate::value::dict_entries_sorted(map)
                .into_iter()
                .map(|(k, v)| {
                    Value::Tuple(vec![
                        Value::dict_entry_key_for_iteration(v, k),
                        Value::dict_entry_value_for_iteration(v),
                    ])
                })
                .collect();
            Value::array(entries)
        }
        "map_values" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_dict_map_values(
                map,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        // `Map<K, V>` lowers to the builtin dict, so `map.for_each(\k, v: ...)`
        // has to land here; before this arm existed it failed with
        // "method `for_each` not found on type `dict`" while the array form
        // worked. `each` is accepted as the alias, matching the array arm in
        // codegen/llvm/functions.rs.
        "for_each" | "each" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_dict_for_each(
                map,
                func,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "filter" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            return Ok(Some(eval_dict_filter(
                map,
                func,
                functions,
                classes,
                enums,
                impl_methods,
            )?));
        }
        "compact" => {
            // Remove nil/None entries, unwrap Some values
            let result: HashMap<String, Value> = map
                .iter()
                .filter_map(|(k, v)| match v {
                    Value::Nil => None,
                    Value::Enum {
                        ref enum_name,
                        ref variant,
                        ref payload,
                    } if enum_name == "Option" => {
                        if variant == "Some" {
                            payload.as_ref().map(|p| (k.clone(), p.as_ref().clone()))
                        } else {
                            None
                        }
                    }
                    other => Some((k.clone(), other.clone())),
                })
                .collect();
            Value::Dict(Arc::new(result))
        }
        "fetch" => {
            // Get value at key, or default if not present
            let key_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let key = key_val.to_key_string();
            let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            map.get(&key)
                .cloned()
                .map(|stored| Value::unwrap_dict_entry(&key_val, stored))
                .unwrap_or(default)
        }
        "setdefault" => {
            // Get value if key exists, otherwise set and return default
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_map = map.clone();
            let value = new_map.entry(key).or_insert(default.clone()).clone();
            // Return tuple of [value, new_dict]
            Value::Tuple(vec![value, Value::Dict(Arc::new(new_map))])
        }
        "dig" => {
            // Navigate nested structures safely
            // dig("key1", "key2", "key3") -> dict["key1"]["key2"]["key3"]
            let mut current: Value = Value::Dict(Arc::new(map.clone()));

            for arg in args {
                let key = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                current = match &current {
                    Value::Dict(m) => m
                        .get(&key.to_key_string())
                        .cloned()
                        .map(|stored| Value::unwrap_dict_entry(&key, stored))
                        .unwrap_or(Value::Nil),
                    Value::Array(a) => {
                        if let Ok(idx) = key.as_int() {
                            a.get(idx as usize).cloned().unwrap_or(Value::Nil)
                        } else {
                            Value::Nil
                        }
                    }
                    _ => Value::Nil,
                };

                // Stop if we hit nil
                if matches!(current, Value::Nil) {
                    break;
                }
            }

            current
        }
        _ => {
            // Check if the dict contains a callable value at this key (module-style calls)
            if let Some(value) = map.get(method) {
                match value {
                    Value::Function { def, captured_env, .. } => {
                        // Call the function with the provided arguments
                        // Use the caller's env for evaluating arguments, but merge with captured_env for the function body
                        let mut merged_env = Env::clone(captured_env);
                        merged_env.extend(env.clone());
                        let result = exec_function(
                            def,
                            args,
                            &mut merged_env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            None,
                        )?;
                        return Ok(Some(result));
                    }
                    Value::Lambda {
                        params,
                        body,
                        env: captured,
                    } => {
                        // Call the lambda
                        let mut local_env = Env::clone(captured);
                        for (i, param) in params.iter().enumerate() {
                            let arg_val = eval_arg(args, i, Value::Nil, env, functions, classes, enums, impl_methods)?;
                            local_env.insert(param.clone(), arg_val);
                        }
                        let result = evaluate_expr(body, &mut local_env, functions, classes, enums, impl_methods)?;
                        return Ok(Some(result));
                    }
                    Value::Constructor { class_name } => {
                        // Instantiate the class
                        let result = instantiate_class(class_name, args, env, functions, classes, enums, impl_methods)?;
                        return Ok(Some(result));
                    }
                    _ => return Ok(None),
                }
            }
            return Ok(None);
        }
    };
    Ok(Some(result))
}

// Lane C10 regression coverage: take_while/skip_while/count/partition lambda
// predicates must trust `.?`'s own presence decision instead of re-testing
// the unwrapped payload's truthiness. See
// doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md
// ("Known follow-up") and N2's `is_condition_present` (interpreter_control.rs).
#[cfg(test)]
mod is_condition_present_tests {
    use super::*;

    fn exists_check_cond() -> Expr {
        Expr::ExistsCheck(Box::new(Expr::Identifier("x".to_string())))
    }

    #[test]
    fn trusts_exists_check_presence_for_falsy_payload() {
        let cond = exists_check_cond();
        assert!(is_condition_present(&cond, &Value::Int(0)));
        assert!(is_condition_present(&cond, &Value::Bool(false)));
    }

    #[test]
    fn trusts_exists_check_absence_for_nil() {
        let cond = exists_check_cond();
        assert!(!is_condition_present(&cond, &Value::Nil));
    }

    #[test]
    fn falls_back_to_generic_truthy_for_non_exists_check() {
        let cond = Expr::Integer(0);
        assert!(!is_condition_present(&cond, &Value::Int(0)));
        assert!(is_condition_present(&cond, &Value::Int(1)));
    }
}
