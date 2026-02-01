use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::Expr;

use super::evaluate_expr;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

use super::super::{
    comprehension_iterate, create_range_object_opt, normalize_index, slice_collection, ClassDef, Enums, Env,
    FunctionDef, ImplMethods,
};

/// Compute slice indices from start, end, length, and inclusive flag.
/// Handles negative indices (counted from end) and bounds clamping.
fn compute_slice_indices(start: i64, end: Option<i64>, len: i64, inclusive: bool) -> (usize, usize) {
    let start_idx = if start < 0 {
        (len + start).max(0) as usize
    } else {
        start as usize
    };
    let end_idx = match end {
        Some(e) => {
            let e = if e < 0 { (len + e).max(0) as i64 } else { e };
            if inclusive {
                (e + 1).min(len) as usize
            } else {
                e.min(len) as usize
            }
        }
        None => len as usize,
    };
    (start_idx, end_idx)
}

pub(super) fn eval_collection_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::StructInit { name, fields } => {
            let mut map = HashMap::new();
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
            // Strip module prefix from class name (e.g., "dt.Duration" -> "Duration")
            // This ensures method lookup works correctly for imported types
            let class_name = name.rsplit('.').next().unwrap_or(name).to_string();
            Ok(Some(Value::Object {
                class: class_name,
                fields: Arc::new(map),
            }))
        }
        Expr::Path(segments) => {
            let result = if segments.len() == 2 {
                let enum_name = &segments[0];
                let variant = &segments[1];
                if let Some(enum_def) = enums.get(enum_name) {
                    if enum_def.variants.iter().any(|v| &v.name == variant) {
                        Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: variant.clone(),
                            payload: None,
                        })
                    } else {
                        let ctx = ErrorContext::new().with_code(codes::INVALID_PATTERN).with_help(format!(
                            "check that '{}' is a valid variant of enum '{}'",
                            variant, enum_name
                        ));
                        Err(CompileError::semantic_with_context(
                            format!("invalid pattern: unknown variant {} for enum {}", variant, enum_name),
                            ctx,
                        ))
                    }
                } else if let Some(func) = functions.get(variant).cloned() {
                    Ok(Value::Function {
                        name: variant.clone(),
                        def: Box::new(func.clone()),
                        captured_env: Env::new(),
                    })
                } else if classes.contains_key(variant) {
                    Ok(Value::Constructor {
                        class_name: variant.clone(),
                    })
                } else {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("path must reference a valid enum variant, function, or class");
                    Err(CompileError::semantic_with_context(
                        format!("invalid operation: unknown path {}::{}", segments[0], variant),
                        ctx,
                    ))
                }
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("path expressions must have exactly 2 segments (Type::Variant)");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: unsupported path: {:?}", segments),
                    ctx,
                ))
            };
            Ok(Some(result?))
        }
        Expr::Dict(entries) => {
            let mut map = HashMap::new();
            for (k, v) in entries {
                // Handle dict spread: **expr
                if let Expr::DictSpread(inner) = k {
                    let spread_val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(spread_map) = spread_val {
                        for (sk, sv) in spread_map {
                            map.insert(sk, sv);
                        }
                    } else {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("dict spread operator (**) can only be used with dict values");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "type mismatch: dict spread requires dict value, got {}",
                                spread_val.type_name()
                            ),
                            ctx,
                        ));
                    }
                } else {
                    let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                    let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                    map.insert(key_val.to_key_string(), val);
                }
            }
            Ok(Some(Value::Dict(map)))
        }
        Expr::Range { start, end, bound } => {
            let start_val = start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.as_int())
                .transpose()?;

            let end_val = end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()?
                .map(|v| v.as_int())
                .transpose()?;

            Ok(Some(create_range_object_opt(start_val, end_val, *bound)))
        }
        Expr::Array(items) => {
            let mut arr = Vec::new();
            for item in items {
                // Handle spread operator: *expr
                if let Expr::Spread(inner) = item {
                    let spread_val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    match spread_val {
                        Value::Array(spread_arr) => arr.extend(spread_arr),
                        Value::Tuple(tup) => arr.extend(tup),
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("spread operator (*) can only be used with array or tuple values");
                            return Err(CompileError::semantic_with_context(
                                format!(
                                    "invalid operation: spread operator requires array or tuple, got {}",
                                    spread_val.type_name()
                                ),
                                ctx,
                            ));
                        }
                    }
                } else {
                    arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
                }
            }
            Ok(Some(Value::Array(arr)))
        }
        // Vec literals are treated as arrays at runtime
        Expr::VecLiteral(items) => {
            let mut arr = Vec::new();
            for item in items {
                arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Some(Value::Array(arr)))
        }
        Expr::ArrayRepeat { value, count } => {
            // Evaluate the count first
            let count_val = evaluate_expr(count, env, functions, classes, enums, impl_methods)?;
            let count_int = match count_val {
                Value::Int(n) => n,
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("array repeat count must be an integer");
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "type mismatch: array repeat count must be an integer, got {}",
                            count_val.type_name()
                        ),
                        ctx,
                    ));
                }
            };
            if count_int < 0 {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("array repeat count must be non-negative");
                return Err(CompileError::semantic_with_context(
                    format!(
                        "invalid operation: array repeat count cannot be negative (got {})",
                        count_int
                    ),
                    ctx,
                ));
            }
            // Evaluate the value once and clone it
            let val = evaluate_expr(value, env, functions, classes, enums, impl_methods)?;
            let arr: Vec<Value> = std::iter::repeat(val).take(count_int as usize).collect();
            Ok(Some(Value::Array(arr)))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Some(Value::Tuple(tup)))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;

            // Check if idx_val is a range object for slicing
            if let Value::Object { class, fields } = &idx_val {
                if class == crate::value::BUILTIN_RANGE {
                    // Extract range bounds
                    let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
                    let end = fields.get("end").and_then(|v| v.as_int().ok());
                    let inclusive = fields
                        .get("inclusive")
                        .and_then(|v| if let Value::Bool(b) = v { Some(*b) } else { None })
                        .unwrap_or(false);

                    return Ok(Some(match recv_val {
                        Value::Array(arr) => {
                            let len = arr.len() as i64;
                            let (start_idx, end_idx) = compute_slice_indices(start, end, len, inclusive);
                            let sliced: Vec<Value> = arr
                                .get(start_idx..end_idx.min(arr.len()))
                                .map(|s| s.to_vec())
                                .unwrap_or_default();
                            Ok(Value::Array(sliced))
                        }
                        Value::Str(s) => {
                            let chars: Vec<char> = s.chars().collect();
                            let len = chars.len() as i64;
                            let (start_idx, end_idx) = compute_slice_indices(start, end, len, inclusive);
                            let sliced: String = chars
                                .get(start_idx..end_idx.min(chars.len()))
                                .map(|s| s.iter().collect())
                                .unwrap_or_default();
                            Ok(Value::Str(sliced))
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("slicing is only supported on arrays, tuples, and strings");
                            Err(CompileError::semantic_with_context(
                                format!("invalid operation: cannot slice value of type {}", recv_val.type_name()),
                                ctx,
                            ))
                        }
                    }?));
                }
            }

            let result = match recv_val {
                Value::Array(arr) => {
                    // E1043 - Invalid Index Type
                    let raw_idx = idx_val.as_int().map_err(|_| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_INDEX_TYPE)
                            .with_help("array indices must be integers");
                        CompileError::semantic_with_context(
                            format!("cannot index array with type `{}`", idx_val.type_name()),
                            ctx,
                        )
                    })?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx).cloned().ok_or_else(|| {
                        // E3002 - Index Out Of Bounds
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help(format!("array has {} element(s)", len))
                            .with_note("ensure the index is within bounds");
                        CompileError::semantic_with_context(
                            format!("array index out of bounds: index is {} but length is {}", raw_idx, len),
                            ctx,
                        )
                    })
                }
                Value::Tuple(tup) => {
                    // E1043 - Invalid Index Type
                    let raw_idx = idx_val.as_int().map_err(|_| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_INDEX_TYPE)
                            .with_help("tuple indices must be integers");
                        CompileError::semantic_with_context(
                            format!("cannot index tuple with type `{}`", idx_val.type_name()),
                            ctx,
                        )
                    })?;
                    let len = tup.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    tup.get(idx).cloned().ok_or_else(|| {
                        // E3002 - Index Out Of Bounds
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help(format!("tuple has {} element(s)", len))
                            .with_note("ensure the index is within bounds");
                        CompileError::semantic_with_context(
                            format!("tuple index out of bounds: index is {} but length is {}", raw_idx, len),
                            ctx,
                        )
                    })
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    // Return nil for missing keys instead of erroring
                    Ok(map.get(&key).cloned().unwrap_or(Value::Nil))
                }
                Value::Str(s) => {
                    // E1043 - Invalid Index Type
                    let raw_idx = idx_val.as_int().map_err(|_| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_INDEX_TYPE)
                            .with_help("string indices must be integers");
                        CompileError::semantic_with_context(
                            format!("cannot index string with type `{}`", idx_val.type_name()),
                            ctx,
                        )
                    })?;
                    // Fast path: if string is ASCII-only, use byte indexing O(1)
                    // instead of chars().nth() which is O(n)
                    if s.is_ascii() {
                        let len = s.len() as i64;
                        let idx = if raw_idx < 0 {
                            (len + raw_idx) as usize
                        } else {
                            raw_idx as usize
                        };
                        if idx < s.len() {
                            Ok(Value::Str(String::from(s.as_bytes()[idx] as char)))
                        } else {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                .with_help(format!("string has {} character(s)", len))
                                .with_note("ensure the index is within bounds");
                            Err(CompileError::semantic_with_context(
                                format!("string index out of bounds: index is {} but length is {}", raw_idx, len),
                                ctx,
                            ))
                        }
                    } else {
                        let len = s.chars().count() as i64;
                        // Support negative indexing
                        let idx = if raw_idx < 0 {
                            (len + raw_idx) as usize
                        } else {
                            raw_idx as usize
                        };
                        s.chars().nth(idx).map(|c| Value::Str(c.to_string())).ok_or_else(|| {
                            // E3002 - Index Out Of Bounds
                            let ctx = ErrorContext::new()
                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                .with_help(format!("string has {} character(s)", len))
                                .with_note("ensure the index is within bounds");
                            CompileError::semantic_with_context(
                                format!("string index out of bounds: index is {} but length is {}", raw_idx, len),
                                ctx,
                            )
                        })
                    }
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields.get(&key).cloned().ok_or_else(|| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help("ensure the field exists in the object before accessing it");
                        CompileError::semantic_with_context(
                            format!("index out of bounds: field not found: {}", key),
                            ctx,
                        )
                    })
                }
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("index access is only supported on arrays, tuples, dicts, and strings");
                    Err(CompileError::semantic_with_context(
                        format!("invalid operation: cannot index value of type {}", recv_val.type_name()),
                        ctx,
                    ))
                }
            };
            Ok(Some(result?))
        }
        Expr::TupleIndex { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let result = match recv_val {
                Value::Tuple(tup) => tup.get(*index).cloned().ok_or_else(|| {
                    // E1044 - Tuple Index OOB
                    let ctx = ErrorContext::new()
                        .with_code(codes::TUPLE_INDEX_OOB)
                        .with_note(format!("tuple has {} element(s)", tup.len()))
                        .with_help("ensure the index is within bounds");
                    CompileError::semantic_with_context(
                        format!(
                            "tuple index out of bounds: index is {} but length is {}",
                            index,
                            tup.len()
                        ),
                        ctx,
                    )
                }),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("tuple indexing is only supported on tuple values");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: tuple index access on non-tuple type {}",
                            recv_val.type_name()
                        ),
                        ctx,
                    ))
                }
            };
            Ok(Some(result?))
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let envs = comprehension_iterate(
                &iter_val,
                pattern,
                condition,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            let mut result = Vec::new();
            for mut inner_env in envs {
                let val = evaluate_expr(expr, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.push(val);
            }
            Ok(Some(Value::Array(result)))
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let envs = comprehension_iterate(
                &iter_val,
                pattern,
                condition,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            let mut result = HashMap::new();
            for mut inner_env in envs {
                let k = evaluate_expr(key, &mut inner_env, functions, classes, enums, impl_methods)?;
                let v = evaluate_expr(value, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.insert(k.to_key_string(), v);
            }
            Ok(Some(Value::Dict(result)))
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let len = match &recv_val {
                Value::Array(arr) => arr.len() as i64,
                Value::Str(s) => s.len() as i64,
                Value::Tuple(t) => t.len() as i64,
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("slicing with step is only supported on arrays, tuples, and strings");
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: cannot slice value of type {} with step",
                            recv_val.type_name()
                        ),
                        ctx,
                    ));
                }
            };

            // Parse start, end, step with Python-style semantics
            let start_idx = if let Some(s) = start {
                let v = evaluate_expr(s, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                0
            };

            let end_idx = if let Some(e) = end {
                let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                len
            };

            let step_val = if let Some(st) = step {
                evaluate_expr(st, env, functions, classes, enums, impl_methods)?.as_int()?
            } else {
                1
            };

            if step_val == 0 {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("slice step must be non-zero");
                return Err(CompileError::semantic_with_context(
                    "invalid operation: slice step cannot be zero".to_string(),
                    ctx,
                ));
            }

            let result = match recv_val {
                Value::Array(arr) => Ok(Value::array(slice_collection(&arr, start_idx, end_idx, step_val))),
                Value::Str(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    let sliced = slice_collection(&chars, start_idx, end_idx, step_val);
                    Ok(Value::Str(sliced.into_iter().collect()))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(&tup, start_idx, end_idx, step_val))),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("slicing with step is only supported on arrays, tuples, and strings");
                    Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: cannot slice value of type {} with step",
                            recv_val.type_name()
                        ),
                        ctx,
                    ))
                }
            };
            Ok(Some(result?))
        }
        Expr::Spread(inner) => {
            // Spread is handled by Array/Dict evaluation, but standalone should work too
            Ok(Some(evaluate_expr(
                inner,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?))
        }
        Expr::DictSpread(inner) => {
            // DictSpread is handled by Dict evaluation
            Ok(Some(evaluate_expr(
                inner,
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
