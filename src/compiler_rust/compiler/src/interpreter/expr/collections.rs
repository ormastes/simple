use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::Expr;

use super::{evaluate_expr, try_unwrap_option_or_result};
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
            let e = if e < 0 { (len + e).max(0) } else { e };
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

fn require_integer_index_value(value: &Value, context: &str) -> Result<i64, CompileError> {
    match value {
        Value::Int(i) => return Ok(*i),
        Value::UInt { value: u, .. } => {
            return i64::try_from(*u).map_err(|_| {
                let help = match context {
                    "array" | "frozen array" | "fixed-size array" | "tuple" | "string" => {
                        format!("{context} indices must fit in signed 64-bit range")
                    }
                    "slice start" | "slice end" | "slice step" => {
                        format!("{context} must fit in signed 64-bit range")
                    }
                    _ => format!("{context} must fit in signed 64-bit range"),
                };
                let ctx = ErrorContext::new().with_code(codes::INVALID_INDEX_TYPE).with_help(help);
                CompileError::semantic_with_context(
                    format!("cannot index {context} with value `{}`", value.type_name()),
                    ctx,
                )
            });
        }
        _ => {}
    }

    let help = match context {
        "array" | "frozen array" | "fixed-size array" | "tuple" | "string" => {
            format!("{context} indices must be integers")
        }
        "slice start" | "slice end" | "slice step" => format!("{context} must be an integer"),
        _ => format!("{context} must be an integer"),
    };

    let message = match context {
        "array" | "frozen array" | "fixed-size array" | "tuple" | "string" => {
            format!("cannot index {context} with type `{}`", value.type_name())
        }
        "slice start" | "slice end" | "slice step" => {
            format!("type mismatch: {context} must be int, got {}", value.type_name())
        }
        _ => format!("type mismatch: {context} must be int, got {}", value.type_name()),
    };

    let ctx = ErrorContext::new().with_code(codes::INVALID_INDEX_TYPE).with_help(help);
    Err(CompileError::semantic_with_context(message, ctx))
}

fn string_index_out_of_bounds(s: &str, raw_idx: i64, len: i64) -> CompileError {
    let preview: String = s.chars().take(60).collect::<String>().replace('\n', "\\n");
    let ctx = ErrorContext::new()
        .with_code(codes::INDEX_OUT_OF_BOUNDS)
        .with_help(format!("string has {} character(s); preview={:?}", len, preview))
        .with_note("ensure the index is within bounds");
    CompileError::semantic_with_context(
        format!(
            "string index out of bounds: index is {} but length is {} (preview={:?})",
            raw_idx, len, preview
        ),
        ctx,
    )
}

fn indexed_string_char(s: &str, raw_idx: i64) -> Result<Value, CompileError> {
    if s.is_ascii() {
        let len = s.len() as i64;
        let idx = if raw_idx < 0 { len + raw_idx } else { raw_idx };
        if (0..len).contains(&idx) {
            return Ok(Value::text(String::from(s.as_bytes()[idx as usize] as char)));
        }
        return Err(string_index_out_of_bounds(s, raw_idx, len));
    }

    if raw_idx >= 0 {
        if let Some(c) = s.chars().nth(raw_idx as usize) {
            return Ok(Value::text(c.to_string()));
        }
        let len = s.chars().count() as i64;
        return Err(string_index_out_of_bounds(s, raw_idx, len));
    }

    let len = s.chars().count() as i64;
    let idx = len + raw_idx;
    if (0..len).contains(&idx) {
        return Ok(Value::text(
            s.chars()
                .nth(idx as usize)
                .expect("bounds checked string character index")
                .to_string(),
        ));
    }
    Err(string_index_out_of_bounds(s, raw_idx, len))
}

pub(super) fn eval_collection_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::StructInit { name, fields, spread } => {
            let mut map = HashMap::new();

            // Strip module prefix from class name (e.g., "dt.Duration" -> "Duration")
            // This ensures method lookup works correctly for imported types
            let class_name = name.rsplit('.').next().unwrap_or(name).to_string();

            // Pre-fill every declared field with its `= default` expression (or nil
            // when no default is given), matching paren-form construction
            // (instantiate_class in interpreter_call/core/class_instantiation.rs).
            // Without this, brace-form init omits fields entirely when the
            // literal doesn't mention them, so later `.field` access fails with
            // "class has no field named X" instead of yielding nil.
            if let Some(class_def) = classes.get(&class_name).cloned() {
                for field in &class_def.fields {
                    let val = if let Some(default_expr) = &field.default {
                        evaluate_expr(default_expr, env, functions, classes, enums, impl_methods)?
                    } else {
                        Value::Nil
                    };
                    map.insert(field.name.clone(), val);
                }
            }

            // If there's a spread expression, evaluate it first to get the base struct
            if let Some(spread_expr) = spread {
                let base_val = evaluate_expr(spread_expr, env, functions, classes, enums, impl_methods)?;
                match &base_val {
                    Value::Object {
                        fields: base_fields, ..
                    } => {
                        // Copy all fields from the base struct
                        for (k, v) in base_fields.as_ref() {
                            map.insert(k.clone(), v.clone());
                        }
                    }
                    Value::Dict(base_map) => {
                        // Also support dicts as spread base
                        for (k, v) in base_map.iter() {
                            map.insert(k.clone(), v.clone());
                        }
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("struct spread (..) requires an object or dict value as base");
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "type mismatch: struct spread requires object or dict, got {}",
                                base_val.type_name()
                            ),
                            ctx,
                        ));
                    }
                }
            }

            // Explicit fields override spread fields
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
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
                        def: func,
                        captured_env: Arc::new(Env::new()),
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
                        for (sk, sv) in spread_map.iter() {
                            map.insert(sk.clone(), sv.clone());
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
                    map.insert(key_val.to_key_string(), Value::wrap_dict_entry(&key_val, val));
                }
            }
            Ok(Some(Value::Dict(Arc::new(map))))
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
                        Value::Array(spread_arr) => arr.extend(spread_arr.iter().cloned()),
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
            Ok(Some(Value::array(arr)))
        }
        // Vec literals are treated as arrays at runtime
        Expr::VecLiteral(items) => {
            let mut arr = Vec::new();
            for item in items {
                arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Some(Value::array(arr)))
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
            let arr: Vec<Value> = std::iter::repeat_n(val, count_int as usize).collect();
            Ok(Some(Value::array(arr)))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Some(Value::Tuple(tup)))
        }
        Expr::LabeledTuple(fields) => {
            let mut labels = Vec::new();
            let mut values = Vec::new();
            for field in fields {
                labels.push(field.label.clone());
                values.push(evaluate_expr(
                    &field.value,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?);
            }
            Ok(Some(Value::LabeledTuple { labels, values }))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            // Flow-sensitive nil checks narrow `T?` at compile time, but the
            // interpreter still carries the runtime Option wrapper.  Keep
            // indexing aligned with field/method access by consuming a present
            // Option/Result payload before dispatching on the collection kind.
            let recv_val = try_unwrap_option_or_result(&recv_val).unwrap_or(recv_val);
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
                            Ok(Value::array(sliced))
                        }
                        Value::ByteArray(bytes) => {
                            let len = bytes.len() as i64;
                            let (start_idx, end_idx) = compute_slice_indices(start, end, len, inclusive);
                            let sliced = bytes
                                .get(start_idx..end_idx.min(bytes.len()))
                                .map(<[u8]>::to_vec)
                                .unwrap_or_default();
                            Ok(Value::byte_array(sliced))
                        }
                        Value::FrozenByteArray(bytes) => {
                            let len = bytes.len() as i64;
                            let (start_idx, end_idx) = compute_slice_indices(start, end, len, inclusive);
                            let sliced = bytes
                                .get(start_idx..end_idx.min(bytes.len()))
                                .map(<[u8]>::to_vec)
                                .unwrap_or_default();
                            Ok(Value::frozen_byte_array(sliced))
                        }
                        Value::Str(s) => {
                            // BYTE-indexed, matching the native lane (`rt_slice`
                            // slices `s->data` raw bytes), the byte-indexed
                            // `.slice()`/`.substring()` methods, and the
                            // Expr::Slice path below. Indexing by CHARACTER here
                            // silently corrupted every byte-offset slice on
                            // multi-byte text — the engine divergence behind
                            // doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md
                            // (glob `_glob_at` false negatives, js `string_charAt`
                            // returning empty for CJK under `bin/simple test`'s
                            // forced SIMPLE_EXECUTION_MODE=interpret).
                            let bytes = s.as_bytes();
                            let len = bytes.len() as i64;
                            let (start_idx, end_idx) = compute_slice_indices(start, end, len, inclusive);
                            // A range that splits a multi-byte codepoint cannot
                            // be held in a Rust String; preserve the RAW bytes
                            // (Value::StrBytes) so reassembly re-validates —
                            // U+FFFD substitution here shredded every 1-unit
                            // slice walk (json/toml tokenizers) because the
                            // original byte was unrecoverable at concat time.
                            let sliced: Vec<u8> = bytes
                                .get(start_idx..end_idx.min(bytes.len()))
                                .map(|b| b.to_vec())
                                .unwrap_or_default();
                            Ok(Value::text_from_bytes(sliced))
                        }
                        Value::Object {
                            ref class, ref fields, ..
                        } => {
                            // Try __getitem__ for slice on Objects
                            let getitem_method = classes
                                .get(class.as_str())
                                .and_then(|cd| cd.methods.iter().find(|m| m.name == "__getitem__").cloned())
                                .map(Arc::new)
                                .or_else(|| {
                                    impl_methods
                                        .get(class.as_str())
                                        .and_then(|ms| ms.iter().find(|m| m.name == "__getitem__").cloned())
                                });
                            if let Some(method) = getitem_method {
                                let self_ctx = Some((class.as_str(), fields));
                                super::super::interpreter_call::exec_function_with_values_and_self(
                                    &method,
                                    std::slice::from_ref(&idx_val),
                                    env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                    self_ctx,
                                )
                            } else {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::INVALID_OPERATION)
                                    .with_help("slicing is only supported on arrays, tuples, strings, and objects with __getitem__");
                                Err(CompileError::semantic_with_context(
                                    format!("invalid operation: cannot slice value of type {}", recv_val.type_name()),
                                    ctx,
                                ))
                            }
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
                    let raw_idx = require_integer_index_value(&idx_val, "array")?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx).cloned().ok_or_else(|| {
                        // E3002 - Index Out Of Bounds
                        if std::env::var("SIMPLE_INTERP_OOB_DEBUG").is_ok() {
                            let recv_dbg = format!("{:?}", receiver);
                            let idx_dbg = format!("{:?}", index);
                            eprintln!(
                                "[oob-debug] recv={} idx={}\n[oob-debug-bt] {}",
                                &recv_dbg[..recv_dbg.len().min(400)],
                                &idx_dbg[..idx_dbg.len().min(400)],
                                std::backtrace::Backtrace::force_capture()
                            );
                        }
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
                Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => {
                    let raw_idx = require_integer_index_value(&idx_val, "byte array")?;
                    let len = bytes.len() as i64;
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    bytes
                        .get(idx)
                        .map(|byte| Value::UInt {
                            value: u64::from(*byte),
                            width: 8,
                        })
                        .ok_or_else(|| {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INDEX_OUT_OF_BOUNDS)
                                .with_help(format!("byte array has {} element(s)", len));
                            CompileError::semantic_with_context(
                                format!("array index out of bounds: index is {} but length is {}", raw_idx, len),
                                ctx,
                            )
                        })
                }
                Value::FrozenArray(arr) => {
                    let raw_idx = require_integer_index_value(&idx_val, "frozen array")?;
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
                            .with_help(format!("frozen array has {} element(s)", len))
                            .with_note("ensure the index is within bounds");
                        CompileError::semantic_with_context(
                            format!("array index out of bounds: index is {} but length is {}", raw_idx, len),
                            ctx,
                        )
                    })
                }
                Value::FixedSizeArray { size, data } => {
                    let raw_idx = require_integer_index_value(&idx_val, "fixed-size array")?;
                    let len = size as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    data.get(idx).cloned().ok_or_else(|| {
                        // E3002 - Index Out Of Bounds
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help(format!("fixed-size array has {} element(s)", size))
                            .with_note("ensure the index is within bounds");
                        CompileError::semantic_with_context(
                            format!("array index out of bounds: index is {} but length is {}", raw_idx, size),
                            ctx,
                        )
                    })
                }
                Value::Tuple(tup) => {
                    let raw_idx = require_integer_index_value(&idx_val, "tuple")?;
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
                Value::LabeledTuple { values, .. } => {
                    let raw_idx = require_integer_index_value(&idx_val, "tuple")?;
                    let len = values.len() as i64;
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    values.get(idx).cloned().ok_or_else(|| {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INDEX_OUT_OF_BOUNDS)
                            .with_help(format!("tuple has {} element(s)", values.len()))
                            .with_note("ensure the index is within bounds");
                        CompileError::semantic_with_context(
                            format!(
                                "tuple index out of bounds: index is {} but length is {}",
                                raw_idx,
                                values.len()
                            ),
                            ctx,
                        )
                    })
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    // Return nil for missing keys instead of erroring
                    Ok(map
                        .get(&key)
                        .cloned()
                        .map(|stored| Value::unwrap_dict_entry(&idx_val, stored))
                        .unwrap_or(Value::Nil))
                }
                Value::FrozenDict(map) => {
                    let key = idx_val.to_key_string();
                    // Return nil for missing keys instead of erroring
                    Ok(map
                        .get(&key)
                        .cloned()
                        .map(|stored| Value::unwrap_dict_entry(&idx_val, stored))
                        .unwrap_or(Value::Nil))
                }
                Value::Str(s) => {
                    let raw_idx = require_integer_index_value(&idx_val, "string")?;
                    indexed_string_char(&s, raw_idx)
                }
                // A `StrBytes` is a text value whose bytes are not valid UTF-8 —
                // it is produced by `Value::text_from_bytes` whenever a byte
                // slice lands mid-codepoint (see value_impl.rs). It is still a
                // string as far as the language is concerned (`type_name()`
                // reports "str"), so indexing it MUST work; falling through to
                // the catch-all below produced the nonsensical
                // "cannot index value of type str" abort. Index it by BYTE, to
                // match the byte-transparent slice path that created it.
                Value::StrBytes(bytes) => {
                    let raw_idx = require_integer_index_value(&idx_val, "string")?;
                    let len = bytes.len() as i64;
                    let idx = if raw_idx < 0 { len + raw_idx } else { raw_idx };
                    if (0..len).contains(&idx) {
                        Ok(Value::text_from_bytes(vec![bytes[idx as usize]]))
                    } else {
                        Err(string_index_out_of_bounds(
                            &String::from_utf8_lossy(&bytes),
                            raw_idx,
                            len,
                        ))
                    }
                }
                Value::Object {
                    ref class, ref fields, ..
                } => {
                    // Try __getitem__ method first (operator overloading)
                    let getitem_method = classes
                        .get(class.as_str())
                        .and_then(|cd| cd.methods.iter().find(|m| m.name == "__getitem__").cloned())
                        .map(Arc::new)
                        .or_else(|| {
                            impl_methods
                                .get(class.as_str())
                                .and_then(|ms| ms.iter().find(|m| m.name == "__getitem__").cloned())
                        });
                    if let Some(method) = getitem_method {
                        let self_ctx = Some((class.as_str(), fields));
                        super::super::interpreter_call::exec_function_with_values_and_self(
                            &method,
                            std::slice::from_ref(&idx_val),
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            self_ctx,
                        )
                    } else {
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
            // Keep positional tuple access in parity with ordinary Index: an
            // Option<Tuple>/Result<Tuple> which has been flow-narrowed still
            // carries its Some/Ok wrapper in the interpreter value.
            let recv_val = try_unwrap_option_or_result(&recv_val).unwrap_or(recv_val);
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
                Value::LabeledTuple { values, .. } => values.get(*index).cloned().ok_or_else(|| {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TUPLE_INDEX_OOB)
                        .with_note(format!("tuple has {} element(s)", values.len()))
                        .with_help("ensure the index is within bounds");
                    CompileError::semantic_with_context(
                        format!(
                            "tuple index out of bounds: index is {} but length is {}",
                            index,
                            values.len()
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
            Ok(Some(Value::array(result)))
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
                result.insert(k.to_key_string(), Value::wrap_dict_entry(&k, v));
            }
            Ok(Some(Value::Dict(Arc::new(result))))
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
                Value::ByteArray(arr) | Value::FrozenByteArray(arr) => arr.len() as i64,
                Value::Str(s) => s.len() as i64,
                Value::Tuple(t) => t.len() as i64,
                Value::LabeledTuple { values, .. } => values.len() as i64,
                Value::Object {
                    ref class, ref fields, ..
                } => {
                    // Try __getslice__ method for slicing
                    let getslice_method = classes
                        .get(class.as_str())
                        .and_then(|cd| cd.methods.iter().find(|m| m.name == "__getslice__").cloned())
                        .map(Arc::new)
                        .or_else(|| {
                            impl_methods
                                .get(class.as_str())
                                .and_then(|ms| ms.iter().find(|m| m.name == "__getslice__").cloned())
                        });
                    if let Some(method) = getslice_method {
                        let start_val = if let Some(s) = start {
                            evaluate_expr(s, env, functions, classes, enums, impl_methods)?
                        } else {
                            Value::Int(0)
                        };
                        let end_val = if let Some(e) = end {
                            evaluate_expr(e, env, functions, classes, enums, impl_methods)?
                        } else {
                            Value::Int(-1)
                        };
                        let self_ctx = Some((class.as_str(), fields));
                        return Ok(Some(
                            super::super::interpreter_call::exec_function_with_values_and_self(
                                &method,
                                &[start_val, end_val],
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                                self_ctx,
                            )?,
                        ));
                    }
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("slicing requires __getslice__ method on object");
                    return Err(CompileError::semantic_with_context(
                        format!(
                            "invalid operation: cannot slice value of type {} with step",
                            recv_val.type_name()
                        ),
                        ctx,
                    ));
                }
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
                let value = evaluate_expr(s, env, functions, classes, enums, impl_methods)?;
                let v = require_integer_index_value(&value, "slice start")?;
                normalize_index(v, len)
            } else {
                0
            };

            let end_idx = if let Some(e) = end {
                let value = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                let v = require_integer_index_value(&value, "slice end")?;
                normalize_index(v, len)
            } else {
                len
            };

            let step_val = if let Some(st) = step {
                let value = evaluate_expr(st, env, functions, classes, enums, impl_methods)?;
                require_integer_index_value(&value, "slice step")?
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

            // Negative step (Python-style `s[::-1]`/`s[9:0:-1]`) is not part of
            // the language: negative INDICES (Ruby-style, count from the end)
            // remain fully supported, but reversal must always be an explicit
            // `.reversed()` call, never an index trick. See
            // doc/04_architecture/language/slicing/+adr/negative_step_not_supported_2026-07-30.md.
            // Before this check, this exact `Expr::Slice` path silently
            // implemented Python semantics for a negative step (reversed the
            // receiver) instead of erroring, diverging from the default/
            // native-codegen lane, which silently returned an empty result
            // for every negative-step form -- neither was intentional
            // language behavior.
            if step_val < 0 {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("use .reversed() to reverse a string, array, or tuple; negative step is not supported");
                return Err(CompileError::semantic_with_context(
                    "invalid operation: negative slice step is not supported -- use .reversed() to reverse".to_string(),
                    ctx,
                ));
            }

            let result = match recv_val {
                Value::Array(arr) => Ok(Value::array(slice_collection(&arr, start_idx, end_idx, step_val))),
                Value::ByteArray(bytes) => Ok(Value::byte_array(slice_collection(
                    &bytes, start_idx, end_idx, step_val,
                ))),
                Value::FrozenByteArray(bytes) => Ok(Value::frozen_byte_array(slice_collection(
                    &bytes, start_idx, end_idx, step_val,
                ))),
                Value::Str(s) => {
                    // BYTE-indexed slicing. The `len` these indices were
                    // normalized against (above) is already the BYTE length
                    // (`s.len()`), but this arm then sliced a CHAR vector with
                    // those byte-derived indices — an internally mixed index
                    // space that corrupted every multi-byte slice (e.g.
                    // "日本語"[3:6] returned "" instead of "本"). Slicing the
                    // byte slice makes the unit match the normalization and the
                    // native lane; a range that splits a codepoint preserves
                    // the RAW bytes (Value::StrBytes) so reassembly
                    // re-validates, matching the compiled lane.
                    let sliced = slice_collection(s.as_bytes(), start_idx, end_idx, step_val);
                    // UTF-8 slice audit, stage 1 (COUNTING ONLY, default off).
                    // Preserving the RAW bytes is what makes a mid-codepoint
                    // boundary invisible: `Value::StrBytes` holds them and the
                    // byte length is the only tell. Record it; do not fail.
                    if simple_runtime::text_slice_audit::enabled() {
                        simple_runtime::text_slice_audit::note(
                            simple_runtime::text_slice_audit::site::INTERP_BRACKET,
                            start_idx,
                            end_idx,
                            s.as_bytes(),
                            &sliced,
                        );
                    }
                    Ok(Value::text_from_bytes(sliced))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(&tup, start_idx, end_idx, step_val))),
                Value::LabeledTuple { values, .. } => {
                    Ok(Value::Tuple(slice_collection(&values, start_idx, end_idx, step_val)))
                }
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

#[cfg(test)]
mod seed_regression_tests {
    //! Regression tests for 0ee3727522d: the interpreter's brace-form
    //! `Expr::StructInit` handler (this file, `eval_collection_expr`) used to
    //! build its field map purely from spread base + explicit fields, never
    //! consulting the class's declared fields -- an omitted `= default` (or
    //! bare, no-default) field was left missing from the map ENTIRELY, so
    //! later `.field` access failed with "class has no field named X"
    //! instead of yielding the default or nil. The paren-form constructor
    //! path (`instantiate_class`) already pre-filled every declared field;
    //! this fix brought brace-form construction to parity.

    use crate::interpreter::evaluate_module;
    use simple_parser::Parser;

    /// Run a Simple snippet and return the `main = <expr>` exit code.
    fn run(src: &str) -> i32 {
        let mut parser = Parser::new(src);
        let module = parser.parse().expect("parse");
        evaluate_module(&module.items).expect("evaluate")
    }

    #[test]
    fn brace_form_omitted_field_with_declared_default_uses_default_value() {
        let src = r#"
class Widget:
    a: i64
    b: i64 = 42
    c: i64

val w = Widget { a: 1, c: 3 }
var result_ = -1
if w.a == 1 and w.b == 42 and w.c == 3:
    result_ = 0
else:
    result_ = 1
main = result_
"#;
        assert_eq!(
            run(src),
            0,
            "omitted field `b` (declared default 42) must be pre-filled, not missing entirely"
        );
    }

    #[test]
    fn brace_form_omitted_field_with_no_default_is_nil_not_missing() {
        let src = r#"
class Widget:
    a: i64
    b: i64
    c: i64

val w = Widget { a: 1, c: 3 }
var result_ = -1
if w.a == 1 and w.c == 3 and w.b == nil:
    result_ = 0
else:
    result_ = 1
main = result_
"#;
        // Pre-fix this either errored ("class has no field named b") or hit
        // an out-of-bounds/incoherent read; post-fix `w.b` must read back
        // as nil rather than the field being absent from the map.
        assert_eq!(
            run(src),
            0,
            "omitted field `b` with no declared default must read back as nil, not be missing (no OOB)"
        );
    }

    #[test]
    fn brace_form_all_fields_present_still_assigns_correct_values() {
        let src = r#"
class Widget:
    a: i64
    b: i64 = 42
    c: i64

val w = Widget { a: 10, b: 20, c: 30 }
var result_ = -1
if w.a == 10 and w.b == 20 and w.c == 30:
    result_ = 0
else:
    result_ = 1
main = result_
"#;
        assert_eq!(
            run(src),
            0,
            "explicitly provided fields must not be clobbered by the default pre-fill pass"
        );
    }

    #[test]
    fn tuple_index_consumes_present_option_payload() {
        let src = r#"
val pair = Some((7, 11))
main = pair.0
"#;
        assert_eq!(run(src), 7);
    }

    #[test]
    fn tuple_index_consumes_ok_result_payload() {
        let src = r#"
val pair = Ok((13, 17))
main = pair.0
"#;
        assert_eq!(run(src), 13);
    }
}
