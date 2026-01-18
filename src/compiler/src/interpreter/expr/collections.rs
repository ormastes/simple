use std::collections::HashMap;

use simple_parser::ast::Expr;

use super::evaluate_expr;
use crate::error::CompileError;
use crate::value::Value;

use super::super::{
    comprehension_iterate, create_range_object, normalize_index, slice_collection, ClassDef, Enums, Env, FunctionDef,
    ImplMethods,
};

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
            Ok(Some(Value::Object {
                class: name.clone(),
                fields: map,
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
                        Err(CompileError::Semantic(format!(
                            "unknown variant {variant} for enum {enum_name}"
                        )))
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
                    Err(CompileError::Semantic(format!(
                        "unknown path: {:?}::{variant}",
                        segments[0]
                    )))
                }
            } else {
                Err(CompileError::Semantic(format!("unsupported path: {:?}", segments)))
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
                        return Err(CompileError::Semantic("dict spread requires dict value".into()));
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
            let start = match start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()
            {
                Ok(val) => val,
                Err(err) => return Err(err),
            }
            .unwrap_or(Value::Int(0))
            .as_int()?;
            let end = match end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()
            {
                Ok(val) => val,
                Err(err) => return Err(err),
            }
            .unwrap_or(Value::Int(0))
            .as_int()?;
            Ok(Some(create_range_object(start, end, *bound)))
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
                        _ => return Err(CompileError::Semantic("spread operator requires array or tuple".into())),
                    }
                } else {
                    arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
                }
            }
            Ok(Some(Value::Array(arr)))
        }
        Expr::ArrayRepeat { value, count } => {
            // Evaluate the count first
            let count_val = evaluate_expr(count, env, functions, classes, enums, impl_methods)?;
            let count_int = match count_val {
                Value::Int(n) => n,
                _ => return Err(CompileError::Semantic("array repeat count must be an integer".into())),
            };
            if count_int < 0 {
                return Err(CompileError::Semantic("array repeat count cannot be negative".into()));
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
                            let sliced: Vec<Value> = arr
                                .get(start_idx..end_idx.min(arr.len()))
                                .map(|s| s.to_vec())
                                .unwrap_or_default();
                            Ok(Value::Array(sliced))
                        }
                        Value::Str(s) => {
                            let chars: Vec<char> = s.chars().collect();
                            let len = chars.len() as i64;
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
                            let sliced: String = chars
                                .get(start_idx..end_idx.min(chars.len()))
                                .map(|s| s.iter().collect())
                                .unwrap_or_default();
                            Ok(Value::Str(sliced))
                        }
                        _ => Err(CompileError::Semantic("slice on non-sliceable type".into())),
                    }?));
                }
            }

            let result = match recv_val {
                Value::Array(arr) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("array index out of bounds: {raw_idx}")))
                }
                Value::Tuple(tup) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = tup.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    tup.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("tuple index out of bounds: {raw_idx}")))
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    map.get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
                }
                Value::Str(s) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = s.chars().count() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    s.chars()
                        .nth(idx)
                        .map(|c| Value::Str(c.to_string()))
                        .ok_or_else(|| CompileError::Semantic(format!("string index out of bounds: {raw_idx}")))
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic("index access on non-indexable type".into())),
            };
            Ok(Some(result?))
        }
        Expr::TupleIndex { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();
            let result = match recv_val {
                Value::Tuple(tup) => tup
                    .get(*index)
                    .cloned()
                    .ok_or_else(|| CompileError::Semantic(format!("tuple index out of bounds: {index}"))),
                _ => Err(CompileError::Semantic("tuple index access on non-tuple type".into())),
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
                _ => return Err(CompileError::Semantic("slice on non-sliceable type".into())),
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
                return Err(CompileError::Semantic("slice step cannot be zero".into()));
            }

            let result = match recv_val {
                Value::Array(arr) => Ok(Value::Array(slice_collection(&arr, start_idx, end_idx, step_val))),
                Value::Str(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    let sliced = slice_collection(&chars, start_idx, end_idx, step_val);
                    Ok(Value::Str(sliced.into_iter().collect()))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(&tup, start_idx, end_idx, step_val))),
                _ => Err(CompileError::Semantic("slice on non-sliceable type".into())),
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
