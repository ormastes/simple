// Collection type methods: Array, Tuple, Dict

use super::super::{
    eval_arg, eval_arg_usize, eval_array_all, eval_array_any, eval_array_filter, eval_array_find, eval_array_map,
    eval_array_reduce, eval_dict_filter, eval_dict_map_values, evaluate_expr, exec_function, instantiate_class, Enums,
    ImplMethods,
};
use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef};
use std::collections::HashMap;

/// Handle Array methods
pub fn handle_array_methods(
    arr: &[Value],
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" => Value::Int(arr.len() as i64),
        "is_empty" => Value::Bool(arr.is_empty()),
        "first" => arr.first().cloned().unwrap_or(Value::Nil),
        "last" => arr.last().cloned().unwrap_or(Value::Nil),
        "get" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            arr.get(idx).cloned().unwrap_or(Value::Nil)
        }
        "contains" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Value::Bool(arr.contains(&needle))
        }
        "push" | "append" => {
            let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            new_arr.push(item);
            Value::Array(new_arr)
        }
        "pop" => {
            let mut new_arr = arr.to_vec();
            new_arr.pop();
            Value::Array(new_arr)
        }
        "concat" | "extend" => {
            let other = eval_arg(
                args,
                0,
                Value::Array(vec![]),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Value::Array(other_arr) = other {
                let mut new_arr = arr.to_vec();
                new_arr.extend(other_arr);
                Value::Array(new_arr)
            } else {
                return Err(CompileError::Semantic("concat expects array argument".into()));
            }
        }
        "insert" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let item = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            if idx <= new_arr.len() {
                new_arr.insert(idx, item);
            }
            Value::Array(new_arr)
        }
        "remove" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            let mut new_arr = arr.to_vec();
            if idx < new_arr.len() {
                new_arr.remove(idx);
            }
            Value::Array(new_arr)
        }
        "reverse" => {
            let mut new_arr = arr.to_vec();
            new_arr.reverse();
            Value::Array(new_arr)
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
            Value::Array(arr[start..end].to_vec())
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
            let sep = eval_arg(
                args,
                0,
                Value::Str("".into()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?
            .to_display_string();
            let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
            Value::Str(parts.join(&sep))
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
                .get(0)
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
            Value::Array(new_arr)
        }
        "sort_desc" => {
            let mut new_arr = arr.to_vec();
            new_arr.sort_by(|a, b| match (a, b) {
                (Value::Int(a), Value::Int(b)) => b.cmp(a),
                (Value::Float(a), Value::Float(b)) => b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => b.cmp(a),
                _ => std::cmp::Ordering::Equal,
            });
            Value::Array(new_arr)
        }
        "enumerate" => {
            let result: Vec<Value> = arr
                .iter()
                .enumerate()
                .map(|(i, v)| Value::Tuple(vec![Value::Int(i as i64), v.clone()]))
                .collect();
            Value::Array(result)
        }
        "zip" => {
            let other = eval_arg(
                args,
                0,
                Value::Array(vec![]),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Value::Array(other_arr) = other {
                let result: Vec<Value> = arr
                    .iter()
                    .zip(other_arr.iter())
                    .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()]))
                    .collect();
                Value::Array(result)
            } else {
                return Err(CompileError::Semantic("zip expects array argument".into()));
            }
        }
        "flat_map" => {
            let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mapped = eval_array_map(arr, func, functions, classes, enums, impl_methods)?;
            if let Value::Array(mapped_arr) = mapped {
                let mut result = Vec::new();
                for item in mapped_arr {
                    if let Value::Array(inner) = item {
                        result.extend(inner);
                    } else {
                        result.push(item);
                    }
                }
                Value::Array(result)
            } else {
                Value::Array(vec![])
            }
        }
        "flatten" => {
            let mut result = Vec::new();
            for item in arr {
                if let Value::Array(inner) = item {
                    result.extend(inner.clone());
                } else {
                    result.push(item.clone());
                }
            }
            Value::Array(result)
        }
        "take" => {
            let n = eval_arg_usize(args, 0, arr.len(), env, functions, classes, enums, impl_methods)?;
            Value::Array(arr.iter().take(n).cloned().collect())
        }
        "skip" | "drop" => {
            let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            Value::Array(arr.iter().skip(n).cloned().collect())
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
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                    if !pred.truthy() {
                        break;
                    }
                    result.push(item.clone());
                }
            }
            Value::Array(result)
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
                        let mut local_env = captured.clone();
                        if let Some(param) = params.first() {
                            local_env.insert(param.clone(), item.clone());
                        }
                        let pred = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                        if !pred.truthy() {
                            dropping = false;
                            result.push(item.clone());
                        }
                    } else {
                        result.push(item.clone());
                    }
                }
            }
            Value::Array(result)
        }
        "chunk" | "chunks" => {
            let size = eval_arg_usize(args, 0, 1, env, functions, classes, enums, impl_methods)?.max(1);
            let result: Vec<Value> = arr.chunks(size).map(|chunk| Value::Array(chunk.to_vec())).collect();
            Value::Array(result)
        }
        "unique" | "distinct" => {
            let mut seen = Vec::new();
            let mut result = Vec::new();
            for item in arr {
                if !seen.contains(item) {
                    seen.push(item.clone());
                    result.push(item.clone());
                }
            }
            Value::Array(result)
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
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                    if pred.truthy() {
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
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let pred = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                    if pred.truthy() {
                        pass.push(item.clone());
                    } else {
                        fail.push(item.clone());
                    }
                }
            }
            Value::Tuple(vec![Value::Array(pass), Value::Array(fail)])
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
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let key = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                    let key_str = key.to_key_string();
                    groups.entry(key_str).or_default().push(item.clone());
                }
            }
            let result: HashMap<String, Value> = groups.into_iter().map(|(k, v)| (k, Value::Array(v))).collect();
            Value::Dict(result)
        }
        _ => return Ok(None),
    };
    Ok(Some(result))
}

/// Handle Tuple methods
pub fn handle_tuple_methods(
    tup: &[Value],
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" => Value::Int(tup.len() as i64),
        "is_empty" => Value::Bool(tup.is_empty()),
        "get" => {
            let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
            tup.get(idx).cloned().unwrap_or(Value::Nil)
        }
        "first" => tup.first().cloned().unwrap_or(Value::Nil),
        "last" => tup.last().cloned().unwrap_or(Value::Nil),
        "to_array" => Value::Array(tup.to_vec()),
        "contains" => {
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
        "reverse" => {
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
                    let mut local_env = captured.clone();
                    if let Some(param) = params.first() {
                        local_env.insert(param.clone(), item.clone());
                    }
                    let mapped = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
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
                return Err(CompileError::Semantic("zip expects tuple argument".into()));
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

/// Handle Dict methods
pub fn handle_dict_methods(
    map: &HashMap<String, Value>,
    method: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let result = match method {
        "len" => Value::Int(map.len() as i64),
        "is_empty" => Value::Bool(map.is_empty()),
        "contains_key" | "contains" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            Value::Bool(map.contains_key(&key))
        }
        "get" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            map.get(&key).cloned().unwrap_or(Value::Nil)
        }
        "keys" => {
            let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
            Value::Array(keys)
        }
        "values" => {
            let vals: Vec<Value> = map.values().cloned().collect();
            Value::Array(vals)
        }
        "set" | "insert" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            let value = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let mut new_map = map.clone();
            new_map.insert(key, value);
            Value::Dict(new_map)
        }
        "remove" | "delete" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            let mut new_map = map.clone();
            new_map.remove(&key);
            Value::Dict(new_map)
        }
        "merge" | "extend" => {
            let other = eval_arg(
                args,
                0,
                Value::Dict(HashMap::new()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            if let Value::Dict(other_map) = other {
                let mut new_map = map.clone();
                new_map.extend(other_map);
                Value::Dict(new_map)
            } else {
                return Err(CompileError::Semantic("merge expects dict argument".into()));
            }
        }
        "get_or" => {
            let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
            let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            map.get(&key).cloned().unwrap_or(default)
        }
        "entries" | "items" => {
            let entries: Vec<Value> = map
                .iter()
                .map(|(k, v)| Value::Tuple(vec![Value::Str(k.clone()), v.clone()]))
                .collect();
            Value::Array(entries)
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
        _ => {
            // Check if the dict contains a callable value at this key (module-style calls)
            if let Some(value) = map.get(method) {
                match value {
                    Value::Function { def, captured_env, .. } => {
                        // Call the function with the provided arguments
                        // Use the caller's env for evaluating arguments, but merge with captured_env for the function body
                        let mut merged_env = captured_env.clone();
                        merged_env.extend(env.clone());
                        let result =
                            exec_function(def, args, &merged_env, functions, classes, enums, impl_methods, None)?;
                        return Ok(Some(result));
                    }
                    Value::Lambda {
                        params,
                        body,
                        env: captured,
                    } => {
                        // Call the lambda
                        let mut local_env = captured.clone();
                        for (i, param) in params.iter().enumerate() {
                            let arg_val = eval_arg(args, i, Value::Nil, env, functions, classes, enums, impl_methods)?;
                            local_env.insert(param.clone(), arg_val);
                        }
                        let result = evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)?;
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
