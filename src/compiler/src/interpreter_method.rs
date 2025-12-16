// Method call evaluation (part of interpreter module)

fn evaluate_method_call(
    receiver: &Box<Expr>,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Support module-style dot calls (lib.func()) by resolving directly to imported functions/classes.
    if let Expr::Identifier(module_name) = receiver.as_ref() {
        if env.get(module_name).is_none() {
            if let Some(func) = functions.get(method) {
                return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
            }
            if classes.contains_key(method) {
                return instantiate_class(method, args, env, functions, classes, enums, impl_methods);
            }
        }
    }

    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // BDD assertion methods: to(matcher) and not_to(matcher)
    // These work on any value type and are used with matchers like eq(5), gt(3), etc.
    match method {
        "to" | "not_to" => {
            let matcher = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let matched = match &matcher {
                Value::Matcher(m) => m.matches(&recv_val),
                // If the argument isn't a Matcher, treat it as an equality check
                other => recv_val == *other,
            };
            let passed = if method == "not_to" { !matched } else { matched };
            return Ok(Value::Bool(passed));
        }
        _ => {}
    }

    // Built-in methods for Int
    if let Value::Int(n) = recv_val {
        match method {
            "abs" => return Ok(Value::Int(n.abs())),
            "sign" | "signum" => return Ok(Value::Int(n.signum())),
            "is_positive" => return Ok(Value::Bool(n > 0)),
            "is_negative" => return Ok(Value::Bool(n < 0)),
            "is_zero" => return Ok(Value::Bool(n == 0)),
            "is_even" => return Ok(Value::Bool(n % 2 == 0)),
            "is_odd" => return Ok(Value::Bool(n % 2 != 0)),
            "to_float" => return Ok(Value::Float(n as f64)),
            "to_string" => return Ok(Value::Str(n.to_string())),
            "clamp" => {
                let min = eval_arg(args, 0, Value::Int(i64::MIN), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(i64::MIN);
                let max = eval_arg(args, 1, Value::Int(i64::MAX), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(i64::MAX);
                return Ok(Value::Int(n.clamp(min, max)));
            }
            "min" => {
                let other = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(n);
                return Ok(Value::Int(n.min(other)));
            }
            "max" => {
                let other = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(n);
                return Ok(Value::Int(n.max(other)));
            }
            "pow" => {
                let exp = eval_arg(args, 0, Value::Int(1), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(1) as u32;
                return Ok(Value::Int(n.saturating_pow(exp)));
            }
            "bit_count" | "count_ones" => return Ok(Value::Int(n.count_ones() as i64)),
            "leading_zeros" => return Ok(Value::Int(n.leading_zeros() as i64)),
            "trailing_zeros" => return Ok(Value::Int(n.trailing_zeros() as i64)),
            "to_hex" => return Ok(Value::Str(format!("{:x}", n))),
            "to_bin" => return Ok(Value::Str(format!("{:b}", n))),
            "to_oct" => return Ok(Value::Str(format!("{:o}", n))),
            "times" => {
                // Call a function n times, returning array of results
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut results = Vec::new();
                if let Value::Lambda { params, body, env: captured } = func {
                    for i in 0..n.max(0) {
                        let mut local_env = captured.clone();
                        if let Some(param) = params.first() {
                            local_env.insert(param.clone(), Value::Int(i));
                        }
                        let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                        results.push(result);
                    }
                }
                return Ok(Value::Array(results));
            }
            "up_to" => {
                // Create range from self to n (exclusive)
                let end = eval_arg(args, 0, Value::Int(n), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(n);
                let range: Vec<Value> = (n..end).map(Value::Int).collect();
                return Ok(Value::Array(range));
            }
            "down_to" => {
                // Create range from self down to n (exclusive)
                let end = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(0);
                let range: Vec<Value> = (end..n).rev().map(Value::Int).collect();
                return Ok(Value::Array(range));
            }
            _ => {}
        }
    }

    // Built-in methods for Float
    if let Value::Float(f) = recv_val {
        match method {
            "abs" => return Ok(Value::Float(f.abs())),
            "sign" | "signum" => return Ok(Value::Float(f.signum())),
            "is_positive" => return Ok(Value::Bool(f > 0.0)),
            "is_negative" => return Ok(Value::Bool(f < 0.0)),
            "is_zero" => return Ok(Value::Bool(f == 0.0)),
            "is_nan" => return Ok(Value::Bool(f.is_nan())),
            "is_infinite" => return Ok(Value::Bool(f.is_infinite())),
            "is_finite" => return Ok(Value::Bool(f.is_finite())),
            "to_int" | "truncate" => return Ok(Value::Int(f.trunc() as i64)),
            "to_string" => return Ok(Value::Str(f.to_string())),
            "floor" => return Ok(Value::Float(f.floor())),
            "ceil" => return Ok(Value::Float(f.ceil())),
            "round" => return Ok(Value::Float(f.round())),
            "trunc" => return Ok(Value::Float(f.trunc())),
            "fract" => return Ok(Value::Float(f.fract())),
            "sqrt" => return Ok(Value::Float(f.sqrt())),
            "cbrt" => return Ok(Value::Float(f.cbrt())),
            "exp" => return Ok(Value::Float(f.exp())),
            "exp2" => return Ok(Value::Float(f.exp2())),
            "ln" => return Ok(Value::Float(f.ln())),
            "log2" => return Ok(Value::Float(f.log2())),
            "log10" => return Ok(Value::Float(f.log10())),
            "sin" => return Ok(Value::Float(f.sin())),
            "cos" => return Ok(Value::Float(f.cos())),
            "tan" => return Ok(Value::Float(f.tan())),
            "asin" => return Ok(Value::Float(f.asin())),
            "acos" => return Ok(Value::Float(f.acos())),
            "atan" => return Ok(Value::Float(f.atan())),
            "sinh" => return Ok(Value::Float(f.sinh())),
            "cosh" => return Ok(Value::Float(f.cosh())),
            "tanh" => return Ok(Value::Float(f.tanh())),
            "clamp" => {
                let min = eval_arg(args, 0, Value::Float(f64::MIN), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(f64::MIN);
                let max = eval_arg(args, 1, Value::Float(f64::MAX), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(f64::MAX);
                return Ok(Value::Float(f.clamp(min, max)));
            }
            "min" => {
                let other = eval_arg(args, 0, Value::Float(f), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(f);
                return Ok(Value::Float(f.min(other)));
            }
            "max" => {
                let other = eval_arg(args, 0, Value::Float(f), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(f);
                return Ok(Value::Float(f.max(other)));
            }
            "pow" | "powf" => {
                let exp = eval_arg(args, 0, Value::Float(1.0), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(1.0);
                return Ok(Value::Float(f.powf(exp)));
            }
            "powi" => {
                let exp = eval_arg(args, 0, Value::Int(1), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(1) as i32;
                return Ok(Value::Float(f.powi(exp)));
            }
            "log" => {
                let base = eval_arg(args, 0, Value::Float(std::f64::consts::E), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(std::f64::consts::E);
                return Ok(Value::Float(f.log(base)));
            }
            "atan2" => {
                let other = eval_arg(args, 0, Value::Float(1.0), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(1.0);
                return Ok(Value::Float(f.atan2(other)));
            }
            "hypot" => {
                let other = eval_arg(args, 0, Value::Float(0.0), env, functions, classes, enums, impl_methods)?
                    .as_float().unwrap_or(0.0);
                return Ok(Value::Float(f.hypot(other)));
            }
            "to_degrees" => return Ok(Value::Float(f.to_degrees())),
            "to_radians" => return Ok(Value::Float(f.to_radians())),
            "round_to" => {
                let places = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?
                    .as_int().unwrap_or(0) as i32;
                let multiplier = 10f64.powi(places);
                return Ok(Value::Float((f * multiplier).round() / multiplier));
            }
            _ => {}
        }
    }

    // Built-in methods for Unit values (unit-suffixed numbers/strings)
    if let Value::Unit { value, suffix, family } = &recv_val {
        match method {
            "value" => return Ok((**value).clone()),
            "suffix" => return Ok(Value::Str(suffix.clone())),
            "family" => return Ok(family.clone().map_or(Value::Nil, Value::Str)),
            "to_string" => return Ok(Value::Str(format!("{}_{}", value.to_display_string(), suffix))),
            // For dynamic to_X() conversion methods, check if method starts with "to_"
            other if other.starts_with("to_") => {
                let target_suffix = &other[3..]; // Remove "to_" prefix

                // Get the family name - either from the Unit value or look it up
                let family_name = family.clone().or_else(|| {
                    UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned())
                });

                let Some(family_name) = family_name else {
                    return Err(CompileError::Semantic(format!(
                        "Unit '{}' does not belong to a unit family, cannot convert to '{}'",
                        suffix, target_suffix
                    )));
                };

                // Look up conversions for this family
                let conversion_result = UNIT_FAMILY_CONVERSIONS.with(|cell| {
                    let families = cell.borrow();
                    let Some(conversions) = families.get(&family_name) else {
                        return Err(CompileError::Semantic(format!(
                            "Unit family '{}' not found", family_name
                        )));
                    };

                    // Get source and target conversion factors
                    let Some(source_factor) = conversions.get(suffix) else {
                        return Err(CompileError::Semantic(format!(
                            "Unit '{}' not found in family '{}'", suffix, family_name
                        )));
                    };
                    let Some(target_factor) = conversions.get(target_suffix) else {
                        return Err(CompileError::Semantic(format!(
                            "Target unit '{}' not found in family '{}'. Available: {:?}",
                            target_suffix, family_name, conversions.keys().collect::<Vec<_>>()
                        )));
                    };

                    Ok((*source_factor, *target_factor))
                })?;

                let (source_factor, target_factor) = conversion_result;

                // Perform the conversion: new_value = old_value * (source_factor / target_factor)
                // e.g., 2_km to m: 2 * (1000.0 / 1.0) = 2000
                let converted_value = match value.as_ref() {
                    Value::Int(n) => {
                        let converted = (*n as f64) * (source_factor / target_factor);
                        // Keep as float if not a whole number
                        if converted.fract() == 0.0 {
                            Value::Int(converted as i64)
                        } else {
                            Value::Float(converted)
                        }
                    }
                    Value::Float(f) => {
                        Value::Float(f * (source_factor / target_factor))
                    }
                    _ => {
                        return Err(CompileError::Semantic(format!(
                            "Cannot convert non-numeric unit value: {:?}", value
                        )));
                    }
                };

                // Return a new Unit value with the target suffix
                return Ok(Value::Unit {
                    value: Box::new(converted_value),
                    suffix: target_suffix.to_string(),
                    family: Some(family_name),
                });
            }
            _ => {}
        }
    }

    // Built-in methods for Bool
    if let Value::Bool(b) = recv_val {
        match method {
            "to_int" => return Ok(Value::Int(if b { 1 } else { 0 })),
            "to_string" => return Ok(Value::Str(b.to_string())),
            "then" => {
                // Returns Some(result) if true, None if false
                if b {
                    let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda { params: _, body, env: captured } = func {
                        let result = evaluate_expr(&body, &captured, functions, classes, enums, impl_methods)?;
                        return Ok(Value::some(result));
                    }
                    return Ok(Value::some(Value::Nil));
                }
                return Ok(Value::none());
            }
            "then_else" => {
                let then_func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let else_func = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let func = if b { then_func } else { else_func };
                if let Value::Lambda { params: _, body, env: captured } = func {
                    return evaluate_expr(&body, &captured, functions, classes, enums, impl_methods);
                }
                return Ok(Value::Nil);
            }
            _ => {}
        }
    }

    // Built-in methods for Array
    if let Value::Array(ref arr) = recv_val {
        match method {
            "len" => return Ok(Value::Int(arr.len() as i64)),
            "is_empty" => return Ok(Value::Bool(arr.is_empty())),
            "first" => return Ok(arr.first().cloned().unwrap_or(Value::Nil)),
            "last" => return Ok(arr.last().cloned().unwrap_or(Value::Nil)),
            "get" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(arr.get(idx).cloned().unwrap_or(Value::Nil));
            }
            "contains" => {
                let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Bool(arr.contains(&needle)));
            }
            "push" | "append" => {
                let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                new_arr.push(item);
                return Ok(Value::Array(new_arr));
            }
            "pop" => {
                let mut new_arr = arr.clone();
                new_arr.pop();
                return Ok(Value::Array(new_arr));
            }
            "concat" | "extend" => {
                let other = eval_arg(args, 0, Value::Array(vec![]), env, functions, classes, enums, impl_methods)?;
                if let Value::Array(other_arr) = other {
                    let mut new_arr = arr.clone();
                    new_arr.extend(other_arr);
                    return Ok(Value::Array(new_arr));
                }
                return Err(CompileError::Semantic("concat expects array argument".into()));
            }
            "insert" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let item = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                if idx <= new_arr.len() {
                    new_arr.insert(idx, item);
                }
                return Ok(Value::Array(new_arr));
            }
            "remove" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let mut new_arr = arr.clone();
                if idx < new_arr.len() {
                    new_arr.remove(idx);
                }
                return Ok(Value::Array(new_arr));
            }
            "reverse" => {
                let mut new_arr = arr.clone();
                new_arr.reverse();
                return Ok(Value::Array(new_arr));
            }
            "slice" => {
                let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let end = args.get(1)
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .transpose()?
                    .map(|v| v.as_int().unwrap_or(arr.len() as i64) as usize)
                    .unwrap_or(arr.len());
                let end = end.min(arr.len());
                let start = start.min(end);
                return Ok(Value::Array(arr[start..end].to_vec()));
            }
            "map" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_map(arr, func, functions, classes, enums, impl_methods);
            }
            "filter" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_filter(arr, func, functions, classes, enums, impl_methods);
            }
            "reduce" | "fold" => {
                let init = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
                let func = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_reduce(arr, init, func, functions, classes, enums, impl_methods);
            }
            "find" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_find(arr, func, functions, classes, enums, impl_methods);
            }
            "any" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_any(arr, func, functions, classes, enums, impl_methods);
            }
            "all" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_array_all(arr, func, functions, classes, enums, impl_methods);
            }
            "join" => {
                let sep = eval_arg(args, 0, Value::Str("".into()), env, functions, classes, enums, impl_methods)?.to_display_string();
                let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "sum" => {
                let mut total: i64 = 0;
                for item in arr {
                    if let Value::Int(n) = item {
                        total += n;
                    }
                }
                return Ok(Value::Int(total));
            }
            "index_of" => {
                let needle = args.get(0)
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                for (i, item) in arr.iter().enumerate() {
                    if item == &needle {
                        return Ok(Value::Int(i as i64));
                    }
                }
                return Ok(Value::Int(-1));
            }
            "sort" => {
                let mut new_arr = arr.clone();
                new_arr.sort_by(|a, b| {
                    match (a, b) {
                        (Value::Int(a), Value::Int(b)) => a.cmp(b),
                        (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                        (Value::Str(a), Value::Str(b)) => a.cmp(b),
                        _ => std::cmp::Ordering::Equal,
                    }
                });
                return Ok(Value::Array(new_arr));
            }
            "sort_desc" => {
                let mut new_arr = arr.clone();
                new_arr.sort_by(|a, b| {
                    match (a, b) {
                        (Value::Int(a), Value::Int(b)) => b.cmp(a),
                        (Value::Float(a), Value::Float(b)) => b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal),
                        (Value::Str(a), Value::Str(b)) => b.cmp(a),
                        _ => std::cmp::Ordering::Equal,
                    }
                });
                return Ok(Value::Array(new_arr));
            }
            "enumerate" => {
                let result: Vec<Value> = arr.iter()
                    .enumerate()
                    .map(|(i, v)| Value::Tuple(vec![Value::Int(i as i64), v.clone()]))
                    .collect();
                return Ok(Value::Array(result));
            }
            "zip" => {
                let other = eval_arg(args, 0, Value::Array(vec![]), env, functions, classes, enums, impl_methods)?;
                if let Value::Array(other_arr) = other {
                    let result: Vec<Value> = arr.iter()
                        .zip(other_arr.iter())
                        .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()]))
                        .collect();
                    return Ok(Value::Array(result));
                }
                return Err(CompileError::Semantic("zip expects array argument".into()));
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
                    return Ok(Value::Array(result));
                }
                return Ok(Value::Array(vec![]));
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
                return Ok(Value::Array(result));
            }
            "take" => {
                let n = eval_arg_usize(args, 0, arr.len(), env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Array(arr.iter().take(n).cloned().collect()));
            }
            "skip" | "drop" => {
                let n = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Array(arr.iter().skip(n).cloned().collect()));
            }
            "take_while" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut result = Vec::new();
                if let Value::Lambda { params, body, env: captured } = func {
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
                return Ok(Value::Array(result));
            }
            "skip_while" | "drop_while" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut result = Vec::new();
                let mut dropping = true;
                if let Value::Lambda { params, body, env: captured } = func {
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
                return Ok(Value::Array(result));
            }
            "chunk" | "chunks" => {
                let size = eval_arg_usize(args, 0, 1, env, functions, classes, enums, impl_methods)?.max(1);
                let result: Vec<Value> = arr.chunks(size)
                    .map(|chunk| Value::Array(chunk.to_vec()))
                    .collect();
                return Ok(Value::Array(result));
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
                return Ok(Value::Array(result));
            }
            "min" => {
                let min_val = arr.iter().min_by(|a, b| {
                    match (a, b) {
                        (Value::Int(a), Value::Int(b)) => a.cmp(b),
                        (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                        (Value::Str(a), Value::Str(b)) => a.cmp(b),
                        _ => std::cmp::Ordering::Equal,
                    }
                });
                return Ok(min_val.cloned().unwrap_or(Value::Nil));
            }
            "max" => {
                let max_val = arr.iter().max_by(|a, b| {
                    match (a, b) {
                        (Value::Int(a), Value::Int(b)) => a.cmp(b),
                        (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal),
                        (Value::Str(a), Value::Str(b)) => a.cmp(b),
                        _ => std::cmp::Ordering::Equal,
                    }
                });
                return Ok(max_val.cloned().unwrap_or(Value::Nil));
            }
            "count" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda { params, body, env: captured } = func {
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
                    return Ok(Value::Int(count));
                }
                return Ok(Value::Int(arr.len() as i64));
            }
            "partition" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut pass = Vec::new();
                let mut fail = Vec::new();
                if let Value::Lambda { params, body, env: captured } = func {
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
                return Ok(Value::Tuple(vec![Value::Array(pass), Value::Array(fail)]));
            }
            "group_by" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut groups: HashMap<String, Vec<Value>> = HashMap::new();
                if let Value::Lambda { params, body, env: captured } = func {
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
                let result: HashMap<String, Value> = groups.into_iter()
                    .map(|(k, v)| (k, Value::Array(v)))
                    .collect();
                return Ok(Value::Dict(result));
            }
            _ => {}
        }
    }

    // Built-in methods for Tuple
    if let Value::Tuple(ref tup) = recv_val {
        match method {
            "len" => return Ok(Value::Int(tup.len() as i64)),
            "is_empty" => return Ok(Value::Bool(tup.is_empty())),
            "get" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                return Ok(tup.get(idx).cloned().unwrap_or(Value::Nil));
            }
            "first" => return Ok(tup.first().cloned().unwrap_or(Value::Nil)),
            "last" => return Ok(tup.last().cloned().unwrap_or(Value::Nil)),
            "to_array" => return Ok(Value::Array(tup.clone())),
            "contains" => {
                let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Bool(tup.contains(&needle)));
            }
            "index_of" => {
                let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                for (i, item) in tup.iter().enumerate() {
                    if item == &needle {
                        return Ok(Value::Int(i as i64));
                    }
                }
                return Ok(Value::Int(-1));
            }
            "reverse" => {
                let mut new_tup = tup.clone();
                new_tup.reverse();
                return Ok(Value::Tuple(new_tup));
            }
            "map" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                if let Value::Lambda { params, body, env: captured } = func {
                    let mut result = Vec::new();
                    for item in tup {
                        let mut local_env = captured.clone();
                        if let Some(param) = params.first() {
                            local_env.insert(param.clone(), item.clone());
                        }
                        let mapped = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                        result.push(mapped);
                    }
                    return Ok(Value::Tuple(result));
                }
                return Ok(recv_val.clone());
            }
            "zip" => {
                let other = eval_arg(args, 0, Value::Tuple(vec![]), env, functions, classes, enums, impl_methods)?;
                if let Value::Tuple(other_tup) = other {
                    let result: Vec<Value> = tup.iter()
                        .zip(other_tup.iter())
                        .map(|(a, b)| Value::Tuple(vec![a.clone(), b.clone()]))
                        .collect();
                    return Ok(Value::Tuple(result));
                }
                return Err(CompileError::Semantic("zip expects tuple argument".into()));
            }
            "enumerate" => {
                let result: Vec<Value> = tup.iter()
                    .enumerate()
                    .map(|(i, v)| Value::Tuple(vec![Value::Int(i as i64), v.clone()]))
                    .collect();
                return Ok(Value::Tuple(result));
            }
            _ => {}
        }
    }

    // Built-in methods for Dict
    if let Value::Dict(ref map) = recv_val {
        match method {
            "len" => return Ok(Value::Int(map.len() as i64)),
            "is_empty" => return Ok(Value::Bool(map.is_empty())),
            "contains_key" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(map.contains_key(&key)));
            }
            "get" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(map.get(&key).cloned().unwrap_or(Value::Nil));
            }
            "keys" => {
                let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
                return Ok(Value::Array(keys));
            }
            "values" => {
                let vals: Vec<Value> = map.values().cloned().collect();
                return Ok(Value::Array(vals));
            }
            "set" | "insert" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let value = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let mut new_map = map.clone();
                new_map.insert(key, value);
                return Ok(Value::Dict(new_map));
            }
            "remove" | "delete" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let mut new_map = map.clone();
                new_map.remove(&key);
                return Ok(Value::Dict(new_map));
            }
            "merge" | "extend" => {
                let other = eval_arg(args, 0, Value::Dict(HashMap::new()), env, functions, classes, enums, impl_methods)?;
                if let Value::Dict(other_map) = other {
                    let mut new_map = map.clone();
                    new_map.extend(other_map);
                    return Ok(Value::Dict(new_map));
                }
                return Err(CompileError::Semantic("merge expects dict argument".into()));
            }
            "get_or" => {
                let key = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?.to_key_string();
                let default = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return Ok(map.get(&key).cloned().unwrap_or(default));
            }
            "entries" | "items" => {
                let entries: Vec<Value> = map.iter()
                    .map(|(k, v)| Value::Tuple(vec![Value::Str(k.clone()), v.clone()]))
                    .collect();
                return Ok(Value::Array(entries));
            }
            "map_values" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_dict_map_values(map, func, functions, classes, enums, impl_methods);
            }
            "filter" => {
                let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                return eval_dict_filter(map, func, functions, classes, enums, impl_methods);
            }
            _ => {}
        }
    }

    // Built-in methods for String
    if let Value::Str(ref s) = recv_val {
        match method {
            "len" => return Ok(Value::Int(s.len() as i64)),
            "char_count" => return Ok(Value::Int(s.chars().count() as i64)),
            "is_empty" => return Ok(Value::Bool(s.is_empty())),
            "chars" => {
                let chars: Vec<Value> = s.chars().map(|c| Value::Str(c.to_string())).collect();
                return Ok(Value::Array(chars));
            }
            "bytes" => {
                let bytes: Vec<Value> = s.bytes().map(|b| Value::Int(b as i64)).collect();
                return Ok(Value::Array(bytes));
            }
            "contains" => {
                let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.contains(&needle)));
            }
            "starts_with" => {
                let prefix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.starts_with(&prefix)));
            }
            "ends_with" => {
                let suffix = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Bool(s.ends_with(&suffix)));
            }
            "to_upper" | "to_uppercase" => return Ok(Value::Str(s.to_uppercase())),
            "to_lower" | "to_lowercase" => return Ok(Value::Str(s.to_lowercase())),
            "trim" => return Ok(Value::Str(s.trim().to_string())),
            "trim_start" | "trim_left" => return Ok(Value::Str(s.trim_start().to_string())),
            "trim_end" | "trim_right" => return Ok(Value::Str(s.trim_end().to_string())),
            "split" => {
                let sep = eval_arg(args, 0, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?.to_key_string();
                let parts: Vec<Value> = s.split(&sep).map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            "split_lines" | "lines" => {
                let parts: Vec<Value> = s.lines().map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            "replace" => {
                let old = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                let new = eval_arg(args, 1, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Str(s.replace(&old, &new)));
            }
            "replace_first" => {
                let old = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                let new = eval_arg(args, 1, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Str(s.replacen(&old, &new, 1)));
            }
            "slice" | "substring" => {
                let start = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let end = args.get(1)
                    .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                    .transpose()?
                    .map(|v| v.as_int().unwrap_or(s.len() as i64) as usize)
                    .unwrap_or(s.len());
                // Work with char indices for unicode safety
                let chars: Vec<char> = s.chars().collect();
                let end = end.min(chars.len());
                let start = start.min(end);
                let result: String = chars[start..end].iter().collect();
                return Ok(Value::Str(result));
            }
            "repeat" => {
                let n = eval_arg_usize(args, 0, 1, env, functions, classes, enums, impl_methods)?;
                return Ok(Value::Str(s.repeat(n)));
            }
            "reverse" => {
                return Ok(Value::Str(s.chars().rev().collect()));
            }
            "index_of" | "find" => {
                let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                match s.find(&needle) {
                    Some(idx) => return Ok(Value::Int(idx as i64)),
                    None => return Ok(Value::Int(-1)),
                }
            }
            "last_index_of" | "rfind" => {
                let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                match s.rfind(&needle) {
                    Some(idx) => return Ok(Value::Int(idx as i64)),
                    None => return Ok(Value::Int(-1)),
                }
            }
            "parse_int" => {
                match s.trim().parse::<i64>() {
                    Ok(n) => return Ok(Value::some(Value::Int(n))),
                    Err(_) => return Ok(Value::none()),
                }
            }
            "parse_float" => {
                match s.trim().parse::<f64>() {
                    Ok(n) => return Ok(Value::some(Value::Float(n))),
                    Err(_) => return Ok(Value::none()),
                }
            }
            "to_int" => {
                match s.trim().parse::<i64>() {
                    Ok(n) => return Ok(Value::Int(n)),
                    Err(_) => return Ok(Value::Int(0)),
                }
            }
            "to_float" => {
                match s.trim().parse::<f64>() {
                    Ok(n) => return Ok(Value::Float(n)),
                    Err(_) => return Ok(Value::Float(0.0)),
                }
            }
            "char_at" | "at" => {
                let idx = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                match s.chars().nth(idx) {
                    Some(c) => return Ok(Value::Str(c.to_string())),
                    None => return Ok(Value::Nil),
                }
            }
            "pad_left" | "pad_start" => {
                let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let pad_char = eval_arg(args, 1, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?
                    .to_key_string()
                    .chars()
                    .next()
                    .unwrap_or(' ');
                let current_len = s.chars().count();
                if current_len >= width {
                    return Ok(Value::Str(s.clone()));
                }
                let padding: String = std::iter::repeat(pad_char).take(width - current_len).collect();
                return Ok(Value::Str(format!("{}{}", padding, s)));
            }
            "pad_right" | "pad_end" => {
                let width = eval_arg_usize(args, 0, 0, env, functions, classes, enums, impl_methods)?;
                let pad_char = eval_arg(args, 1, Value::Str(" ".into()), env, functions, classes, enums, impl_methods)?
                    .to_key_string()
                    .chars()
                    .next()
                    .unwrap_or(' ');
                let current_len = s.chars().count();
                if current_len >= width {
                    return Ok(Value::Str(s.clone()));
                }
                let padding: String = std::iter::repeat(pad_char).take(width - current_len).collect();
                return Ok(Value::Str(format!("{}{}", s, padding)));
            }
            "is_numeric" => {
                return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_ascii_digit())));
            }
            "is_alpha" => {
                return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphabetic())));
            }
            "is_alphanumeric" => {
                return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_alphanumeric())));
            }
            "is_whitespace" => {
                return Ok(Value::Bool(!s.is_empty() && s.chars().all(|c| c.is_whitespace())));
            }
            "count" => {
                let needle = eval_arg(args, 0, Value::Str(String::new()), env, functions, classes, enums, impl_methods)?.to_key_string();
                return Ok(Value::Int(s.matches(&needle).count() as i64));
            }
            _ => {}
        }
    }

    // Built-in methods for Option and Result using type-safe variants
    if let Value::Enum { enum_name, variant, payload } = &recv_val {
        // Use typed enum matching for Option
        if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) {
            let opt_variant = OptionVariant::from_name(variant);
            match method {
                "is_some" => return Ok(Value::Bool(opt_variant == Some(OptionVariant::Some))),
                "is_none" => return Ok(Value::Bool(opt_variant == Some(OptionVariant::None))),
                "unwrap" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap on None".into()));
                }
                "expect" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    let msg = eval_arg(args, 0, Value::Str("Option was None".into()), env, functions, classes, enums, impl_methods)?;
                    return Err(CompileError::Semantic(msg.to_display_string()));
                }
                "unwrap_or" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "unwrap_or_else" => {
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    // Call the function to get default value
                    let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda { params: _, body, env: captured } = func_arg {
                        return evaluate_expr(&body, &captured, functions, classes, enums, impl_methods);
                    }
                    return Ok(Value::Nil);
                }
                "map" => {
                    return eval_option_map(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "and_then" => {
                    return eval_option_and_then(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "or_else" => {
                    return eval_option_or_else(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "filter" => {
                    return eval_option_filter(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "flatten" => {
                    // Option<Option<T>> -> Option<T>
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(inner) = payload {
                            // If inner is also an Option, return it
                            if let Value::Enum { enum_name: inner_enum, .. } = inner.as_ref() {
                                if inner_enum == "Option" {
                                    return Ok(inner.as_ref().clone());
                                }
                            }
                        }
                    }
                    return Ok(Value::none());
                }
                "take" => {
                    // Returns the value and replaces with None (for mutable contexts)
                    // In immutable context, just returns the value
                    if opt_variant == Some(OptionVariant::Some) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return Ok(Value::none());
                }
                _ => {}
            }
        }
        // Use typed enum matching for Result
        if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) {
            let res_variant = ResultVariant::from_name(variant);
            match method {
                "is_ok" => return Ok(Value::Bool(res_variant == Some(ResultVariant::Ok))),
                "is_err" => return Ok(Value::Bool(res_variant == Some(ResultVariant::Err))),
                "unwrap" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    if res_variant == Some(ResultVariant::Err) {
                        if let Some(err_val) = payload {
                            return Err(CompileError::Semantic(format!("called unwrap on Err: {}", err_val.to_display_string())));
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap on Err".into()));
                }
                "expect" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    let msg = eval_arg(args, 0, Value::Str("Result was Err".into()), env, functions, classes, enums, impl_methods)?;
                    if res_variant == Some(ResultVariant::Err) {
                        if let Some(err_val) = payload {
                            return Err(CompileError::Semantic(format!("{}: {}", msg.to_display_string(), err_val.to_display_string())));
                        }
                    }
                    return Err(CompileError::Semantic(msg.to_display_string()));
                }
                "unwrap_or" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "unwrap_or_else" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    // Call the function with error value to get default
                    if let Some(err_val) = payload {
                        let func_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                        if let Value::Lambda { params, body, env: captured } = func_arg {
                            let mut local_env = captured.clone();
                            if let Some(param) = params.first() {
                                local_env.insert(param.clone(), err_val.as_ref().clone());
                            }
                            return evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods);
                        }
                    }
                    return Ok(Value::Nil);
                }
                "unwrap_err" => {
                    if res_variant == Some(ResultVariant::Err) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    return Err(CompileError::Semantic("called unwrap_err on Ok".into()));
                }
                "expect_err" => {
                    if res_variant == Some(ResultVariant::Err) {
                        if let Some(val) = payload {
                            return Ok(val.as_ref().clone());
                        }
                    }
                    let msg = eval_arg(args, 0, Value::Str("Result was Ok".into()), env, functions, classes, enums, impl_methods)?;
                    return Err(CompileError::Semantic(msg.to_display_string()));
                }
                "ok" => {
                    if res_variant == Some(ResultVariant::Ok) {
                        return Ok(payload.as_ref().map(|p| Value::some(p.as_ref().clone())).unwrap_or_else(Value::none));
                    }
                    return Ok(Value::none());
                }
                "err" => {
                    if res_variant == Some(ResultVariant::Err) {
                        return Ok(payload.as_ref().map(|p| Value::some(p.as_ref().clone())).unwrap_or_else(Value::none));
                    }
                    return Ok(Value::none());
                }
                "map" => {
                    return eval_result_map(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "map_err" => {
                    return eval_result_map_err(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "and_then" => {
                    return eval_result_and_then(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "or_else" => {
                    return eval_result_or_else(variant, payload, args, env, functions, classes, enums, impl_methods);
                }
                "flatten" => {
                    // Result<Result<T, E>, E> -> Result<T, E>
                    if res_variant == Some(ResultVariant::Ok) {
                        if let Some(inner) = payload {
                            // If inner is also a Result, return it
                            if let Value::Enum { enum_name: inner_enum, .. } = inner.as_ref() {
                                if inner_enum == "Result" {
                                    return Ok(inner.as_ref().clone());
                                }
                            }
                        }
                    }
                    // Return Err as-is
                    return Ok(recv_val.clone());
                }
                _ => {}
            }
        }

        // User-defined methods on enums via impl blocks
        if let Some(methods) = impl_methods.get(enum_name) {
            for m in methods {
                if m.name == method {
                    // For enum methods, we pass self as a special context
                    // Create a fields map with just "self" for the enum value
                    let mut enum_fields = HashMap::new();
                    enum_fields.insert("self".to_string(), recv_val.clone());
                    return exec_function(m, args, env, functions, classes, enums, impl_methods, Some((enum_name, &enum_fields)));
                }
            }
        }
    }

    // TraitObject - dynamic dispatch through trait implementation
    // The inner value must implement the trait, so we dispatch to the inner value's methods
    if let Value::TraitObject { trait_name, inner } = recv_val.clone() {
        // Extract the inner value's class/type
        if let Value::Object { class, fields } = inner.as_ref() {
            // Try to find and execute the method on the inner object
            if let Some(result) = find_and_exec_method(method, args, class, fields, env, functions, classes, enums, impl_methods)? {
                return Ok(result);
            }
            return Err(CompileError::Semantic(format!(
                "Method '{}' not found on dyn {} (type: {})",
                method, trait_name, class
            )));
        }
        return Err(CompileError::Semantic(format!(
            "Cannot call method '{}' on dyn {}: inner value is not an object",
            method, trait_name
        )));
    }

    // Object methods (class/struct)
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some(result) = find_and_exec_method(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok(result);
        }
        // Collect available methods for typo suggestion
        let mut available_methods: Vec<&str> = Vec::new();
        if let Some(methods) = impl_methods.get(&class) {
            available_methods.extend(methods.iter().map(|m| m.name.as_str()));
        }
        // Add built-in methods for common types
        available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
        bail_unknown_method!(method, class, available_methods);
    }

    // Future methods (join, await, get, is_ready)
    if let Value::Future(ref future) = recv_val {
        match method {
            "join" | "await" | "get" => {
                return future.await_result().map_err(|e| CompileError::Semantic(e));
            }
            "is_ready" => {
                return Ok(Value::Bool(future.is_ready()));
            }
            _ => {
                let available = ["join", "await", "get", "is_ready"];
                bail_unknown_method!(method, "Future", available);
            }
        }
    }

    // Channel methods (send, recv, try_recv)
    if let Value::Channel(ref channel) = recv_val {
        match method {
            "send" => {
                let val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                channel.send(val).map_err(|e| CompileError::Semantic(e))?;
                return Ok(Value::Nil);
            }
            "recv" => {
                let val = channel.recv().map_err(|e| CompileError::Semantic(e))?;
                return Ok(val);
            }
            "try_recv" => {
                return Ok(match channel.try_recv() {
                    Some(val) => Value::Enum {
                        enum_name: "Option".to_string(),
                        variant: "Some".to_string(),
                        payload: Some(Box::new(val)),
                    },
                    None => Value::Enum {
                        enum_name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: None,
                    },
                });
            }
            _ => {
                let available = ["send", "recv", "try_recv"];
                bail_unknown_method!(method, "Channel", available);
            }
        }
    }

    // ThreadPool methods (submit)
    if let Value::ThreadPool(ref _pool) = recv_val {
        match method {
            "submit" => {
                // pool.submit(func, arg) - submit a task to the pool
                let func_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let arg_val = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
                let future = spawn_future_with_callable(func_val, arg_val, functions, classes, enums, impl_methods);
                return Ok(Value::Future(future));
            }
            _ => {
                let available = ["submit"];
                bail_unknown_method!(method, "ThreadPool", available);
            }
        }
    }

    // Static method calls on class constructor (e.g. Calculator.add(...))
    if let Value::Constructor { ref class_name } = recv_val {
        if let Some(class_def) = classes.get(class_name) {
            // Find static method (no self parameter)
            if let Some(method_def) = class_def.methods.iter().find(|m| m.name == method) {
                // Execute without self
                let mut local_env = env.clone();
                let mut positional_idx = 0;
                for arg in args {
                    let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                    if let Some(name) = &arg.name {
                        local_env.insert(name.clone(), val);
                    } else if positional_idx < method_def.params.len() {
                        let param = &method_def.params[positional_idx];
                        local_env.insert(param.name.clone(), val);
                        positional_idx += 1;
                    }
                }
                return match exec_block(&method_def.body, &mut local_env, functions, classes, enums, impl_methods) {
                    Ok(Control::Return(v)) => Ok(v),
                    Ok(_) => Ok(Value::Nil),
                    Err(e) => Err(e),
                };
            }
            // Collect available static methods for suggestion
            let available: Vec<&str> = class_def
                .methods
                .iter()
                .filter(|m| !m.params.iter().any(|p| p.name == "self"))
                .map(|m| m.name.as_str())
                .collect();
            let mut msg = format!("unknown static method {method} on class {class_name}");
            if let Some(suggestion) = crate::error::typo::format_suggestion(method, available) {
                msg.push_str(&format!("; {}", suggestion));
            }
            return Err(CompileError::Semantic(msg));
        }
        // Collect available classes for suggestion
        let available: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
        let mut msg = format!("unknown class {class_name}");
        if let Some(suggestion) = crate::error::typo::format_suggestion(class_name, available) {
            msg.push_str(&format!("; {}", suggestion));
        }
        return Err(CompileError::Semantic(msg));
    }

    // Mock object methods (when, with, returns, returnsOnce, verify, called, calledTimes, calledWith, reset)
    if let Value::Mock(ref mock) = recv_val {
        match method {
            // when(:method_name) - Configure a method for stubbing
            "when" => {
                let method_name = eval_arg(args, 0, Value::Symbol("".to_string()), env, functions, classes, enums, impl_methods)?;
                let method_str = match &method_name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => return Err(CompileError::Semantic("when expects symbol or string method name".into())),
                };
                mock.when_method(&method_str);
                return Ok(Value::Mock(mock.clone()));
            }
            // withArgs(args...) - Set argument matchers for current configuration
            // Note: "with" is a reserved keyword, so we use "withArgs" or "with_args"
            "withArgs" | "with_args" => {
                let mut matchers = Vec::new();
                for arg in args {
                    let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                    let matcher = match val {
                        Value::Matcher(m) => m,
                        other => crate::value::MatcherValue::Exact(Box::new(other)),
                    };
                    matchers.push(matcher);
                }
                mock.with_args(matchers);
                return Ok(Value::Mock(mock.clone()));
            }
            // returns(value) - Set return value for configured method
            "returns" => {
                let return_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                mock.returns(return_val);
                return Ok(Value::Mock(mock.clone()));
            }
            // returnsOnce(value) - Set return value for next call only
            "returnsOnce" | "returns_once" => {
                let return_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                mock.returns_once(return_val);
                return Ok(Value::Mock(mock.clone()));
            }
            // verify(:method_name) - Start verification for a method
            "verify" => {
                let method_name = eval_arg(args, 0, Value::Symbol("".to_string()), env, functions, classes, enums, impl_methods)?;
                let method_str = match &method_name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => return Err(CompileError::Semantic("verify expects symbol or string method name".into())),
                };
                mock.when_method(&method_str); // Reuse to set current method
                return Ok(Value::Mock(mock.clone()));
            }
            // called() - Check if method was called at least once (returns bool)
            "called" => {
                let configuring = mock.configuring_method.lock().unwrap();
                if let Some(ref method_name) = *configuring {
                    let was_called = mock.was_called(method_name);
                    return Ok(Value::Bool(was_called));
                }
                return Err(CompileError::Semantic("called() must be chained after verify(:method)".into()));
            }
            // calledTimes(n) - Check exact call count (returns bool)
            "calledTimes" | "called_times" => {
                let expected = eval_arg_int(args, 0, 1, env, functions, classes, enums, impl_methods)?;
                let configuring = mock.configuring_method.lock().unwrap();
                if let Some(ref method_name) = *configuring {
                    let actual = mock.call_count(method_name) as i64;
                    return Ok(Value::Bool(actual == expected));
                }
                return Err(CompileError::Semantic("calledTimes() must be chained after verify(:method)".into()));
            }
            // calledWith(args...) - Check if method was called with specific arguments (returns bool)
            "calledWith" | "called_with" => {
                let mut expected_args = Vec::new();
                for arg in args {
                    let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                    expected_args.push(val);
                }
                let configuring = mock.configuring_method.lock().unwrap();
                if let Some(ref method_name) = *configuring {
                    let was_called_with = mock.was_called_with(method_name, &expected_args);
                    return Ok(Value::Bool(was_called_with));
                }
                return Err(CompileError::Semantic("calledWith() must be chained after verify(:method)".into()));
            }
            // reset() - Clear all call records
            "reset" => {
                mock.reset();
                return Ok(Value::Mock(mock.clone()));
            }
            // getCalls(:method) - Get all calls to a method (for debugging/custom assertions)
            "getCalls" | "get_calls" => {
                let method_name = eval_arg(args, 0, Value::Symbol("".to_string()), env, functions, classes, enums, impl_methods)?;
                let method_str = match &method_name {
                    Value::Symbol(s) => s.clone(),
                    Value::Str(s) => s.clone(),
                    _ => return Err(CompileError::Semantic("getCalls expects symbol or string method name".into())),
                };
                let calls = mock.get_calls(&method_str);
                let call_arrays: Vec<Value> = calls.into_iter().map(Value::Array).collect();
                return Ok(Value::Array(call_arrays));
            }
            // Any other method is treated as a mock call that should be recorded
            _ => {
                // Evaluate arguments
                let mut call_args = Vec::new();
                for arg in args {
                    let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                    call_args.push(val);
                }
                // Record the call
                mock.record_call(method, call_args.clone());
                // Return configured value
                return Ok(mock.get_return_value(method, &call_args));
            }
        }
    }

    Err(CompileError::Semantic(format!("method call on unsupported type: {method}")))
}

/// Evaluate a method call and return both the result and the potentially modified self.
/// This is used when we need to persist mutations to self back to the calling environment.
fn evaluate_method_call_with_self_update(
    receiver: &Box<Expr>,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<Value>), CompileError> {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Only handle Object methods with self mutation
    if let Value::Object { class, fields } = recv_val.clone() {
        // Try to find and execute the method
        if let Some((result, updated_self)) = find_and_exec_method_with_self(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            return Ok((result, Some(updated_self)));
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(method, args, &class, &fields, env, functions, classes, enums, impl_methods)? {
            // method_missing returns just a result, self is not mutated
            return Ok((result, None));
        }
        // Collect available methods for typo suggestion
        let mut available_methods: Vec<&str> = Vec::new();
        if let Some(methods) = impl_methods.get(&class) {
            available_methods.extend(methods.iter().map(|m| m.name.as_str()));
        }
        available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
        bail_unknown_method!(method, class, available_methods);
    }

    // For non-objects, just use regular method call
    let result = evaluate_method_call(receiver, method, args, env, functions, classes, enums, impl_methods)?;
    Ok((result, None))
}

/// Find and execute a method, returning both result and modified self.
fn find_and_exec_method_with_self(
    method: &str,
    args: &[simple_parser::ast::Argument],
    class: &str,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Value, Value)>, CompileError> {
    // Check class methods
    if let Some(class_def) = classes.get(class) {
        if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(func, args, env, functions, classes, enums, impl_methods, class, fields)?;
            return Ok(Some((result, updated_self)));
        }
    }
    // Check impl methods
    if let Some(methods) = impl_methods.get(class) {
        if let Some(func) = methods.iter().find(|m| m.name == method) {
            let (result, updated_self) = exec_function_with_self_return(func, args, env, functions, classes, enums, impl_methods, class, fields)?;
            return Ok(Some((result, updated_self)));
        }
    }
    Ok(None)
}

/// Execute a function and return both the result and the modified self value.
fn exec_function_with_self_return(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    class_name: &str,
    fields: &HashMap<String, Value>,
) -> Result<(Value, Value), CompileError> {
    let mut local_env = Env::new();

    // Set up self
    local_env.insert(
        "self".into(),
        Value::Object {
            class: class_name.to_string(),
            fields: fields.clone(),
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

    // Execute the function body with implicit return support
    let result = match exec_block_fn(&func.body, &mut local_env, functions, classes, enums, impl_methods) {
        Ok((Control::Return(v), _)) => v,
        Ok((_, Some(v))) => v, // Implicit return from last expression
        Ok((_, None)) => Value::Nil,
        Err(CompileError::TryError(val)) => val,
        Err(e) => return Err(e),
    };

    // Get the potentially modified self
    let updated_self = local_env.get("self").cloned().unwrap_or_else(|| Value::Object {
        class: class_name.to_string(),
        fields: fields.clone(),
    });

    Ok((result, updated_self))
}
