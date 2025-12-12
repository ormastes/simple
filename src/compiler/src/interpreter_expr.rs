/// Evaluate a constant expression at compile time
#[instrument(skip(env, functions, classes, enums, impl_methods))]
pub(crate) fn evaluate_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(Value::Int(*value)),
        Expr::TypedInteger(value, _suffix) => {
            // For now, we treat typed integers the same as regular integers
            // The type suffix is used for type checking, not runtime behavior
            Ok(Value::Int(*value))
        }
        Expr::Float(value) => Ok(Value::Float(*value)),
        Expr::TypedFloat(value, _suffix) => {
            // For now, we treat typed floats the same as regular floats
            Ok(Value::Float(*value))
        }
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Nil => Ok(Value::Nil),
        Expr::String(s) => Ok(Value::Str(s.clone())),
        Expr::TypedString(s, _suffix) => {
            // For now, we treat typed strings the same as regular strings
            // The unit suffix is used for type checking, not runtime behavior
            Ok(Value::Str(s.clone()))
        }
        Expr::FString(parts) => {
            let mut out = String::new();
            for part in parts {
                match part {
                    FStringPart::Literal(lit) => out.push_str(lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        out.push_str(&v.to_display_string());
                    }
                }
            }
            Ok(Value::Str(out))
        }
        Expr::Symbol(s) => Ok(Value::Symbol(s.clone())),
        Expr::Identifier(name) => {
            // Check for Option::None literal using type-safe variant
            if name == OptionVariant::None.as_str() {
                return Ok(Value::none());
            }
            // First check env for local variables and closures
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            // Then check functions for top-level function definitions
            // Return as Value::Function for first-class function usage
            if let Some(func) = functions.get(name) {
                return Ok(Value::Function {
                    name: name.clone(),
                    def: Box::new(func.clone()),
                    captured_env: Env::new(), // Top-level functions don't capture
                });
            }
            // Check classes - return as Constructor for constructor polymorphism
            if classes.contains_key(name) {
                return Ok(Value::Constructor {
                    class_name: name.clone(),
                });
            }
            // Collect all known names for typo suggestion
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut msg = format!("undefined variable: {name}");
            if let Some(suggestion) = crate::error::typo::format_suggestion(name, known_names) {
                msg.push_str(&format!("; {}", suggestion));
            }
            Err(CompileError::Semantic(msg))
        }
        Expr::New { kind, expr } => {
            let inner = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            match kind {
                PointerKind::Unique => Ok(Value::Unique(ManualUniqueValue::new(inner))),
                PointerKind::Shared => Ok(Value::Shared(ManualSharedValue::new(inner))),
                PointerKind::Weak => {
                    if let Value::Shared(shared) = inner {
                        Ok(Value::Weak(ManualWeakValue::new_from_shared(&shared)))
                    } else {
                        Err(CompileError::Semantic(
                            "new - expects a shared pointer to create a weak reference".into(),
                        ))
                    }
                }
                PointerKind::Handle => Ok(Value::Handle(ManualHandleValue::new(inner))),
                PointerKind::Borrow => Ok(Value::Borrow(BorrowValue::new(inner))),
                PointerKind::BorrowMut => Ok(Value::BorrowMut(BorrowMutValue::new(inner))),
            }
        }
        Expr::Binary { op, left, right } => {
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
            match op {
                BinOp::Add => match (left_val, right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
                    (Value::Str(a), b) => Ok(Value::Str(format!("{a}{}", b.to_display_string()))),
                    (a, Value::Str(b)) => Ok(Value::Str(format!("{}{}", a.to_display_string(), b))),
                    (l, r) => Ok(Value::Int(l.as_int()? + r.as_int()?)),
                },
                BinOp::Sub => Ok(Value::Int(left_val.as_int()? - right_val.as_int()?)),
                BinOp::Mul => Ok(Value::Int(left_val.as_int()? * right_val.as_int()?)),
                BinOp::Div => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("division by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? / r))
                    }
                }
                BinOp::Mod => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("modulo by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? % r))
                    }
                }
                BinOp::Eq => Ok(Value::Bool(left_val == right_val)),
                BinOp::NotEq => Ok(Value::Bool(left_val != right_val)),
                BinOp::Lt => Ok(Value::Bool(left_val.as_int()? < right_val.as_int()?)),
                BinOp::Gt => Ok(Value::Bool(left_val.as_int()? > right_val.as_int()?)),
                BinOp::LtEq => Ok(Value::Bool(left_val.as_int()? <= right_val.as_int()?)),
                BinOp::GtEq => Ok(Value::Bool(left_val.as_int()? >= right_val.as_int()?)),
                BinOp::Is => Ok(Value::Bool(left_val == right_val)),
                BinOp::And => Ok(Value::Bool(left_val.truthy() && right_val.truthy())),
                BinOp::Or => Ok(Value::Bool(left_val.truthy() || right_val.truthy())),
                BinOp::Pow => {
                    let base = left_val.as_int()?;
                    let exp = right_val.as_int()?;
                    if exp < 0 {
                        Err(CompileError::Semantic(
                            "negative exponent not supported for integers".into(),
                        ))
                    } else {
                        Ok(Value::Int(base.pow(exp as u32)))
                    }
                }
                BinOp::FloorDiv => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("floor division by zero".into()))
                    } else {
                        let l = left_val.as_int()?;
                        // Floor division: always round towards negative infinity
                        Ok(Value::Int(l.div_euclid(r)))
                    }
                }
                BinOp::BitAnd => Ok(Value::Int(left_val.as_int()? & right_val.as_int()?)),
                BinOp::BitOr => Ok(Value::Int(left_val.as_int()? | right_val.as_int()?)),
                BinOp::BitXor => Ok(Value::Int(left_val.as_int()? ^ right_val.as_int()?)),
                BinOp::ShiftLeft => Ok(Value::Int(left_val.as_int()? << right_val.as_int()?)),
                BinOp::ShiftRight => Ok(Value::Int(left_val.as_int()? >> right_val.as_int()?)),
                BinOp::In => {
                    // Membership test: check if left is in right (array, tuple, dict, or string)
                    match right_val {
                        Value::Array(arr) => Ok(Value::Bool(arr.contains(&left_val))),
                        Value::Tuple(tup) => Ok(Value::Bool(tup.contains(&left_val))),
                        Value::Dict(dict) => {
                            let key = left_val.to_key_string();
                            Ok(Value::Bool(dict.contains_key(&key)))
                        }
                        Value::Str(s) => {
                            let needle = left_val.to_key_string();
                            Ok(Value::Bool(s.contains(&needle)))
                        }
                        _ => Err(CompileError::Semantic(
                            "'in' operator requires array, tuple, dict, or string".into(),
                        )),
                    }
                }
            }
        }
        Expr::Unary { op, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)?;
            match op {
                UnaryOp::Neg => Ok(Value::Int(-val.as_int()?)),
                UnaryOp::Not => Ok(Value::Bool(!val.truthy())),
                UnaryOp::BitNot => Ok(Value::Int(!val.as_int()?)),
                UnaryOp::Ref => Ok(Value::Borrow(BorrowValue::new(val))),
                UnaryOp::RefMut => Ok(Value::BorrowMut(BorrowMutValue::new(val))),
                UnaryOp::Deref => Ok(val.deref_pointer()),
            }
        }
        Expr::Lambda { params, body, move_mode } => {
            let names: Vec<String> = params
                .iter()
                .map(|LambdaParam { name, .. }| name.clone())
                .collect();
            // For move closures, we capture by value (clone the environment)
            // For regular closures, we share the environment reference
            // In the interpreter, both behave the same since we clone env anyway
            let captured_env = if move_mode.is_move() {
                // Move closure: capture a snapshot of current env
                env.clone()
            } else {
                env.clone()
            };
            Ok(Value::Lambda {
                params: names,
                body: body.clone(),
                env: captured_env,
            })
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)
            } else {
                Ok(Value::Nil)
            }
        }
        Expr::Match { subject, arms } => {
            let subject_val = evaluate_expr(subject, env, functions, classes, enums, impl_methods)?;

            // Check for strong enum - disallow wildcard/catch-all patterns
            if let Value::Enum { enum_name, .. } = &subject_val {
                if let Some(enum_def) = enums.get(enum_name) {
                    let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);
                    if is_strong {
                        for arm in arms {
                            if is_catch_all_pattern(&arm.pattern) {
                                return Err(CompileError::Semantic(format!(
                                    "strong enum '{}' does not allow wildcard or catch-all patterns in match",
                                    enum_name
                                )));
                            }
                        }
                    }
                }
            }

            for arm in arms {
                let mut arm_bindings = HashMap::new();
                if pattern_matches(&arm.pattern, &subject_val, &mut arm_bindings, enums)? {
                    if let Some(guard) = &arm.guard {
                        let mut guard_env = env.clone();
                        for (name, value) in &arm_bindings {
                            guard_env.insert(name.clone(), value.clone());
                        }
                        let guard_result = evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                        if !guard_result.truthy() {
                            continue;
                        }
                    }
                    let mut arm_env = env.clone();
                    for (name, value) in arm_bindings {
                        arm_env.insert(name, value);
                    }
                    let mut result = Value::Nil;
                    for stmt in &arm.body.statements {
                        match exec_node(stmt, &mut arm_env, functions, classes, enums, impl_methods)? {
                            Control::Return(v) => return Ok(v),
                            Control::Break(_) => return Ok(Value::Nil),
                            Control::Continue => break,
                            Control::Next => {
                                if let Node::Expression(expr) = stmt {
                                    result = evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                }
                            }
                        }
                    }
                    return Ok(result);
                }
            }
            Err(CompileError::Semantic("match exhausted: no pattern matched".into()))
        }
        Expr::Call { callee, args } => {
            evaluate_call(callee, args, env, functions, classes, enums, impl_methods)
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => evaluate_method_call(
            receiver,
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::FieldAccess { receiver, field } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            match recv_val {
                Value::Object { ref fields, ref class, .. } => {
                    // First, try direct field access
                    if let Some(val) = fields.get(field) {
                        return Ok(val.clone());
                    }
                    // Auto-initializing internal fields: fields starting with '_' default to 0
                    if field.starts_with('_') {
                        return Ok(Value::Int(0));
                    }
                    // Auto-forwarding: try get_<field>() or is_<field>() methods
                    let getter_name = format!("get_{}", field);
                    let is_getter_name = format!("is_{}", field);

                    if let Some(class_def) = classes.get(class) {
                        // Try get_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == getter_name) {
                            // Call the getter method with self
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return exec_method_function(method, &[], &self_val, env, functions, classes, enums, impl_methods);
                        }
                        // Try is_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == is_getter_name) {
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return exec_method_function(method, &[], &self_val, env, functions, classes, enums, impl_methods);
                        }
                    }
                    Err(CompileError::Semantic(format!("unknown field {field}")))
                }
                Value::Constructor { ref class_name } => {
                    // Look up static method on class
                    if let Some(class_def) = classes.get(class_name) {
                        if let Some(method) = class_def.methods.iter().find(|m| &m.name == field) {
                            // Return as a function value for call
                            Ok(Value::Function {
                                name: method.name.clone(),
                                def: Box::new(method.clone()),
                                captured_env: Env::new(),
                            })
                        } else {
                            Err(CompileError::Semantic(format!("unknown method {field} on class {class_name}")))
                        }
                    } else {
                        Err(CompileError::Semantic(format!("unknown class {class_name}")))
                    }
                }
                _ => Err(CompileError::Semantic("field access on non-object".into())),
            }
        }
        Expr::StructInit { name, fields } => {
            let mut map = HashMap::new();
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
            Ok(Value::Object {
                class: name.clone(),
                fields: map,
            })
        }
        Expr::Path(segments) => {
            if segments.len() == 2 {
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
                } else {
                    Err(CompileError::Semantic(format!("unknown enum: {enum_name}")))
                }
            } else {
                Err(CompileError::Semantic(format!(
                    "unsupported path: {:?}",
                    segments
                )))
            }
        }
        Expr::Dict(entries) => {
            let mut map = HashMap::new();
            for (k, v) in entries {
                // Handle dict spread: **expr
                if let Expr::DictSpread(inner) = k {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(spread_map) = spread_val {
                        for (sk, sv) in spread_map {
                            map.insert(sk, sv);
                        }
                    } else {
                        return Err(CompileError::Semantic(
                            "dict spread requires dict value".into(),
                        ));
                    }
                } else {
                    let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                    let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                    map.insert(key_val.to_key_string(), val);
                }
            }
            Ok(Value::Dict(map))
        }
        Expr::Range { start, end, bound } => {
            let start = start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            let end = end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            Ok(create_range_object(start, end, *bound))
        }
        Expr::Array(items) => {
            let mut arr = Vec::new();
            for item in items {
                // Handle spread operator: *expr
                if let Expr::Spread(inner) = item {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    match spread_val {
                        Value::Array(spread_arr) => arr.extend(spread_arr),
                        Value::Tuple(tup) => arr.extend(tup),
                        _ => {
                            return Err(CompileError::Semantic(
                                "spread operator requires array or tuple".into(),
                            ))
                        }
                    }
                } else {
                    arr.push(evaluate_expr(
                        item,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?);
                }
            }
            Ok(Value::Array(arr))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(
                    item,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?);
            }
            Ok(Value::Tuple(tup))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
            match recv_val {
                Value::Array(arr) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("array index out of bounds: {raw_idx}"))
                    })
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
                    tup.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("tuple index out of bounds: {raw_idx}"))
                    })
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
                        .ok_or_else(|| {
                            CompileError::Semantic(format!("string index out of bounds: {raw_idx}"))
                        })
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic(
                    "index access on non-indexable type".into(),
                )),
            }
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let envs = comprehension_iterate(
                &iter_val, pattern, condition, env, functions, classes, enums, impl_methods,
            )?;

            let mut result = Vec::new();
            for mut inner_env in envs {
                let val = evaluate_expr(expr, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.push(val);
            }
            Ok(Value::Array(result))
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
                &iter_val, pattern, condition, env, functions, classes, enums, impl_methods,
            )?;

            let mut result = HashMap::new();
            for mut inner_env in envs {
                let k = evaluate_expr(key, &mut inner_env, functions, classes, enums, impl_methods)?;
                let v = evaluate_expr(value, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.insert(k.to_key_string(), v);
            }
            Ok(Value::Dict(result))
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
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

            match recv_val {
                Value::Array(arr) => Ok(Value::Array(slice_collection(
                    &arr, start_idx, end_idx, step_val,
                ))),
                Value::Str(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    let sliced = slice_collection(&chars, start_idx, end_idx, step_val);
                    Ok(Value::Str(sliced.into_iter().collect()))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(
                    &tup, start_idx, end_idx, step_val,
                ))),
                _ => Err(CompileError::Semantic("slice on non-sliceable type".into())),
            }
        }
        Expr::Spread(inner) => {
            // Spread is handled by Array/Dict evaluation, but standalone should work too
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::DictSpread(inner) => {
            // DictSpread is handled by Dict evaluation
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::Spawn(inner) => Ok(spawn_actor_with_expr(
            inner,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )),
        Expr::Await(inner) => {
            check_async_violation("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => f.await_result().map_err(|e| CompileError::Semantic(e)),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| CompileError::Semantic(e))?;
                    Ok(Value::Nil)
                }
                other => Ok(other),
            }
        }
        Expr::Yield(maybe_val) => {
            let yield_val = match maybe_val {
                Some(expr) => evaluate_expr(expr, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };

            let added = GENERATOR_YIELDS.with(|cell| {
                if let Some(yields) = cell.borrow_mut().as_mut() {
                    yields.push(yield_val.clone());
                    true
                } else {
                    false
                }
            });

            if !added {
                return Err(CompileError::Semantic(
                    "yield called outside of generator".into(),
                ));
            }

            Ok(Value::Nil)
        }
        Expr::FunctionalUpdate {
            target,
            method,
            args,
        } => {
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
        }
        Expr::MacroInvocation {
            name,
            args: macro_args,
        } => evaluate_macro_invocation(
            name,
            macro_args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::Try(inner) => {
            // Try operator: expr? - unwrap Ok or propagate Err
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) => {
                    match ResultVariant::from_name(variant) {
                        Some(ResultVariant::Ok) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(ResultVariant::Err) => {
                            // Return the Err as a TryError that should be propagated
                            Err(CompileError::TryError(val))
                        }
                        None => Err(CompileError::Semantic(format!(
                            "invalid Result variant: {}",
                            variant
                        ))),
                    }
                }
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) => {
                    match OptionVariant::from_name(variant) {
                        Some(OptionVariant::Some) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(OptionVariant::None) => {
                            // Return None as a TryError
                            Err(CompileError::TryError(val))
                        }
                        None => Err(CompileError::Semantic(format!(
                            "invalid Option variant: {}",
                            variant
                        ))),
                    }
                }
                _ => Err(CompileError::Semantic(
                    "? operator requires Result or Option type".into(),
                )),
            }
        }
        #[allow(unreachable_patterns)]
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}
