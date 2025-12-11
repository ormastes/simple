// ============================================================================
// Control flow execution functions for the interpreter
// ============================================================================

/// Handle loop control flow result. Returns Some if we should exit the loop.
#[inline]
fn handle_loop_control(ctrl: Control) -> Option<Result<Control, CompileError>> {
    match ctrl {
        Control::Next => None,
        Control::Continue => None, // caller handles continue
        Control::Break(_) => Some(Ok(Control::Next)),
        ret @ Control::Return(_) => Some(Ok(ret)),
    }
}

fn exec_if(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Handle if-let: if let PATTERN = EXPR:
    if let Some(pattern) = &if_stmt.let_pattern {
        let value = evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?;
        let mut bindings = HashMap::new();
        if pattern_matches(pattern, &value, &mut bindings, enums)? {
            // Pattern matched - add bindings and execute then block
            for (name, val) in bindings {
                env.insert(name, val);
            }
            return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
        } else if let Some(block) = &if_stmt.else_block {
            // Pattern didn't match - execute else block
            return exec_block(block, env, functions, classes, enums, impl_methods);
        }
        return Ok(Control::Next);
    }

    // Normal if condition
    if evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
        return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
    }
    for (cond, block) in &if_stmt.elif_branches {
        if evaluate_expr(cond, env, functions, classes, enums, impl_methods)?.truthy() {
            return exec_block(block, env, functions, classes, enums, impl_methods);
        }
    }
    if let Some(block) = &if_stmt.else_block {
        return exec_block(block, env, functions, classes, enums, impl_methods);
    }
    Ok(Control::Next)
}

fn exec_while(
    while_stmt: &simple_parser::ast::WhileStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Handle while-let: while let PATTERN = EXPR:
    if let Some(pattern) = &while_stmt.let_pattern {
        loop {
            let value = evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?;
            let mut bindings = HashMap::new();
            if !pattern_matches(pattern, &value, &mut bindings, enums)? {
                break;
            }
            // Pattern matched - add bindings and execute body
            for (name, val) in bindings {
                env.insert(name, val);
            }
            let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
            if matches!(ctrl, Control::Continue) { continue; }
            if let Some(result) = handle_loop_control(ctrl) { return result; }
        }
        return Ok(Control::Next);
    }

    // Normal while loop
    loop {
        if !evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
            break;
        }
        let ctrl = exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
    }
    Ok(Control::Next)
}

fn exec_loop(
    loop_stmt: &simple_parser::ast::LoopStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        let ctrl = exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
    }
}

fn exec_context(
    ctx_stmt: &ContextStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let context_obj = evaluate_expr(&ctx_stmt.context, env, functions, classes, enums, impl_methods)?;
    let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));
    let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);
    result
}

/// Execute a with statement (context manager pattern)
/// with resource as name:
///     body
/// Calls __enter__ before body, __exit__ after (even on error)
fn exec_with(
    with_stmt: &WithStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let resource = evaluate_expr(&with_stmt.resource, env, functions, classes, enums, impl_methods)?;

    // Call __enter__ if it exists
    let enter_result = call_method_if_exists(&resource, "__enter__", &[], env, functions, classes, enums, impl_methods)?;

    // Bind the result to the name if provided
    if let Some(name) = &with_stmt.name {
        env.insert(name.clone(), enter_result.unwrap_or(resource.clone()));
    }

    // Execute the body
    let result = exec_block(&with_stmt.body, env, functions, classes, enums, impl_methods);

    // Always call __exit__ (even if body failed)
    let _ = call_method_if_exists(&resource, "__exit__", &[], env, functions, classes, enums, impl_methods);

    // Remove the binding if it was created
    if let Some(name) = &with_stmt.name {
        env.remove(name);
    }

    result
}

/// Helper to execute a method body with self and fields bound
fn exec_method_body(
    method: &FunctionDef,
    receiver: &Value,
    fields: &HashMap<String, Value>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = env.clone();
    local_env.insert("self".to_string(), receiver.clone());
    for (k, v) in fields {
        local_env.insert(k.clone(), v.clone());
    }
    let result = exec_block(&method.body, &mut local_env, functions, classes, enums, impl_methods)?;
    Ok(if let Control::Return(val) = result { val } else { Value::Nil })
}

/// Helper to call a method if it exists on an object
fn call_method_if_exists(
    receiver: &Value,
    method_name: &str,
    _args: &[Value],
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if let Value::Object { class, fields } = receiver {
        // Check if the class has the method
        if let Some(class_def) = classes.get(class) {
            if let Some(method) = class_def.methods.iter().find(|m| m.name == method_name) {
                return Ok(Some(exec_method_body(method, receiver, fields, env, functions, classes, enums, impl_methods)?));
            }
        }
        // Check impl_methods
        if let Some(methods) = impl_methods.get(class) {
            if let Some(method) = methods.iter().find(|m| m.name == method_name) {
                return Ok(Some(exec_method_body(method, receiver, fields, env, functions, classes, enums, impl_methods)?));
            }
        }
    }
    Ok(None)
}

fn exec_for(
    for_stmt: &simple_parser::ast::ForStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let iterable = evaluate_expr(&for_stmt.iterable, env, functions, classes, enums, impl_methods)?;
    let items = match iterable {
        Value::Object { class, fields } if class == BUILTIN_RANGE => {
            if let Some(Value::Int(start)) = fields.get("start") {
                if let Some(Value::Int(end)) = fields.get("end") {
                    let inclusive = matches!(fields.get("inclusive"), Some(Value::Bool(true)));
                    let mut v = Vec::new();
                    let mut i = *start;
                    if inclusive {
                        while i <= *end {
                            v.push(i);
                            i += 1;
                        }
                    } else {
                        while i < *end {
                            v.push(i);
                            i += 1;
                        }
                    }
                    v
                } else {
                    return Err(CompileError::Semantic("invalid range".into()));
                }
            } else {
                return Err(CompileError::Semantic("invalid range".into()));
            }
        }
        Value::Object { class, fields } if class == BUILTIN_ARRAY => {
            let mut out = Vec::new();
            for (_, v) in fields {
                if let Value::Int(i) = v {
                    out.push(i);
                }
            }
            out
        }
        Value::Array(items) => {
            let mut out = Vec::new();
            for v in items {
                if let Value::Int(i) = v {
                    out.push(i);
                }
            }
            out
        }
        _ => return Err(CompileError::Semantic("for expects range or array".into())),
    };

    for val in items {
        if let Pattern::Identifier(name) = &for_stmt.pattern {
            env.insert(name.clone(), Value::Int(val));
        }
        let ctrl = exec_block(&for_stmt.body, env, functions, classes, enums, impl_methods)?;
        if matches!(ctrl, Control::Continue) { continue; }
        if let Some(result) = handle_loop_control(ctrl) { return result; }
    }
    Ok(Control::Next)
}

fn is_catch_all_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Identifier(_) | Pattern::MutIdentifier(_) => true,
        _ => false,
    }
}

fn exec_match(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let subject = evaluate_expr(&match_stmt.subject, env, functions, classes, enums, impl_methods)?;

    // Check for strong enum - disallow wildcard/catch-all patterns
    if let Value::Enum { enum_name, .. } = &subject {
        if let Some(enum_def) = enums.get(enum_name) {
            let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);
            if is_strong {
                for arm in &match_stmt.arms {
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

    for arm in &match_stmt.arms {
        let mut bindings = HashMap::new();
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums)? {
            if let Some(guard) = &arm.guard {
                let mut guard_env = env.clone();
                for (name, value) in &bindings {
                    guard_env.insert(name.clone(), value.clone());
                }
                if !evaluate_expr(guard, &guard_env, functions, classes, enums, impl_methods)?.truthy() {
                    continue;
                }
            }

            for (name, value) in bindings {
                env.insert(name, value);
            }

            return exec_block(&arm.body, env, functions, classes, enums, impl_methods);
        }
    }

    Ok(Control::Next)
}

fn pattern_matches(
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
) -> Result<bool, CompileError> {
    match pattern {
        Pattern::Wildcard => Ok(true),

        Pattern::Identifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MutIdentifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::Literal(lit_expr) => {
            match lit_expr.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => {
                    if let Value::Int(v) = value {
                        Ok(*v == *i)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Float(f) | Expr::TypedFloat(f, _) => {
                    if let Value::Float(v) = value {
                        Ok((*v - *f).abs() < f64::EPSILON)
                    } else {
                        Ok(false)
                    }
                }
                Expr::String(s) => {
                    if let Value::Str(v) = value {
                        Ok(v == s)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Symbol(sym) => {
                    if let Value::Symbol(v) = value {
                        Ok(v == sym)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Bool(b) => {
                    if let Value::Bool(v) = value {
                        Ok(*v == *b)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Nil => Ok(matches!(value, Value::Nil)),
                _ => Ok(false),
            }
        }

        Pattern::Enum { name: enum_name, variant, payload } => {
            if let Value::Enum { enum_name: ve, variant: vv, payload: value_payload } = value {
                if enum_name == ve && variant == vv {
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        if patterns.len() == 1 {
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)? {
                                return Ok(true);
                            }
                        }
                    }
                    if payload.is_none() && value_payload.is_some() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        Pattern::Tuple(patterns) => {
            if let Value::Tuple(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Array(patterns) => {
            if let Value::Array(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Struct { name, fields } => {
            if let Value::Object { class, fields: obj_fields } = value {
                if class == name {
                    for (field_name, field_pat) in fields {
                        if let Some(field_val) = obj_fields.get(field_name) {
                            if !pattern_matches(field_pat, field_val, bindings, enums)? {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Or(patterns) => {
            for pat in patterns {
                let mut temp_bindings = HashMap::new();
                if pattern_matches(pat, value, &mut temp_bindings, enums)? {
                    bindings.extend(temp_bindings);
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Typed { pattern, ty } => {
            let type_matches = match ty {
                Type::Simple(name) => value.matches_type(name),
                Type::Union(types) => {
                    types.iter().any(|t| {
                        if let Type::Simple(name) = t {
                            value.matches_type(name)
                        } else {
                            true
                        }
                    })
                }
                _ => true,
            };

            if type_matches {
                pattern_matches(pattern, value, bindings, enums)
            } else {
                Ok(false)
            }
        }

        Pattern::Range { start, end, inclusive } => {
            // Range patterns only work with integers
            let Value::Int(val) = value else {
                return Ok(false);
            };
            // Evaluate start and end expressions (must be integer literals)
            let start_val = match start.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            let end_val = match end.as_ref() {
                Expr::Integer(i) | Expr::TypedInteger(i, _) => *i,
                _ => return Ok(false),
            };
            // Check if value is in range
            if *inclusive {
                Ok(*val >= start_val && *val <= end_val)
            } else {
                Ok(*val >= start_val && *val < end_val)
            }
        }

        Pattern::Rest => {
            Ok(true)
        }
    }
}
