// Block closure execution helpers for interpreter_call module

fn get_iterator_values(iterable: &Value) -> Result<Vec<Value>, CompileError> {
    match iterable {
        Value::Array(arr) => Ok(arr.clone()),
        Value::Tuple(t) => Ok(t.clone()),
        Value::Str(s) => {
            Ok(s.chars().map(|c| Value::Str(c.to_string())).collect())
        }
        Value::Generator(gen) => {
            Ok(gen.collect_remaining())
        }
        Value::Object { class, fields } => {
            // Handle Range class objects
            if class == "Range" {
                let start = fields.get("start").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let end = fields.get("end").and_then(|v| v.as_int().ok()).unwrap_or(0);
                let inclusive = fields.get("inclusive").map(|v| v.truthy()).unwrap_or(false);
                let mut values = Vec::new();
                if inclusive {
                    for i in start..=end {
                        values.push(Value::Int(i));
                    }
                } else {
                    for i in start..end {
                        values.push(Value::Int(i));
                    }
                }
                return Ok(values);
            }
            bail_semantic!("Object is not iterable")
        }
        _ => bail_semantic!("Value is not iterable"),
    }
}

/// Execute a block closure (BDD DSL colon-block)
/// Executes each statement in sequence and returns the last expression's value (or Nil)
fn exec_block_closure(
    nodes: &[simple_parser::ast::Node],
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use simple_parser::ast::Node;

    let mut local_env = captured_env.clone();
    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                last_value = evaluate_expr(expr, &local_env, functions, classes, enums, impl_methods)?;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, &local_env, functions, classes, enums, impl_methods)?;
                    // Extract name from pattern
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, &local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    local_env.insert(name.clone(), val);
                }
                last_value = Value::Nil;
            }
            Node::Context(ctx_stmt) => {
                // Handle context statement for BDD nested contexts
                let context_obj = evaluate_expr(&ctx_stmt.context, &local_env, functions, classes, enums, impl_methods)?;

                // Check if this is a BDD-style context (string or symbol description)
                match &context_obj {
                    Value::Str(name) | Value::Symbol(name) => {
                        // BDD-style context: context "description": block
                        let name_str = if matches!(context_obj, Value::Symbol(_)) {
                            format!("with {}", name)
                        } else {
                            name.clone()
                        };

                        // Check if this is a symbol referencing a context_def
                        let ctx_def_blocks = if matches!(context_obj, Value::Symbol(_)) {
                            BDD_CONTEXT_DEFS.with(|cell| {
                                cell.borrow().get(name).cloned()
                            })
                        } else {
                            None
                        };

                        // Get current indent level
                        let indent = BDD_INDENT.with(|cell| *cell.borrow());
                        let indent_str = "  ".repeat(indent);

                        // Print context name
                        println!("{}{}", indent_str, name_str);

                        // Increase indent for nested blocks
                        BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

                        // Push new hook level for this context
                        BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
                        BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));

                        // If this is a context_def reference, execute its givens first
                        if let Some(ctx_blocks) = ctx_def_blocks {
                            for ctx_block in ctx_blocks {
                                exec_block_value(ctx_block, &local_env, functions, classes, enums, impl_methods)?;
                            }
                        }

                        // Execute the block by recursively processing its nodes
                        last_value = exec_block_closure(&ctx_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;

                        // Pop hook level
                        BDD_BEFORE_EACH.with(|cell| { cell.borrow_mut().pop(); });
                        BDD_AFTER_EACH.with(|cell| { cell.borrow_mut().pop(); });

                        // Note: lazy values persist within the describe block
                        // They'll be overwritten if a sibling context defines the same name

                        // Restore indent
                        BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);
                    }
                    _ => {
                        // Non-BDD context: execute body with context object set
                        // For now, just execute the body
                        last_value = exec_block_closure(&ctx_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;
                    }
                }
            }
            Node::If(if_stmt) => {
                // Handle if-let patterns: if let PATTERN = EXPR:
                if let Some(pattern) = &if_stmt.let_pattern {
                    let value = evaluate_expr(&if_stmt.condition, &local_env, functions, classes, enums, impl_methods)?;
                    let mut bindings = std::collections::HashMap::new();
                    if pattern_matches(pattern, &value, &mut bindings, enums)? {
                        // Pattern matched - add bindings to local env for this block
                        for (name, val) in bindings {
                            local_env.insert(name, val);
                        }
                        last_value = exec_block_closure_mut(&if_stmt.then_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(&else_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else {
                        last_value = Value::Nil;
                    }
                } else {
                    // Handle normal if statements in block closures
                    if evaluate_expr(&if_stmt.condition, &local_env, functions, classes, enums, impl_methods)?.truthy() {
                        last_value = exec_block_closure_mut(&if_stmt.then_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else if let Some(ref else_block) = if_stmt.else_block {
                        last_value = exec_block_closure_mut(&else_block.statements, &mut local_env, functions, classes, enums, impl_methods)?;
                    } else {
                        last_value = Value::Nil;
                    }
                }
            }
            Node::For(for_stmt) => {
                // Handle for loops in block closures
                let iterable = evaluate_expr(&for_stmt.iterable, &local_env, functions, classes, enums, impl_methods)?;
                let iter_values = get_iterator_values(&iterable)?;
                for val in iter_values {
                    // Bind the loop variable
                    if let simple_parser::ast::Pattern::Identifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(ref name) = for_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                    last_value = exec_block_closure(&for_stmt.body.statements, &local_env, functions, classes, enums, impl_methods)?;
                }
            }
            _ => {
                // For other node types, just skip for now
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}

/// Execute statements in an already-existing mutable environment.
/// Used for if-let blocks where assignments should propagate to the outer scope.
fn exec_block_closure_mut(
    nodes: &[simple_parser::ast::Node],
    local_env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use simple_parser::ast::Node;

    let mut last_value = Value::Nil;

    for node in nodes {
        match node {
            Node::Expression(expr) => {
                last_value = evaluate_expr(expr, local_env, functions, classes, enums, impl_methods)?;
            }
            Node::Let(let_stmt) => {
                if let Some(ref value_expr) = let_stmt.value {
                    let val = evaluate_expr(value_expr, local_env, functions, classes, enums, impl_methods)?;
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        local_env.insert(name.clone(), val);
                    }
                }
                last_value = Value::Nil;
            }
            Node::Assignment(assign_stmt) => {
                let val = evaluate_expr(&assign_stmt.value, local_env, functions, classes, enums, impl_methods)?;
                if let simple_parser::ast::Expr::Identifier(name) = &assign_stmt.target {
                    local_env.insert(name.clone(), val);
                }
                last_value = Value::Nil;
            }
            _ => {
                last_value = Value::Nil;
            }
        }
    }

    Ok(last_value)
}
