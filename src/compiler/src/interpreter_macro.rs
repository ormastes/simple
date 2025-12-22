// Macro invocation and expansion (part of interpreter module)

fn evaluate_macro_invocation(
    name: &str,
    macro_args: &[MacroArg],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match name {
        "println" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            println!("{}", output);
            Ok(Value::Nil)
        }
        "print" => {
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                print!("{}", val.to_display_string());
            }
            Ok(Value::Nil)
        }
        "vec" => {
            let mut items = Vec::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Array(items))
        }
        "assert" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                if !val.truthy() {
                    return Err(CompileError::Semantic("assertion failed".into()));
                }
            }
            Ok(Value::Nil)
        }
        "assert_eq" => {
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(left), MacroArg::Expr(right)) = (&macro_args[0], &macro_args[1]);
                let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                if left_val != right_val {
                    return Err(CompileError::Semantic(format!(
                        "assertion failed: {:?} != {:?}",
                        left_val, right_val
                    )));
                }
            }
            Ok(Value::Nil)
        }
        "assert_unit" => {
            // assert_unit!(value, "unit_type") - validate value is of expected unit type
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(value_expr), MacroArg::Expr(type_expr)) =
                    (&macro_args[0], &macro_args[1]);
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                let type_val = evaluate_expr(type_expr, env, functions, classes, enums, impl_methods)?;

                // Extract type name from string or symbol
                let type_name = match &type_val {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => {
                        return Err(CompileError::Semantic(
                            "assert_unit: second argument must be a string or symbol representing the unit type".into(),
                        ));
                    }
                };

                // Check if the type is a valid unit type
                if !is_unit_type(&type_name) {
                    return Err(CompileError::Semantic(format!(
                        "assert_unit: '{}' is not a registered unit type (family or compound unit)",
                        type_name
                    )));
                }

                // Validate the value against the unit type
                if let Err(e) = validate_unit_type(&value, &type_name) {
                    return Err(CompileError::Semantic(format!(
                        "unit assertion failed: {}",
                        e
                    )));
                }
            } else {
                return Err(CompileError::Semantic(
                    "assert_unit requires two arguments: assert_unit!(value, \"unit_type\")".into(),
                ));
            }
            Ok(Value::Nil)
        }
        "panic" => {
            let msg = macro_args
                .first()
                .map(|arg| {
                    if let MacroArg::Expr(e) = arg {
                        evaluate_expr(e, env, functions, classes, enums, impl_methods)
                            .map(|v| v.to_display_string())
                            .unwrap_or_else(|_| "panic".into())
                    } else {
                        "panic".into()
                    }
                })
                .unwrap_or_else(|| "explicit panic".into());
            Err(CompileError::Semantic(format!("panic: {}", msg)))
        }
        "format" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            Ok(Value::Str(output))
        }
        "dbg" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                eprintln!("[dbg] {:?}", val);
                Ok(val)
            } else {
                Ok(Value::Nil)
            }
        }
        _ => {
            let macro_def = USER_MACROS.with(|cell| cell.borrow().get(name).cloned());
            if let Some(m) = macro_def {
                expand_user_macro(&m, macro_args, env, functions, classes, enums, impl_methods)
            } else {
                Err(CompileError::Semantic(format!("unknown macro: {}!", name)))
            }
        }
    }
}

/// Expand a user-defined macro with given arguments
fn expand_user_macro(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = env.clone();
    let const_bindings = build_macro_const_bindings(macro_def, args, env, functions, classes, enums, impl_methods)?;

    for (idx, param) in macro_def.params.iter().enumerate() {
        if let Some(MacroArg::Expr(e)) = args.get(idx) {
            let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
            local_env.insert(param.name.clone(), val);
        }
    }

    let return_label = macro_def
        .contract
        .iter()
        .find_map(|item| match item {
            MacroContractItem::Returns(ret) => ret.label.clone(),
            _ => None,
        });

    let mut last_value = Value::Nil;

    for stmt in &macro_def.body {
        match stmt {
            MacroStmt::ConstEval(block) => {
                match exec_block(block, &mut local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(v) => return Ok(v),
                    Control::Break(_) | Control::Continue => {}
                    Control::Next => {}
                }
            }
            MacroStmt::Emit { label, block } => {
                let expanded_block = substitute_block_templates(block, &const_bindings);
                let (control, maybe_value) =
                    exec_block_fn(&expanded_block, &mut local_env, functions, classes, enums, impl_methods)?;
                if let Control::Return(v) = control {
                    return Ok(v);
                }
                let should_capture = if let Some(expected) = &return_label {
                    expected == label
                } else {
                    label == "result"
                };
                if should_capture {
                    if let Some(val) = maybe_value {
                        last_value = val;
                    }
                }
            }
            MacroStmt::Stmt(node) => match exec_node(node, &mut local_env, functions, classes, enums, impl_methods)? {
                Control::Return(v) => return Ok(v),
                Control::Break(_) | Control::Continue => {}
                Control::Next => {}
            },
        }
    }

    Ok(last_value)
}

fn build_macro_const_bindings(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<HashMap<String, String>, CompileError> {
    let mut bindings = HashMap::new();
    for (idx, param) in macro_def.params.iter().enumerate() {
        if !param.is_const {
            continue;
        }
        let Some(MacroArg::Expr(expr)) = args.get(idx) else {
            continue;
        };
        let value = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
        if let Some(text) = const_value_to_string(&value) {
            bindings.insert(param.name.clone(), text);
        }
    }
    Ok(bindings)
}

fn const_value_to_string(value: &Value) -> Option<String> {
    match value {
        Value::Str(s) => Some(s.clone()),
        Value::Symbol(s) => Some(s.clone()),
        Value::Int(i) => Some(i.to_string()),
        Value::Float(f) => Some(f.to_string()),
        Value::Bool(b) => Some(b.to_string()),
        Value::Nil => Some("nil".to_string()),
        _ => None,
    }
}

fn substitute_block_templates(
    block: &Block,
    const_bindings: &HashMap<String, String>,
) -> Block {
    let mut statements = Vec::new();
    for stmt in &block.statements {
        statements.push(substitute_node_templates(stmt, const_bindings));
    }
    Block {
        span: block.span,
        statements,
    }
}

fn substitute_node_templates(
    node: &Node,
    const_bindings: &HashMap<String, String>,
) -> Node {
    match node {
        Node::Expression(expr) => Node::Expression(substitute_expr_templates(expr, const_bindings)),
        Node::Let(let_stmt) => Node::Let(LetStmt {
            span: let_stmt.span,
            pattern: let_stmt.pattern.clone(),
            ty: let_stmt.ty.clone(),
            value: let_stmt
                .value
                .as_ref()
                .map(|expr| substitute_expr_templates(expr, const_bindings)),
            mutability: let_stmt.mutability,
            storage_class: let_stmt.storage_class,
        }),
        Node::Assignment(assign) => Node::Assignment(AssignmentStmt {
            span: assign.span,
            target: substitute_expr_templates(&assign.target, const_bindings),
            op: assign.op,
            value: substitute_expr_templates(&assign.value, const_bindings),
        }),
        Node::Return(ret) => Node::Return(ReturnStmt {
            span: ret.span,
            value: ret
                .value
                .as_ref()
                .map(|expr| substitute_expr_templates(expr, const_bindings)),
        }),
        Node::If(stmt) => Node::If(IfStmt {
            span: stmt.span,
            condition: substitute_expr_templates(&stmt.condition, const_bindings),
            then_block: substitute_block_templates(&stmt.then_block, const_bindings),
            elif_branches: stmt
                .elif_branches
                .iter()
                .map(|(cond, block)| {
                    (
                        substitute_expr_templates(cond, const_bindings),
                        substitute_block_templates(block, const_bindings),
                    )
                })
                .collect(),
            else_block: stmt
                .else_block
                .as_ref()
                .map(|block| substitute_block_templates(block, const_bindings)),
            let_pattern: stmt.let_pattern.clone(),
        }),
        Node::Match(stmt) => Node::Match(MatchStmt {
            span: stmt.span,
            subject: substitute_expr_templates(&stmt.subject, const_bindings),
            arms: stmt
                .arms
                .iter()
                .map(|arm| MatchArm {
                    span: arm.span,
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(|expr| substitute_expr_templates(expr, const_bindings)),
                    body: substitute_block_templates(&arm.body, const_bindings),
                })
                .collect(),
        }),
        Node::For(stmt) => Node::For(ForStmt {
            span: stmt.span,
            pattern: stmt.pattern.clone(),
            iterable: substitute_expr_templates(&stmt.iterable, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::While(stmt) => Node::While(WhileStmt {
            span: stmt.span,
            condition: substitute_expr_templates(&stmt.condition, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
            let_pattern: stmt.let_pattern.clone(),
        }),
        Node::Loop(stmt) => Node::Loop(LoopStmt {
            span: stmt.span,
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::Context(stmt) => Node::Context(ContextStmt {
            span: stmt.span,
            context: substitute_expr_templates(&stmt.context, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::With(stmt) => Node::With(WithStmt {
            span: stmt.span,
            resource: substitute_expr_templates(&stmt.resource, const_bindings),
            name: stmt.name.clone(),
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::Break(_) | Node::Continue(_) => node.clone(),
        _ => node.clone(),
    }
}

fn substitute_expr_templates(
    expr: &Expr,
    const_bindings: &HashMap<String, String>,
) -> Expr {
    match expr {
        Expr::String(value) => Expr::String(substitute_template_string(value, const_bindings)),
        Expr::TypedString(value, suffix) => Expr::TypedString(
            substitute_template_string(value, const_bindings),
            suffix.clone(),
        ),
        Expr::FString(parts) => Expr::FString(
            parts
                .iter()
                .map(|part| match part {
                    FStringPart::Literal(text) => FStringPart::Literal(
                        substitute_template_string(text, const_bindings),
                    ),
                    FStringPart::Expr(expr_text) => FStringPart::Expr(expr_text.clone()),
                })
                .collect(),
        ),
        Expr::Binary { op, left, right } => Expr::Binary {
            op: op.clone(),
            left: Box::new(substitute_expr_templates(left, const_bindings)),
            right: Box::new(substitute_expr_templates(right, const_bindings)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: op.clone(),
            operand: Box::new(substitute_expr_templates(operand, const_bindings)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(substitute_expr_templates(callee, const_bindings)),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            field: field.clone(),
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            index: Box::new(substitute_expr_templates(index, const_bindings)),
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            index: *index,
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(substitute_expr_templates(condition, const_bindings)),
            then_branch: Box::new(substitute_expr_templates(then_branch, const_bindings)),
            else_branch: else_branch
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(substitute_expr_templates(subject, const_bindings)),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    span: arm.span,
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(|expr| substitute_expr_templates(expr, const_bindings)),
                    body: substitute_block_templates(&arm.body, const_bindings),
                })
                .collect(),
        },
        Expr::Tuple(items) => Expr::Tuple(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::Array(items) => Expr::Array(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::VecLiteral(items) => Expr::VecLiteral(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .iter()
                .map(|(k, v)| {
                    (
                        substitute_expr_templates(k, const_bindings),
                        substitute_expr_templates(v, const_bindings),
                    )
                })
                .collect(),
        ),
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => Expr::ListComprehension {
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
            pattern: pattern.clone(),
            iterable: Box::new(substitute_expr_templates(iterable, const_bindings)),
            condition: condition
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => Expr::DictComprehension {
            key: Box::new(substitute_expr_templates(key, const_bindings)),
            value: Box::new(substitute_expr_templates(value, const_bindings)),
            pattern: pattern.clone(),
            iterable: Box::new(substitute_expr_templates(iterable, const_bindings)),
            condition: condition
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            start: start
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            end: end
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            step: step
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Spread(expr) => Expr::Spread(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::DictSpread(expr) => {
            Expr::DictSpread(Box::new(substitute_expr_templates(expr, const_bindings)))
        }
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, expr)| {
                    (
                        field.clone(),
                        substitute_expr_templates(expr, const_bindings),
                    )
                })
                .collect(),
        },
        Expr::Spawn(expr) => Expr::Spawn(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Await(expr) => Expr::Await(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Yield(expr) => {
            Expr::Yield(expr.as_ref().map(|e| Box::new(substitute_expr_templates(e, const_bindings))))
        }
        Expr::New { kind, expr } => Expr::New {
            kind: *kind,
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
            target_type: target_type.clone(),
        },
        Expr::Range { start, end, bound } => Expr::Range {
            start: start
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            end: end
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            bound: *bound,
        },
        Expr::FunctionalUpdate { target, method, args } => Expr::FunctionalUpdate {
            target: Box::new(substitute_expr_templates(target, const_bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::MacroInvocation { name, args } => Expr::MacroInvocation {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    MacroArg::Expr(expr) => {
                        MacroArg::Expr(substitute_expr_templates(expr, const_bindings))
                    }
                })
                .collect(),
        },
        Expr::Try(expr) => Expr::Try(Box::new(substitute_expr_templates(expr, const_bindings))),
        _ => expr.clone(),
    }
}

fn substitute_template_string(
    input: &str,
    const_bindings: &HashMap<String, String>,
) -> String {
    let mut output = input.to_string();
    for (key, value) in const_bindings {
        let needle = format!("{{{}}}", key);
        if output.contains(&needle) {
            output = output.replace(&needle, value);
        }
    }
    output
}
