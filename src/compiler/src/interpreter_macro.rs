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
                if let MacroArg::Expr(e) = arg {
                    let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                    output.push_str(&val.to_display_string());
                }
            }
            println!("{}", output);
            Ok(Value::Nil)
        }
        "print" => {
            for arg in macro_args {
                if let MacroArg::Expr(e) = arg {
                    let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                    print!("{}", val.to_display_string());
                }
            }
            Ok(Value::Nil)
        }
        "vec" => {
            let mut items = Vec::new();
            for arg in macro_args {
                if let MacroArg::Expr(e) = arg {
                    items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
                }
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
                if let (MacroArg::Expr(left), MacroArg::Expr(right)) = (&macro_args[0], &macro_args[1]) {
                    let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                    let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                    if left_val != right_val {
                        return Err(CompileError::Semantic(format!(
                            "assertion failed: {:?} != {:?}",
                            left_val, right_val
                        )));
                    }
                }
            }
            Ok(Value::Nil)
        }
        "assert_unit" => {
            // assert_unit!(value, "unit_type") - validate value is of expected unit type
            if macro_args.len() >= 2 {
                if let (MacroArg::Expr(value_expr), MacroArg::Expr(type_expr)) = (&macro_args[0], &macro_args[1]) {
                    let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                    let type_val = evaluate_expr(type_expr, env, functions, classes, enums, impl_methods)?;

                    // Extract type name from string or symbol
                    let type_name = match &type_val {
                        Value::Str(s) => s.clone(),
                        Value::Symbol(s) => s.clone(),
                        _ => return Err(CompileError::Semantic(
                            "assert_unit: second argument must be a string or symbol representing the unit type".into()
                        )),
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
                            "unit assertion failed: {}", e
                        )));
                    }
                }
            } else {
                return Err(CompileError::Semantic(
                    "assert_unit requires two arguments: assert_unit!(value, \"unit_type\")".into()
                ));
            }
            Ok(Value::Nil)
        }
        "panic" => {
            let msg = macro_args.first()
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
                if let MacroArg::Expr(e) = arg {
                    let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                    output.push_str(&val.to_display_string());
                }
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
    let pattern = macro_def.patterns.first()
        .ok_or_else(|| CompileError::Semantic(format!("macro {} has no patterns", macro_def.name)))?;

    let mut bindings: HashMap<String, Value> = HashMap::new();
    let mut arg_exprs: HashMap<String, Expr> = HashMap::new();

    for (i, param) in pattern.params.iter().enumerate() {
        match param {
            MacroParam::Ident(name) | MacroParam::Expr(name) => {
                if let Some(MacroArg::Expr(e)) = args.get(i) {
                    let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                    bindings.insert(name.clone(), val);
                    arg_exprs.insert(name.clone(), e.clone());
                } else if let Some(MacroArg::Tokens(s)) = args.get(i) {
                    bindings.insert(name.clone(), Value::Str(s.clone()));
                }
            }
            MacroParam::Type(name) => {
                if let Some(MacroArg::Type(_t)) = args.get(i) {
                    bindings.insert(name.clone(), Value::Nil);
                }
            }
            MacroParam::Variadic { name, separator: _ } => {
                let mut items = Vec::new();
                for arg in args.iter().skip(i) {
                    if let MacroArg::Expr(e) = arg {
                        items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
                    }
                }
                bindings.insert(name.clone(), Value::Array(items));
            }
            MacroParam::Literal(_) => {
            }
        }
    }

    match &pattern.body {
        MacroBody::Expr(e) => {
            let substituted = substitute_macro_params(e, &bindings, &arg_exprs)?;
            evaluate_expr(&substituted, env, functions, classes, enums, impl_methods)
        }
        MacroBody::Block(block) => {
            let mut local_env = env.clone();
            for (name, value) in &bindings {
                local_env.insert(format!("${}", name), value.clone());
                local_env.insert(name.clone(), value.clone());
            }

            let mut last_val = Value::Nil;
            for stmt in &block.statements {
                let substituted_stmt = substitute_macro_params_in_node(stmt, &arg_exprs)?;
                match exec_node(&substituted_stmt, &mut local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(v) => {
                        last_val = v;
                        break;
                    }
                    Control::Break(_) => break,
                    Control::Continue => continue,
                    Control::Next => {}
                }
            }
            Ok(last_val)
        }
        MacroBody::Tokens(_tokens) => {
            Ok(Value::Nil)
        }
    }
}

fn substitute_macro_params(
    expr: &Expr,
    bindings: &HashMap<String, Value>,
    arg_exprs: &HashMap<String, Expr>,
) -> Result<Expr, CompileError> {
    match expr {
        Expr::Identifier(name) => {
            if let Some(stripped) = name.strip_prefix('$') {
                if let Some(original_expr) = arg_exprs.get(stripped) {
                    return Ok(original_expr.clone());
                }
            }
            Ok(expr.clone())
        }
        Expr::Binary { left, op, right } => {
            Ok(Expr::Binary {
                left: Box::new(substitute_macro_params(left, bindings, arg_exprs)?),
                op: op.clone(),
                right: Box::new(substitute_macro_params(right, bindings, arg_exprs)?),
            })
        }
        Expr::Unary { op, operand } => {
            Ok(Expr::Unary {
                op: op.clone(),
                operand: Box::new(substitute_macro_params(operand, bindings, arg_exprs)?),
            })
        }
        Expr::Call { callee, args } => {
            let mut new_args = Vec::new();
            for arg in args {
                new_args.push(simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_macro_params(&arg.value, bindings, arg_exprs)?,
                });
            }
            Ok(Expr::Call {
                callee: Box::new(substitute_macro_params(callee, bindings, arg_exprs)?),
                args: new_args,
            })
        }
        Expr::If { condition, then_branch, else_branch } => {
            Ok(Expr::If {
                condition: Box::new(substitute_macro_params(condition, bindings, arg_exprs)?),
                then_branch: Box::new(substitute_macro_params(then_branch, bindings, arg_exprs)?),
                else_branch: else_branch.as_ref()
                    .map(|e| substitute_macro_params(e, bindings, arg_exprs))
                    .transpose()?
                    .map(Box::new),
            })
        }
        _ => Ok(expr.clone()),
    }
}

fn substitute_macro_params_in_node(
    node: &Node,
    arg_exprs: &HashMap<String, Expr>,
) -> Result<Node, CompileError> {
    use simple_parser::ast::{ReturnStmt, AssignmentStmt, LetStmt};
    let empty_bindings = HashMap::new();
    match node {
        Node::Return(ret_stmt) => {
            Ok(Node::Return(ReturnStmt {
                span: ret_stmt.span,
                value: ret_stmt.value.as_ref()
                    .map(|e| substitute_macro_params(e, &empty_bindings, arg_exprs))
                    .transpose()?,
            }))
        }
        Node::Expression(e) => {
            Ok(Node::Expression(substitute_macro_params(e, &empty_bindings, arg_exprs)?))
        }
        Node::If(if_stmt) => {
            Ok(Node::If(IfStmt {
                span: if_stmt.span,
                let_pattern: if_stmt.let_pattern.clone(),
                condition: substitute_macro_params(&if_stmt.condition, &empty_bindings, arg_exprs)?,
                then_block: substitute_block(&if_stmt.then_block, arg_exprs)?,
                elif_branches: if_stmt.elif_branches.iter()
                    .map(|(cond, block)| {
                        Ok((
                            substitute_macro_params(cond, &empty_bindings, arg_exprs)?,
                            substitute_block(block, arg_exprs)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, CompileError>>()?,
                else_block: if_stmt.else_block.as_ref()
                    .map(|b| substitute_block(b, arg_exprs))
                    .transpose()?,
            }))
        }
        Node::Let(let_stmt) => {
            Ok(Node::Let(LetStmt {
                span: let_stmt.span,
                pattern: let_stmt.pattern.clone(),
                ty: let_stmt.ty.clone(),
                value: let_stmt.value.as_ref()
                    .map(|e| substitute_macro_params(e, &empty_bindings, arg_exprs))
                    .transpose()?,
                mutability: let_stmt.mutability,
                storage_class: let_stmt.storage_class,
            }))
        }
        Node::Assignment(assign) => {
            Ok(Node::Assignment(AssignmentStmt {
                span: assign.span,
                target: substitute_macro_params(&assign.target, &empty_bindings, arg_exprs)?,
                op: assign.op.clone(),
                value: substitute_macro_params(&assign.value, &empty_bindings, arg_exprs)?,
            }))
        }
        _ => Ok(node.clone()),
    }
}

fn substitute_block(
    block: &Block,
    arg_exprs: &HashMap<String, Expr>,
) -> Result<Block, CompileError> {
    let mut statements = Vec::new();
    for stmt in &block.statements {
        statements.push(substitute_macro_params_in_node(stmt, arg_exprs)?);
    }
    Ok(Block {
        span: block.span,
        statements,
    })
}
