// Macro invocation and expansion (part of interpreter module)

use crate::macro_contracts::{process_macro_contract, MacroContractResult};
use crate::macro_validation::validate_macro_defined_before_use;

#[path = "interpreter_macro/helpers.rs"]
mod helpers;
use helpers::{build_macro_const_bindings, const_value_to_string};

thread_local! {
    /// Accumulates symbols introduced by macro expansion
    /// These need to be registered by the caller after macro invocation
    static MACRO_INTRODUCED_SYMBOLS: RefCell<Option<MacroContractResult>> = RefCell::new(None);
}

/// Get and clear introduced symbols from last macro expansion
pub fn take_macro_introduced_symbols() -> Option<MacroContractResult> {
    MACRO_INTRODUCED_SYMBOLS.with(|cell| cell.borrow_mut().take())
}

fn evaluate_macro_invocation(
    name: &str,
    macro_args: &[MacroArg],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
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
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Validate ordering: macro must be defined before use (#1304)
    let definition_order = MACRO_DEFINITION_ORDER.with(|cell| cell.borrow().clone());
    validate_macro_defined_before_use(&macro_def.name, 0, &definition_order)?;

    let mut local_env = env.clone();
    let const_bindings = build_macro_const_bindings(macro_def, args, env, functions, classes, enums, impl_methods)?;
    let mut hygiene_ctx = MacroHygieneContext::new();

    // Process macro contracts to determine introduced symbols (#1303)
    // Also performs shadowing validation (#1304)
    let contract_result = process_macro_contract(macro_def, &const_bindings, env, functions, classes)?;

    // Store introduced symbols in thread-local for caller to register
    // This is necessary because symbol tables are immutable during evaluation
    MACRO_INTRODUCED_SYMBOLS.with(|cell| {
        *cell.borrow_mut() = Some(contract_result);
    });

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
                let hygienic_block = apply_macro_hygiene_block(block, &mut hygiene_ctx, false);
                match exec_block(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(v) => return Ok(v),
                    Control::Break(_) | Control::Continue => {}
                    Control::Next => {}
                }
            }
            MacroStmt::Emit { label, block } => {
                let expanded_block = substitute_block_templates(block, &const_bindings);
                let hygienic_block = apply_macro_hygiene_block(&expanded_block, &mut hygiene_ctx, false);
                let (control, maybe_value) =
                    exec_block_fn(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)?;
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
            MacroStmt::Stmt(node) => {
                let hygienic_node = apply_macro_hygiene_node(node, &mut hygiene_ctx);
                match exec_node(&hygienic_node, &mut local_env, functions, classes, enums, impl_methods)? {
                Control::Return(v) => return Ok(v),
                Control::Break(_) | Control::Continue => {}
                Control::Next => {}
                }
            }
        }
    }

    Ok(last_value)
}

#[derive(Debug, Default)]
struct MacroHygieneContext {
    gensym_counter: usize,
    scopes: Vec<HashMap<String, String>>,
}

impl MacroHygieneContext {
    fn new() -> Self {
        Self {
            gensym_counter: 0,
            scopes: vec![HashMap::new()],
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn resolve(&self, name: &str) -> Option<String> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name).cloned())
    }

    fn bind(&mut self, name: &str, reuse_if_bound: bool) -> String {
        if reuse_if_bound {
            if let Some(scope) = self.scopes.last() {
                if let Some(existing) = scope.get(name) {
                    return existing.clone();
                }
            }
        }
        self.gensym_counter += 1;
        let new_name = format!("{name}_gensym_{}", self.gensym_counter);
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), new_name.clone());
        }
        new_name
    }
}

fn apply_macro_hygiene_block(
    block: &Block,
    ctx: &mut MacroHygieneContext,
    push_scope: bool,
) -> Block {
    if push_scope {
        ctx.push_scope();
    }
    let mut statements = Vec::new();
    for stmt in &block.statements {
        statements.push(apply_macro_hygiene_node(stmt, ctx));
    }
    if push_scope {
        ctx.pop_scope();
    }
    Block {
        span: block.span,
        statements,
    }
}

fn apply_macro_hygiene_node(
    node: &Node,
    ctx: &mut MacroHygieneContext,
) -> Node {
    match node {
        Node::Let(let_stmt) => {
            let value = let_stmt
                .value
                .as_ref()
                .map(|expr| apply_macro_hygiene_expr(expr, ctx));
            let pattern = apply_macro_hygiene_pattern(&let_stmt.pattern, ctx, false);
            Node::Let(LetStmt {
                span: let_stmt.span,
                pattern,
                ty: let_stmt.ty.clone(),
                value,
                mutability: let_stmt.mutability,
                storage_class: let_stmt.storage_class,
                is_ghost: let_stmt.is_ghost,
            })
        }
        Node::Const(const_stmt) => {
            let mut new_stmt = const_stmt.clone();
            new_stmt.value = apply_macro_hygiene_expr(&const_stmt.value, ctx);
            new_stmt.name = ctx.bind(&const_stmt.name, false);
            Node::Const(new_stmt)
        }
        Node::Static(static_stmt) => {
            let mut new_stmt = static_stmt.clone();
            new_stmt.value = apply_macro_hygiene_expr(&static_stmt.value, ctx);
            new_stmt.name = ctx.bind(&static_stmt.name, false);
            Node::Static(new_stmt)
        }
        Node::Assignment(assign) => Node::Assignment(AssignmentStmt {
            span: assign.span,
            target: apply_macro_hygiene_expr(&assign.target, ctx),
            op: assign.op,
            value: apply_macro_hygiene_expr(&assign.value, ctx),
        }),
        Node::Return(ret) => Node::Return(ReturnStmt {
            span: ret.span,
            value: ret
                .value
                .as_ref()
                .map(|expr| apply_macro_hygiene_expr(expr, ctx)),
        }),
        Node::If(stmt) => {
            if let Some(let_pattern) = &stmt.let_pattern {
                let condition = apply_macro_hygiene_expr(&stmt.condition, ctx);
                ctx.push_scope();
                let new_pattern = apply_macro_hygiene_pattern(let_pattern, ctx, false);
                let then_block = apply_macro_hygiene_block(&stmt.then_block, ctx, false);
                ctx.pop_scope();
                let elif_branches = stmt
                    .elif_branches
                    .iter()
                    .map(|(cond, block)| {
                        (
                            apply_macro_hygiene_expr(cond, ctx),
                            apply_macro_hygiene_block(block, ctx, true),
                        )
                    })
                    .collect();
                let else_block = stmt
                    .else_block
                    .as_ref()
                    .map(|block| apply_macro_hygiene_block(block, ctx, true));
                Node::If(IfStmt {
                    span: stmt.span,
                    condition,
                    then_block,
                    elif_branches,
                    else_block,
                    let_pattern: Some(new_pattern),
                })
            } else {
                Node::If(IfStmt {
                    span: stmt.span,
                    condition: apply_macro_hygiene_expr(&stmt.condition, ctx),
                    then_block: apply_macro_hygiene_block(&stmt.then_block, ctx, true),
                    elif_branches: stmt
                        .elif_branches
                        .iter()
                        .map(|(cond, block)| {
                            (
                                apply_macro_hygiene_expr(cond, ctx),
                                apply_macro_hygiene_block(block, ctx, true),
                            )
                        })
                        .collect(),
                    else_block: stmt
                        .else_block
                        .as_ref()
                        .map(|block| apply_macro_hygiene_block(block, ctx, true)),
                    let_pattern: None,
                })
            }
        }
        Node::Match(stmt) => Node::Match(MatchStmt {
            span: stmt.span,
            subject: apply_macro_hygiene_expr(&stmt.subject, ctx),
            arms: stmt
                .arms
                .iter()
                .map(|arm| {
                    ctx.push_scope();
                    let pattern = apply_macro_hygiene_pattern(&arm.pattern, ctx, true);
                    let guard = arm
                        .guard
                        .as_ref()
                        .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                    let body = apply_macro_hygiene_block(&arm.body, ctx, false);
                    ctx.pop_scope();
                    MatchArm {
                        span: arm.span,
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect(),
        }),
        Node::For(stmt) => {
            let iterable = apply_macro_hygiene_expr(&stmt.iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(&stmt.pattern, ctx, false);
            let body = apply_macro_hygiene_block(&stmt.body, ctx, false);
            ctx.pop_scope();
            Node::For(ForStmt {
                span: stmt.span,
                pattern,
                iterable,
                body,
            })
        }
        Node::While(stmt) => {
            let condition = apply_macro_hygiene_expr(&stmt.condition, ctx);
            let (let_pattern, body) = if let Some(let_pattern) = &stmt.let_pattern {
                ctx.push_scope();
                let new_pattern = apply_macro_hygiene_pattern(let_pattern, ctx, false);
                let new_body = apply_macro_hygiene_block(&stmt.body, ctx, false);
                ctx.pop_scope();
                (Some(new_pattern), new_body)
            } else {
                (None, apply_macro_hygiene_block(&stmt.body, ctx, true))
            };
            Node::While(WhileStmt {
                span: stmt.span,
                condition,
                body,
                let_pattern,
            })
        }
        Node::Loop(stmt) => Node::Loop(LoopStmt {
            span: stmt.span,
            body: apply_macro_hygiene_block(&stmt.body, ctx, true),
        }),
        Node::Context(stmt) => Node::Context(ContextStmt {
            span: stmt.span,
            context: apply_macro_hygiene_expr(&stmt.context, ctx),
            body: apply_macro_hygiene_block(&stmt.body, ctx, true),
        }),
        Node::With(stmt) => {
            let resource = apply_macro_hygiene_expr(&stmt.resource, ctx);
            if let Some(name) = &stmt.name {
                ctx.push_scope();
                let new_name = ctx.bind(name, false);
                let body = apply_macro_hygiene_block(&stmt.body, ctx, false);
                ctx.pop_scope();
                Node::With(WithStmt {
                    span: stmt.span,
                    resource,
                    name: Some(new_name),
                    body,
                })
            } else {
                Node::With(WithStmt {
                    span: stmt.span,
                    resource,
                    name: None,
                    body: apply_macro_hygiene_block(&stmt.body, ctx, true),
                })
            }
        }
        Node::Function(def) => {
            let mut new_def = def.clone();
            new_def.name = ctx.bind(&def.name, false);
            ctx.push_scope();
            let mut params = Vec::with_capacity(def.params.len());
            for param in &def.params {
                let default = param
                    .default
                    .as_ref()
                    .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                let new_name = ctx.bind(&param.name, false);
                let mut new_param = param.clone();
                new_param.name = new_name;
                new_param.default = default;
                params.push(new_param);
            }
            new_def.params = params;
            new_def.body = apply_macro_hygiene_block(&def.body, ctx, false);
            ctx.pop_scope();
            Node::Function(new_def)
        }
        Node::Expression(expr) => Node::Expression(apply_macro_hygiene_expr(expr, ctx)),
        _ => node.clone(),
    }
}

fn apply_macro_hygiene_expr(
    expr: &Expr,
    ctx: &mut MacroHygieneContext,
) -> Expr {
    match expr {
        Expr::Identifier(name) => ctx
            .resolve(name)
            .map(Expr::Identifier)
            .unwrap_or_else(|| expr.clone()),
        Expr::FString(parts) => Expr::FString(
            parts
                .iter()
                .map(|part| match part {
                    FStringPart::Literal(text) => FStringPart::Literal(text.clone()),
                    FStringPart::Expr(expr) => FStringPart::Expr(apply_macro_hygiene_expr(expr, ctx)),
                })
                .collect(),
        ),
        Expr::Binary { op, left, right } => Expr::Binary {
            op: op.clone(),
            left: Box::new(apply_macro_hygiene_expr(left, ctx)),
            right: Box::new(apply_macro_hygiene_expr(right, ctx)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: *op,
            operand: Box::new(apply_macro_hygiene_expr(operand, ctx)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(apply_macro_hygiene_expr(callee, ctx)),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            field: field.clone(),
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            index: Box::new(apply_macro_hygiene_expr(index, ctx)),
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            index: *index,
        },
        Expr::Lambda {
            params,
            body,
            move_mode,
        } => {
            ctx.push_scope();
            let new_params = params
                .iter()
                .map(|param| {
                    let new_name = ctx.bind(&param.name, false);
                    simple_parser::ast::LambdaParam {
                        name: new_name,
                        ty: param.ty.clone(),
                    }
                })
                .collect();
            let new_body = apply_macro_hygiene_expr(body, ctx);
            ctx.pop_scope();
            Expr::Lambda {
                params: new_params,
                body: Box::new(new_body),
                move_mode: *move_mode,
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(apply_macro_hygiene_expr(condition, ctx)),
            then_branch: Box::new(apply_macro_hygiene_expr(then_branch, ctx)),
            else_branch: else_branch
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        },
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(apply_macro_hygiene_expr(subject, ctx)),
            arms: arms
                .iter()
                .map(|arm| {
                    ctx.push_scope();
                    let pattern = apply_macro_hygiene_pattern(&arm.pattern, ctx, true);
                    let guard = arm
                        .guard
                        .as_ref()
                        .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                    let body = apply_macro_hygiene_block(&arm.body, ctx, false);
                    ctx.pop_scope();
                    MatchArm {
                        span: arm.span,
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect(),
        },
        Expr::Tuple(items) => {
            Expr::Tuple(items.iter().map(|item| apply_macro_hygiene_expr(item, ctx)).collect())
        }
        Expr::Array(items) => {
            Expr::Array(items.iter().map(|item| apply_macro_hygiene_expr(item, ctx)).collect())
        }
        Expr::VecLiteral(items) => Expr::VecLiteral(
            items
                .iter()
                .map(|item| apply_macro_hygiene_expr(item, ctx))
                .collect(),
        ),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .iter()
                .map(|(k, v)| {
                    (
                        apply_macro_hygiene_expr(k, ctx),
                        apply_macro_hygiene_expr(v, ctx),
                    )
                })
                .collect(),
        ),
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iterable = apply_macro_hygiene_expr(iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(pattern, ctx, false);
            let expr = apply_macro_hygiene_expr(expr, ctx);
            let condition = condition
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx)));
            ctx.pop_scope();
            Expr::ListComprehension {
                expr: Box::new(expr),
                pattern,
                iterable: Box::new(iterable),
                condition,
            }
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            let iterable = apply_macro_hygiene_expr(iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(pattern, ctx, false);
            let key = apply_macro_hygiene_expr(key, ctx);
            let value = apply_macro_hygiene_expr(value, ctx);
            let condition = condition
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx)));
            ctx.pop_scope();
            Expr::DictComprehension {
                key: Box::new(key),
                value: Box::new(value),
                pattern,
                iterable: Box::new(iterable),
                condition,
            }
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            start: start
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            end: end
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            step: step
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        },
        Expr::Spread(expr) => Expr::Spread(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::DictSpread(expr) => {
            Expr::DictSpread(Box::new(apply_macro_hygiene_expr(expr, ctx)))
        }
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, expr)| {
                    (
                        field.clone(),
                        apply_macro_hygiene_expr(expr, ctx),
                    )
                })
                .collect(),
        },
        Expr::Spawn(expr) => Expr::Spawn(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::Await(expr) => Expr::Await(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::Yield(expr) => Expr::Yield(
            expr
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        ),
        Expr::New { kind, expr } => Expr::New {
            kind: *kind,
            expr: Box::new(apply_macro_hygiene_expr(expr, ctx)),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(apply_macro_hygiene_expr(expr, ctx)),
            target_type: target_type.clone(),
        },
        Expr::Range { start, end, bound } => Expr::Range {
            start: start
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            end: end
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            bound: *bound,
        },
        Expr::FunctionalUpdate { target, method, args } => Expr::FunctionalUpdate {
            target: Box::new(apply_macro_hygiene_expr(target, ctx)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::MacroInvocation { name, args } => Expr::MacroInvocation {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    MacroArg::Expr(expr) => MacroArg::Expr(apply_macro_hygiene_expr(expr, ctx)),
                })
                .collect(),
        },
        Expr::Try(expr) => Expr::Try(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::ContractOld(expr) => Expr::ContractOld(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::DoBlock(nodes) => {
            ctx.push_scope();
            let mut statements = Vec::new();
            for node in nodes {
                statements.push(apply_macro_hygiene_node(node, ctx));
            }
            ctx.pop_scope();
            Expr::DoBlock(statements)
        }
        _ => expr.clone(),
    }
}

fn apply_macro_hygiene_pattern(
    pattern: &Pattern,
    ctx: &mut MacroHygieneContext,
    reuse_if_bound: bool,
) -> Pattern {
    match pattern {
        Pattern::Identifier(name) => Pattern::Identifier(ctx.bind(name, reuse_if_bound)),
        Pattern::MutIdentifier(name) => Pattern::MutIdentifier(ctx.bind(name, reuse_if_bound)),
        Pattern::Literal(expr) => {
            Pattern::Literal(Box::new(apply_macro_hygiene_expr(expr, ctx)))
        }
        Pattern::Tuple(items) => Pattern::Tuple(
            items
                .iter()
                .map(|item| apply_macro_hygiene_pattern(item, ctx, reuse_if_bound))
                .collect(),
        ),
        Pattern::Array(items) => Pattern::Array(
            items
                .iter()
                .map(|item| apply_macro_hygiene_pattern(item, ctx, reuse_if_bound))
                .collect(),
        ),
        Pattern::Struct { name, fields } => Pattern::Struct {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, pat)| {
                    (
                        field.clone(),
                        apply_macro_hygiene_pattern(pat, ctx, reuse_if_bound),
                    )
                })
                .collect(),
        },
        Pattern::Enum {
            name,
            variant,
            payload,
        } => Pattern::Enum {
            name: name.clone(),
            variant: variant.clone(),
            payload: payload.as_ref().map(|payload| {
                payload
                    .iter()
                    .map(|pat| apply_macro_hygiene_pattern(pat, ctx, reuse_if_bound))
                    .collect()
            }),
        },
        Pattern::Or(patterns) => Pattern::Or(
            patterns
                .iter()
                .map(|pat| apply_macro_hygiene_pattern(pat, ctx, true))
                .collect(),
        ),
        Pattern::Typed { pattern, ty } => Pattern::Typed {
            pattern: Box::new(apply_macro_hygiene_pattern(pattern, ctx, reuse_if_bound)),
            ty: ty.clone(),
        },
        Pattern::Range {
            start,
            end,
            inclusive,
        } => Pattern::Range {
            start: Box::new(apply_macro_hygiene_expr(start, ctx)),
            end: Box::new(apply_macro_hygiene_expr(end, ctx)),
            inclusive: *inclusive,
        },
        _ => pattern.clone(),
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
            is_ghost: let_stmt.is_ghost,
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
