use simple_parser::ast::*;
use simple_parser::ast::Argument;
use std::collections::HashMap;

#[derive(Debug, Default)]
pub(super) struct MacroHygieneContext {
    gensym_counter: usize,
    scopes: Vec<HashMap<String, String>>,
}

impl MacroHygieneContext {
    pub(super) fn new() -> Self {
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

pub(super) fn apply_macro_hygiene_block(
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

pub(super) fn apply_macro_hygiene_node(
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
                    is_suspend: stmt.is_suspend,
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
                    is_suspend: stmt.is_suspend,
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
                is_suspend: stmt.is_suspend,
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
                is_suspend: stmt.is_suspend,
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

pub(super) fn apply_macro_hygiene_expr(
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
                .map(|arg| Argument {
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
                .map(|arg| Argument {
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
                .map(|param| LambdaParam {
                    name: ctx.bind(&param.name, false),
                    ty: param.ty.clone(),
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
        Expr::DictSpread(expr) => Expr::DictSpread(Box::new(apply_macro_hygiene_expr(expr, ctx))),
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
                .map(|arg| Argument {
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

pub(super) fn apply_macro_hygiene_pattern(
    pattern: &Pattern,
    ctx: &mut MacroHygieneContext,
    reuse_if_bound: bool,
) -> Pattern {
    match pattern {
        Pattern::Identifier(name) => Pattern::Identifier(ctx.bind(name, reuse_if_bound)),
        Pattern::MutIdentifier(name) => Pattern::MutIdentifier(ctx.bind(name, reuse_if_bound)),
        Pattern::Literal(expr) => Pattern::Literal(Box::new(apply_macro_hygiene_expr(expr, ctx))),
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
