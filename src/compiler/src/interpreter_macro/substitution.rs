//! Template substitution for macro expansion
//!
//! Replaces template placeholders like `{var}` with their const-evaluated values
//! in macro bodies. Operates recursively on all AST nodes.

use simple_parser::ast::*;
use std::collections::HashMap;

// Helper functions to reduce duplication

fn substitute_args(
    args: &[Argument],
    const_bindings: &HashMap<String, String>,
) -> Vec<Argument> {
    args.iter()
        .map(|arg| Argument {
            name: arg.name.clone(),
            value: substitute_expr_templates(&arg.value, const_bindings),
        })
        .collect()
}

fn substitute_match_arm(
    arm: &MatchArm,
    const_bindings: &HashMap<String, String>,
) -> MatchArm {
    MatchArm {
        span: arm.span,
        pattern: arm.pattern.clone(),
        guard: arm
            .guard
            .as_ref()
            .map(|expr| substitute_expr_templates(expr, const_bindings)),
        body: substitute_block_templates(&arm.body, const_bindings),
    }
}

fn substitute_opt_boxed(
    expr: &Option<Box<Expr>>,
    const_bindings: &HashMap<String, String>,
) -> Option<Box<Expr>> {
    expr.as_ref()
        .map(|e| Box::new(substitute_expr_templates(e, const_bindings)))
}

fn substitute_boxed(
    expr: &Expr,
    const_bindings: &HashMap<String, String>,
) -> Box<Expr> {
    Box::new(substitute_expr_templates(expr, const_bindings))
}

pub(super) fn substitute_block_templates(
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

pub(super) fn substitute_node_templates(
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
                .map(|arm| substitute_match_arm(arm, const_bindings))
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

pub(super) fn substitute_expr_templates(
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
            left: substitute_boxed(left, const_bindings),
            right: substitute_boxed(right, const_bindings),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: op.clone(),
            operand: substitute_boxed(operand, const_bindings),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: substitute_boxed(callee, const_bindings),
            args: substitute_args(args, const_bindings),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: substitute_boxed(receiver, const_bindings),
            method: method.clone(),
            args: substitute_args(args, const_bindings),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: substitute_boxed(receiver, const_bindings),
            field: field.clone(),
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: substitute_boxed(receiver, const_bindings),
            index: substitute_boxed(index, const_bindings),
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: substitute_boxed(receiver, const_bindings),
            index: *index,
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: substitute_boxed(condition, const_bindings),
            then_branch: substitute_boxed(then_branch, const_bindings),
            else_branch: substitute_opt_boxed(else_branch, const_bindings),
        },
        Expr::Match { subject, arms } => Expr::Match {
            subject: substitute_boxed(subject, const_bindings),
            arms: arms
                .iter()
                .map(|arm| substitute_match_arm(arm, const_bindings))
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
            expr: substitute_boxed(expr, const_bindings),
            pattern: pattern.clone(),
            iterable: substitute_boxed(iterable, const_bindings),
            condition: substitute_opt_boxed(condition, const_bindings),
        },
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => Expr::DictComprehension {
            key: substitute_boxed(key, const_bindings),
            value: substitute_boxed(value, const_bindings),
            pattern: pattern.clone(),
            iterable: substitute_boxed(iterable, const_bindings),
            condition: substitute_opt_boxed(condition, const_bindings),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: substitute_boxed(receiver, const_bindings),
            start: substitute_opt_boxed(start, const_bindings),
            end: substitute_opt_boxed(end, const_bindings),
            step: substitute_opt_boxed(step, const_bindings),
        },
        Expr::Spread(expr) => Expr::Spread(substitute_boxed(expr, const_bindings)),
        Expr::DictSpread(expr) => Expr::DictSpread(substitute_boxed(expr, const_bindings)),
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
        Expr::Spawn(expr) => Expr::Spawn(substitute_boxed(expr, const_bindings)),
        Expr::Await(expr) => Expr::Await(substitute_boxed(expr, const_bindings)),
        Expr::Yield(expr) => Expr::Yield(substitute_opt_boxed(expr, const_bindings)),
        Expr::New { kind, expr } => Expr::New {
            kind: *kind,
            expr: substitute_boxed(expr, const_bindings),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: substitute_boxed(expr, const_bindings),
            target_type: target_type.clone(),
        },
        Expr::Range { start, end, bound } => Expr::Range {
            start: substitute_opt_boxed(start, const_bindings),
            end: substitute_opt_boxed(end, const_bindings),
            bound: *bound,
        },
        Expr::FunctionalUpdate { target, method, args } => Expr::FunctionalUpdate {
            target: substitute_boxed(target, const_bindings),
            method: method.clone(),
            args: substitute_args(args, const_bindings),
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
        Expr::Try(expr) => Expr::Try(substitute_boxed(expr, const_bindings)),
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
