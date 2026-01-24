use simple_parser::ast::{
    Argument, AssignmentStmt, Block, ContextStmt, Expr, FStringPart, ForStmt, IfStmt, LetStmt, LoopStmt, MacroArg,
    MatchArm, MatchStmt, Node, RangeBound, ReturnStmt, WhileStmt, WithStmt,
};
use std::collections::HashMap;

pub(super) fn substitute_block_templates(block: &Block, const_bindings: &HashMap<String, String>) -> Block {
    let mut statements = Vec::new();
    for stmt in &block.statements {
        // Check if this is a for-loop that can be unrolled at const-eval time
        if let Some(unrolled) = try_unroll_const_for_loop(stmt, const_bindings) {
            statements.extend(unrolled);
        } else {
            statements.push(substitute_node_templates(stmt, const_bindings));
        }
    }
    Block {
        span: block.span,
        statements,
    }
}

/// Try to unroll a for-loop at const-eval time if it has const bounds
/// Returns None if the loop can't be unrolled (not a const range)
fn try_unroll_const_for_loop(node: &Node, const_bindings: &HashMap<String, String>) -> Option<Vec<Node>> {
    // Only handle Node::For
    let for_stmt = match node {
        Node::For(stmt) => stmt,
        _ => return None,
    };

    // Check if the iterable is a range expression with const bounds
    let (start, end) = match &for_stmt.iterable {
        Expr::Range {
            start,
            end,
            bound: RangeBound::Exclusive,
        } => {
            let start_val = eval_const_expr_to_i64(start.as_ref()?, const_bindings)?;
            let end_val = eval_const_expr_to_i64(end.as_ref()?, const_bindings)?;
            (start_val, end_val)
        }
        Expr::Range {
            start,
            end,
            bound: RangeBound::Inclusive,
        } => {
            let start_val = eval_const_expr_to_i64(start.as_ref()?, const_bindings)?;
            let end_val = eval_const_expr_to_i64(end.as_ref()?, const_bindings)?;
            (start_val, end_val + 1) // Inclusive, so add 1 to end
        }
        _ => return None,
    };

    // Get the loop variable name from the pattern
    let loop_var = match &for_stmt.pattern {
        simple_parser::ast::Pattern::Identifier(name) => name.clone(),
        _ => return None, // Only simple identifier patterns for now
    };

    // Unroll the loop
    let mut unrolled_statements = Vec::new();
    for i in start..end {
        // Create new bindings with the loop variable
        let mut iter_bindings = const_bindings.clone();
        iter_bindings.insert(loop_var.clone(), i.to_string());

        // Substitute and add all statements from the loop body
        for body_stmt in &for_stmt.body.statements {
            // Recursively try to unroll nested const for-loops
            if let Some(nested_unrolled) = try_unroll_const_for_loop(body_stmt, &iter_bindings) {
                unrolled_statements.extend(nested_unrolled);
            } else {
                unrolled_statements.push(substitute_node_templates(body_stmt, &iter_bindings));
            }
        }
    }

    Some(unrolled_statements)
}

/// Evaluate a const expression to i64
fn eval_const_expr_to_i64(expr: &Expr, const_bindings: &HashMap<String, String>) -> Option<i64> {
    match expr {
        Expr::Integer(i) => Some(*i),
        Expr::Identifier(name) => const_bindings.get(name).and_then(|v| v.parse::<i64>().ok()),
        Expr::Binary { op, left, right } => {
            let l = eval_const_expr_to_i64(left, const_bindings)?;
            let r = eval_const_expr_to_i64(right, const_bindings)?;
            match op {
                simple_parser::ast::BinOp::Add => Some(l + r),
                simple_parser::ast::BinOp::Sub => Some(l - r),
                simple_parser::ast::BinOp::Mul => Some(l * r),
                simple_parser::ast::BinOp::Div => Some(l / r),
                simple_parser::ast::BinOp::Mod => Some(l % r),
                _ => None,
            }
        }
        _ => None,
    }
}

fn substitute_node_templates(node: &Node, const_bindings: &HashMap<String, String>) -> Node {
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
            is_suspend: let_stmt.is_suspend,
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
            is_suspend: stmt.is_suspend,
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
            is_suspend: stmt.is_suspend,
            auto_enumerate: stmt.auto_enumerate,
            invariants: stmt.invariants.clone(),
        }),
        Node::While(stmt) => Node::While(WhileStmt {
            span: stmt.span,
            condition: substitute_expr_templates(&stmt.condition, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
            let_pattern: stmt.let_pattern.clone(),
            is_suspend: stmt.is_suspend,
            invariants: stmt.invariants.clone(),
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
        Node::Function(def) => {
            // Substitute templates in function name, body, and parameters
            let mut new_def = def.clone();
            // Substitute template in function name (e.g., "get_{i}" -> "get_0")
            // Also strip quotes if the name was quoted in the source (for templated names)
            let substituted_name = substitute_template_string(&def.name, const_bindings);
            new_def.name =
                if substituted_name.starts_with('"') && substituted_name.ends_with('"') && substituted_name.len() > 2 {
                    substituted_name[1..substituted_name.len() - 1].to_string()
                } else {
                    substituted_name
                };
            new_def.body = substitute_block_templates(&def.body, const_bindings);
            // Also substitute in default parameter values
            new_def.params = def
                .params
                .iter()
                .map(|param| {
                    let mut new_param = param.clone();
                    new_param.default = param
                        .default
                        .as_ref()
                        .map(|expr| substitute_expr_templates(expr, const_bindings));
                    new_param
                })
                .collect();
            Node::Function(new_def)
        }
        _ => node.clone(),
    }
}

fn substitute_expr_templates(expr: &Expr, const_bindings: &HashMap<String, String>) -> Expr {
    match expr {
        Expr::String(value) => Expr::String(substitute_template_string(value, const_bindings)),
        Expr::TypedString(value, suffix) => {
            Expr::TypedString(substitute_template_string(value, const_bindings), suffix.clone())
        }
        Expr::FString { parts, type_meta } => Expr::FString {
            parts: parts
                .iter()
                .map(|part| match part {
                    FStringPart::Literal(text) => {
                        FStringPart::Literal(substitute_template_string(text, const_bindings))
                    }
                    FStringPart::Expr(expr_text) => FStringPart::Expr(expr_text.clone()),
                })
                .collect(),
            type_meta: type_meta.clone(),
        },
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
                .map(|arg| Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::MethodCall { receiver, method, args } => Expr::MethodCall {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| Argument {
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
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            let_pattern: let_pattern.clone(),
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
        Expr::DictSpread(expr) => Expr::DictSpread(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, expr)| (field.clone(), substitute_expr_templates(expr, const_bindings)))
                .collect(),
        },
        Expr::Spawn(expr) => Expr::Spawn(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Await(expr) => Expr::Await(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Yield(expr) => Expr::Yield(
            expr.as_ref()
                .map(|e| Box::new(substitute_expr_templates(e, const_bindings))),
        ),
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
                .map(|arg| Argument {
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
                    MacroArg::Expr(expr) => MacroArg::Expr(substitute_expr_templates(expr, const_bindings)),
                })
                .collect(),
        },
        Expr::Try(expr) => Expr::Try(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::ExistsCheck(expr) => Expr::ExistsCheck(Box::new(substitute_expr_templates(expr, const_bindings))),
        // Handle bare identifiers that match const parameters
        Expr::Identifier(name) => {
            if let Some(value) = const_bindings.get(name) {
                // Try to parse as integer first, then as string
                if let Ok(i) = value.parse::<i64>() {
                    Expr::Integer(i)
                } else {
                    // Keep as string literal if it's a string const
                    Expr::String(value.clone())
                }
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

fn substitute_template_string(input: &str, const_bindings: &HashMap<String, String>) -> String {
    let mut output = input.to_string();
    for (key, value) in const_bindings {
        let needle = format!("{{{}}}", key);
        if output.contains(&needle) {
            output = output.replace(&needle, value);
        }
    }
    output
}
