//! Placeholder lambda transformation
//!
//! Transforms expressions containing `_` placeholder identifiers into lambdas.
//!
//! Example transformations:
//! - `_ * 2` -> `\__p0: __p0 * 2`
//! - `_ + _` -> `\__p0, __p1: __p0 + __p1`
//! - `_.field` -> `\__p0: __p0.field`

use crate::ast::enums::MoveMode;
use crate::ast::{Argument, Expr, LambdaParam};

/// Transform placeholder lambda syntax: expressions containing `_` identifiers
/// become lambdas with generated parameter names.
///
/// If no `_` placeholders are found, returns the expression unchanged.
pub fn transform_placeholder_lambda(expr: Expr) -> Expr {
    // First, count how many placeholders are in the expression
    let placeholder_count = count_placeholders(&expr);

    if placeholder_count == 0 {
        return expr;
    }

    // Replace placeholders with numbered parameter names
    let mut counter = 0usize;
    let transformed_body = replace_placeholders(expr, &mut counter);

    // Generate parameter names: __p0, __p1, ...
    let params: Vec<LambdaParam> = (0..placeholder_count)
        .map(|i| LambdaParam {
            name: format!("__p{}", i),
            ty: None,
        })
        .collect();

    Expr::Lambda {
        params,
        body: Box::new(transformed_body),
        move_mode: MoveMode::Copy,
        capture_all: false,
    }
}

/// Count the number of `_` placeholder identifiers in an expression
fn count_placeholders(expr: &Expr) -> usize {
    match expr {
        Expr::Identifier(name) if name == "_" => 1,
        Expr::Binary { left, right, .. } => count_placeholders(left) + count_placeholders(right),
        Expr::Unary { operand, .. } => count_placeholders(operand),
        Expr::Call { callee, args } => {
            count_placeholders(callee) + args.iter().map(|a| count_placeholders(&a.value)).sum::<usize>()
        }
        Expr::MethodCall { receiver, args, .. } => {
            count_placeholders(receiver) + args.iter().map(|a| count_placeholders(&a.value)).sum::<usize>()
        }
        Expr::FieldAccess { receiver, .. } => count_placeholders(receiver),
        Expr::Index { receiver, index } => count_placeholders(receiver) + count_placeholders(index),
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            count_placeholders(condition)
                + count_placeholders(then_branch)
                + else_branch.as_ref().map_or(0, |e| count_placeholders(e))
        }
        Expr::Tuple(items) | Expr::Array(items) => items.iter().map(count_placeholders).sum(),
        Expr::Dict(entries) => entries
            .iter()
            .map(|(k, v)| count_placeholders(k) + count_placeholders(v))
            .sum(),
        Expr::OptionalChain { expr, .. } => count_placeholders(expr),
        Expr::Coalesce { expr, default } => count_placeholders(expr) + count_placeholders(default),
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            count_placeholders(receiver)
                + start.as_ref().map_or(0, |e| count_placeholders(e))
                + end.as_ref().map_or(0, |e| count_placeholders(e))
                + step.as_ref().map_or(0, |e| count_placeholders(e))
        }
        Expr::Cast { expr, .. } => count_placeholders(expr),
        Expr::Spread(inner) => count_placeholders(inner),
        // Lambda bodies should not be traversed (they have their own scope)
        Expr::Lambda { .. } => 0,
        // Terminal expressions with no sub-expressions
        Expr::Integer(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::Identifier(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Symbol(_) => 0,
        // Other complex expressions - for simplicity, return 0
        _ => 0,
    }
}

/// Replace `_` placeholder identifiers with numbered parameter names
fn replace_placeholders(expr: Expr, counter: &mut usize) -> Expr {
    match expr {
        Expr::Identifier(name) if name == "_" => {
            let new_name = format!("__p{}", *counter);
            *counter += 1;
            Expr::Identifier(new_name)
        }
        Expr::Binary { op, left, right } => Expr::Binary {
            op,
            left: Box::new(replace_placeholders(*left, counter)),
            right: Box::new(replace_placeholders(*right, counter)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op,
            operand: Box::new(replace_placeholders(*operand, counter)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(replace_placeholders(*callee, counter)),
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_placeholders(a.value, counter), a.span))
                .collect(),
        },
        Expr::MethodCall { receiver, method, args } => Expr::MethodCall {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            method,
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_placeholders(a.value, counter), a.span))
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            field,
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            index: Box::new(replace_placeholders(*index, counter)),
        },
        Expr::If {
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            let_pattern,
            condition: Box::new(replace_placeholders(*condition, counter)),
            then_branch: Box::new(replace_placeholders(*then_branch, counter)),
            else_branch: else_branch.map(|e| Box::new(replace_placeholders(*e, counter))),
        },
        Expr::Tuple(items) => Expr::Tuple(items.into_iter().map(|e| replace_placeholders(e, counter)).collect()),
        Expr::Array(items) => Expr::Array(items.into_iter().map(|e| replace_placeholders(e, counter)).collect()),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .into_iter()
                .map(|(k, v)| (replace_placeholders(k, counter), replace_placeholders(v, counter)))
                .collect(),
        ),
        Expr::OptionalChain { expr, field } => Expr::OptionalChain {
            expr: Box::new(replace_placeholders(*expr, counter)),
            field,
        },
        Expr::Coalesce { expr, default } => Expr::Coalesce {
            expr: Box::new(replace_placeholders(*expr, counter)),
            default: Box::new(replace_placeholders(*default, counter)),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            start: start.map(|e| Box::new(replace_placeholders(*e, counter))),
            end: end.map(|e| Box::new(replace_placeholders(*e, counter))),
            step: step.map(|e| Box::new(replace_placeholders(*e, counter))),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(replace_placeholders(*expr, counter)),
            target_type,
        },
        Expr::Spread(inner) => Expr::Spread(Box::new(replace_placeholders(*inner, counter))),
        // Don't descend into lambdas (they have their own scope)
        Expr::Lambda { .. } => expr,
        // Terminal expressions with no sub-expressions - return unchanged
        _ => expr,
    }
}
