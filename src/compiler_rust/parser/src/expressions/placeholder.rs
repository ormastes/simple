//! Placeholder lambda transformation
//!
//! Transforms expressions containing `_` or `_N` placeholder identifiers into lambdas.
//!
//! Example transformations:
//! - `_ * 2` -> `\__p0: __p0 * 2`
//! - `_ + _` -> `\__p0, __p1: __p0 + __p1`
//! - `_.field` -> `\__p0: __p0.field`
//! - `_1 * 10` -> `\__p0: __p0 * 10`
//! - `_2 - _1` -> `\__p0, __p1: __p1 - __p0`

use crate::ast::enums::MoveMode;
use crate::ast::{Argument, Expr, LambdaParam};

/// Check if an identifier is a numbered placeholder like `_1`, `_2`, etc.
fn is_numbered_placeholder(name: &str) -> bool {
    if name.len() < 2 || !name.starts_with('_') {
        return false;
    }
    name[1..].chars().all(|c| c.is_ascii_digit())
}

/// Parse the number from a numbered placeholder (1-indexed). Returns None if not a numbered placeholder.
fn numbered_placeholder_index(name: &str) -> Option<usize> {
    if is_numbered_placeholder(name) {
        name[1..].parse::<usize>().ok()
    } else {
        None
    }
}

/// Transform placeholder lambda syntax: expressions containing `_` or `_N` identifiers
/// become lambdas with generated parameter names.
///
/// If no placeholders are found, returns the expression unchanged.
pub fn transform_placeholder_lambda(expr: Expr) -> Expr {
    // Check for numbered placeholders first (_1, _2, etc.)
    let max_numbered = find_max_numbered(&expr);

    if max_numbered > 0 {
        // Numbered placeholder mode: _1 maps to __p0, _2 maps to __p1, etc.
        let transformed_body = replace_numbered_placeholders(expr);

        let params: Vec<LambdaParam> = (0..max_numbered)
            .map(|i| LambdaParam {
                name: format!("__p{}", i),
                ty: None,
            })
            .collect();

        return Expr::Lambda {
            params,
            body: Box::new(transformed_body),
            move_mode: MoveMode::Copy,
            capture_all: false,
        };
    }

    // Fall back to unnamed placeholder mode (_)
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

/// Find the maximum numbered placeholder index in an expression.
/// Returns 0 if no numbered placeholders found.
fn find_max_numbered(expr: &Expr) -> usize {
    match expr {
        Expr::Identifier(name) => numbered_placeholder_index(name).unwrap_or(0),
        Expr::Binary { left, right, .. } => find_max_numbered(left).max(find_max_numbered(right)),
        Expr::Unary { operand, .. } => find_max_numbered(operand),
        Expr::Call { callee, args } => {
            let c = find_max_numbered(callee);
            args.iter().fold(c, |acc, a| acc.max(find_max_numbered(&a.value)))
        }
        Expr::MethodCall { receiver, args, .. } => {
            let r = find_max_numbered(receiver);
            args.iter().fold(r, |acc, a| acc.max(find_max_numbered(&a.value)))
        }
        Expr::FieldAccess { receiver, .. } => find_max_numbered(receiver),
        Expr::Index { receiver, index } => find_max_numbered(receiver).max(find_max_numbered(index)),
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            let m = find_max_numbered(condition).max(find_max_numbered(then_branch));
            else_branch.as_ref().map_or(m, |e| m.max(find_max_numbered(e)))
        }
        Expr::Tuple(items) | Expr::Array(items) => items.iter().fold(0, |acc, e| acc.max(find_max_numbered(e))),
        Expr::Dict(entries) => entries
            .iter()
            .fold(0, |acc, (k, v)| acc.max(find_max_numbered(k)).max(find_max_numbered(v))),
        Expr::OptionalChain { expr, .. } => find_max_numbered(expr),
        Expr::Coalesce { expr, default } => find_max_numbered(expr).max(find_max_numbered(default)),
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            let mut m = find_max_numbered(receiver);
            if let Some(s) = start {
                m = m.max(find_max_numbered(s));
            }
            if let Some(e) = end {
                m = m.max(find_max_numbered(e));
            }
            if let Some(st) = step {
                m = m.max(find_max_numbered(st));
            }
            m
        }
        Expr::Cast { expr, .. } => find_max_numbered(expr),
        Expr::Spread(inner) => find_max_numbered(inner),
        Expr::Lambda { .. } => 0,
        _ => 0,
    }
}

/// Replace numbered placeholders `_1`, `_2` etc. with `__p0`, `__p1` (1-indexed to 0-indexed)
fn replace_numbered_placeholders(expr: Expr) -> Expr {
    match expr {
        Expr::Identifier(ref name) => {
            if let Some(n) = numbered_placeholder_index(name) {
                Expr::Identifier(format!("__p{}", n - 1))
            } else {
                expr
            }
        }
        Expr::Binary { op, left, right } => Expr::Binary {
            op,
            left: Box::new(replace_numbered_placeholders(*left)),
            right: Box::new(replace_numbered_placeholders(*right)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op,
            operand: Box::new(replace_numbered_placeholders(*operand)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(replace_numbered_placeholders(*callee)),
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_numbered_placeholders(a.value), a.span))
                .collect(),
        },
        Expr::MethodCall { receiver, method, args } => Expr::MethodCall {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            method,
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_numbered_placeholders(a.value), a.span))
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            field,
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            index: Box::new(replace_numbered_placeholders(*index)),
        },
        Expr::If {
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            let_pattern,
            condition: Box::new(replace_numbered_placeholders(*condition)),
            then_branch: Box::new(replace_numbered_placeholders(*then_branch)),
            else_branch: else_branch.map(|e| Box::new(replace_numbered_placeholders(*e))),
        },
        Expr::Tuple(items) => Expr::Tuple(items.into_iter().map(replace_numbered_placeholders).collect()),
        Expr::Array(items) => Expr::Array(items.into_iter().map(replace_numbered_placeholders).collect()),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .into_iter()
                .map(|(k, v)| (replace_numbered_placeholders(k), replace_numbered_placeholders(v)))
                .collect(),
        ),
        Expr::OptionalChain { expr, field } => Expr::OptionalChain {
            expr: Box::new(replace_numbered_placeholders(*expr)),
            field,
        },
        Expr::Coalesce { expr, default } => Expr::Coalesce {
            expr: Box::new(replace_numbered_placeholders(*expr)),
            default: Box::new(replace_numbered_placeholders(*default)),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            start: start.map(|e| Box::new(replace_numbered_placeholders(*e))),
            end: end.map(|e| Box::new(replace_numbered_placeholders(*e))),
            step: step.map(|e| Box::new(replace_numbered_placeholders(*e))),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(replace_numbered_placeholders(*expr)),
            target_type,
        },
        Expr::Spread(inner) => Expr::Spread(Box::new(replace_numbered_placeholders(*inner))),
        Expr::Lambda { .. } => expr,
        _ => expr,
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
