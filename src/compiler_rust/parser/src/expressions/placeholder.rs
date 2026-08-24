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
use crate::ast::{extract_fstring_keys, Argument, Expr, FStringPart, LambdaParam, TypeMeta};

/// Check if an identifier is a numbered placeholder like `_1`, `_2`, etc.
fn is_numbered_placeholder(name: &str) -> bool {
    if name.len() < 2 || !name.starts_with('_') {
        return false;
    }
    // Numbered placeholders are canonical and 1-indexed. Reject `_0` and
    // leading-zero aliases before replacement subtracts one from the index.
    if name.as_bytes()[1] == b'0' {
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
    if is_exact_placeholder_expr(&expr) {
        return expr;
    }
    force_transform_placeholder_lambda(expr)
}

/// Transform placeholder lambda syntax even when the whole expression is a
/// single placeholder. This is used for known higher-order call sites such as
/// `.map(_1)`, while ordinary calls like `int(_1)` keep `_1` available for the
/// enclosing placeholder expression.
pub fn force_transform_placeholder_lambda(expr: Expr) -> Expr {
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

/// Return true for a bare placeholder expression (`_`, `_1`, `_2`, ...).
pub fn is_exact_placeholder_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Identifier(name) => name == "_" || is_numbered_placeholder(name),
        _ => false,
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
        Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => find_max_numbered(receiver),
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
        Expr::FString { parts, .. } => parts.iter().fold(0, |acc, part| {
            acc.max(match part {
                FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => find_max_numbered(expr),
                FStringPart::Literal(_) => 0,
            })
        }),
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
        // Match: scan the scrutinee (subject) only. Arms are a scoping boundary
        // because `case _:` uses `_` as a wildcard pattern, not a placeholder.
        Expr::Match { subject, .. } => find_max_numbered(subject),
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
        Expr::MethodCall {
            receiver,
            method,
            args,
            generic_args,
        } => Expr::MethodCall {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            method,
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_numbered_placeholders(a.value), a.span))
                .collect(),
            generic_args,
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            field,
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(replace_numbered_placeholders(*receiver)),
            index,
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
        Expr::FString { parts, .. } => {
            let parts = replace_numbered_fstring_parts(parts);
            let type_meta = TypeMeta::with_const_keys(extract_fstring_keys(&parts));
            Expr::FString { parts, type_meta }
        }
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
        // Match: replace placeholders in the scrutinee (subject) only.
        // Arms are a scoping boundary; their bodies and patterns are left
        // unchanged so that `case _:` wildcards are not mis-replaced.
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(replace_numbered_placeholders(*subject)),
            arms,
        },
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
        Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => count_placeholders(receiver),
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
        // Bug (2026-07-30, string_template_multi_placeholder_slot_not_found): a
        // bare (unnumbered) `_` used more than once across an f-string's
        // `{...}` interpolation regions always refers to the SAME implicit
        // bound value -- the one argument a higher-order callback such as
        // `.map("{_.0}: {_.1}")` receives per call -- unlike an ordinary
        // expression like `_ + _`, where each `_` is legitimately a distinct
        // positional lambda parameter. Summing per-occurrence (as the
        // general-expression arms above do) over-counts and makes
        // `force_transform_placeholder_lambda` synthesize a lambda with more
        // parameters than `.map` ever supplies, leaving the extra `__pN`
        // unbound ("semantic: variable `__pN` not found"). Collapse to at
        // most 1 (presence, not count) so the whole f-string shares one slot,
        // mirroring how a repeated numbered placeholder (`_1` used twice)
        // already collapses via `find_max_numbered`/`replace_numbered_placeholders`.
        Expr::FString { parts, .. } => {
            if parts.iter().any(|part| match part {
                FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => count_placeholders(expr) > 0,
                FStringPart::Literal(_) => false,
            }) {
                1
            } else {
                0
            }
        }
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
        // Match: count placeholders in the scrutinee only; arms are a scoping boundary.
        Expr::Match { subject, .. } => count_placeholders(subject),
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
        Expr::MethodCall {
            receiver,
            method,
            args,
            generic_args,
        } => Expr::MethodCall {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            method,
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_placeholders(a.value, counter), a.span))
                .collect(),
            generic_args,
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            field,
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(replace_placeholders(*receiver, counter)),
            index,
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
        Expr::FString { parts, .. } => {
            // See the matching note in `count_placeholders`'s `Expr::FString`
            // arm: every bare `_` inside one f-string shares a SINGLE slot
            // (reserved once from the outer counter), instead of each
            // occurrence grabbing its own incrementing slot.
            let has_bare_placeholder = parts.iter().any(|part| match part {
                FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => count_placeholders(expr) > 0,
                FStringPart::Literal(_) => false,
            });
            let parts = if has_bare_placeholder {
                let slot = *counter;
                *counter += 1;
                replace_fstring_parts_shared_slot(parts, slot)
            } else {
                parts
            };
            let type_meta = TypeMeta::with_const_keys(extract_fstring_keys(&parts));
            Expr::FString { parts, type_meta }
        }
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
        // Match: replace placeholders in the scrutinee only.
        // Arms are a scoping boundary; their bodies/patterns are left unchanged
        // so that `case _:` wildcards are not mis-replaced.
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(replace_placeholders(*subject, counter)),
            arms,
        },
        // Terminal expressions with no sub-expressions - return unchanged
        _ => expr,
    }
}

/// Replace every bare `_` placeholder inside an f-string's interpolation
/// parts with the SAME fixed slot number (see the note in
/// `replace_placeholders`'s `Expr::FString` arm). Used only for f-string
/// bodies, where all bare `_` occurrences denote one shared implicit value
/// rather than independent positional lambda parameters.
fn replace_fstring_parts_shared_slot(parts: Vec<FStringPart>, slot: usize) -> Vec<FStringPart> {
    parts
        .into_iter()
        .map(|part| match part {
            FStringPart::Expr(expr) => FStringPart::Expr(replace_bare_placeholder_fixed(expr, slot)),
            FStringPart::ExprWithFormat(expr, format_spec) => {
                FStringPart::ExprWithFormat(replace_bare_placeholder_fixed(expr, slot), format_spec)
            }
            FStringPart::Literal(text) => FStringPart::Literal(text),
        })
        .collect()
}

/// Like `replace_placeholders`, but every bare `_` maps to the SAME fixed
/// slot instead of an incrementing counter.
fn replace_bare_placeholder_fixed(expr: Expr, slot: usize) -> Expr {
    match expr {
        Expr::Identifier(name) if name == "_" => Expr::Identifier(format!("__p{}", slot)),
        Expr::Binary { op, left, right } => Expr::Binary {
            op,
            left: Box::new(replace_bare_placeholder_fixed(*left, slot)),
            right: Box::new(replace_bare_placeholder_fixed(*right, slot)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op,
            operand: Box::new(replace_bare_placeholder_fixed(*operand, slot)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(replace_bare_placeholder_fixed(*callee, slot)),
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_bare_placeholder_fixed(a.value, slot), a.span))
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
            generic_args,
        } => Expr::MethodCall {
            receiver: Box::new(replace_bare_placeholder_fixed(*receiver, slot)),
            method,
            args: args
                .into_iter()
                .map(|a| Argument::with_span(a.name, replace_bare_placeholder_fixed(a.value, slot), a.span))
                .collect(),
            generic_args,
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(replace_bare_placeholder_fixed(*receiver, slot)),
            field,
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(replace_bare_placeholder_fixed(*receiver, slot)),
            index,
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(replace_bare_placeholder_fixed(*receiver, slot)),
            index: Box::new(replace_bare_placeholder_fixed(*index, slot)),
        },
        Expr::If {
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            let_pattern,
            condition: Box::new(replace_bare_placeholder_fixed(*condition, slot)),
            then_branch: Box::new(replace_bare_placeholder_fixed(*then_branch, slot)),
            else_branch: else_branch.map(|e| Box::new(replace_bare_placeholder_fixed(*e, slot))),
        },
        Expr::Tuple(items) => Expr::Tuple(
            items
                .into_iter()
                .map(|e| replace_bare_placeholder_fixed(e, slot))
                .collect(),
        ),
        Expr::Array(items) => Expr::Array(
            items
                .into_iter()
                .map(|e| replace_bare_placeholder_fixed(e, slot))
                .collect(),
        ),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .into_iter()
                .map(|(k, v)| {
                    (
                        replace_bare_placeholder_fixed(k, slot),
                        replace_bare_placeholder_fixed(v, slot),
                    )
                })
                .collect(),
        ),
        Expr::FString { parts, .. } => {
            let parts = replace_fstring_parts_shared_slot(parts, slot);
            let type_meta = TypeMeta::with_const_keys(extract_fstring_keys(&parts));
            Expr::FString { parts, type_meta }
        }
        Expr::OptionalChain { expr, field } => Expr::OptionalChain {
            expr: Box::new(replace_bare_placeholder_fixed(*expr, slot)),
            field,
        },
        Expr::Coalesce { expr, default } => Expr::Coalesce {
            expr: Box::new(replace_bare_placeholder_fixed(*expr, slot)),
            default: Box::new(replace_bare_placeholder_fixed(*default, slot)),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(replace_bare_placeholder_fixed(*receiver, slot)),
            start: start.map(|e| Box::new(replace_bare_placeholder_fixed(*e, slot))),
            end: end.map(|e| Box::new(replace_bare_placeholder_fixed(*e, slot))),
            step: step.map(|e| Box::new(replace_bare_placeholder_fixed(*e, slot))),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(replace_bare_placeholder_fixed(*expr, slot)),
            target_type,
        },
        Expr::Spread(inner) => Expr::Spread(Box::new(replace_bare_placeholder_fixed(*inner, slot))),
        Expr::Lambda { .. } => expr,
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(replace_bare_placeholder_fixed(*subject, slot)),
            arms,
        },
        _ => expr,
    }
}

fn replace_numbered_fstring_parts(parts: Vec<FStringPart>) -> Vec<FStringPart> {
    parts
        .into_iter()
        .map(|part| match part {
            FStringPart::Expr(expr) => FStringPart::Expr(replace_numbered_placeholders(expr)),
            FStringPart::ExprWithFormat(expr, format_spec) => {
                FStringPart::ExprWithFormat(replace_numbered_placeholders(expr), format_spec)
            }
            FStringPart::Literal(text) => FStringPart::Literal(text),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbered_placeholders_are_canonical_and_one_based() {
        for rejected in ["_0", "_00", "_01", "env_get", "_a", "_9x"] {
            assert!(!is_numbered_placeholder(rejected), "accepted {rejected}");
            assert_eq!(numbered_placeholder_index(rejected), None);
        }
        assert_eq!(numbered_placeholder_index("_1"), Some(1));
        assert_eq!(numbered_placeholder_index("_10"), Some(10));
    }

    fn fstring_with_expr(expr: Expr) -> Expr {
        let parts = vec![FStringPart::Literal("item:".to_string()), FStringPart::Expr(expr)];
        Expr::FString {
            type_meta: TypeMeta::with_const_keys(extract_fstring_keys(&parts)),
            parts,
        }
    }

    #[test]
    fn transforms_numbered_placeholders_inside_fstring_interpolation() {
        let transformed = force_transform_placeholder_lambda(fstring_with_expr(Expr::Identifier("_1".to_string())));

        match transformed {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name, "__p0");
                match *body {
                    Expr::FString { parts, type_meta } => {
                        assert_eq!(type_meta.const_keys(), Some(&vec!["__p0".to_string()]));
                        assert_eq!(parts[0], FStringPart::Literal("item:".to_string()));
                        assert_eq!(parts[1], FStringPart::Expr(Expr::Identifier("__p0".to_string())));
                    }
                    other => panic!("expected f-string body, got {other:?}"),
                }
            }
            other => panic!("expected lambda, got {other:?}"),
        }
    }

    #[test]
    fn transforms_bare_placeholders_inside_formatted_fstring_interpolation() {
        let parts = vec![FStringPart::ExprWithFormat(
            Expr::Identifier("_".to_string()),
            ">8".to_string(),
        )];
        let transformed = force_transform_placeholder_lambda(Expr::FString {
            type_meta: TypeMeta::with_const_keys(extract_fstring_keys(&parts)),
            parts,
        });

        match transformed {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name, "__p0");
                match *body {
                    Expr::FString { parts, .. } => {
                        assert_eq!(
                            parts[0],
                            FStringPart::ExprWithFormat(Expr::Identifier("__p0".to_string()), ">8".to_string())
                        );
                    }
                    other => panic!("expected f-string body, got {other:?}"),
                }
            }
            other => panic!("expected lambda, got {other:?}"),
        }
    }

    #[test]
    fn transforms_tuple_index_placeholders_inside_fstring_interpolation() {
        let transformed = force_transform_placeholder_lambda(fstring_with_expr(Expr::TupleIndex {
            receiver: Box::new(Expr::Identifier("_1".to_string())),
            index: 1,
        }));

        match transformed {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name, "__p0");
                match *body {
                    Expr::FString { parts, .. } => {
                        assert_eq!(
                            parts[1],
                            FStringPart::Expr(Expr::TupleIndex {
                                receiver: Box::new(Expr::Identifier("__p0".to_string())),
                                index: 1,
                            })
                        );
                    }
                    other => panic!("expected f-string body, got {other:?}"),
                }
            }
            other => panic!("expected lambda, got {other:?}"),
        }
    }

    #[test]
    fn two_bare_placeholders_in_one_fstring_share_one_param() {
        // Regression for string_template_multi_placeholder_slot_not_found
        // (2026-07-30): `"{_.0}: {_.1}"` (two bare `_` across different
        // interpolation regions of the SAME f-string) must synthesize a
        // single-parameter lambda (`__p0` reused for both), not a two-param
        // lambda -- `.map()` only ever supplies one argument per call, so a
        // second parameter is never bound and previously failed at semantic
        // analysis with "variable `__p1` not found".
        let parts = vec![
            FStringPart::Expr(Expr::TupleIndex {
                receiver: Box::new(Expr::Identifier("_".to_string())),
                index: 0,
            }),
            FStringPart::Literal(": ".to_string()),
            FStringPart::Expr(Expr::TupleIndex {
                receiver: Box::new(Expr::Identifier("_".to_string())),
                index: 1,
            }),
        ];
        let transformed = force_transform_placeholder_lambda(Expr::FString {
            type_meta: TypeMeta::with_const_keys(extract_fstring_keys(&parts)),
            parts,
        });

        match transformed {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1, "expected exactly one shared parameter");
                assert_eq!(params[0].name, "__p0");
                match *body {
                    Expr::FString { parts, .. } => {
                        assert_eq!(
                            parts[0],
                            FStringPart::Expr(Expr::TupleIndex {
                                receiver: Box::new(Expr::Identifier("__p0".to_string())),
                                index: 0,
                            })
                        );
                        assert_eq!(
                            parts[2],
                            FStringPart::Expr(Expr::TupleIndex {
                                receiver: Box::new(Expr::Identifier("__p0".to_string())),
                                index: 1,
                            })
                        );
                    }
                    other => panic!("expected f-string body, got {other:?}"),
                }
            }
            other => panic!("expected lambda, got {other:?}"),
        }
    }

    #[test]
    fn same_bare_placeholder_reused_twice_in_one_fstring_shares_one_param() {
        // Regression: `"{_.0}-{_.0}"` (the SAME field, referenced twice)
        // previously ALSO failed with "variable `__p1` not found" -- proving
        // this was never about distinct positions, just occurrence count.
        let parts = vec![
            FStringPart::Expr(Expr::TupleIndex {
                receiver: Box::new(Expr::Identifier("_".to_string())),
                index: 0,
            }),
            FStringPart::Literal("-".to_string()),
            FStringPart::Expr(Expr::TupleIndex {
                receiver: Box::new(Expr::Identifier("_".to_string())),
                index: 0,
            }),
        ];
        let transformed = force_transform_placeholder_lambda(Expr::FString {
            type_meta: TypeMeta::with_const_keys(extract_fstring_keys(&parts)),
            parts,
        });

        match transformed {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1, "expected exactly one shared parameter");
                assert_eq!(params[0].name, "__p0");
            }
            other => panic!("expected lambda, got {other:?}"),
        }
    }
}
