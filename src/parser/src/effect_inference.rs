//! Effect inference for automatic async/sync detection.
//!
//! This module analyzes function bodies to determine whether they should be
//! marked as async based on suspension operator usage.
//!
//! Suspension operators that imply async effect:
//! - `~=` (suspension assignment)
//! - `if~`, `while~`, `for~` (suspension guards)
//! - `and~`, `or~` (suspension boolean operators)
//! - `~+=`, `~-=`, `~*=`, `~/=` (compound suspension operators)

use crate::ast::{AssignOp, BinOp, Block, Expr, Node};

/// Check if a function body contains suspension operators.
/// Returns true if any suspension operator is found, indicating async effect.
pub fn has_suspension_in_body(body: &Block) -> bool {
    for stmt in &body.statements {
        if has_suspension_in_node(stmt) {
            return true;
        }
    }
    false
}

/// Check if a node contains suspension operators.
fn has_suspension_in_node(node: &Node) -> bool {
    match node {
        // Let statement with suspension
        Node::Let(let_stmt) => {
            if let_stmt.is_suspend {
                return true;
            }
            // Also check the value expression
            if let Some(ref value) = let_stmt.value {
                if has_suspension_in_expr(value) {
                    return true;
                }
            }
            false
        }

        // If statement with suspension
        Node::If(if_stmt) => {
            if if_stmt.is_suspend {
                return true;
            }
            // Check condition
            if has_suspension_in_expr(&if_stmt.condition) {
                return true;
            }
            // Check then block
            if has_suspension_in_body(&if_stmt.then_block) {
                return true;
            }
            // Check elif branches
            for (cond, block) in &if_stmt.elif_branches {
                if has_suspension_in_expr(cond) || has_suspension_in_body(block) {
                    return true;
                }
            }
            // Check else block
            if let Some(ref else_block) = if_stmt.else_block {
                if has_suspension_in_body(else_block) {
                    return true;
                }
            }
            false
        }

        // While statement with suspension
        Node::While(while_stmt) => {
            if while_stmt.is_suspend {
                return true;
            }
            if has_suspension_in_expr(&while_stmt.condition) {
                return true;
            }
            has_suspension_in_body(&while_stmt.body)
        }

        // For statement with suspension
        Node::For(for_stmt) => {
            if for_stmt.is_suspend {
                return true;
            }
            if has_suspension_in_expr(&for_stmt.iterable) {
                return true;
            }
            has_suspension_in_body(&for_stmt.body)
        }

        // Assignment statement - check for suspension operators
        Node::Assignment(assign) => {
            if is_suspension_assign_op(&assign.op) {
                return true;
            }
            has_suspension_in_expr(&assign.target) || has_suspension_in_expr(&assign.value)
        }

        // Expression statement
        Node::Expression(expr) => has_suspension_in_expr(expr),

        // Return statement
        Node::Return(ret) => {
            if let Some(ref value) = ret.value {
                has_suspension_in_expr(value)
            } else {
                false
            }
        }

        // Loop statement
        Node::Loop(loop_stmt) => has_suspension_in_body(&loop_stmt.body),

        // Match statement
        Node::Match(match_stmt) => {
            if has_suspension_in_expr(&match_stmt.subject) {
                return true;
            }
            for arm in &match_stmt.arms {
                if has_suspension_in_body(&arm.body) {
                    return true;
                }
                if let Some(ref guard) = arm.guard {
                    if has_suspension_in_expr(guard) {
                        return true;
                    }
                }
            }
            false
        }

        // With statement
        Node::With(with_stmt) => {
            if has_suspension_in_expr(&with_stmt.resource) {
                return true;
            }
            has_suspension_in_body(&with_stmt.body)
        }

        // Nested function - don't traverse into it (has its own effect)
        Node::Function(_) => false,

        // Other nodes that don't contain suspension
        _ => false,
    }
}

/// Check if an expression contains suspension operators.
fn has_suspension_in_expr(expr: &Expr) -> bool {
    match expr {
        // Binary operators - check for and~/or~
        Expr::Binary { op, left, right } => {
            if matches!(op, BinOp::AndSuspend | BinOp::OrSuspend) {
                return true;
            }
            has_suspension_in_expr(left) || has_suspension_in_expr(right)
        }

        // Unary operators
        Expr::Unary { operand, .. } => has_suspension_in_expr(operand),

        // Call expressions
        Expr::Call { callee, args } => {
            if has_suspension_in_expr(callee) {
                return true;
            }
            for arg in args {
                if has_suspension_in_expr(&arg.value) {
                    return true;
                }
            }
            false
        }

        // Method calls
        Expr::MethodCall { receiver, args, .. } => {
            if has_suspension_in_expr(receiver) {
                return true;
            }
            for arg in args {
                if has_suspension_in_expr(&arg.value) {
                    return true;
                }
            }
            false
        }

        // Index/subscript
        Expr::Index { receiver, index } => {
            has_suspension_in_expr(receiver) || has_suspension_in_expr(index)
        }

        // Field access
        Expr::FieldAccess { receiver, .. } => has_suspension_in_expr(receiver),

        // Array/list
        Expr::Array(elements) => elements.iter().any(|e| has_suspension_in_expr(e)),

        // Tuple
        Expr::Tuple(elements) => elements.iter().any(|e| has_suspension_in_expr(e)),

        // Lambda - don't traverse into it (has its own effect)
        Expr::Lambda { .. } => false,

        // Do block
        Expr::DoBlock(nodes) => {
            // Check each node in the do block for suspension
            for node in nodes {
                if has_suspension_in_node(node) {
                    return true;
                }
            }
            false
        }

        // Range
        Expr::Range { start, end, .. } => {
            if let Some(ref s) = start {
                if has_suspension_in_expr(s) {
                    return true;
                }
            }
            if let Some(ref e) = end {
                if has_suspension_in_expr(e) {
                    return true;
                }
            }
            false
        }

        // Struct initialization
        Expr::StructInit { fields, .. } => {
            for (_, expr) in fields {
                if has_suspension_in_expr(expr) {
                    return true;
                }
            }
            false
        }

        // Dict literal
        Expr::Dict(entries) => {
            for (k, v) in entries {
                if has_suspension_in_expr(k) || has_suspension_in_expr(v) {
                    return true;
                }
            }
            false
        }

        // Spread
        Expr::Spread(inner) => has_suspension_in_expr(inner),

        // Try expression (?)
        Expr::Try(inner) => has_suspension_in_expr(inner),

        // All other expressions (literals, identifiers, etc.) - no suspension
        // This includes: Int, Float, String, Bool, Char, Identifier, SelfRef, Nil, etc.
        _ => false,
    }
}

/// Check if an assignment operator is a suspension operator.
fn is_suspension_assign_op(op: &AssignOp) -> bool {
    matches!(
        op,
        AssignOp::SuspendAssign
            | AssignOp::SuspendAddAssign
            | AssignOp::SuspendSubAssign
            | AssignOp::SuspendMulAssign
            | AssignOp::SuspendDivAssign
    )
}

// Tests are in simple/std_lib/test/features/concurrency/effect_inference_spec.spl
