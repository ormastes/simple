//! Receiver discovery for class/struct declaration metadata.
use super::*;

pub fn block_uses_self(body: &Block) -> bool {
    body.statements.iter().any(node_uses_self)
}

fn node_uses_self(node: &Node) -> bool {
    match node {
        Node::Let(stmt) => stmt.value.as_ref().map(expr_uses_self).unwrap_or(false),
        Node::Assignment(stmt) => expr_uses_self(&stmt.target) || expr_uses_self(&stmt.value),
        Node::Return(stmt) => stmt.value.as_ref().map(expr_uses_self).unwrap_or(false),
        Node::If(stmt) => {
            expr_uses_self(&stmt.condition)
                || block_uses_self(&stmt.then_block)
                || stmt
                    .elif_branches
                    .iter()
                    .any(|(_, condition, block)| expr_uses_self(condition) || block_uses_self(block))
                || stmt.else_block.as_ref().map(block_uses_self).unwrap_or(false)
        }
        Node::Match(stmt) => {
            expr_uses_self(&stmt.subject)
                || stmt
                    .arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().map(expr_uses_self).unwrap_or(false) || block_uses_self(&arm.body))
        }
        Node::For(stmt) => expr_uses_self(&stmt.iterable) || block_uses_self(&stmt.body),
        Node::While(stmt) => expr_uses_self(&stmt.condition) || block_uses_self(&stmt.body),
        Node::Loop(stmt) => block_uses_self(&stmt.body),
        Node::Expression(expr) => expr_uses_self(expr),
        _ => false,
    }
}

fn args_use_self(args: &[Argument]) -> bool {
    args.iter().any(|arg| expr_uses_self(&arg.value))
}

fn expr_uses_self(expr: &Expr) -> bool {
    match expr {
        Expr::Identifier(name) => name == "self",
        Expr::FString { parts, .. } => fstring_parts_use_self(parts),
        Expr::I18nTemplate { parts, args, .. } => {
            fstring_parts_use_self(parts) || args.iter().any(|(_, expr)| expr_uses_self(expr))
        }
        Expr::Binary { left, right, .. } => expr_uses_self(left) || expr_uses_self(right),
        Expr::Unary { operand, .. } => expr_uses_self(operand),
        Expr::Cast { expr, .. } => expr_uses_self(expr),
        Expr::Call { callee, args } => expr_uses_self(callee) || args_use_self(args),
        Expr::MethodCall { receiver, args, .. } => expr_uses_self(receiver) || args_use_self(args),
        Expr::FieldAccess { receiver, .. } => expr_uses_self(receiver),
        Expr::Index { receiver, index } => expr_uses_self(receiver) || expr_uses_self(index),
        Expr::TupleIndex { receiver, .. } => expr_uses_self(receiver),
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            expr_uses_self(condition)
                || expr_uses_self(then_branch)
                || else_branch.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false)
        }
        Expr::Match { subject, arms } => {
            expr_uses_self(subject)
                || arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().map(expr_uses_self).unwrap_or(false) || block_uses_self(&arm.body))
        }
        Expr::Tuple(exprs) | Expr::Array(exprs) | Expr::VecLiteral(exprs) => {
            exprs.iter().any(expr_uses_self)
        }
        Expr::Dict(pairs) => pairs
            .iter()
            .any(|(key, value)| expr_uses_self(key) || expr_uses_self(value)),
        Expr::ArrayRepeat { value, count } => expr_uses_self(value) || expr_uses_self(count),
        Expr::StructInit { fields, spread, .. } => {
            fields.iter().any(|(_, value)| expr_uses_self(value))
                || spread.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false)
        }
        Expr::Yield(value) => value.as_ref().map(|expr| expr_uses_self(expr)).unwrap_or(false),
        Expr::Try(expr)
        | Expr::ForceUnwrap(expr)
        | Expr::ExistsCheck(expr)
        | Expr::Await(expr)
        | Expr::Spawn(expr)
        | Expr::ContractOld(expr) => expr_uses_self(expr),
        Expr::UnwrapOrReturn { expr, default } => expr_uses_self(expr) || expr_uses_self(default),
        Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes, _) => nodes.iter().any(node_uses_self),
        _ => false,
    }
}

fn fstring_parts_use_self(parts: &[FStringPart]) -> bool {
    parts.iter().any(|part| match part {
        FStringPart::Literal(_) => false,
        FStringPart::Expr(expr) => expr_uses_self(expr),
        FStringPart::ExprWithFormat(expr, _) => expr_uses_self(expr),
    })
}

#[cfg(test)]
mod implicit_receiver_tests {
    use super::expr_uses_self;
    use crate::Expr;

    #[test]
    fn dict_literals_retain_implicit_receiver_from_keys_and_values() {
        let self_expr = || Expr::Identifier("self".to_string());
        let literal = |value: &str| Expr::String(value.to_string());

        assert!(expr_uses_self(&Expr::Dict(vec![(self_expr(), literal("value"))])));
        assert!(expr_uses_self(&Expr::Dict(vec![(literal("key"), self_expr())])));
        assert!(!expr_uses_self(&Expr::Dict(vec![(literal("key"), literal("value"))])));
    }
}
