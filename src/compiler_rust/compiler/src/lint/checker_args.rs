//! Lint check for unnamed arguments when multiple parameters share the same type.
//!
//! #![skip_todo]

use super::checker_core::{format_type, FunctionInfo, LintChecker, ParamInfo};
use super::super::types::LintName;
use simple_parser::ast::{Argument, Expr, Node};
use simple_parser::token::Span;
use std::collections::HashMap;

impl LintChecker {
    /// Check for unnamed arguments when parameters share the same type
    pub(super) fn check_unnamed_duplicate_typed_args(&mut self, items: &[Node]) {
        // Check for file-level allow via #![allow(unnamed_duplicate_typed_args)]
        if self.has_file_level_allow("unnamed_duplicate_typed_args") {
            return; // File-level allow, skip this lint
        }

        // Find parameter indices that share a type with at least one other parameter.
        // O(n) via grouping by type string key.
        fn find_duplicate_typed_params(params: &[ParamInfo]) -> std::collections::HashSet<usize> {
            let mut by_type: HashMap<String, Vec<usize>> = HashMap::new();
            for (i, param) in params.iter().enumerate() {
                if let Some(ref ty) = param.ty {
                    by_type.entry(format_type(ty)).or_default().push(i);
                }
            }
            let mut duplicates = std::collections::HashSet::new();
            for indices in by_type.values() {
                if indices.len() > 1 {
                    for &i in indices {
                        duplicates.insert(i);
                    }
                }
            }
            duplicates
        }

        // Get the function name from a callee expression
        fn get_callee_name(expr: &Expr) -> Option<String> {
            match expr {
                Expr::Identifier(name) => Some(name.clone()),
                Expr::FieldAccess { field, .. } => Some(field.clone()),
                _ => None,
            }
        }

        // Check a call expression
        fn check_call(checker: &mut LintChecker, callee_name: &str, args: &[Argument], _span: Span) {
            // Look up the function in the registry
            let func_info = match checker.functions.get(callee_name) {
                Some(info) => info.clone(),
                None => return, // Function not found, skip
            };

            let duplicate_indices = find_duplicate_typed_params(&func_info.params);
            if duplicate_indices.is_empty() {
                return; // No duplicate types
            }

            // Pre-compute peer name map: for each duplicate index, the names of
            // other params sharing the same type. O(n) instead of re-scanning per arg.
            let mut peer_names: HashMap<usize, (String, Vec<String>)> = HashMap::new();
            {
                // Group by type string
                let mut by_type: HashMap<String, Vec<usize>> = HashMap::new();
                for &i in &duplicate_indices {
                    if let Some(ref ty) = func_info.params[i].ty {
                        by_type.entry(format_type(ty)).or_default().push(i);
                    }
                }
                for (type_str, indices) in &by_type {
                    for &i in indices {
                        let peers: Vec<String> = indices
                            .iter()
                            .filter(|&&j| j != i)
                            .map(|&j| func_info.params[j].name.clone())
                            .collect();
                        peer_names.insert(i, (type_str.clone(), peers));
                    }
                }
            }

            // Check if any duplicate-typed parameter is passed positionally
            for (arg_idx, arg) in args.iter().enumerate() {
                if arg.name.is_some() {
                    continue; // Named argument, OK
                }

                // This is a positional argument
                if arg_idx >= func_info.params.len() {
                    continue; // Extra args (variadic or error)
                }

                if let Some((type_str, peers)) = peer_names.get(&arg_idx) {
                    let param = &func_info.params[arg_idx];

                    checker.emit(
                        LintName::UnnamedDuplicateTypedArgs,
                        arg.span, // Use the argument's span for proper location reporting
                        format!(
                            "positional argument for parameter `{}` which shares type `{}` with `{}`",
                            param.name,
                            type_str,
                            peers.join("`, `")
                        ),
                        Some(format!("consider using named argument: `{}: <value>`", param.name)),
                    );
                }
            }
        }

        // Recursively check expressions
        fn check_expr(checker: &mut LintChecker, expr: &Expr) {
            match expr {
                Expr::Call { callee, args } => {
                    if let Some(name) = get_callee_name(callee) {
                        check_call(checker, &name, args, Span::new(0, 0, 0, 0));
                    }
                    check_expr(checker, callee);
                    for arg in args {
                        check_expr(checker, &arg.value);
                    }
                }
                Expr::MethodCall {
                    receiver, method, args, ..
                } => {
                    // Try to look up method
                    check_call(checker, method, args, Span::new(0, 0, 0, 0));
                    check_expr(checker, receiver);
                    for arg in args {
                        check_expr(checker, &arg.value);
                    }
                }
                Expr::Binary { left, right, .. } => {
                    check_expr(checker, left);
                    check_expr(checker, right);
                }
                Expr::Unary { operand, .. } => {
                    check_expr(checker, operand);
                }
                Expr::FieldAccess { receiver, .. } => {
                    check_expr(checker, receiver);
                }
                Expr::Index { receiver, index } => {
                    check_expr(checker, receiver);
                    check_expr(checker, index);
                }
                Expr::Lambda { body, .. } => {
                    check_expr(checker, body);
                }
                Expr::Array(elements) => {
                    for elem in elements {
                        check_expr(checker, elem);
                    }
                }
                Expr::Tuple(elements) => {
                    for elem in elements {
                        check_expr(checker, elem);
                    }
                }
                Expr::DoBlock(stmts) => {
                    for stmt in stmts {
                        check_stmt(checker, stmt);
                    }
                }
                Expr::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    check_expr(checker, condition);
                    check_expr(checker, then_branch);
                    if let Some(eb) = else_branch {
                        check_expr(checker, eb);
                    }
                }
                _ => {}
            }
        }

        // Recursively check statements
        fn check_stmt(checker: &mut LintChecker, node: &Node) {
            use simple_parser::ast::{LetStmt, ReturnStmt};

            match node {
                Node::Expression(expr) => check_expr(checker, expr),
                Node::Let(LetStmt { value: Some(v), .. }) => {
                    check_expr(checker, v);
                }
                Node::Assignment(assign) => {
                    check_expr(checker, &assign.value);
                }
                Node::Return(ReturnStmt { value: Some(v), .. }) => {
                    check_expr(checker, v);
                }
                Node::If(if_stmt) => {
                    check_expr(checker, &if_stmt.condition);
                    for stmt in &if_stmt.then_block.statements {
                        check_stmt(checker, stmt);
                    }
                    for (_elif_pattern, elif_cond, elif_block) in &if_stmt.elif_branches {
                        check_expr(checker, elif_cond);
                        for stmt in &elif_block.statements {
                            check_stmt(checker, stmt);
                        }
                    }
                    if let Some(else_block) = &if_stmt.else_block {
                        for stmt in &else_block.statements {
                            check_stmt(checker, stmt);
                        }
                    }
                }
                Node::Match(match_stmt) => {
                    check_expr(checker, &match_stmt.subject);
                    for arm in &match_stmt.arms {
                        for stmt in &arm.body.statements {
                            check_stmt(checker, stmt);
                        }
                    }
                }
                Node::For(for_stmt) => {
                    check_expr(checker, &for_stmt.iterable);
                    for stmt in &for_stmt.body.statements {
                        check_stmt(checker, stmt);
                    }
                }
                Node::While(while_stmt) => {
                    check_expr(checker, &while_stmt.condition);
                    for stmt in &while_stmt.body.statements {
                        check_stmt(checker, stmt);
                    }
                }
                Node::Loop(loop_stmt) => {
                    for stmt in &loop_stmt.body.statements {
                        check_stmt(checker, stmt);
                    }
                }
                Node::Function(func) => {
                    for stmt in &func.body.statements {
                        check_stmt(checker, stmt);
                    }
                }
                _ => {}
            }
        }

        for item in items {
            check_stmt(self, item);
        }
    }
}
