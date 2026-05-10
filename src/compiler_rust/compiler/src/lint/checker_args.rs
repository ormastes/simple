//! Lint checker: duplicate typed arguments and call-site checks.

use super::super::types::LintName;
use super::checker_core::{format_type, FunctionInfo, ParamInfo};
use simple_common::diagnostic::{EasyFix, FixConfidence, Replacement};
use simple_parser::ast::{Argument, Expr, Node};
use std::collections::HashMap;

use super::LintChecker;

impl LintChecker {
    /// Check for a file-level lint suppression attribute.
    pub(super) fn has_file_level_allow(&self, lint_name: &str) -> bool {
        if let Some(ref path) = self.source_file {
            if let Ok(source) = std::fs::read_to_string(path) {
                let pattern = format!("{}!{}{}({})]", "#", "[", "allow", lint_name);
                // Check first 50 lines for a file-level suppression marker.
                for line in source.lines().take(50) {
                    if line.contains(&pattern) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Check for unnamed arguments when parameters share the same type
    pub(super) fn check_unnamed_duplicate_typed_args(&mut self, items: &[Node]) {
        // Check for a file-level suppression marker for this lint.
        if self.has_file_level_allow("unnamed_duplicate_typed_args") {
            return; // File-level suppression, skip this lint
        }
        if self.source_file.as_deref().is_some_and(Self::is_test_like_path) {
            return;
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

        fn build_named_arg_fix(
            source_file: Option<&str>,
            source_text: Option<&str>,
            func_info: &FunctionInfo,
            arg: &Argument,
            param: &ParamInfo,
        ) -> Option<EasyFix> {
            if !func_info.named_call_rewrite_safe || arg.label.is_some() {
                return None;
            }

            let file = source_file?;
            let source = source_text?;
            if arg.span.start >= arg.span.end || arg.span.end > source.len() {
                return None;
            }

            let arg_text = source.get(arg.span.start..arg.span.end)?;
            Some(EasyFix {
                id: format!(
                    "L:{}:{}:{}",
                    LintName::UnnamedDuplicateTypedArgs.as_str(),
                    arg.span.line,
                    param.name
                ),
                description: format!("rewrite positional argument as named argument `{}`", param.name),
                replacements: vec![Replacement {
                    file: file.to_string(),
                    span: simple_common::diagnostic::Span::new(
                        arg.span.start,
                        arg.span.end,
                        arg.span.line,
                        arg.span.column,
                    ),
                    new_text: format!("{}: {}", param.name, arg_text),
                }],
                confidence: FixConfidence::Safe,
            })
        }

        // Check a call expression
        fn check_call(
            checker: &mut LintChecker,
            callee_name: &str,
            args: &[Argument],
            source_file: Option<&str>,
            source_text: Option<&str>,
        ) {
            // Look up the function in the registry
            let func_info = match checker.functions.get(callee_name) {
                Some(info) => info.clone(),
                None => return, // Function not found, skip
            };
            if !func_info.lint_unnamed_duplicate_typed_args {
                return;
            }

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
                    if arg.label.is_some() && arg.label == param.call_site_label {
                        continue;
                    }

                    let label_hint = param
                        .call_site_label
                        .as_ref()
                        .map(|label| format!(" or using its call-site label `{}`", label))
                        .unwrap_or_default();

                    let easy_fix = build_named_arg_fix(source_file, source_text, &func_info, arg, param);
                    let suggestion = if easy_fix.is_some() {
                        Some(format!(
                            "rewrite this same-file call as named argument `{}: <value>`; an automatic fix is available",
                            param.name
                        ))
                    } else {
                        Some(match &param.call_site_label {
                            Some(label) => format!(
                                "consider using named argument `{}: <value>` or labeled argument `<value> {}`",
                                param.name, label
                            ),
                            None => format!("consider using named argument: `{}: <value>`", param.name),
                        })
                    };

                    checker.emit_with_fix(
                        LintName::UnnamedDuplicateTypedArgs,
                        arg.span, // Use the argument's span for proper location reporting
                        format!(
                            "positional argument for parameter `{}` which shares type `{}` with `{}`{}",
                            param.name,
                            type_str,
                            peers.join("`, `"),
                            label_hint
                        ),
                        suggestion,
                        easy_fix,
                    );
                }
            }
        }

        // Recursively check expressions
        fn check_expr(checker: &mut LintChecker, expr: &Expr, source_file: Option<&str>, source_text: Option<&str>) {
            match expr {
                Expr::Call { callee, args } => {
                    if let Some(name) = get_callee_name(callee) {
                        check_call(checker, &name, args, source_file, source_text);
                    }
                    check_expr(checker, callee, source_file, source_text);
                    for arg in args {
                        check_expr(checker, &arg.value, source_file, source_text);
                    }
                }
                Expr::MethodCall {
                    receiver, method, args, ..
                } => {
                    // Try to look up method
                    check_call(checker, method, args, None, None);
                    check_expr(checker, receiver, source_file, source_text);
                    for arg in args {
                        check_expr(checker, &arg.value, source_file, source_text);
                    }
                }
                Expr::Binary { left, right, .. } => {
                    check_expr(checker, left, source_file, source_text);
                    check_expr(checker, right, source_file, source_text);
                }
                Expr::Unary { operand, .. } => {
                    check_expr(checker, operand, source_file, source_text);
                }
                Expr::FieldAccess { receiver, .. } => {
                    check_expr(checker, receiver, source_file, source_text);
                }
                Expr::Index { receiver, index } => {
                    check_expr(checker, receiver, source_file, source_text);
                    check_expr(checker, index, source_file, source_text);
                }
                Expr::Lambda { body, .. } => {
                    check_expr(checker, body, source_file, source_text);
                }
                Expr::Array(elements) => {
                    for elem in elements {
                        check_expr(checker, elem, source_file, source_text);
                    }
                }
                Expr::Tuple(elements) => {
                    for elem in elements {
                        check_expr(checker, elem, source_file, source_text);
                    }
                }
                Expr::DoBlock(stmts) => {
                    for stmt in stmts {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                }
                Expr::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    check_expr(checker, condition, source_file, source_text);
                    check_expr(checker, then_branch, source_file, source_text);
                    if let Some(eb) = else_branch {
                        check_expr(checker, eb, source_file, source_text);
                    }
                }
                _ => {}
            }
        }

        // Recursively check statements
        fn check_stmt(checker: &mut LintChecker, node: &Node, source_file: Option<&str>, source_text: Option<&str>) {
            use simple_parser::ast::{LetStmt, ReturnStmt};

            match node {
                Node::Expression(expr) => check_expr(checker, expr, source_file, source_text),
                Node::Let(LetStmt { value: Some(v), .. }) => {
                    check_expr(checker, v, source_file, source_text);
                }
                Node::Assignment(assign) => {
                    check_expr(checker, &assign.value, source_file, source_text);
                }
                Node::Return(ReturnStmt { value: Some(v), .. }) => {
                    check_expr(checker, v, source_file, source_text);
                }
                Node::If(if_stmt) => {
                    check_expr(checker, &if_stmt.condition, source_file, source_text);
                    for stmt in &if_stmt.then_block.statements {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                    for (_elif_pattern, elif_cond, elif_block) in &if_stmt.elif_branches {
                        check_expr(checker, elif_cond, source_file, source_text);
                        for stmt in &elif_block.statements {
                            check_stmt(checker, stmt, source_file, source_text);
                        }
                    }
                    if let Some(else_block) = &if_stmt.else_block {
                        for stmt in &else_block.statements {
                            check_stmt(checker, stmt, source_file, source_text);
                        }
                    }
                }
                Node::Match(match_stmt) => {
                    check_expr(checker, &match_stmt.subject, source_file, source_text);
                    for arm in &match_stmt.arms {
                        for stmt in &arm.body.statements {
                            check_stmt(checker, stmt, source_file, source_text);
                        }
                    }
                }
                Node::For(for_stmt) => {
                    check_expr(checker, &for_stmt.iterable, source_file, source_text);
                    for stmt in &for_stmt.body.statements {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                }
                Node::While(while_stmt) => {
                    check_expr(checker, &while_stmt.condition, source_file, source_text);
                    for stmt in &while_stmt.body.statements {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                }
                Node::Loop(loop_stmt) => {
                    for stmt in &loop_stmt.body.statements {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                }
                Node::Function(func) => {
                    for stmt in &func.body.statements {
                        check_stmt(checker, stmt, source_file, source_text);
                    }
                }
                _ => {}
            }
        }

        let source_text = self
            .source_file
            .as_ref()
            .and_then(|path| std::fs::read_to_string(path).ok());
        let source_file = self.source_file.as_ref().map(|path| path.display().to_string());

        for item in items {
            check_stmt(self, item, source_file.as_deref(), source_text.as_deref());
        }
    }
}
