//! Lint checker: SSpec, TODO format, source quality, and stub pattern checks.

use super::super::types::LintName;
use simple_common::diagnostic::{EasyFix, FixConfidence, Replacement};
use simple_parser::ast::{ClassDef, Expr, FunctionDef, Node, StructDef};
use simple_parser::token::Span;

use super::LintChecker;

impl LintChecker {
    /// Check for print() calls in test spec files
    pub(super) fn check_print_in_test_spec(&mut self, items: &[Node]) {
        use simple_parser::ast::Expr;

        // Helper to check expressions for print calls
        fn check_expr(checker: &mut LintChecker, expr: &Expr) {
            match expr {
                Expr::Call { callee, .. } => {
                    // Check if callee is "print"
                    if let Expr::Identifier(name) = &**callee {
                        if name == "print" {
                            // Note: Expr doesn't track source spans - would need AST refactor to support
                            checker.emit(
                                LintName::PrintInTestSpec,
                                Span::new(0, 0, 0, 0),
                                "print() call in test spec file".to_string(),
                                Some("use triple-quoted strings \"\"\" for test output, or add #[allow(print_in_test_spec)] if print is needed".to_string()),
                            );
                        }
                    }
                    // Recursively check callee and arguments
                    check_expr(checker, callee);
                }
                Expr::Binary { left, right, .. } => {
                    check_expr(checker, left);
                    check_expr(checker, right);
                }
                Expr::Unary { operand, .. } => {
                    check_expr(checker, operand);
                }
                Expr::MethodCall { receiver, args, .. } => {
                    check_expr(checker, receiver);
                    for arg in args {
                        check_expr(checker, &arg.value);
                    }
                }
                Expr::FieldAccess { receiver, .. } => {
                    check_expr(checker, receiver);
                }
                Expr::Index { receiver, index } => {
                    check_expr(checker, receiver);
                    check_expr(checker, index);
                }
                Expr::TupleIndex { receiver, .. } => {
                    check_expr(checker, receiver);
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
                Expr::DoBlock(statements) => {
                    for stmt in statements {
                        check_stmt(checker, stmt);
                    }
                }
                _ => {}
            }
        }

        // Helper to check statements
        fn check_stmt(checker: &mut LintChecker, node: &Node) {
            use simple_parser::ast::{IfStmt, LetStmt, MatchStmt, ReturnStmt};

            match node {
                Node::Expression(expr) => check_expr(checker, expr),
                Node::Let(LetStmt { value: Some(ref v), .. }) => {
                    check_expr(checker, v);
                }
                Node::Assignment(assign) => {
                    check_expr(checker, &assign.value);
                }
                Node::Return(ReturnStmt { value: Some(ref v), .. }) => {
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
                    if let Some(ref else_block) = if_stmt.else_block {
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

        // Check all top-level items
        for item in items {
            check_stmt(self, item);
        }
    }

    /// Check if file has #![skip_todo] at the top
    pub(super) fn has_file_level_skip_todo_format(content: &str) -> bool {
        // Check first 20 lines for skip markers
        for line in content.lines().take(20) {
            let trimmed = line.trim();
            // Primary pattern: #![skip_todo]
            if trimmed.contains("#![skip_todo]") {
                return true;
            }
            // Also support: #![allow(todo_format)] for lint consistency
            if trimmed.contains("#![allow(todo_format)]") {
                return true;
            }
            // Comment-based alternatives
            // Rust: // skip_todo
            // Simple: # skip_todo
            if trimmed.contains("skip_todo") && (trimmed.starts_with("//") || trimmed.starts_with('#')) {
                return true;
            }
        }
        false
    }

    /// Check TODO/FIXME comment format
    pub(super) fn check_todo_format(&mut self, source_file: &std::path::Path) {
        // Read the source file
        let source = match std::fs::read_to_string(source_file) {
            Ok(s) => s,
            Err(_) => return, // Can't read file, skip this lint
        };

        // Check for file-level skip attribute
        if Self::has_file_level_skip_todo_format(&source) {
            return;
        }

        // Valid areas and priorities (from .claude/skills/todo.md)
        const TODO_AREAS: &[&str] = &[
            "runtime", "codegen", "compiler", "parser", "type", "stdlib", "gpu", "ui", "test", "driver", "loader",
            "pkg", "doc",
        ];
        const TODO_PRIORITIES: &[&str] = &["P0", "P1", "P2", "P3", "critical", "high", "medium", "low"];

        // Regex pattern for TODO format: TODO: [area][priority] description
        let todo_pattern = regex::Regex::new(r"(TODO|FIXME):\s*\[([^\]]+)\]\[([^\]]+)\]\s*(.+)").unwrap();

        // Check each line, tracking byte offset for accurate spans
        let mut byte_offset = 0usize;
        for (line_num, line) in source.lines().enumerate() {
            let line_num = line_num + 1; // 1-indexed
            let line_start = byte_offset;

            // Skip if not a comment
            let trimmed = line.trim();
            if !trimmed.starts_with('#') {
                byte_offset += line.len() + 1; // +1 for newline
                continue;
            }

            // Check if contains TODO or FIXME
            if !trimmed.contains("TODO") && !trimmed.contains("FIXME") {
                byte_offset += line.len() + 1;
                continue;
            }

            // Skip if TODO/FIXME is inside a string literal (quoted)
            // Count quotes before the TODO - if odd, we're inside a string
            if let Some(todo_pos) = trimmed.find("TODO").or_else(|| trimmed.find("FIXME")) {
                let before_todo = &trimmed[..todo_pos];
                let double_quote_count = before_todo.matches('"').count();
                let single_quote_count = before_todo.matches('\'').count();
                if double_quote_count % 2 == 1 || single_quote_count % 2 == 1 {
                    byte_offset += line.len() + 1;
                    continue;
                }
            }

            // Find the column where TODO/FIXME starts
            let todo_col = line
                .find("TODO")
                .or_else(|| line.find("FIXME"))
                .map(|pos| pos + 1) // 1-indexed column
                .unwrap_or(1);

            // Calculate byte positions for the TODO comment
            let todo_start = line_start + todo_col.saturating_sub(1);
            let todo_end = line_start + line.len();

            // Extract the comment content (after #)
            let comment = trimmed.trim_start_matches('#').trim();

            // Check if it starts with TODO: or FIXME:
            if !comment.starts_with("TODO:") && !comment.starts_with("FIXME:") {
                byte_offset += line.len() + 1;
                continue; // Not a standard TODO comment
            }

            // Try to match the required format
            if let Some(captures) = todo_pattern.captures(comment) {
                let area = captures.get(2).map(|m| m.as_str()).unwrap_or("");
                let priority = captures.get(3).map(|m| m.as_str()).unwrap_or("");

                // Validate area
                if !TODO_AREAS.contains(&area) {
                    self.emit(
                        LintName::TodoFormat,
                        Span::new(todo_start, todo_end, line_num, todo_col),
                        format!("TODO/FIXME has invalid area '{}'", area),
                        Some(format!("valid areas: {}", TODO_AREAS.join(", "))),
                    );
                }

                // Validate priority
                if !TODO_PRIORITIES.contains(&priority) {
                    self.emit(
                        LintName::TodoFormat,
                        Span::new(todo_start, todo_end, line_num, todo_col),
                        format!("TODO/FIXME has invalid priority '{}'", priority),
                        Some(format!("valid priorities: {}", TODO_PRIORITIES.join(", "))),
                    );
                }
            } else {
                // Doesn't match format — build an EasyFix that inserts [runtime][P2] placeholder
                let file_path = source_file.display().to_string();
                let keyword_end_pos = if comment.starts_with("TODO:") {
                    // Find the position right after "TODO: " in the line
                    line.find("TODO:").map(|p| line_start + p + 5)
                } else {
                    line.find("FIXME:").map(|p| line_start + p + 6)
                };
                let easy_fix = keyword_end_pos.map(|pos| {
                    // Insert after the colon+space: "TODO: " -> "TODO: [runtime][P2] "
                    let insert_pos = if source.as_bytes().get(pos) == Some(&b' ') {
                        pos + 1
                    } else {
                        pos
                    };
                    EasyFix {
                        id: format!("L:todo_format:{}", line_num),
                        description: "add [area][priority] format to TODO comment".to_string(),
                        replacements: vec![Replacement {
                            file: file_path.clone(),
                            span: simple_common::diagnostic::Span::new(
                                insert_pos,
                                insert_pos,
                                line_num,
                                insert_pos - line_start + 1,
                            ),
                            new_text: "[runtime][P2] ".to_string(),
                        }],
                        confidence: FixConfidence::Uncertain,
                    }
                });

                self.emit_with_fix(
                    LintName::TodoFormat,
                    Span::new(todo_start, todo_end, line_num, todo_col),
                    "TODO/FIXME missing [area][priority] format".to_string(),
                    Some(
                        "use format: TODO: [area][P0-P3] description (e.g., TODO: [runtime][P1] implement feature)"
                            .to_string(),
                    ),
                    easy_fix,
                );
            }

            byte_offset += line.len() + 1;
        }
    }

    /// Check for print-based BDD tests (sspec_no_print_based_tests)
    pub(super) fn check_sspec_print_based_tests(&mut self, items: &[Node]) {
        use simple_parser::ast::Expr;

        const BDD_KEYWORDS: &[&str] = &["describe", "context", "it ", "[PASS]", "[FAIL]"];

        fn check_expr(checker: &mut LintChecker, expr: &Expr) {
            match expr {
                Expr::Call { callee, args, .. } => {
                    if let Expr::Identifier(name) = &**callee {
                        if name == "print" {
                            for arg in args {
                                if let Expr::String(s) = &arg.value {
                                    for keyword in BDD_KEYWORDS {
                                        if s.contains(keyword) {
                                            checker.emit(
                                                LintName::SSpecNoPrintBasedTests,
                                                Span::new(0, 0, 0, 0),
                                                format!("print-based BDD test detected: contains '{}'", keyword.trim()),
                                                Some("use proper SSpec syntax: describe/context/it blocks".to_string()),
                                            );
                                            return;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    check_expr(checker, callee);
                    for arg in args {
                        check_expr(checker, &arg.value);
                    }
                }
                Expr::Binary { left, right, .. } => {
                    check_expr(checker, left);
                    check_expr(checker, right);
                }
                Expr::DoBlock(stmts) => {
                    for stmt in stmts {
                        check_stmt(checker, stmt);
                    }
                }
                _ => {}
            }
        }

        fn check_stmt(checker: &mut LintChecker, node: &Node) {
            use simple_parser::ast::LetStmt;
            match node {
                Node::Expression(expr) => check_expr(checker, expr),
                Node::Let(LetStmt { value: Some(v), .. }) => {
                    check_expr(checker, v);
                }
                Node::If(if_stmt) => {
                    for stmt in &if_stmt.then_block.statements {
                        check_stmt(checker, stmt);
                    }
                    if let Some(else_block) = &if_stmt.else_block {
                        for stmt in &else_block.statements {
                            check_stmt(checker, stmt);
                        }
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

    /// Check for minimal docstring usage in SSpec files
    pub(super) fn check_sspec_minimal_docstrings(&mut self, source_file: &std::path::Path) {
        let source = match std::fs::read_to_string(source_file) {
            Ok(s) => s,
            Err(_) => return,
        };

        let docstring_count = source.matches("\"\"\"").count() / 2;
        const MIN_DOCSTRINGS: usize = 2;

        if docstring_count < MIN_DOCSTRINGS {
            self.emit(
                LintName::SSpecMinimalDocstrings,
                Span::new(0, 0, 1, 1),
                format!(
                    "file has only {} docstring(s) (minimum: {})",
                    docstring_count, MIN_DOCSTRINGS
                ),
                Some("add docstrings to describe/context/it blocks".to_string()),
            );
        }
    }

    /// Check for manual assertion tracking patterns
    pub(super) fn check_sspec_manual_assertions(&mut self, items: &[Node]) {
        use simple_parser::ast::{BinOp, Expr, LetStmt, Pattern};

        fn get_pattern_name(pattern: &Pattern) -> Option<&str> {
            match pattern {
                Pattern::Identifier(name) => Some(name),
                Pattern::MutIdentifier(name) => Some(name),
                Pattern::MoveIdentifier(name) => Some(name),
                _ => None,
            }
        }

        fn check_node(checker: &mut LintChecker, node: &Node) {
            match node {
                Node::Let(LetStmt { pattern, value, .. }) => {
                    if let Some(name) = get_pattern_name(pattern) {
                        if name == "passed" || name == "failed" {
                            if let Some(Expr::Integer(0)) = value {
                                checker.emit(
                                    LintName::SSpecManualAssertions,
                                    Span::new(0, 0, 0, 0),
                                    format!("manual assertion tracking: '{}' counter", name),
                                    Some("use expect() assertions instead".to_string()),
                                );
                            }
                        }
                    }
                }
                Node::Assignment(assign) => {
                    if let Expr::Identifier(name) = &assign.target {
                        if name == "passed" || name == "failed" {
                            if let Expr::Binary { op, .. } = &assign.value {
                                if matches!(op, BinOp::Add) {
                                    checker.emit(
                                        LintName::SSpecManualAssertions,
                                        Span::new(0, 0, 0, 0),
                                        format!("manual assertion tracking: incrementing '{}'", name),
                                        Some("use expect() assertions instead".to_string()),
                                    );
                                }
                            }
                        }
                    }
                }
                Node::If(if_stmt) => {
                    for stmt in &if_stmt.then_block.statements {
                        check_node(checker, stmt);
                    }
                    if let Some(else_block) = &if_stmt.else_block {
                        for stmt in &else_block.statements {
                            check_node(checker, stmt);
                        }
                    }
                }
                Node::Function(func) => {
                    for stmt in &func.body.statements {
                        check_node(checker, stmt);
                    }
                }
                _ => {}
            }
        }

        for item in items {
            check_node(self, item);
        }
    }

    pub(super) fn check_source_backed_quality_patterns(&mut self, source_file: &std::path::Path) {
        let source = match std::fs::read_to_string(source_file) {
            Ok(s) => s,
            Err(_) => return,
        };

        if Self::is_test_like_path(source_file) {
            self.check_sspec_placeholder_patterns(&source);
            self.check_sspec_example_bodies_from_source(&source);
        } else {
            self.check_stub_placeholder_bodies(&source);
        }
        self.check_required_comment_patterns(&source);
    }

    pub(super) fn is_test_like_path(source_file: &std::path::Path) -> bool {
        let path = source_file.to_string_lossy();
        path.ends_with("_spec.spl") || path.ends_with("_test.spl") || path.contains("/test/")
    }

    pub(super) fn normalize_quality_line(line: &str) -> String {
        line.replace([' ', '\t'], "")
    }

    pub(super) fn extract_expect_subject(normalized: &str) -> Option<&str> {
        let start = normalized.find("expect(")?;
        let tail = &normalized[start + 7..];
        if let Some(end) = tail.find(").to_equal(") {
            return Some(&tail[..end]);
        }
        if let Some(end) = tail.find(").to_be(") {
            return Some(&tail[..end]);
        }
        None
    }

    pub(super) fn is_boolean_wrapper_assertion(normalized: &str) -> bool {
        let compares_to_bool = normalized.contains(").to_equal(true)")
            || normalized.contains(").to_equal(false)")
            || normalized.contains(").to_be(true)")
            || normalized.contains(").to_be(false)");
        if !compares_to_bool {
            return false;
        }

        let subject = match Self::extract_expect_subject(normalized) {
            Some(subject) if !subject.is_empty() && subject != "true" && subject != "false" => subject,
            _ => return false,
        };

        subject.contains("==")
            || subject.contains("!=")
            || subject.contains(">=")
            || subject.contains("<=")
            || subject.contains('>')
            || subject.contains('<')
    }

    fn indent_width(line: &str) -> usize {
        let mut width = 0usize;
        for ch in line.chars() {
            if ch == ' ' {
                width += 1;
                continue;
            }
            if ch == '\t' {
                width += 4;
                continue;
            }
            break;
        }
        width
    }

    pub(super) fn is_assertion_like(normalized: &str) -> bool {
        normalized.contains("expect(")
            || normalized.contains("to_equal(")
            || normalized.contains("to_be(")
            || normalized.contains("to_contain(")
            || normalized.contains("to_start_with(")
            || normalized.contains("to_end_with(")
            || normalized.contains("to_be_greater_than(")
            || normalized.contains("to_be_less_than(")
    }

    pub(super) fn is_sanctioned_skip(normalized: &str) -> bool {
        normalized == "skip:"
            || normalized.starts_with("skip:")
            || normalized.contains("return\"skip:")
            || normalized.contains("return'skip:")
    }

    pub(super) fn is_placeholder_stmt(normalized: &str) -> bool {
        normalized == "pass_todo"
            || normalized == "pass_do_nothing"
            || normalized == "pass_dn"
            || normalized.starts_with("pass_todo(")
            || normalized.starts_with("pass_do_nothing(")
            || normalized.starts_with("pass_dn(")
    }

    fn required_comment_is_weak(value: &str) -> bool {
        let text = value.trim().to_lowercase();
        text.is_empty()
            || text.len() < 10
            || matches!(
                text.as_str(),
                "todo" | "fix" | "later" | "unknown" | "because" | "n/a" | "na"
            )
    }

    fn nth_string_arg(line: &str, ordinal: usize) -> Option<String> {
        let mut strings = Vec::new();
        let mut in_string = false;
        let mut escaped = false;
        let mut current = String::new();
        for ch in line.chars() {
            if in_string {
                if escaped {
                    current.push(ch);
                    escaped = false;
                } else if ch == '\\' {
                    escaped = true;
                } else if ch == '"' {
                    strings.push(current.clone());
                    current.clear();
                    in_string = false;
                } else {
                    current.push(ch);
                }
            } else if ch == '"' {
                in_string = true;
            }
        }
        strings.get(ordinal).cloned()
    }

    pub(super) fn check_required_comment_patterns(&mut self, source: &str) {
        for (idx, line) in source.lines().enumerate() {
            let line_num = idx + 1;
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            let normalized = Self::normalize_quality_line(trimmed);
            if normalized == "pass_todo" || normalized == "pass_do_nothing" || normalized == "pass_dn" {
                self.emit(
                    LintName::RequiredCommentPass,
                    Span::new(0, 0, line_num, 1),
                    "REQC001: pass_* used without a rationale".to_string(),
                    Some("use pass_todo(\"what remains\", \"hint or issue\") or pass_do_nothing(\"why no-op is correct\")".to_string()),
                );
            }
            if normalized.starts_with("pass_todo(")
                || normalized.starts_with("pass_do_nothing(")
                || normalized.starts_with("pass_dn(")
            {
                let reason = Self::nth_string_arg(trimmed, 0).unwrap_or_default();
                if Self::required_comment_is_weak(&reason) {
                    self.emit(
                        LintName::RequiredCommentPass,
                        Span::new(0, 0, line_num, 1),
                        "REQC001: pass_* used without a useful rationale".to_string(),
                        Some("use pass_todo(\"what remains\", \"hint or issue\") or pass_do_nothing(\"why no-op is correct\")".to_string()),
                    );
                }
            }
            if normalized.starts_with("todo(") || normalized.contains(":todo(") || normalized.contains("=todo(") {
                let what = Self::nth_string_arg(trimmed, 0).unwrap_or_default();
                let hint = Self::nth_string_arg(trimmed, 1).unwrap_or_default();
                if Self::required_comment_is_weak(&what) || Self::required_comment_is_weak(&hint) {
                    self.emit(
                        LintName::RequiredCommentTodo,
                        Span::new(0, 0, line_num, 1),
                        "REQC003: todo used without what-remains and next-step strings".to_string(),
                        Some("use todo(\"what remains\", \"hint or issue\")".to_string()),
                    );
                }
            }
            let dangerous_call = normalized.starts_with("dangerous_token_but_needs(")
                || normalized.starts_with("loss(")
                || normalized.starts_with("unsafe_cast(")
                || normalized.starts_with("raw_pointer(")
                || normalized.starts_with("unchecked(");
            if dangerous_call {
                let reason = Self::nth_string_arg(trimmed, 0).unwrap_or_default();
                if Self::required_comment_is_weak(&reason) {
                    self.emit(
                        LintName::RequiredCommentDangerous,
                        Span::new(0, 0, line_num, 1),
                        "REQC002: dangerous keyword used without a useful rationale".to_string(),
                        Some("add a first string argument explaining why the escape hatch is correct".to_string()),
                    );
                }
            }
            if normalized.starts_with("case_:")
                || normalized.starts_with("case_->")
                || normalized.starts_with("case_=>")
                || normalized == "_=>"
                || normalized == "_->"
            {
                self.emit(
                    LintName::RequiredCommentWildcard,
                    Span::new(0, 0, line_num, 1),
                    "REQC004: wildcard match arm used without a rationale".to_string(),
                    Some("use case _(\"why catch-all is correct\"):".to_string()),
                );
            }
            if normalized.starts_with("case_(\"") {
                let reason = Self::nth_string_arg(trimmed, 0).unwrap_or_default();
                if Self::required_comment_is_weak(&reason) {
                    self.emit(
                        LintName::RequiredCommentWildcard,
                        Span::new(0, 0, line_num, 1),
                        "REQC004: wildcard match arm used without a useful rationale".to_string(),
                        Some("use case _(\"why catch-all is correct\"):".to_string()),
                    );
                }
            }
        }
    }

    pub(super) fn check_sspec_placeholder_patterns(&mut self, source: &str) {
        for (idx, line) in source.lines().enumerate() {
            let line_num = idx + 1;
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            let normalized = Self::normalize_quality_line(trimmed);
            let has_literal_tautology = normalized.contains("expect(true).to_equal(true)")
                || normalized.contains("expect(false).to_equal(false)")
                || normalized.contains("expect(true).to_be(true)")
                || normalized.contains("expect(false).to_be(false)");
            if has_literal_tautology {
                self.emit(
                    LintName::SSpecPlaceholderTests,
                    Span::new(0, 0, line_num, 1),
                    "tautological assertion in spec/example".to_string(),
                    Some("assert returned data, state, or capability outcome instead of a literal boolean".to_string()),
                );
            }

            let has_pass_helper = normalized == "pass_todo"
                || normalized == "pass_do_nothing"
                || normalized == "pass_dn"
                || normalized.contains(":pass_todo")
                || normalized.contains(":pass_do_nothing")
                || normalized.contains(":pass_dn");
            if has_pass_helper {
                self.emit(
                    LintName::SSpecPlaceholderTests,
                    Span::new(0, 0, line_num, 1),
                    "placeholder pass helper in spec/example".to_string(),
                    Some("use skip: for unsupported environments, or assert a real result".to_string()),
                );
            }

            let is_match_arm = trimmed.starts_with("Ok(")
                || trimmed.starts_with("Err(")
                || trimmed.starts_with("case Ok(")
                || trimmed.starts_with("case Err(");
            if is_match_arm && (has_literal_tautology || has_pass_helper) {
                self.emit(
                    LintName::SSpecPlaceholderTests,
                    Span::new(0, 0, line_num, 1),
                    "placeholder success/failure arm in match-based spec assertion".to_string(),
                    Some("assert concrete fields from Ok/Err, or use skip: before the match".to_string()),
                );
            }

            let has_print_skip = normalized.contains("print(\"[skip]")
                || normalized.contains("print\"[skip]")
                || normalized.contains("print'[skip]")
                || normalized.contains("print(\"skip:")
                || normalized.contains("print\"skip:");
            if has_print_skip {
                self.emit(
                    LintName::SSpecNoPrintBasedTests,
                    Span::new(0, 0, line_num, 1),
                    "print-based skip placeholder in spec/example".to_string(),
                    Some("use skip: for sanctioned environment skips instead of print-and-return".to_string()),
                );
            }

            if Self::is_boolean_wrapper_assertion(&normalized) {
                self.emit(
                    LintName::SSpecBooleanWrapperAssertions,
                    Span::new(0, 0, line_num, 1),
                    "boolean-wrapper assertion in spec/example".to_string(),
                    Some("assert the underlying value or capability result directly".to_string()),
                );
            }
        }
    }

    pub(super) fn check_sspec_example_bodies_from_source(&mut self, source: &str) {
        let lines: Vec<&str> = source.lines().collect();
        let mut i = 0usize;
        while i < lines.len() {
            let line = lines[i];
            let trimmed = line.trim();
            if !(trimmed.starts_with("it \"") || trimmed.starts_with("slow_it \"")) {
                i += 1;
                continue;
            }

            let header_indent = Self::indent_width(line);
            let mut j = i + 1;
            let mut body: Vec<&str> = Vec::new();
            while j < lines.len() {
                let body_line = lines[j];
                let body_trimmed = body_line.trim();
                if !body_trimmed.is_empty()
                    && !body_trimmed.starts_with('#')
                    && Self::indent_width(body_line) <= header_indent
                {
                    break;
                }
                body.push(body_line);
                j += 1;
            }

            let statements: Vec<&str> = body
                .iter()
                .copied()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .collect();

            let line_num = i + 1;
            if statements.is_empty() {
                self.emit(
                    LintName::SSpecEmptyExamples,
                    Span::new(0, 0, line_num, 1),
                    "SSpec example has no body".to_string(),
                    Some("add a real assertion or use skip: for a sanctioned skip".to_string()),
                );
                i = j;
                continue;
            }

            let has_real_assertion = statements
                .iter()
                .any(|stmt| Self::is_assertion_like(&Self::normalize_quality_line(stmt)));
            let has_sanctioned_skip = statements
                .iter()
                .any(|stmt| Self::is_sanctioned_skip(&Self::normalize_quality_line(stmt)));
            if !has_real_assertion && !has_sanctioned_skip {
                self.emit(
                    LintName::SSpecEmptyExamples,
                    Span::new(0, 0, line_num, 1),
                    "SSpec example has no real assertion or sanctioned skip".to_string(),
                    Some("assert a concrete result, or use skip: when the environment legitimately cannot run the example".to_string()),
                );
            }

            i = j;
        }
    }

    pub(super) fn check_stub_placeholder_bodies(&mut self, source: &str) {
        let lines: Vec<&str> = source.lines().collect();
        let mut i = 0usize;
        while i < lines.len() {
            let line = lines[i];
            let trimmed = line.trim();
            let is_fn_header = trimmed.starts_with("fn ")
                || trimmed.starts_with("pub fn ")
                || trimmed.starts_with("me ")
                || trimmed.starts_with("pub me ");
            if !is_fn_header {
                i += 1;
                continue;
            }

            let header_indent = Self::indent_width(line);
            let mut j = i + 1;
            let mut body: Vec<&str> = Vec::new();
            while j < lines.len() {
                let body_line = lines[j];
                let body_trimmed = body_line.trim();
                if !body_trimmed.is_empty()
                    && !body_trimmed.starts_with('#')
                    && Self::indent_width(body_line) <= header_indent
                {
                    break;
                }
                body.push(body_line);
                j += 1;
            }

            let statements: Vec<String> = body
                .iter()
                .copied()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .map(Self::normalize_quality_line)
                .collect();

            if statements.len() == 1 && Self::is_placeholder_stmt(&statements[0]) {
                self.emit(
                    LintName::StubImpl,
                    Span::new(0, 0, i + 1, 1),
                    "explicit placeholder function body".to_string(),
                    Some(
                        "replace the placeholder body with a real implementation or suppress stub_impl explicitly"
                            .to_string(),
                    ),
                );
            }

            i = j;
        }
    }
}
