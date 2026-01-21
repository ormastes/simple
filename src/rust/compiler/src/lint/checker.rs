//! Lint checker implementation for AST traversal.

use super::config::LintConfig;
use super::diagnostics::LintDiagnostic;
use super::rules::{is_bare_bool, is_primitive_type};
use super::types::{LintLevel, LintName};
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Node, StructDef, TraitDef, Type};
use simple_parser::token::Span;

/// Lint checker for a compilation unit
pub struct LintChecker {
    /// Current lint configuration
    config: LintConfig,
    /// Collected diagnostics
    diagnostics: Vec<LintDiagnostic>,
    /// Source file path (for file-based lints)
    source_file: Option<std::path::PathBuf>,
}

impl LintChecker {
    pub fn new() -> Self {
        Self {
            config: LintConfig::new(),
            diagnostics: Vec::new(),
            source_file: None,
        }
    }

    pub fn with_config(config: LintConfig) -> Self {
        Self {
            config,
            diagnostics: Vec::new(),
            source_file: None,
        }
    }

    pub fn with_source_file(mut self, source_file: Option<std::path::PathBuf>) -> Self {
        self.source_file = source_file;
        self
    }

    /// Get collected diagnostics
    pub fn diagnostics(&self) -> &[LintDiagnostic] {
        &self.diagnostics
    }

    /// Take collected diagnostics
    pub fn take_diagnostics(&mut self) -> Vec<LintDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Export diagnostics as JSON (#903)
    pub fn to_json(&self, file: Option<String>) -> Result<String, serde_json::Error> {
        use simple_common::diagnostic::Diagnostics;

        let mut diags = Diagnostics::new();
        for lint_diag in &self.diagnostics {
            diags.push(lint_diag.to_diagnostic(file.clone()));
        }
        diags.to_json()
    }

    /// Export diagnostics as compact JSON (#903)
    pub fn to_json_compact(&self, file: Option<String>) -> Result<String, serde_json::Error> {
        use simple_common::diagnostic::Diagnostics;

        let mut diags = Diagnostics::new();
        for lint_diag in &self.diagnostics {
            diags.push(lint_diag.to_diagnostic(file.clone()));
        }
        diags.to_json_compact()
    }

    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_error())
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_warning())
    }

    /// Emit a lint diagnostic if not allowed
    fn emit(&mut self, lint: LintName, span: Span, message: String, suggestion: Option<String>) {
        let level = self.config.get_level(lint);
        if level == LintLevel::Allow {
            return;
        }

        let mut diagnostic = LintDiagnostic::new(lint, level, span, message);
        if let Some(s) = suggestion {
            diagnostic = diagnostic.with_suggestion(s);
        }
        self.diagnostics.push(diagnostic);
    }

    /// Check a module for lint violations
    pub fn check_module(&mut self, items: &[Node]) {
        // Run file-based lints first
        if let Some(source_file) = self.source_file.clone() {
            // Check for print in test spec files
            if source_file.to_string_lossy().ends_with("_spec.spl") {
                self.check_print_in_test_spec(items);
                // SSpec-specific lints
                self.check_sspec_print_based_tests(items);
                self.check_sspec_minimal_docstrings(&source_file);
                self.check_sspec_manual_assertions(items);
            }

            // Check TODO format
            self.check_todo_format(&source_file);
        }

        // Run AST-based lints
        for item in items {
            self.check_node(item);
        }
    }

    /// Check a single AST node
    fn check_node(&mut self, node: &Node) {
        match node {
            Node::Function(func) => self.check_function(func),
            Node::Struct(s) => self.check_struct(s),
            Node::Class(c) => self.check_class(c),
            Node::Enum(e) => self.check_enum(e),
            Node::Trait(t) => self.check_trait(t),
            _ => {}
        }
    }

    /// Check a function definition
    fn check_function(&mut self, func: &FunctionDef) {
        // Only check public functions
        if !func.visibility.is_public() {
            return;
        }

        // Create scoped config with function attributes
        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&func.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check parameters
        for param in &func.params {
            if let Some(ref ty) = param.ty {
                self.check_type_in_public_api(ty, param.span, &param.name, "parameter");
            }
        }

        // Check return type
        if let Some(ref ret_ty) = func.return_type {
            self.check_type_in_public_api(ret_ty, func.span, &func.name, "return type");
        }

        // Restore original config
        self.config = original_config;
    }

    /// Check a struct definition
    fn check_struct(&mut self, s: &StructDef) {
        if !s.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&s.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check public fields
        for field in &s.fields {
            if field.visibility.is_public() {
                self.check_type_in_public_api(&field.ty, field.span, &field.name, "field");
            }
        }

        // Check public methods
        for method in &s.methods {
            if method.visibility.is_public() {
                self.check_function(method);
            }
        }

        self.config = original_config;
    }

    /// Check a class definition
    fn check_class(&mut self, c: &ClassDef) {
        if !c.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&c.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check public fields
        for field in &c.fields {
            if field.visibility.is_public() {
                self.check_type_in_public_api(&field.ty, field.span, &field.name, "field");
            }
        }

        // Check public methods
        for method in &c.methods {
            if method.visibility.is_public() {
                self.check_function(method);
            }
        }

        self.config = original_config;
    }

    /// Check an enum definition
    fn check_enum(&mut self, e: &EnumDef) {
        if !e.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&e.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check variant fields
        for variant in &e.variants {
            if let Some(ref fields) = variant.fields {
                for (i, field) in fields.iter().enumerate() {
                    let field_desc = match &field.name {
                        Some(name) => format!("{}::{}.{}", e.name, variant.name, name),
                        None => format!("{}::{}.{}", e.name, variant.name, i),
                    };
                    self.check_type_in_public_api(&field.ty, variant.span, &field_desc, "variant field");
                }
            }
        }

        self.config = original_config;
    }

    /// Check a trait definition
    fn check_trait(&mut self, t: &TraitDef) {
        if !t.visibility.is_public() {
            return;
        }

        // TraitDef doesn't have attributes field, so use current config
        // Check method signatures
        for method in &t.methods {
            // Trait methods are implicitly public
            for param in &method.params {
                if let Some(ref ty) = param.ty {
                    self.check_type_in_public_api(ty, param.span, &param.name, "parameter");
                }
            }
            if let Some(ref ret_ty) = method.return_type {
                self.check_type_in_public_api(ret_ty, method.span, &method.name, "return type");
            }
        }
    }

    /// Check a type used in a public API
    fn check_type_in_public_api(&mut self, ty: &Type, span: Span, name: &str, context: &str) {
        // Check for bare bool (more specific lint)
        if is_bare_bool(ty) {
            self.emit(
                LintName::BareBool,
                span,
                format!("bare `bool` in public API {} `{}`", context, name),
                Some("consider using an enum with descriptive variants instead".to_string()),
            );
        }

        // Check for any primitive type
        if is_primitive_type(ty) {
            let type_name = match ty {
                Type::Simple(n) => n.as_str(),
                _ => "primitive",
            };
            self.emit(
                LintName::PrimitiveApi,
                span,
                format!("bare primitive `{}` in public API {} `{}`", type_name, context, name),
                Some(format!(
                    "consider using a unit type or newtype wrapper instead of `{}`",
                    type_name
                )),
            );
        }

        // Recursively check nested types
        match ty {
            Type::Array { element, .. } => {
                self.check_type_in_public_api(element, span, name, context);
            }
            Type::Tuple(types) => {
                for t in types {
                    self.check_type_in_public_api(t, span, name, context);
                }
            }
            Type::Generic { args, .. } => {
                for arg in args {
                    self.check_type_in_public_api(arg, span, name, context);
                }
            }
            Type::Function { params, ret } => {
                for p in params {
                    self.check_type_in_public_api(p, span, name, context);
                }
                if let Some(r) = ret {
                    self.check_type_in_public_api(r, span, name, context);
                }
            }
            Type::Optional(inner) => {
                self.check_type_in_public_api(inner, span, name, context);
            }
            Type::Union(types) => {
                for t in types {
                    self.check_type_in_public_api(t, span, name, context);
                }
            }
            Type::Pointer { inner, .. } => {
                self.check_type_in_public_api(inner, span, name, context);
            }
            Type::Simd { element, .. } => {
                self.check_type_in_public_api(element, span, name, context);
            }
            _ => {}
        }
    }

    /// Check for print() calls in test spec files
    fn check_print_in_test_spec(&mut self, items: &[Node]) {
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
                Node::Let(LetStmt { value, .. }) => {
                    if let Some(ref v) = value {
                        check_expr(checker, v);
                    }
                }
                Node::Assignment(assign) => {
                    check_expr(checker, &assign.value);
                }
                Node::Return(ReturnStmt { value, .. }) => {
                    if let Some(ref v) = value {
                        check_expr(checker, v);
                    }
                }
                Node::If(if_stmt) => {
                    check_expr(checker, &if_stmt.condition);
                    for stmt in &if_stmt.then_block.statements {
                        check_stmt(checker, stmt);
                    }
                    for (elif_cond, elif_block) in &if_stmt.elif_branches {
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

    /// Check TODO/FIXME comment format
    fn check_todo_format(&mut self, source_file: &std::path::Path) {
        // Read the source file
        let source = match std::fs::read_to_string(source_file) {
            Ok(s) => s,
            Err(_) => return, // Can't read file, skip this lint
        };

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
                // Doesn't match format
                self.emit(
                    LintName::TodoFormat,
                    Span::new(todo_start, todo_end, line_num, todo_col),
                    "TODO/FIXME missing [area][priority] format".to_string(),
                    Some(
                        "use format: TODO: [area][P0-P3] description (e.g., TODO: [runtime][P1] implement feature)"
                            .to_string(),
                    ),
                );
            }

            byte_offset += line.len() + 1;
        }
    }

    /// Check for print-based BDD tests (sspec_no_print_based_tests)
    fn check_sspec_print_based_tests(&mut self, items: &[Node]) {
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
                Node::Let(LetStmt { value, .. }) => {
                    if let Some(v) = value {
                        check_expr(checker, v);
                    }
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
    fn check_sspec_minimal_docstrings(&mut self, source_file: &std::path::Path) {
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
    fn check_sspec_manual_assertions(&mut self, items: &[Node]) {
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
}

impl Default for LintChecker {
    fn default() -> Self {
        Self::new()
    }
}
