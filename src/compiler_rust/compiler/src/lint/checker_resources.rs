//! Lint checks for resource leaks, init-boundary violations, bypass validity,
//! too-many-arguments, and filesystem helpers used by boundary checks.
//!
//! #![skip_todo]

use super::checker_core::{format_type, LintChecker};
use super::super::types::{LintLevel, LintName};
use simple_parser::ast::{Expr, FunctionDef, Node, Type};
use simple_parser::token::Span;
use std::collections::HashMap;
use std::path::Path;

impl LintChecker {
    /// Check for potential resource leaks in functions
    ///
    /// This lint tracks Resource-typed variables and warns if they are not
    /// properly closed via close(), defer, or with statements.
    pub(super) fn check_resource_leaks(&mut self, items: &[Node]) {
        // Known Resource types
        const RESOURCE_TYPES: &[&str] = &[
            "File",
            "TcpStream",
            "TcpListener",
            "UdpSocket",
            "DatabaseConnection",
            "Connection",
        ];

        // Known Resource factory methods (pattern: Type.method)
        const RESOURCE_FACTORIES: &[(&str, &str)] = &[
            ("File", "open"),
            ("File", "open_str"),
            ("File", "open_read_sync"),
            ("TcpStream", "connect"),
            ("TcpStream", "connect_str"),
            ("TcpListener", "bind"),
            ("TcpListener", "bind_str"),
            ("UdpSocket", "bind"),
            ("UdpSocket", "bind_str"),
        ];

        // Check if a type is a Resource type
        fn is_resource_type(ty: &Type) -> bool {
            match ty {
                Type::Simple(name) => RESOURCE_TYPES.contains(&name.as_str()),
                Type::Generic { name, .. } => {
                    // Check for Option<Resource>, Result<Resource, E>, etc.
                    if name == "Option" || name == "Result" {
                        // Would need to check inner type
                        false
                    } else {
                        RESOURCE_TYPES.contains(&name.as_str())
                    }
                }
                _ => false,
            }
        }

        // Check if an expression creates a Resource
        fn creates_resource(expr: &Expr) -> Option<String> {
            match expr {
                // Type.factory() pattern
                Expr::Call { callee, .. } => {
                    if let Expr::FieldAccess { receiver, field } = &**callee {
                        if let Expr::Identifier(type_name) = &**receiver {
                            for (resource_type, factory_method) in RESOURCE_FACTORIES {
                                if type_name == *resource_type && field == *factory_method {
                                    return Some(type_name.clone());
                                }
                            }
                        }
                    }
                    None
                }
                // Await on resource factory
                Expr::Await(operand) => creates_resource(operand),
                // Try operator on resource factory
                Expr::Try(operand) => creates_resource(operand),
                _ => None,
            }
        }

        // Track state for a function body
        struct FunctionScope {
            // Variables holding Resource types: name -> (span, resource_type, closed)
            resources: HashMap<String, (Span, String, bool)>,
            // Whether we're inside a with/using statement
            in_with: bool,
            // Whether there's a defer for a specific variable
            deferred: std::collections::HashSet<String>,
        }

        impl FunctionScope {
            fn new() -> Self {
                Self {
                    resources: HashMap::new(),
                    in_with: false,
                    deferred: std::collections::HashSet::new(),
                }
            }

            fn add_resource(&mut self, name: String, span: Span, resource_type: String) {
                self.resources.insert(name, (span, resource_type, false));
            }

            fn mark_closed(&mut self, name: &str) {
                if let Some((_, _, closed)) = self.resources.get_mut(name) {
                    *closed = true;
                }
            }

            fn mark_deferred(&mut self, name: &str) {
                self.deferred.insert(name.to_string());
            }

            fn unclosed_resources(&self) -> Vec<(&str, Span, &str)> {
                self.resources
                    .iter()
                    .filter(|(name, (_, _, closed))| !*closed && !self.deferred.contains(*name))
                    .map(|(name, (span, ty, _))| (name.as_str(), *span, ty.as_str()))
                    .collect()
            }
        }

        // Check expressions for resource usage
        fn check_expr_for_close(scope: &mut FunctionScope, expr: &Expr) {
            match expr {
                Expr::MethodCall { receiver, method, .. } => {
                    if method == "close" {
                        // Mark the receiver as closed
                        if let Expr::Identifier(name) = &**receiver {
                            scope.mark_closed(name);
                        }
                    }
                    check_expr_for_close(scope, receiver);
                }
                Expr::Call { callee, args } => {
                    check_expr_for_close(scope, callee);
                    for arg in args {
                        check_expr_for_close(scope, &arg.value);
                    }
                }
                Expr::Binary { left, right, .. } => {
                    check_expr_for_close(scope, left);
                    check_expr_for_close(scope, right);
                }
                Expr::Unary { operand, .. } => {
                    check_expr_for_close(scope, operand);
                }
                Expr::FieldAccess { receiver, .. } => {
                    check_expr_for_close(scope, receiver);
                }
                Expr::Index { receiver, index } => {
                    check_expr_for_close(scope, receiver);
                    check_expr_for_close(scope, index);
                }
                Expr::Lambda { body, .. } => {
                    check_expr_for_close(scope, body);
                }
                Expr::DoBlock(stmts) => {
                    for stmt in stmts {
                        check_stmt_for_resources(scope, stmt);
                    }
                }
                _ => {}
            }
        }

        // Check statements for resource creation and closing
        fn check_stmt_for_resources(scope: &mut FunctionScope, node: &Node) {
            use simple_parser::ast::{LetStmt, Pattern};

            fn get_pattern_name(pattern: &Pattern) -> Option<&str> {
                match pattern {
                    Pattern::Identifier(name) => Some(name),
                    Pattern::MutIdentifier(name) => Some(name),
                    Pattern::MoveIdentifier(name) => Some(name),
                    _ => None,
                }
            }

            match node {
                Node::Let(LetStmt {
                    pattern,
                    value: Some(val),
                    ty,
                    span,
                    ..
                }) => {
                    // Check if value creates a resource
                    if let Some(resource_type) = creates_resource(val) {
                        if let Some(name) = get_pattern_name(pattern) {
                            scope.add_resource(name.to_string(), *span, resource_type);
                        }
                    }
                    // Also check if type annotation indicates a resource
                    else if let Some(type_ann) = ty {
                        if is_resource_type(type_ann) {
                            if let Some(name) = get_pattern_name(pattern) {
                                let type_str = format_type(type_ann);
                                scope.add_resource(name.to_string(), *span, type_str);
                            }
                        }
                    }

                    check_expr_for_close(scope, val);
                }
                Node::Expression(expr) => {
                    check_expr_for_close(scope, expr);
                }
                Node::Defer(defer_stmt) => {
                    // Check if defer closes a resource
                    match &defer_stmt.body {
                        simple_parser::ast::DeferBody::Expr(expr) => {
                            if let Expr::MethodCall { receiver, method, .. } = expr {
                                if method == "close" {
                                    if let Expr::Identifier(name) = &**receiver {
                                        scope.mark_deferred(name);
                                    }
                                }
                            }
                        }
                        simple_parser::ast::DeferBody::Block(block) => {
                            for stmt in &block.statements {
                                if let Node::Expression(Expr::MethodCall { receiver, method, .. }) = stmt {
                                    if method == "close" {
                                        if let Expr::Identifier(name) = &**receiver {
                                            scope.mark_deferred(name);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Node::ErrDefer(errdefer_stmt) => {
                    // Check if errdefer closes a resource (same logic as defer)
                    match &errdefer_stmt.body {
                        simple_parser::ast::DeferBody::Expr(expr) => {
                            if let Expr::MethodCall { receiver, method, .. } = expr {
                                if method == "close" {
                                    if let Expr::Identifier(name) = &**receiver {
                                        scope.mark_deferred(name);
                                    }
                                }
                            }
                        }
                        simple_parser::ast::DeferBody::Block(block) => {
                            for stmt in &block.statements {
                                if let Node::Expression(Expr::MethodCall { receiver, method, .. }) = stmt {
                                    if method == "close" {
                                        if let Expr::Identifier(name) = &**receiver {
                                            scope.mark_deferred(name);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Node::With(with_stmt) => {
                    // Resources in with statements are automatically closed
                    // So we don't track them as potential leaks
                    scope.in_with = true;
                    for stmt in &with_stmt.body.statements {
                        check_stmt_for_resources(scope, stmt);
                    }
                    scope.in_with = false;
                }
                Node::If(if_stmt) => {
                    check_expr_for_close(scope, &if_stmt.condition);
                    for stmt in &if_stmt.then_block.statements {
                        check_stmt_for_resources(scope, stmt);
                    }
                    for (_pattern, cond, block) in &if_stmt.elif_branches {
                        check_expr_for_close(scope, cond);
                        for stmt in &block.statements {
                            check_stmt_for_resources(scope, stmt);
                        }
                    }
                    if let Some(else_block) = &if_stmt.else_block {
                        for stmt in &else_block.statements {
                            check_stmt_for_resources(scope, stmt);
                        }
                    }
                }
                Node::For(for_stmt) => {
                    check_expr_for_close(scope, &for_stmt.iterable);
                    for stmt in &for_stmt.body.statements {
                        check_stmt_for_resources(scope, stmt);
                    }
                }
                Node::While(while_stmt) => {
                    check_expr_for_close(scope, &while_stmt.condition);
                    for stmt in &while_stmt.body.statements {
                        check_stmt_for_resources(scope, stmt);
                    }
                }
                Node::Loop(loop_stmt) => {
                    for stmt in &loop_stmt.body.statements {
                        check_stmt_for_resources(scope, stmt);
                    }
                }
                Node::Return(ret) => {
                    if let Some(val) = &ret.value {
                        check_expr_for_close(scope, val);
                        // If returning a resource, it's not a leak (caller is responsible)
                        if let Expr::Identifier(name) = val {
                            scope.mark_closed(name);
                        }
                    }
                }
                _ => {}
            }
        }

        // Check functions for resource leaks
        fn check_function_body(checker: &mut LintChecker, func: &FunctionDef) {
            // Create scoped config with function attributes
            let mut scoped_config = checker.config.child();
            scoped_config.apply_attributes(&func.attributes);
            let original_config = std::mem::replace(&mut checker.config, scoped_config);

            let mut scope = FunctionScope::new();

            for stmt in &func.body.statements {
                check_stmt_for_resources(&mut scope, stmt);
            }

            // Report unclosed resources
            for (name, span, resource_type) in scope.unclosed_resources() {
                checker.emit(
                    LintName::ResourceLeak,
                    span,
                    format!("resource `{}` of type `{}` may not be closed", name, resource_type),
                    Some(format!(
                        "add `defer {}.close()` after creation, or use `with {} as {}: ...`",
                        name, name, name
                    )),
                );
            }

            checker.config = original_config;
        }

        // Process all functions
        for item in items {
            match item {
                Node::Function(func) => {
                    check_function_body(self, func);
                }
                Node::Class(c) => {
                    for method in &c.methods {
                        check_function_body(self, method);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        check_function_body(self, method);
                    }
                }
                Node::Impl(impl_block) => {
                    for method in &impl_block.methods {
                        check_function_body(self, method);
                    }
                }
                _ => {}
            }
        }
    }

    /// Check if an import path bypasses an __init__.spl boundary.
    ///
    /// When resolving `use crate.pkg.internal.Symbol`, if `pkg/` contains
    /// `__init__.spl`, the import must use symbols exported by that __init__.spl.
    /// Reaching through to `pkg/internal/Symbol` directly is a boundary violation.
    ///
    /// This method checks UseStmt nodes against a provided source root to detect
    /// violations. Directories without __init__.spl are freely accessible.
    pub fn check_init_boundary(&mut self, items: &[Node], source_file: &Path) {
        // Determine the source root by walking up from source_file
        // We check each UseStmt's module path segments against the filesystem
        let source_root = self.find_source_root(source_file);

        fn check_use_stmts(checker: &mut LintChecker, items: &[Node], source_root: &Path) {
            for node in items {
                match node {
                    Node::UseStmt(use_stmt) => {
                        // Only check crate-rooted imports (first segment is "crate")
                        let segments = &use_stmt.path.segments;
                        if segments.first().map(|s| s.as_str()) == Some("crate") {
                            let segments = &segments[1..]; // Skip "crate" prefix
                                                           // Walk the path segments, checking for __init__.spl boundaries
                            let mut current_dir = source_root.to_path_buf();
                            for (i, segment) in segments.iter().enumerate() {
                                let next_dir = current_dir.join(segment);
                                let init_file = next_dir.join("__init__.spl");

                                if next_dir.is_dir() && init_file.exists() {
                                    // This directory has an __init__.spl boundary
                                    // Check if the import tries to go deeper
                                    if i + 1 < segments.len() {
                                        // Check if __init__.spl has bypass attribute
                                        if checker.dir_has_bypass(&init_file) {
                                            // Bypass directory — transparent, continue checking
                                            current_dir = next_dir;
                                            continue;
                                        }

                                        // The remaining segments go past the boundary
                                        let remaining: Vec<&str> =
                                            segments[i + 1..].iter().map(|s| s.as_str()).collect();
                                        let full_path =
                                            segments.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");

                                        checker.emit(
                                            LintName::InitBoundaryViolation,
                                            use_stmt.span,
                                            format!(
                                                "import `crate.{}` bypasses __init__.spl boundary at `{}/`",
                                                full_path,
                                                segment
                                            ),
                                            Some(format!(
                                                "only symbols exported by `{}` are accessible; \
                                                 add `export use {}` to that file, or import from the boundary directly",
                                                init_file.display(),
                                                remaining.join(".")
                                            )),
                                        );
                                        break; // Only report once per import
                                    }
                                }
                                current_dir = next_dir;
                            }
                        }
                    }
                    // Recursively check inline modules
                    Node::ModDecl(mod_decl) => {
                        if let Some(ref body) = mod_decl.body {
                            check_use_stmts(checker, body, source_root);
                        }
                    }
                    _ => {}
                }
            }
        }

        if let Some(root) = source_root {
            check_use_stmts(self, items, &root);
        }
    }

    /// Check if a bypass directory incorrectly contains .spl code files.
    ///
    /// When __init__.spl has `#[bypass]`, the directory must contain only
    /// subdirectories, not .spl code files.
    pub fn check_bypass_validity(&mut self, items: &[Node], source_file: &Path) {
        // Only check __init__.spl files
        let filename = source_file.file_name().and_then(|f| f.to_str()).unwrap_or("");

        if filename != "__init__.spl" {
            return;
        }

        // Check if this __init__.spl has a #[bypass] attribute
        let has_bypass = items.iter().any(|node| {
            if let Node::ModDecl(decl) = node {
                decl.attributes.iter().any(|attr| attr.name == "bypass")
            } else {
                false
            }
        });

        // Also check top-level attributes (file-level #[bypass])
        let has_file_bypass = if let Ok(source) = std::fs::read_to_string(source_file) {
            source.lines().take(20).any(|line| {
                let trimmed = line.trim();
                trimmed == "#[bypass]" || trimmed.starts_with("#[bypass]")
            })
        } else {
            false
        };

        if !has_bypass && !has_file_bypass {
            return;
        }

        // Check if the directory contains any .spl files other than __init__.spl
        if let Some(dir) = source_file.parent() {
            if let Ok(entries) = std::fs::read_dir(dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.is_file() {
                        if let Some(ext) = path.extension() {
                            if ext == "spl" {
                                let fname = path.file_name().and_then(|f| f.to_str()).unwrap_or("");
                                if fname != "__init__.spl" {
                                    self.emit(
                                        LintName::BypassWithCodeFiles,
                                        Span::new(0, 0, 1, 1),
                                        format!(
                                            "#[bypass] directory `{}` contains code file `{}`",
                                            dir.display(),
                                            fname
                                        ),
                                        Some(
                                            "bypass directories must contain only subdirectories; \
                                             move .spl files into subdirectories or remove #[bypass]"
                                                .to_string(),
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Check for functions with too many parameters
    pub(super) fn check_too_many_arguments(&mut self, items: &[Node]) {
        const WARN_THRESHOLD: usize = 7;
        const DENY_THRESHOLD: usize = 12;

        fn check_func_args(checker: &mut LintChecker, func: &FunctionDef) {
            // Count params, excluding 'self'
            let effective_count = func.params.iter().filter(|p| p.name != "self").count();

            if effective_count <= WARN_THRESHOLD {
                return;
            }

            // Skip FFI wrapper naming conventions
            if func.name.starts_with("_ffi_") || func.name.starts_with("_raw_") || func.name.starts_with("rt_") {
                return;
            }

            // Skip constructors (they often need all struct fields)
            if func.name == "new"
                || func.name == "create"
                || func.name == "build"
                || func.name.starts_with("new_")
                || func.name.starts_with("create_")
                || func.name.starts_with("build_")
            {
                return;
            }

            // Check scoped config for allow
            let mut scoped = checker.config.child();
            scoped.apply_attributes(&func.attributes);

            if scoped.get_level(LintName::TooManyArguments) == LintLevel::Allow {
                return;
            }

            if effective_count > DENY_THRESHOLD {
                checker.emit(
                    LintName::TooManyArguments,
                    func.span,
                    format!(
                        "function `{}` has {} parameters (limit: {}). Group related parameters into a struct.",
                        func.name, effective_count, DENY_THRESHOLD
                    ),
                    Some("Consider using an options/config struct".to_string()),
                );
            } else {
                checker.emit(
                    LintName::TooManyArguments,
                    func.span,
                    format!(
                        "function `{}` has {} parameters (recommended max: {}). Consider grouping related parameters.",
                        func.name, effective_count, WARN_THRESHOLD
                    ),
                    Some("Group related parameters into a struct".to_string()),
                );
            }
        }

        for item in items {
            match item {
                Node::Function(func) => check_func_args(self, func),
                Node::Class(c) => {
                    for method in &c.methods {
                        check_func_args(self, method);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        check_func_args(self, method);
                    }
                }
                _ => {}
            }
        }
    }

    /// Find the source root directory by walking up from the source file.
    /// Returns None if unable to determine.
    pub(super) fn find_source_root(&self, source_file: &Path) -> Option<std::path::PathBuf> {
        // Walk up directories looking for simple.sdn or simple.toml
        let mut current = source_file.parent()?;
        for _ in 0..20 {
            let sdn = current.join("simple.sdn");
            let toml = current.join("simple.toml");
            if sdn.exists() || toml.exists() {
                // Found project root, source root is typically "src" under it
                let src_dir = current.join("src");
                if src_dir.exists() {
                    return Some(src_dir);
                }
                return Some(current.to_path_buf());
            }
            current = current.parent()?;
        }
        None
    }

    /// Check if an __init__.spl file has a #[bypass] attribute.
    pub(super) fn dir_has_bypass(&self, init_file: &Path) -> bool {
        if let Ok(source) = std::fs::read_to_string(init_file) {
            source.lines().take(30).any(|line| {
                let trimmed = line.trim();
                trimmed == "#[bypass]" || trimmed.starts_with("#[bypass]")
            })
        } else {
            false
        }
    }
}
