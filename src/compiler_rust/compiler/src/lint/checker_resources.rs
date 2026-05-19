//! Lint checker: resource leak detection, init boundary, bypass validity checks.

use super::super::types::{LintLevel, LintName};
use super::checker_core::format_type;
use simple_parser::ast::{ClassDef, Expr, FunctionDef, ImplBlock, Node, StructDef, Type};
use simple_parser::token::Span;
use std::collections::HashMap;
use std::path::Path;

use super::LintChecker;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RuntimeFamily {
    Common,
    NogcAsyncMutNoalloc,
    NogcAsyncMut,
    NogcAsyncImmut,
    NogcSyncImmut,
    Async,
    NogcSyncMut,
    GcAsyncMut,
    GcAsyncImmut,
    GcSyncMut,
    GcSyncImmut,
}

impl RuntimeFamily {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "common" => Some(Self::Common),
            "nogc_async_mut_noalloc" => Some(Self::NogcAsyncMutNoalloc),
            "nogc_async_mut" => Some(Self::NogcAsyncMut),
            "nogc_async_immut" => Some(Self::NogcAsyncImmut),
            "nogc_sync_immut" => Some(Self::NogcSyncImmut),
            "async" => Some(Self::Async),
            "nogc_sync_mut" => Some(Self::NogcSyncMut),
            "gc_async_mut" => Some(Self::GcAsyncMut),
            "gc_async_immut" => Some(Self::GcAsyncImmut),
            "gc_sync_mut" => Some(Self::GcSyncMut),
            "gc_sync_immut" => Some(Self::GcSyncImmut),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Common => "common",
            Self::NogcAsyncMutNoalloc => "nogc_async_mut_noalloc",
            Self::NogcAsyncMut => "nogc_async_mut",
            Self::NogcAsyncImmut => "nogc_async_immut",
            Self::NogcSyncImmut => "nogc_sync_immut",
            Self::Async => "async",
            Self::NogcSyncMut => "nogc_sync_mut",
            Self::GcAsyncMut => "gc_async_mut",
            Self::GcAsyncImmut => "gc_async_immut",
            Self::GcSyncMut => "gc_sync_mut",
            Self::GcSyncImmut => "gc_sync_immut",
        }
    }

    fn is_gc(self) -> bool {
        matches!(
            self,
            Self::GcAsyncMut | Self::GcAsyncImmut | Self::GcSyncMut | Self::GcSyncImmut
        )
    }

    fn is_nogc(self) -> bool {
        matches!(
            self,
            Self::NogcAsyncMutNoalloc
                | Self::NogcAsyncMut
                | Self::NogcAsyncImmut
                | Self::NogcSyncImmut
                | Self::Async
                | Self::NogcSyncMut
        )
    }

    fn is_noalloc(self) -> bool {
        matches!(self, Self::NogcAsyncMutNoalloc)
    }

    fn is_allocating(self) -> bool {
        !matches!(self, Self::Common | Self::NogcAsyncMutNoalloc)
    }

    fn rank(self) -> i8 {
        match self {
            Self::Common => 0,
            Self::NogcAsyncMutNoalloc => 1,
            Self::NogcAsyncMut | Self::NogcAsyncImmut | Self::NogcSyncImmut => 2,
            Self::Async | Self::NogcSyncMut => 3,
            Self::GcAsyncMut | Self::GcAsyncImmut | Self::GcSyncMut | Self::GcSyncImmut => 4,
        }
    }
}

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
                // Force unwrap on resource factory
                Expr::ForceUnwrap(operand) => creates_resource(operand),
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

    /// Check runtime family imports for GC/noalloc dependency boundary violations.
    ///
    /// Detection order:
    /// 1. Path-based: infer family from `src/lib/<family>/...` path structure
    /// 2. Attribute-based: fall back to `@no_gc`/`@gc` file-level attributes
    ///    for user modules outside standard library paths
    pub fn check_gc_boundary_imports(&mut self, items: &[Node], source_file: &Path) {
        let source_family = match runtime_family_from_source_path(source_file) {
            Some(family) => family,
            None => match runtime_family_from_attributes(items, source_file) {
                Some(family) => family,
                None => return,
            },
        };

        if source_family == RuntimeFamily::Common {
            return;
        }

        fn check_use_stmts(checker: &mut LintChecker, items: &[Node], source_family: RuntimeFamily) {
            for node in items {
                match node {
                    Node::UseStmt(use_stmt) => {
                        let segments = &use_stmt.path.segments;
                        let Some(import_family) = runtime_family_from_import_segments(segments) else {
                            continue;
                        };

                        if import_family == RuntimeFamily::Common {
                            continue;
                        }

                        let module_path = segments.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");
                        if let Some(reason) = runtime_family_import_violation_reason(source_family, import_family) {
                            checker.emit(
                                LintName::GcBoundaryCrossing,
                                use_stmt.span,
                                format!(
                                    "runtime family `{}` must not import `{}` ({})",
                                    source_family.name(),
                                    module_path,
                                    reason
                                ),
                                Some(
                                    "route shared code through std.common or move the dependency to the backend family"
                                        .to_string(),
                                ),
                            );
                        }
                    }
                    Node::ModDecl(mod_decl) => {
                        if let Some(ref body) = mod_decl.body {
                            check_use_stmts(checker, body, source_family);
                        }
                    }
                    _ => {}
                }
            }
        }

        check_use_stmts(self, items, source_family);
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
    fn check_too_many_arguments(&mut self, items: &[Node]) {
        const WARN_THRESHOLD: usize = 7;
        const DENY_THRESHOLD: usize = 12;

        fn check_func_args(checker: &mut LintChecker, func: &FunctionDef) {
            // Count params, excluding 'self'
            let effective_count = func.params.iter().filter(|p| p.name != "self").count();

            if effective_count <= WARN_THRESHOLD {
                return;
            }

            // Skip SFFI wrapper naming conventions
            if func.name.starts_with("_sffi_") || func.name.starts_with("_raw_") || func.name.starts_with("rt_") {
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
    fn dir_has_bypass(&self, init_file: &Path) -> bool {
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

fn runtime_family_from_source_path(source_file: &Path) -> Option<RuntimeFamily> {
    let components: Vec<String> = source_file
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect();

    for pair in components.windows(2) {
        if pair[0] == "lib" {
            return RuntimeFamily::from_name(&pair[1]);
        }
    }

    None
}

fn runtime_family_from_import_segments(segments: &[String]) -> Option<RuntimeFamily> {
    let mut offset = 0;
    if segments.first().map(|s| s.as_str()) == Some("std") || segments.first().map(|s| s.as_str()) == Some("lib") {
        offset = 1;
    }

    segments
        .get(offset)
        .and_then(|segment| RuntimeFamily::from_name(segment))
}

fn runtime_family_import_violation_reason(
    source_family: RuntimeFamily,
    import_family: RuntimeFamily,
) -> Option<&'static str> {
    if import_family == RuntimeFamily::Common {
        return None;
    }

    if source_family.is_noalloc() && import_family.is_gc() {
        return Some("noalloc_imports_gc_family");
    }

    if source_family.is_noalloc() && import_family.is_allocating() {
        return Some("noalloc_imports_allocating_family");
    }

    if !source_family.is_gc() && import_family.is_gc() {
        return Some("nogc_imports_gc_family");
    }

    // Symmetric: GC family must not import from NoGC families
    if source_family.is_gc() && import_family.is_nogc() {
        return Some("gc_imports_nogc_family");
    }

    if import_family.rank() > source_family.rank() {
        return Some("higher_layer_runtime_family");
    }

    None
}

/// Detect runtime family from `@no_gc` / `@gc` file-level attributes.
///
/// Scans:
/// 1. AST-level `ModDecl` attributes (`@no_gc`, `@gc`)
/// 2. Raw source text for `@no_gc` / `@gc` in the first 30 lines
///
/// Returns a representative `RuntimeFamily` — `NogcSyncMut` for `@no_gc`,
/// `GcSyncMut` for `@gc` — since the exact sub-family is unknown for
/// user modules. This is sufficient for import boundary checks.
fn runtime_family_from_attributes(items: &[Node], source_file: &Path) -> Option<RuntimeFamily> {
    // Check AST ModDecl attributes
    for node in items {
        if let Node::ModDecl(decl) = node {
            for attr in &decl.attributes {
                if attr.name == "no_gc" {
                    return Some(RuntimeFamily::NogcSyncMut);
                }
                if attr.name == "gc" {
                    return Some(RuntimeFamily::GcSyncMut);
                }
            }
        }
    }

    // Fall back to raw source text scanning for file-level attributes
    if let Ok(source) = std::fs::read_to_string(source_file) {
        for line in source.lines().take(30) {
            let trimmed = line.trim();
            if trimmed == "@no_gc" || trimmed.starts_with("@no_gc ") || trimmed.starts_with("@no_gc\n") {
                return Some(RuntimeFamily::NogcSyncMut);
            }
            if trimmed == "@gc" || trimmed.starts_with("@gc ") || trimmed.starts_with("@gc\n") {
                return Some(RuntimeFamily::GcSyncMut);
            }
        }
    }

    // Also check parent __init__.spl for directory-level attribute
    if let Some(dir) = source_file.parent() {
        let init_file = dir.join("__init__.spl");
        if init_file.exists() {
            if let Ok(source) = std::fs::read_to_string(&init_file) {
                for line in source.lines().take(30) {
                    let trimmed = line.trim();
                    if trimmed == "@no_gc" || trimmed.starts_with("@no_gc ") {
                        return Some(RuntimeFamily::NogcSyncMut);
                    }
                    if trimmed == "@gc" || trimmed.starts_with("@gc ") {
                        return Some(RuntimeFamily::GcSyncMut);
                    }
                }
            }
        }
    }

    None
}

impl Default for LintChecker {
    fn default() -> Self {
        Self::new()
    }
}
