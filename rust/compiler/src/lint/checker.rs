//! Lint checker implementation for AST traversal.
//!
//! #![skip_todo]

use super::config::LintConfig;
use super::diagnostics::LintDiagnostic;
use super::rules::{is_bare_bool, is_primitive_type};
use super::types::{LintLevel, LintName};
use simple_common::diagnostic::{EasyFix, FixConfidence, Replacement};
use simple_parser::ast::{
    Argument, Attribute, ClassDef, Decorator, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef, Type,
};
use simple_parser::token::Span;
use std::collections::HashMap;
use std::path::Path;

/// Parameter info for duplicate typed args checking
#[derive(Clone, Debug)]
struct ParamInfo {
    name: String,
    ty: Option<Type>,
}

/// Function signature info for call-site checking
#[derive(Clone, Debug)]
struct FunctionInfo {
    params: Vec<ParamInfo>,
}

/// Format a type for user-friendly display
fn format_type(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let args_str: Vec<String> = args.iter().map(format_type).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
        }
        Type::Array { element, size } => {
            let elem_str = format_type(element);
            match size {
                Some(s) => format!("[{}; {:?}]", elem_str, s),
                None => format!("[{}]", elem_str),
            }
        }
        Type::Optional(inner) => format!("{}?", format_type(inner)),
        Type::Tuple(types) => {
            let types_str: Vec<String> = types.iter().map(format_type).collect();
            format!("({})", types_str.join(", "))
        }
        Type::Function { params, ret } => {
            let params_str: Vec<String> = params.iter().map(format_type).collect();
            let ret_str = ret.as_ref().map(|r| format_type(r)).unwrap_or_else(|| "()".to_string());
            format!("fn({}) -> {}", params_str.join(", "), ret_str)
        }
        _ => format!("{:?}", ty),
    }
}

/// Lint checker for a compilation unit
pub struct LintChecker {
    /// Current lint configuration
    config: LintConfig,
    /// Collected diagnostics
    diagnostics: Vec<LintDiagnostic>,
    /// Source file path (for file-based lints)
    source_file: Option<std::path::PathBuf>,
    /// Function registry for call-site checks (populated during check_module)
    functions: HashMap<String, FunctionInfo>,
}

impl LintChecker {
    pub fn new() -> Self {
        Self {
            config: LintConfig::new(),
            diagnostics: Vec::new(),
            source_file: None,
            functions: HashMap::new(),
        }
    }

    pub fn with_config(config: LintConfig) -> Self {
        Self {
            config,
            diagnostics: Vec::new(),
            source_file: None,
            functions: HashMap::new(),
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
        self.emit_with_fix(lint, span, message, suggestion, None);
    }

    /// Emit a lint diagnostic with an optional machine-applicable fix
    fn emit_with_fix(
        &mut self,
        lint: LintName,
        span: Span,
        message: String,
        suggestion: Option<String>,
        easy_fix: Option<simple_common::diagnostic::EasyFix>,
    ) {
        let level = self.config.get_level(lint);
        if level == LintLevel::Allow {
            return;
        }

        let mut diagnostic = LintDiagnostic::new(lint, level, span, message);
        if let Some(s) = suggestion {
            diagnostic = diagnostic.with_suggestion(s);
        }
        if let Some(fix) = easy_fix {
            diagnostic = diagnostic.with_easy_fix(fix);
        }
        self.diagnostics.push(diagnostic);
    }

    /// Check a module for lint violations
    pub fn check_module(&mut self, items: &[Node]) {
        // First pass: collect function definitions for call-site checks
        self.collect_functions(items);

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

            // Check for exports outside __init__.spl
            self.check_export_outside_init(items, &source_file);

            // Check for imports bypassing __init__.spl boundaries
            self.check_init_boundary(items, &source_file);

            // Check for bypass directories with code files
            self.check_bypass_validity(items, &source_file);
        }

        // Check for unknown decorators/attributes
        self.check_unknown_annotations(items);

        // Run AST-based lints
        for item in items {
            self.check_node(item);
        }

        // Check for unnamed duplicate typed args at call sites
        self.check_unnamed_duplicate_typed_args(items);

        // Check for resource leaks
        self.check_resource_leaks(items);
    }

    /// Collect function definitions for call-site checking
    fn collect_functions(&mut self, items: &[Node]) {
        fn collect_from_node(functions: &mut HashMap<String, FunctionInfo>, node: &Node) {
            match node {
                Node::Function(func) => {
                    let info = FunctionInfo {
                        params: func
                            .params
                            .iter()
                            .map(|p| ParamInfo {
                                name: p.name.clone(),
                                ty: p.ty.clone(),
                            })
                            .collect(),
                    };
                    functions.insert(func.name.clone(), info);
                }
                Node::Class(c) => {
                    // Collect methods from class
                    for method in &c.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        // Store as ClassName.method_name for method lookup
                        let key = format!("{}.{}", c.name, method.name);
                        functions.insert(key, info.clone());
                        // Also store just by method name for simple lookup
                        functions.insert(method.name.clone(), info);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        let key = format!("{}.{}", s.name, method.name);
                        functions.insert(key, info.clone());
                        functions.insert(method.name.clone(), info);
                    }
                }
                Node::Impl(impl_block) => {
                    for method in &impl_block.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        // Format target_type for key
                        let type_name = format!("{:?}", impl_block.target_type);
                        let key = format!("{}.{}", type_name, method.name);
                        functions.insert(key, info.clone());
                        functions.insert(method.name.clone(), info);
                    }
                }
                _ => {}
            }
        }

        for item in items {
            collect_from_node(&mut self.functions, item);
        }
    }

    /// Check a single AST node
    /// Known decorator names (whitelist)
    const KNOWN_DECORATORS: &'static [&'static str] = &[
        "async",
        "pure",
        "io",
        "net",
        "fs",
        "unsafe",
        "verify",
        "trusted",
        "ghost",
        "auto_lean",
        "bounds",
        "extern",
        "simd",
        "inline",
        "test",
        "property_test",
        "snapshot_test",
        "deprecated",
        "generated_by",
        "Lib",
        "inject",
        "sys_inject",
    ];

    /// Known attribute names (whitelist)
    const KNOWN_ATTRIBUTES: &'static [&'static str] = &[
        "allow",
        "warn",
        "deny",
        "default",
        "concurrency_mode",
        "layout",
        "pure",
        "snapshot",
        "deprecated",
        "bypass",
        "skip_todo",
        "generated",
        "inline",
        "ignore",
    ];

    /// Check for unknown decorators and attributes across all items
    fn check_unknown_annotations(&mut self, items: &[Node]) {
        for item in items {
            self.check_node_annotations(item);
        }
    }

    /// Check a single node's decorators and attributes
    fn check_node_annotations(&mut self, node: &Node) {
        match node {
            Node::Function(f) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&f.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_decorators(&f.decorators);
                self.check_attributes(&f.attributes);
                self.config = original_config;
            }
            Node::Class(c) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&c.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_attributes(&c.attributes);
                // Check methods within the class
                for method in &c.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
                self.config = original_config;
            }
            Node::Struct(s) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&s.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_attributes(&s.attributes);
                for method in &s.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
                self.config = original_config;
            }
            Node::Enum(e) => {
                self.check_attributes(&e.attributes);
            }
            Node::Trait(_t) => {
                // TraitDef doesn't have attributes field
            }
            Node::Impl(imp) => {
                self.check_attributes(&imp.attributes);
                for method in &imp.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
            }
            Node::ClassAlias(ca) => {
                self.check_decorators(&ca.decorators);
            }
            Node::FunctionAlias(fa) => {
                self.check_decorators(&fa.decorators);
            }
            _ => {}
        }
    }

    /// Check decorators against the known whitelist
    fn check_decorators(&mut self, decorators: &[Decorator]) {
        for dec in decorators {
            if let Expr::Identifier(name) = &dec.name {
                if !Self::KNOWN_DECORATORS.contains(&name.as_str()) {
                    self.emit(
                        LintName::UnknownDecorator,
                        dec.span,
                        format!("unknown decorator '@{}'", name),
                        Some("Suppress with: #[allow(unknown_decorator)]".to_string()),
                    );
                }
            }
        }
    }

    /// Check attributes against the known whitelist
    fn check_attributes(&mut self, attributes: &[Attribute]) {
        for attr in attributes {
            if !Self::KNOWN_ATTRIBUTES.contains(&attr.name.as_str()) {
                self.emit(
                    LintName::UnknownAttribute,
                    attr.span,
                    format!("unknown attribute '#[{}]'", attr.name),
                    Some("Suppress with: #[allow(unknown_attribute)]".to_string()),
                );
            }
        }
    }

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

    /// Check for export statements outside of __init__.spl files
    fn check_export_outside_init(&mut self, items: &[Node], source_file: &std::path::Path) {
        // Check if this is an __init__.spl file
        let filename = source_file.file_name().and_then(|f| f.to_str()).unwrap_or("");

        if filename == "__init__.spl" {
            return; // Exports are allowed in __init__.spl
        }

        // Exports are allowed in test/spec files (they re-export test utilities)
        if filename.ends_with("_spec.spl") || filename.ends_with("_test.spl") {
            return;
        }

        // Scan for ExportUseStmt nodes
        fn check_for_exports(checker: &mut LintChecker, items: &[Node], source_file: &std::path::Path) {
            for node in items {
                match node {
                    Node::ExportUseStmt(export_stmt) => {
                        let file_display = source_file.display().to_string();
                        let suggestion = if let Some(parent) = source_file.parent() {
                            let init_path = parent.join("__init__.spl");
                            format!("move this export to {} (the directory manifest)", init_path.display())
                        } else {
                            "move this export to the directory's __init__.spl file".to_string()
                        };

                        checker.emit(
                            LintName::ExportOutsideInit,
                            export_stmt.span,
                            format!(
                                "export statement not allowed in regular .spl files (found in {})",
                                file_display
                            ),
                            Some(suggestion),
                        );
                    }
                    // Recursively check inline modules
                    Node::ModDecl(mod_decl) => {
                        if let Some(ref body) = mod_decl.body {
                            check_for_exports(checker, body, source_file);
                        }
                    }
                    // Check impl blocks
                    Node::Impl(impl_block) => {
                        // impl blocks don't contain top-level exports, but check for completeness
                    }
                    _ => {}
                }
            }
        }

        check_for_exports(self, items, source_file);
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
    fn has_file_level_skip_todo_format(content: &str) -> bool {
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
    fn check_todo_format(&mut self, source_file: &std::path::Path) {
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

    /// Check for file-level lint allow attribute
    fn has_file_level_allow(&self, lint_name: &str) -> bool {
        if let Some(ref path) = self.source_file {
            if let Ok(source) = std::fs::read_to_string(path) {
                let pattern = format!("#![allow({})]", lint_name);
                // Check first 50 lines for file-level allow
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
    fn check_unnamed_duplicate_typed_args(&mut self, items: &[Node]) {
        // Check for file-level allow via #![allow(unnamed_duplicate_typed_args)]
        if self.has_file_level_allow("unnamed_duplicate_typed_args") {
            return; // File-level allow, skip this lint
        }

        // Helper to check if a type matches another (structural equality)
        fn types_match(ty1: &Option<Type>, ty2: &Option<Type>) -> bool {
            match (ty1, ty2) {
                (Some(t1), Some(t2)) => t1 == t2,
                _ => false, // Can't compare if either type is unknown
            }
        }

        // Find parameter indices that share a type with at least one other parameter
        fn find_duplicate_typed_params(params: &[ParamInfo]) -> Vec<usize> {
            let mut duplicates = Vec::new();
            for (i, param) in params.iter().enumerate() {
                if param.ty.is_none() {
                    continue;
                }
                for (j, other) in params.iter().enumerate() {
                    if i != j && types_match(&param.ty, &other.ty) {
                        if !duplicates.contains(&i) {
                            duplicates.push(i);
                        }
                        break;
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

            // Check if any duplicate-typed parameter is passed positionally
            for (arg_idx, arg) in args.iter().enumerate() {
                if arg.name.is_some() {
                    continue; // Named argument, OK
                }

                // This is a positional argument
                if arg_idx >= func_info.params.len() {
                    continue; // Extra args (variadic or error)
                }

                if duplicate_indices.contains(&arg_idx) {
                    let param = &func_info.params[arg_idx];

                    // Find other params with same type
                    let same_type_params: Vec<&str> = func_info
                        .params
                        .iter()
                        .enumerate()
                        .filter(|(i, p)| *i != arg_idx && types_match(&p.ty, &param.ty))
                        .map(|(_, p)| p.name.as_str())
                        .collect();

                    let type_str = param
                        .ty
                        .as_ref()
                        .map(|t| format_type(t))
                        .unwrap_or_else(|| "unknown".to_string());

                    checker.emit(
                        LintName::UnnamedDuplicateTypedArgs,
                        arg.span, // Use the argument's span for proper location reporting
                        format!(
                            "positional argument for parameter `{}` which shares type `{}` with `{}`",
                            param.name,
                            type_str,
                            same_type_params.join("`, `")
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
                Expr::MethodCall { receiver, method, args } => {
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
            use simple_parser::ast::LetStmt;

            match node {
                Node::Expression(expr) => check_expr(checker, expr),
                Node::Let(LetStmt { value, .. }) => {
                    if let Some(v) = value {
                        check_expr(checker, v);
                    }
                }
                Node::Assignment(assign) => {
                    check_expr(checker, &assign.value);
                }
                Node::Return(ret) => {
                    if let Some(v) = &ret.value {
                        check_expr(checker, v);
                    }
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

    /// Check for potential resource leaks in functions
    ///
    /// This lint tracks Resource-typed variables and warns if they are not
    /// properly closed via close(), defer, or with statements.
    fn check_resource_leaks(&mut self, items: &[Node]) {
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
                    value,
                    ty,
                    span,
                    ..
                }) => {
                    if let Some(val) = value {
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

    /// Find the source root directory by walking up from the source file.
    /// Returns None if unable to determine.
    fn find_source_root(&self, source_file: &Path) -> Option<std::path::PathBuf> {
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

impl Default for LintChecker {
    fn default() -> Self {
        Self::new()
    }
}
