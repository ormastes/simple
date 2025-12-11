//! Lint system for the Simple language compiler.
//!
//! This module provides a configurable lint system that can emit warnings or errors
//! for various code patterns. Key features:
//!
//! - `primitive_api`: Warns/errors when bare primitives are used in public APIs
//! - Lint levels: `allow`, `warn` (default), `deny`
//! - Attribute-based control: `#[allow(lint)]`, `#[warn(lint)]`, `#[deny(lint)]`
//! - Module-level inheritance through `__init__.spl`

use simple_parser::ast::{
    Attribute, ClassDef, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef, Type,
};
use simple_parser::token::Span;
use std::collections::HashMap;

/// Lint severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LintLevel {
    /// Suppress the lint entirely
    Allow,
    /// Emit a warning (default for most lints)
    #[default]
    Warn,
    /// Treat as a compile error
    Deny,
}

impl LintLevel {
    /// Parse lint level from string (attribute value)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "allow" => Some(LintLevel::Allow),
            "warn" => Some(LintLevel::Warn),
            "deny" => Some(LintLevel::Deny),
            _ => None,
        }
    }
}

/// Known lint names
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LintName {
    /// Bare primitives in public API signatures
    PrimitiveApi,
    /// Bare bool parameters (suggest enum)
    BareBool,
}

impl LintName {
    /// Get the string name of the lint
    pub fn as_str(&self) -> &'static str {
        match self {
            LintName::PrimitiveApi => "primitive_api",
            LintName::BareBool => "bare_bool",
        }
    }

    /// Parse lint name from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "primitive_api" => Some(LintName::PrimitiveApi),
            "bare_bool" => Some(LintName::BareBool),
            _ => None,
        }
    }

    /// Get the default level for this lint
    pub fn default_level(&self) -> LintLevel {
        match self {
            LintName::PrimitiveApi => LintLevel::Warn,
            LintName::BareBool => LintLevel::Warn,
        }
    }
}

/// A lint diagnostic message
#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    pub lint: LintName,
    pub level: LintLevel,
    pub span: Span,
    pub message: String,
    pub suggestion: Option<String>,
}

impl LintDiagnostic {
    pub fn new(lint: LintName, level: LintLevel, span: Span, message: String) -> Self {
        Self {
            lint,
            level,
            span,
            message,
            suggestion: None,
        }
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    /// Check if this is an error (deny level)
    pub fn is_error(&self) -> bool {
        self.level == LintLevel::Deny
    }

    /// Check if this is a warning
    pub fn is_warning(&self) -> bool {
        self.level == LintLevel::Warn
    }

    /// Format the diagnostic for display
    pub fn format(&self) -> String {
        let prefix = match self.level {
            LintLevel::Allow => return String::new(), // Don't display allowed lints
            LintLevel::Warn => "warning",
            LintLevel::Deny => "error",
        };

        let mut result = format!(
            "{}: {} [{}]\n  --> line {}, column {}\n",
            prefix,
            self.message,
            self.lint.as_str(),
            self.span.line,
            self.span.column
        );

        if let Some(ref suggestion) = self.suggestion {
            result.push_str(&format!("  = help: {}\n", suggestion));
        }

        result
    }
}

/// Lint configuration for a scope (module, function, etc.)
#[derive(Debug, Clone, Default)]
pub struct LintConfig {
    /// Overridden lint levels
    levels: HashMap<LintName, LintLevel>,
}

impl LintConfig {
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the level for a specific lint
    pub fn set_level(&mut self, lint: LintName, level: LintLevel) {
        self.levels.insert(lint, level);
    }

    /// Get the effective level for a lint
    pub fn get_level(&self, lint: LintName) -> LintLevel {
        self.levels
            .get(&lint)
            .copied()
            .unwrap_or_else(|| lint.default_level())
    }

    /// Parse lint attributes and update config
    /// Handles: #[allow(lint)], #[warn(lint)], #[deny(lint)]
    pub fn apply_attributes(&mut self, attributes: &[Attribute]) {
        for attr in attributes {
            let level = match attr.name.as_str() {
                "allow" => LintLevel::Allow,
                "warn" => LintLevel::Warn,
                "deny" => LintLevel::Deny,
                _ => continue,
            };

            // Parse lint names from args: #[deny(primitive_api, bare_bool)]
            if let Some(ref args) = attr.args {
                for arg in args {
                    if let Expr::Identifier(lint_name) = arg {
                        if let Some(lint) = LintName::from_str(lint_name) {
                            self.set_level(lint, level);
                        }
                    }
                }
            }
        }
    }

    /// Create a child config that inherits from this one
    pub fn child(&self) -> Self {
        Self {
            levels: self.levels.clone(),
        }
    }
}

/// The primitive types that trigger the primitive_api lint
const PRIMITIVE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
];

/// Check if a type is a bare primitive
fn is_primitive_type(ty: &Type) -> bool {
    match ty {
        Type::Simple(name) => PRIMITIVE_TYPES.contains(&name.as_str()),
        _ => false,
    }
}

/// Check if a type is bare bool specifically
fn is_bare_bool(ty: &Type) -> bool {
    matches!(ty, Type::Simple(name) if name == "bool")
}

/// Lint checker for a compilation unit
pub struct LintChecker {
    /// Current lint configuration
    config: LintConfig,
    /// Collected diagnostics
    diagnostics: Vec<LintDiagnostic>,
}

impl LintChecker {
    pub fn new() -> Self {
        Self {
            config: LintConfig::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn with_config(config: LintConfig) -> Self {
        Self {
            config,
            diagnostics: Vec::new(),
        }
    }

    /// Get collected diagnostics
    pub fn diagnostics(&self) -> &[LintDiagnostic] {
        &self.diagnostics
    }

    /// Take collected diagnostics
    pub fn take_diagnostics(&mut self) -> Vec<LintDiagnostic> {
        std::mem::take(&mut self.diagnostics)
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
                for (i, field_ty) in fields.iter().enumerate() {
                    self.check_type_in_public_api(
                        field_ty,
                        variant.span,
                        &format!("{}::{}.{}", e.name, variant.name, i),
                        "variant field",
                    );
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
                format!(
                    "bare primitive `{}` in public API {} `{}`",
                    type_name, context, name
                ),
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
}

impl Default for LintChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_code(code: &str) -> simple_parser::ast::Module {
        let mut parser = Parser::new(code);
        parser.parse().expect("parse failed")
    }

    fn check_code(code: &str) -> Vec<LintDiagnostic> {
        let module = parse_code(code);
        let mut checker = LintChecker::new();
        checker.check_module(&module.items);
        checker.take_diagnostics()
    }

    fn check_code_with_deny(code: &str) -> Vec<LintDiagnostic> {
        let module = parse_code(code);
        let mut config = LintConfig::new();
        config.set_level(LintName::PrimitiveApi, LintLevel::Deny);
        let mut checker = LintChecker::with_config(config);
        checker.check_module(&module.items);
        checker.take_diagnostics()
    }

    #[test]
    fn test_public_function_with_primitive_param() {
        let code = r#"
pub fn get_value(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code(code);
        assert!(!diagnostics.is_empty());
        assert!(diagnostics.iter().any(|d| d.lint == LintName::PrimitiveApi));
        assert!(diagnostics.iter().all(|d| d.level == LintLevel::Warn));
    }

    #[test]
    fn test_private_function_no_warning() {
        let code = r#"
fn internal_compute(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code(code);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_public_function_with_unit_type_no_warning() {
        let code = r#"
pub fn get_user_id() -> UserId:
    return 42
"#;
        let diagnostics = check_code(code);
        // UserId is not a primitive, so no warning
        assert!(diagnostics
            .iter()
            .all(|d| d.lint != LintName::PrimitiveApi));
    }

    #[test]
    fn test_bare_bool_warning() {
        let code = r#"
pub fn set_active(active: bool):
    pass
"#;
        let diagnostics = check_code(code);
        assert!(diagnostics.iter().any(|d| d.lint == LintName::BareBool));
    }

    #[test]
    fn test_deny_makes_error() {
        let code = r#"
pub fn get_value(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code_with_deny(code);
        assert!(!diagnostics.is_empty());
        assert!(diagnostics.iter().any(|d| d.is_error()));
    }

    #[test]
    fn test_allow_suppresses_warning() {
        let code = r#"
#[allow(primitive_api)]
pub fn raw_bytes(count: i32) -> i32:
    return count
"#;
        let diagnostics = check_code(code);
        // The allow attribute should suppress primitive_api warnings
        assert!(diagnostics
            .iter()
            .all(|d| d.lint != LintName::PrimitiveApi));
    }

    #[test]
    fn test_public_struct_field() {
        let code = r#"
pub struct Config:
    pub timeout: i64
    internal: i32
"#;
        let diagnostics = check_code(code);
        // Only public fields should trigger warning
        assert!(diagnostics.len() == 1);
        assert!(diagnostics[0].message.contains("timeout"));
    }

    #[test]
    fn test_string_type_no_warning() {
        let code = r#"
pub fn get_name() -> str:
    return "test"
"#;
        let diagnostics = check_code(code);
        // str is allowed
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_option_type_checks_inner() {
        let code = r#"
pub fn find_value() -> Option[i64]:
    return None
"#;
        let diagnostics = check_code(code);
        // Should warn about i64 inside Option
        assert!(diagnostics.iter().any(|d| d.lint == LintName::PrimitiveApi));
    }

    #[test]
    fn test_lint_level_from_str() {
        assert_eq!(LintLevel::from_str("allow"), Some(LintLevel::Allow));
        assert_eq!(LintLevel::from_str("warn"), Some(LintLevel::Warn));
        assert_eq!(LintLevel::from_str("deny"), Some(LintLevel::Deny));
        assert_eq!(LintLevel::from_str("DENY"), Some(LintLevel::Deny));
        assert_eq!(LintLevel::from_str("invalid"), None);
    }

    #[test]
    fn test_lint_name_from_str() {
        assert_eq!(
            LintName::from_str("primitive_api"),
            Some(LintName::PrimitiveApi)
        );
        assert_eq!(LintName::from_str("bare_bool"), Some(LintName::BareBool));
        assert_eq!(LintName::from_str("unknown"), None);
    }
}
