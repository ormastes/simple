//! i18n string extraction from AST
//!
//! This module provides an AST visitor that extracts all i18n strings
//! from source files, tracking their scope for auto-naming.

use simple_parser::ast::{Block, Expr, FStringPart, FunctionDef, Module, Node, Type};
use std::collections::HashMap;
use std::path::PathBuf;

/// Extract a string representation from a Type
fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        Type::SelfType => "Self".to_string(),
        _ => "Unknown".to_string(),
    }
}

/// Represents an extracted i18n string
#[derive(Debug, Clone)]
pub struct I18nString {
    /// The i18n name (e.g., "Login_failed_", "Welcome_")
    pub name: String,
    /// The default text
    pub default_text: String,
    /// Template variables (if any)
    pub template_vars: Vec<String>,
    /// Source file location
    pub source_file: PathBuf,
    /// Line number
    pub line: usize,
    /// Scope path (e.g., "MyClass.my_method")
    pub scope: String,
}

/// Result of extraction from multiple files
#[derive(Debug, Default)]
pub struct ExtractionResult {
    /// All extracted i18n strings, keyed by name
    pub strings: HashMap<String, I18nString>,
    /// Auto-generated names for plain strings (scope -> counter)
    pub auto_counters: HashMap<String, usize>,
    /// Duplicate name warnings
    pub warnings: Vec<String>,
}

/// AST visitor that extracts i18n strings
pub struct I18nExtractor {
    result: ExtractionResult,
    current_file: PathBuf,
    current_scope: Vec<String>,
    /// Current line number for tracking source locations
    current_line: usize,
}

impl I18nExtractor {
    /// Create a new extractor
    pub fn new() -> Self {
        Self {
            result: ExtractionResult::default(),
            current_file: PathBuf::new(),
            current_scope: Vec::new(),
            current_line: 0,
        }
    }

    /// Extract i18n strings from a module
    pub fn extract_module(&mut self, module: &Module, file_path: PathBuf) {
        self.current_file = file_path;
        self.current_scope.clear();
        self.current_line = 0;

        for item in &module.items {
            self.visit_node(item);
        }
    }

    /// Get the extraction result
    pub fn finish(self) -> ExtractionResult {
        self.result
    }

    /// Get the current scope as a string
    fn scope_string(&self) -> String {
        self.current_scope.join(".")
    }

    /// Generate an auto-name for a plain string in the current scope
    fn generate_auto_name(&mut self, scope: &str) -> String {
        let counter = self.result.auto_counters.entry(scope.to_string()).or_insert(0);
        *counter += 1;
        if scope.is_empty() {
            format!("__string_{}_", counter)
        } else {
            format!("{}__{}_", scope.replace('.', "__"), counter)
        }
    }

    /// Visit an AST node
    fn visit_node(&mut self, node: &Node) {
        match node {
            Node::Function(func) => self.visit_function(func),
            Node::Struct(s) => {
                self.current_line = s.span.line;
                self.current_scope.push(s.name.clone());
                // No body in struct, but could have default values
                self.current_scope.pop();
            }
            Node::Class(c) => {
                self.current_line = c.span.line;
                self.current_scope.push(c.name.clone());
                for method in &c.methods {
                    self.visit_function(method);
                }
                self.current_scope.pop();
            }
            Node::Impl(impl_block) => {
                self.current_line = impl_block.span.line;
                // Extract type name from Type
                let type_name = type_to_string(&impl_block.target_type);
                self.current_scope.push(type_name);
                for method in &impl_block.methods {
                    self.visit_function(method);
                }
                self.current_scope.pop();
            }
            Node::Expression(expr) => self.visit_expr(expr),
            Node::Let(stmt) => {
                self.current_line = stmt.span.line;
                if let Some(init) = &stmt.value {
                    self.visit_expr(init);
                }
            }
            Node::Return(ret) => {
                self.current_line = ret.span.line;
                if let Some(value) = &ret.value {
                    self.visit_expr(value);
                }
            }
            Node::If(if_stmt) => {
                self.current_line = if_stmt.span.line;
                self.visit_expr(&if_stmt.condition);
                self.visit_block(&if_stmt.then_block);
                for elif in &if_stmt.elif_branches {
                    self.visit_expr(&elif.1);
                    self.visit_block(&elif.2);
                }
                if let Some(else_block) = &if_stmt.else_block {
                    self.visit_block(else_block);
                }
            }
            Node::For(for_stmt) => {
                self.current_line = for_stmt.span.line;
                self.visit_expr(&for_stmt.iterable);
                self.visit_block(&for_stmt.body);
            }
            Node::While(while_stmt) => {
                self.current_line = while_stmt.span.line;
                self.visit_expr(&while_stmt.condition);
                self.visit_block(&while_stmt.body);
            }
            Node::Loop(loop_stmt) => {
                self.current_line = loop_stmt.span.line;
                self.visit_block(&loop_stmt.body);
            }
            Node::Match(match_stmt) => {
                self.current_line = match_stmt.span.line;
                self.visit_expr(&match_stmt.subject);
                for arm in &match_stmt.arms {
                    self.visit_block(&arm.body);
                }
            }
            _ => {}
        }
    }

    /// Visit a function definition
    fn visit_function(&mut self, func: &FunctionDef) {
        self.current_line = func.span.line;
        self.current_scope.push(func.name.clone());
        self.visit_block(&func.body);
        self.current_scope.pop();
    }

    /// Visit a block
    fn visit_block(&mut self, block: &Block) {
        for stmt in &block.statements {
            self.visit_node(stmt);
        }
    }

    /// Visit an expression
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::I18nString { name, default_text } => {
                let scope = self.scope_string();
                self.add_i18n_string(name.clone(), default_text.clone(), Vec::new(), scope);
            }
            Expr::I18nTemplate { name, parts, args: _ } => {
                let scope = self.scope_string();
                let template_vars: Vec<String> = parts
                    .iter()
                    .filter_map(|p| {
                        if let FStringPart::Expr(expr) = p {
                            // Extract variable names from simple identifiers
                            if let Expr::Identifier(id) = expr {
                                Some(id.clone())
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect();

                // Reconstruct the default text from parts
                let default_text = parts
                    .iter()
                    .map(|p| match p {
                        FStringPart::Literal(s) => s.clone(),
                        FStringPart::Expr(expr) => {
                            if let Expr::Identifier(id) = expr {
                                format!("{{{}}}", id)
                            } else {
                                "{...}".to_string()
                            }
                        }
                    })
                    .collect::<String>();

                self.add_i18n_string(name.clone(), default_text, template_vars, scope);
            }
            // Also extract plain strings for potential i18n auto-naming
            Expr::String(s) if !s.is_empty() && s.chars().any(|c| c.is_alphabetic()) => {
                // Only consider strings with alphabetic characters (likely user-facing)
                // Skip strings that look like code, paths, etc.
                if !s.contains('/') && !s.contains('\\') && !s.contains("::") {
                    let scope = self.scope_string();
                    let auto_name = self.generate_auto_name(&scope);
                    self.add_i18n_string(auto_name, s.clone(), Vec::new(), scope);
                }
            }
            // Recurse into sub-expressions
            Expr::Binary { left, right, .. } => {
                self.visit_expr(left);
                self.visit_expr(right);
            }
            Expr::Unary { operand, .. } => {
                self.visit_expr(operand);
            }
            Expr::Call { callee, args } => {
                self.visit_expr(callee);
                for arg in args {
                    self.visit_expr(&arg.value);
                }
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.visit_expr(receiver);
                for arg in args {
                    self.visit_expr(&arg.value);
                }
            }
            Expr::FieldAccess { receiver, .. } => {
                self.visit_expr(receiver);
            }
            Expr::Index { receiver, index } => {
                self.visit_expr(receiver);
                self.visit_expr(index);
            }
            Expr::Lambda { body, .. } => {
                self.visit_expr(body);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.visit_expr(condition);
                self.visit_expr(then_branch);
                if let Some(else_expr) = else_branch {
                    self.visit_expr(else_expr);
                }
            }
            Expr::Match { subject, arms } => {
                self.visit_expr(subject);
                for arm in arms {
                    self.visit_block(&arm.body);
                }
            }
            Expr::Tuple(exprs) | Expr::Array(exprs) => {
                for e in exprs {
                    self.visit_expr(e);
                }
            }
            Expr::FString { parts, .. } => {
                for part in parts {
                    if let FStringPart::Expr(e) = part {
                        self.visit_expr(&e);
                    }
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, value) in fields {
                    self.visit_expr(value);
                }
            }
            Expr::DoBlock(stmts) => {
                for stmt in stmts {
                    self.visit_node(stmt);
                }
            }
            _ => {}
        }
    }

    /// Add an i18n string to the result
    fn add_i18n_string(&mut self, name: String, default_text: String, template_vars: Vec<String>, scope: String) {
        let i18n_string = I18nString {
            name: name.clone(),
            default_text,
            template_vars,
            source_file: self.current_file.clone(),
            line: self.current_line,
            scope,
        };

        if let Some(existing) = self.result.strings.get(&name) {
            if existing.default_text != i18n_string.default_text {
                self.result.warnings.push(format!(
                    "Warning: i18n string '{}' has different default texts:\n  '{}' in {}\n  '{}' in {}",
                    name,
                    existing.default_text,
                    existing.source_file.display(),
                    i18n_string.default_text,
                    i18n_string.source_file.display()
                ));
            }
        } else {
            self.result.strings.insert(name, i18n_string);
        }
    }
}

impl Default for I18nExtractor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_module(source: &str) -> Module {
        let mut parser = Parser::new(source);
        parser.parse().unwrap()
    }

    #[test]
    fn test_extract_i18n_string() {
        let source = r#"
fn greet():
    print(Hello_"Hello, World!")
"#;
        let module = parse_module(source);
        let mut extractor = I18nExtractor::new();
        extractor.extract_module(&module, PathBuf::from("test.spl"));
        let result = extractor.finish();

        assert!(result.strings.contains_key("Hello_"));
        assert_eq!(result.strings["Hello_"].default_text, "Hello, World!");
    }

    #[test]
    fn test_extract_with_scope() {
        let source = r#"
fn login():
    print(Error_"Login failed")
"#;
        let module = parse_module(source);
        let mut extractor = I18nExtractor::new();
        extractor.extract_module(&module, PathBuf::from("test.spl"));
        let result = extractor.finish();

        assert!(result.strings.contains_key("Error_"));
        assert_eq!(result.strings["Error_"].scope, "login");
    }

    #[test]
    fn test_extract_with_line_numbers() {
        let source = r#"fn greet():
    print(Hello_"Hello!")

fn login():
    print(Error_"Login failed")
"#;
        let module = parse_module(source);
        let mut extractor = I18nExtractor::new();
        extractor.extract_module(&module, PathBuf::from("test.spl"));
        let result = extractor.finish();

        // Line numbers should be tracked from the containing function
        assert!(result.strings.contains_key("Hello_"));
        assert!(result.strings["Hello_"].line > 0);

        assert!(result.strings.contains_key("Error_"));
        assert!(result.strings["Error_"].line > 0);

        // The login function should have a higher line number than greet
        assert!(result.strings["Error_"].line > result.strings["Hello_"].line);
    }
}
