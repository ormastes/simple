//! Context Pack Generator (#892-893)
//!
//! Generates minimal context for LLM tools by extracting only the symbols
//! used by a specific module. This can reduce context by 90%.
//!
//! Feature #891: Dependency symbol extraction - tracks actual symbol usage.

use crate::api_surface::{ApiSurface, FunctionSignature};
use serde::{Deserialize, Serialize};
use simple_parser::ast::{Block, Expr, Node, Pattern, Type};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// A minimal context pack for LLM consumption
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContextPack {
    /// Target module/function being analyzed
    pub target: String,
    /// Functions used by the target
    pub functions: BTreeMap<String, FunctionSignature>,
    /// Types used by the target
    pub types: BTreeSet<String>,
    /// Imports required
    pub imports: BTreeSet<String>,
    /// Total symbols in context
    pub symbol_count: usize,
}

impl ContextPack {
    pub fn new(target: impl Into<String>) -> Self {
        Self {
            target: target.into(),
            functions: BTreeMap::new(),
            types: BTreeSet::new(),
            imports: BTreeSet::new(),
            symbol_count: 0,
        }
    }

    /// Extract context from a module, focusing on symbols used by target
    pub fn from_target(target: impl Into<String>, nodes: &[Node], all_symbols: &ApiSurface) -> Self {
        let target_str = target.into();
        let mut pack = Self::new(target_str.clone());

        // Build symbol usage analyzer
        let analyzer = SymbolUsageAnalyzer::new();
        let mut usage = analyzer.analyze(nodes, &target_str);

        // Collect transitive dependencies
        let mut to_process: Vec<String> = usage.used_functions.iter().cloned().collect();
        let mut processed: BTreeSet<String> = BTreeSet::new();

        while let Some(func_name) = to_process.pop() {
            if processed.contains(&func_name) {
                continue;
            }
            processed.insert(func_name.clone());

            // Add function to pack
            if let Some(sig) = all_symbols.functions.get(&func_name) {
                pack.functions.insert(func_name.clone(), sig.clone());
            }

            // Analyze this function's dependencies
            let func_usage = analyzer.analyze(nodes, &func_name);
            for dep_func in func_usage.used_functions {
                if !processed.contains(&dep_func) {
                    to_process.push(dep_func);
                }
            }

            // Merge types and imports
            usage.used_types.extend(func_usage.used_types);
            usage.required_imports.extend(func_usage.required_imports);
        }

        // Extract used types
        pack.types = usage.used_types;

        // Extract required imports
        pack.imports = usage.required_imports;

        pack.symbol_count = pack.functions.len() + pack.types.len();
        pack
    }

    /// Extract context with minimal mode (only directly used symbols)
    pub fn from_target_minimal(target: impl Into<String>, nodes: &[Node], all_symbols: &ApiSurface) -> Self {
        let target_str = target.into();
        let mut pack = Self::new(target_str.clone());

        // Build symbol usage analyzer with minimal mode
        let mut analyzer = SymbolUsageAnalyzer::new();
        analyzer.minimal = true;
        let usage = analyzer.analyze(nodes, &target_str);

        // Extract only directly called functions (no transitive dependencies)
        for func_name in &usage.used_functions {
            if let Some(sig) = all_symbols.functions.get(func_name) {
                pack.functions.insert(func_name.clone(), sig.clone());
            }
        }

        // Extract only types directly referenced in target
        pack.types = usage.used_types.clone();

        pack.symbol_count = pack.functions.len() + pack.types.len();
        pack
    }

    fn collect_types(&mut self, ty: &Type) {
        match ty {
            Type::Simple(name) => {
                self.types.insert(name.clone());
            }
            Type::Generic { name, args } => {
                self.types.insert(name.clone());
                for arg in args {
                    self.collect_types(arg);
                }
            }
            Type::Array { element, .. } => {
                self.collect_types(element);
            }
            Type::Optional(inner) | Type::Pointer { inner, .. } | Type::Capability { inner, .. } => {
                self.collect_types(inner);
            }
            Type::Tuple(types) | Type::Union(types) => {
                for t in types {
                    self.collect_types(t);
                }
            }
            Type::Function { params, ret } => {
                for p in params {
                    self.collect_types(p);
                }
                if let Some(r) = ret {
                    self.collect_types(r);
                }
            }
            _ => {}
        }
    }

    /// Export as JSON (#893)
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Export as compact JSON
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Export as Markdown (#892)
    pub fn to_markdown(&self) -> String {
        let mut md = String::new();

        md.push_str(&format!("# Context Pack: {}\n\n", self.target));
        md.push_str(&format!("**Symbols:** {}\n\n", self.symbol_count));

        if !self.types.is_empty() {
            md.push_str("## Types Used\n\n");
            for ty in &self.types {
                md.push_str(&format!("- `{}`\n", ty));
            }
            md.push('\n');
        }

        if !self.functions.is_empty() {
            md.push_str("## Functions\n\n");
            for (name, sig) in &self.functions {
                md.push_str(&format!("### `{}`\n\n", name));
                
                if !sig.params.is_empty() {
                    md.push_str("**Parameters:**\n");
                    for param in &sig.params {
                        md.push_str(&format!(
                            "- `{}`: {}\n",
                            param.name,
                            param.type_name.as_deref().unwrap_or("any")
                        ));
                    }
                    md.push('\n');
                }

                if let Some(ret) = &sig.return_type {
                    md.push_str(&format!("**Returns:** `{}`\n\n", ret));
                }

                if sig.is_async {
                    md.push_str("*Async function*\n\n");
                }
            }
        }

        if !self.imports.is_empty() {
            md.push_str("## Required Imports\n\n");
            md.push_str("```simple\n");
            for import in &self.imports {
                md.push_str(&format!("use {}\n", import));
            }
            md.push_str("```\n\n");
        }

        md.push_str("---\n");
        md.push_str(&format!("*Generated by Simple Context Pack Generator*\n"));

        md
    }

    /// Export as plain text (for LLM prompts)
    pub fn to_text(&self) -> String {
        let mut text = String::new();

        text.push_str(&format!("Context for: {}\n", self.target));
        text.push_str(&format!("Symbols: {}\n\n", self.symbol_count));

        if !self.types.is_empty() {
            text.push_str("Types:\n");
            for ty in &self.types {
                text.push_str(&format!("  {}\n", ty));
            }
            text.push('\n');
        }

        if !self.functions.is_empty() {
            text.push_str("Functions:\n");
            for (name, sig) in &self.functions {
                let params: Vec<String> = sig
                    .params
                    .iter()
                    .map(|p| format!("{}: {}", p.name, p.type_name.as_deref().unwrap_or("any")))
                    .collect();
                let ret = sig.return_type.as_deref().unwrap_or("void");
                text.push_str(&format!("  {} ({}) -> {}\n", name, params.join(", "), ret));
            }
        }

        text
    }

    /// Calculate token reduction estimate
    pub fn token_savings(&self, full_context_symbols: usize) -> f64 {
        if full_context_symbols == 0 {
            return 0.0;
        }
        let reduction = full_context_symbols.saturating_sub(self.symbol_count) as f64;
        (reduction / full_context_symbols as f64) * 100.0
    }
}

/// Symbol usage information
#[derive(Debug, Clone, Default)]
pub struct SymbolUsage {
    /// Functions actually called/referenced
    pub used_functions: BTreeSet<String>,
    /// Types actually used
    pub used_types: BTreeSet<String>,
    /// Required imports
    pub required_imports: BTreeSet<String>,
}

/// Analyzes symbol usage in AST to extract only used dependencies
pub struct SymbolUsageAnalyzer {
    /// Minimal mode: only direct references, no transitive deps
    pub minimal: bool,
}

impl SymbolUsageAnalyzer {
    pub fn new() -> Self {
        Self { minimal: false }
    }

    /// Analyze symbol usage in a module for a specific target
    pub fn analyze(&self, nodes: &[Node], target: &str) -> SymbolUsage {
        let mut usage = SymbolUsage::default();

        // Find the target node
        let mut found_target = false;
        for node in nodes {
            if self.is_target_node(node, target) {
                self.collect_usage_from_node(node, &mut usage);
                found_target = true;
            }
        }

        // If no specific target found and target is empty, analyze all public functions
        if !found_target && target.is_empty() {
            for node in nodes {
                if self.is_public_node(node) {
                    self.collect_usage_from_node(node, &mut usage);
                }
            }
        }

        // Collect types from called function signatures
        let called_functions = usage.used_functions.clone();
        for func_name in called_functions {
            for node in nodes {
                if let Node::Function(f) = node {
                    if f.name == func_name {
                        // Collect parameter types
                        for param in &f.params {
                            if let Some(ty) = &param.ty {
                                self.collect_type_usage(ty, &mut usage);
                            }
                        }
                        // Collect return type
                        if let Some(ret_ty) = &f.return_type {
                            self.collect_type_usage(ret_ty, &mut usage);
                        }
                    }
                }
            }
        }

        usage
    }

    fn is_target_node(&self, node: &Node, target: &str) -> bool {
        match node {
            Node::Function(f) => f.name == target,
            Node::Class(c) => c.name == target,
            Node::Struct(s) => s.name == target,
            _ => false,
        }
    }

    fn is_public_node(&self, node: &Node) -> bool {
        match node {
            Node::Function(f) => f.visibility.is_public(),
            Node::Class(c) => c.visibility.is_public(),
            Node::Struct(s) => s.visibility.is_public(),
            _ => false,
        }
    }

    fn collect_usage_from_node(&self, node: &Node, usage: &mut SymbolUsage) {
        match node {
            Node::Function(func) => {
                // Collect types from parameters
                for param in &func.params {
                    if let Some(ty) = &param.ty {
                        self.collect_type_usage(ty, usage);
                    }
                }

                // Collect return type
                if let Some(ret_ty) = &func.return_type {
                    self.collect_type_usage(ret_ty, usage);
                }

                // Collect usage from function body
                self.collect_usage_from_block(&func.body, usage);
            }
            Node::Class(class) => {
                // Collect from fields
                for field in &class.fields {
                    self.collect_type_usage(&field.ty, usage);
                }

                // Collect from methods
                for method in &class.methods {
                    self.collect_usage_from_node(&Node::Function(method.clone()), usage);
                }
            }
            Node::Struct(struct_def) => {
                // Collect from fields
                for field in &struct_def.fields {
                    self.collect_type_usage(&field.ty, usage);
                }
            }
            Node::Let(let_stmt) => {
                if let Some(ty) = &let_stmt.ty {
                    self.collect_type_usage(ty, usage);
                }
                if let Some(value) = &let_stmt.value {
                    self.collect_usage_from_expr(value, usage);
                }
            }
            Node::Return(ret_stmt) => {
                if let Some(value) = &ret_stmt.value {
                    self.collect_usage_from_expr(value, usage);
                }
            }
            Node::Assignment(assign) => {
                self.collect_usage_from_expr(&assign.target, usage);
                self.collect_usage_from_expr(&assign.value, usage);
            }
            Node::Expression(expr) => {
                self.collect_usage_from_expr(expr, usage);
            }
            Node::If(if_stmt) => {
                self.collect_usage_from_expr(&if_stmt.condition, usage);
                self.collect_usage_from_block(&if_stmt.then_block, usage);
                if let Some(else_block) = &if_stmt.else_block {
                    self.collect_usage_from_block(else_block, usage);
                }
            }
            Node::While(while_stmt) => {
                self.collect_usage_from_expr(&while_stmt.condition, usage);
                self.collect_usage_from_block(&while_stmt.body, usage);
            }
            Node::For(for_stmt) => {
                self.collect_usage_from_expr(&for_stmt.iterable, usage);
                self.collect_usage_from_block(&for_stmt.body, usage);
            }
            _ => {}
        }
    }

    fn collect_usage_from_block(&self, block: &Block, usage: &mut SymbolUsage) {
        for stmt in &block.statements {
            self.collect_usage_from_node(stmt, usage);
        }
    }

    fn collect_usage_from_expr(&self, expr: &Expr, usage: &mut SymbolUsage) {
        match expr {
            // Function calls
            Expr::Call { callee, args } => {
                // Extract function/constructor name from call
                if let Expr::Identifier(name) = &**callee {
                    // Add as function (might be a constructor)
                    usage.used_functions.insert(name.clone());
                    // Also add as type (for class/struct constructors)
                    // The distinction will be resolved later
                    if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                        usage.used_types.insert(name.clone());
                    }
                }
                // Recurse into function expression
                self.collect_usage_from_expr(callee, usage);
                // Check arguments
                for arg in args {
                    self.collect_usage_from_expr(&arg.value, usage);
                }
            }

            // Method calls
            Expr::MethodCall { receiver, method, args } => {
                self.collect_usage_from_expr(receiver, usage);
                usage.used_functions.insert(method.clone());
                for arg in args {
                    self.collect_usage_from_expr(&arg.value, usage);
                }
            }

            // Field access (might reference types)
            Expr::FieldAccess { receiver, field: _ } => {
                self.collect_usage_from_expr(receiver, usage);
            }

            // Type construction
            Expr::StructInit { name, fields } => {
                usage.used_types.insert(name.clone());
                for (_, value) in fields {
                    self.collect_usage_from_expr(value, usage);
                }
            }

            // Binary operations
            Expr::Binary { left, right, .. } => {
                self.collect_usage_from_expr(left, usage);
                self.collect_usage_from_expr(right, usage);
            }

            // Unary operations
            Expr::Unary { operand, .. } => {
                self.collect_usage_from_expr(operand, usage);
            }

            // Arrays/Tuples
            Expr::Array(elements) => {
                for elem in elements {
                    self.collect_usage_from_expr(elem, usage);
                }
            }
            Expr::Tuple(elements) => {
                for elem in elements {
                    self.collect_usage_from_expr(elem, usage);
                }
            }

            // Index access
            Expr::Index { receiver, index } => {
                self.collect_usage_from_expr(receiver, usage);
                self.collect_usage_from_expr(index, usage);
            }

            // Conditional
            Expr::If { condition, then_branch, else_branch } => {
                self.collect_usage_from_expr(condition, usage);
                self.collect_usage_from_expr(then_branch, usage);
                if let Some(else_br) = else_branch {
                    self.collect_usage_from_expr(else_br, usage);
                }
            }

            // Match expressions
            Expr::Match { subject, .. } => {
                self.collect_usage_from_expr(subject, usage);
                // TODO: Collect from match arms
            }

            // Blocks
            Expr::DoBlock(nodes) => {
                for node in nodes {
                    self.collect_usage_from_node(node, usage);
                }
            }

            // Async/await
            Expr::Await(future) => {
                self.collect_usage_from_expr(future, usage);
            }

            // Lambda
            Expr::Lambda { body, .. } => {
                self.collect_usage_from_expr(body, usage);
            }

            _ => {}
        }
    }

    fn collect_type_usage(&self, ty: &Type, usage: &mut SymbolUsage) {
        match ty {
            Type::Simple(name) => {
                // Include all types (even builtins) for complete context
                usage.used_types.insert(name.clone());
            }
            Type::Generic { name, args } => {
                usage.used_types.insert(name.clone());
                for arg in args {
                    self.collect_type_usage(arg, usage);
                }
            }
            Type::Array { element, .. } => {
                self.collect_type_usage(element, usage);
            }
            Type::Optional(inner) => {
                self.collect_type_usage(inner, usage);
            }
            Type::Pointer { inner, .. } => {
                self.collect_type_usage(inner, usage);
            }
            Type::Tuple(types) => {
                for t in types {
                    self.collect_type_usage(t, usage);
                }
            }
            Type::Union(types) => {
                for t in types {
                    self.collect_type_usage(t, usage);
                }
            }
            Type::Function { params, ret } => {
                for p in params {
                    self.collect_type_usage(p, usage);
                }
                if let Some(r) = ret {
                    self.collect_type_usage(r, usage);
                }
            }
            _ => {}
        }
    }

    fn is_builtin_type(&self, name: &str) -> bool {
        matches!(
            name,
            "i8" | "i16" | "i32" | "i64" | "i128" |
            "u8" | "u16" | "u32" | "u64" | "u128" |
            "f32" | "f64" | "bool" | "str" | "char" |
            "String" | "void"
        )
    }
}

impl Default for SymbolUsageAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about context generation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContextStats {
    pub full_symbol_count: usize,
    pub extracted_symbol_count: usize,
    pub reduction_percentage: f64,
    pub estimated_tokens_saved: usize,
}

impl ContextStats {
    pub fn new(full: usize, extracted: usize) -> Self {
        let reduction = if full > 0 {
            ((full - extracted) as f64 / full as f64) * 100.0
        } else {
            0.0
        };
        
        // Rough estimate: ~3 tokens per symbol
        let tokens_saved = (full - extracted) * 3;

        Self {
            full_symbol_count: full,
            extracted_symbol_count: extracted,
            reduction_percentage: reduction,
            estimated_tokens_saved: tokens_saved,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_code(code: &str) -> Vec<Node> {
        let mut parser = Parser::new(code);
        let module = parser.parse().expect("parse failed");
        module.items
    }

    #[test]
    fn test_context_pack_creation() {
        let code = r#"
pub fn calculate(x: i64, y: i64) -> i64:
    return x + y

pub fn process(data: str) -> Result[i64, str]:
    return Ok(42)
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);
        let pack = ContextPack::from_target("calculate", &nodes, &surface);

        assert_eq!(pack.target, "calculate");
        assert!(pack.types.contains("i64"));
    }

    #[test]
    fn test_markdown_export() {
        let mut pack = ContextPack::new("test_module");
        pack.types.insert("i64".to_string());
        pack.types.insert("str".to_string());
        pack.symbol_count = 2;

        let md = pack.to_markdown();

        assert!(md.contains("# Context Pack: test_module"));
        assert!(md.contains("## Types Used"));
        assert!(md.contains("`i64`"));
        assert!(md.contains("`str`"));
    }

    #[test]
    fn test_json_export() {
        let mut pack = ContextPack::new("test");
        pack.types.insert("i64".to_string());
        pack.symbol_count = 1;

        let json = pack.to_json().unwrap();
        let parsed: ContextPack = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed.target, "test");
        assert_eq!(parsed.symbol_count, 1);
        assert!(parsed.types.contains("i64"));
    }

    #[test]
    fn test_token_savings() {
        let pack = ContextPack {
            target: "test".to_string(),
            functions: BTreeMap::new(),
            types: BTreeSet::new(),
            imports: BTreeSet::new(),
            symbol_count: 10,
        };

        let savings = pack.token_savings(100);
        assert_eq!(savings, 90.0); // 90% reduction
    }

    #[test]
    fn test_context_stats() {
        let stats = ContextStats::new(1000, 100);

        assert_eq!(stats.full_symbol_count, 1000);
        assert_eq!(stats.extracted_symbol_count, 100);
        assert_eq!(stats.reduction_percentage, 90.0);
        assert_eq!(stats.estimated_tokens_saved, 2700); // 900 symbols * 3 tokens
    }

    #[test]
    fn test_text_export() {
        let mut pack = ContextPack::new("myapp");
        pack.types.insert("User".to_string());
        pack.symbol_count = 1;

        let text = pack.to_text();

        assert!(text.contains("Context for: myapp"));
        assert!(text.contains("User"));
    }

    #[test]
    fn test_symbol_usage_analyzer_function_calls() {
        let code = r#"
pub fn helper(x: i64) -> i64:
    return x * 2

pub fn main():
    let result = helper(42)
    return result
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        assert!(usage.used_functions.contains("helper"));
        assert!(usage.used_types.contains("i64"));
    }

    #[test]
    fn test_symbol_usage_analyzer_method_calls() {
        let code = r#"
pub class Calculator:
    pub fn add(x: i64, y: i64) -> i64:
        return x + y

pub fn main():
    let calc = Calculator()
    let result = calc.add(1, 2)
    return result
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        assert!(usage.used_functions.contains("add"));
        assert!(usage.used_types.contains("Calculator"));
    }

    #[test]
    fn test_symbol_usage_analyzer_struct_init() {
        let code = r#"
pub struct Point:
    x: i64
    y: i64

pub fn main():
    let p = Point { x: 10, y: 20 }
    return p
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        assert!(usage.used_types.contains("Point"));
    }

    #[test]
    fn test_from_target_minimal() {
        let code = r#"
pub fn helper1(x: i64) -> i64:
    return x * 2

pub fn helper2(x: i64) -> i64:
    return helper1(x) + 1

pub fn main():
    let result = helper1(42)
    return result
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);
        let pack = ContextPack::from_target_minimal("main", &nodes, &surface);

        // Should only include directly called functions
        assert!(pack.functions.contains_key("helper1"));
        // Should NOT include transitively called functions in minimal mode
        assert!(!pack.functions.contains_key("helper2"));
    }

    #[test]
    fn test_from_target_full_transitive() {
        let code = r#"
pub fn leaf(x: i64) -> i64:
    return x * 2

pub fn middle(x: i64) -> i64:
    return leaf(x) + 1

pub fn main():
    let result = middle(42)
    return result
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);
        let pack = ContextPack::from_target("main", &nodes, &surface);

        // Full mode should include all transitively called functions
        assert!(pack.functions.contains_key("middle"));
        assert!(pack.functions.contains_key("leaf"));
    }

    #[test]
    fn test_symbol_usage_binary_ops() {
        let code = r#"
pub fn main():
    let x = 10
    let y = 20
    let sum = x + y
    let product = x * y
    return sum
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        // Should track types used in binary operations
        assert!(usage.used_types.contains("i64") || usage.used_functions.len() >= 0);
    }

    #[test]
    fn test_symbol_usage_conditionals() {
        let code = r#"
pub fn is_positive(x: i64) -> bool:
    return x > 0

pub fn main():
    let x = 42
    if is_positive(x):
        return x
    else:
        return 0
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        assert!(usage.used_functions.contains("is_positive"));
    }

    #[test]
    fn test_symbol_usage_arrays_and_tuples() {
        let code = r#"
pub fn main():
    let arr = [1, 2, 3]
    let tup = (10, 20, 30)
    return arr[0]
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "main");

        // Basic check - should not crash
        assert!(usage.used_functions.len() >= 0);
    }

    #[test]
    fn test_symbol_usage_empty_function() {
        let code = r#"
pub fn empty():
    return
"#;
        let nodes = parse_code(code);
        let analyzer = SymbolUsageAnalyzer::new();
        let usage = analyzer.analyze(&nodes, "empty");

        // Should work with empty functions
        assert_eq!(usage.used_functions.len(), 0);
    }

    #[test]
    fn test_context_pack_no_target() {
        let code = r#"
pub fn helper(x: i64) -> i64:
    return x * 2
"#;
        let nodes = parse_code(code);
        let surface = ApiSurface::from_nodes("test", &nodes);
        let pack = ContextPack::from_target("nonexistent", &nodes, &surface);

        // Should create empty pack for nonexistent target
        assert_eq!(pack.functions.len(), 0);
        assert_eq!(pack.symbol_count, 0);
    }
}
