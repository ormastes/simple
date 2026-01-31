// Symbol usage analysis for context pack generation
//
// This module handles:
// - Analyzing symbol usage in AST
// - Tracking function calls, type references, and imports
// - Collecting transitive dependencies

use simple_parser::ast::{Block, Expr, Node, Pattern, Type};
use std::collections::BTreeSet;

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
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_usage_from_expr(condition, usage);
                self.collect_usage_from_expr(then_branch, usage);
                if let Some(else_br) = else_branch {
                    self.collect_usage_from_expr(else_br, usage);
                }
            }

            // Match expressions
            Expr::Match { subject, arms } => {
                self.collect_usage_from_expr(subject, usage);
                // Collect from match arms
                for arm in arms {
                    // Collect from guard expression if present
                    if let Some(guard) = &arm.guard {
                        self.collect_usage_from_expr(guard, usage);
                    }
                    // Collect from arm body
                    for stmt in &arm.body.statements {
                        self.collect_usage_from_node(stmt, usage);
                    }
                    // Note: We don't collect from pattern as patterns introduce new bindings
                    // rather than referencing existing symbols
                }
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

    #[allow(dead_code)]
    fn is_builtin_type(&self, name: &str) -> bool {
        matches!(
            name,
            "i8" | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "f32"
                | "f64"
                | "bool"
                | "str"
                | "char"
                | "String"
                | "void"
        )
    }
}

impl Default for SymbolUsageAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}
