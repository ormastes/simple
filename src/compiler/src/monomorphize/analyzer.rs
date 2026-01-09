//! Call site analyzer for finding generic function calls.

use super::types::ConcreteType;
use super::util::{ast_type_to_concrete, infer_concrete_type, type_uses_param};
use simple_parser::ast::{Block, Expr, FunctionDef, Module, Node};
use std::collections::HashMap;

/// Analyzes AST to find calls to generic functions and collect the
/// concrete type arguments needed for monomorphization.
///
/// This analyzer walks through the module's code and identifies:
/// 1. Explicit generic calls: `identity[Int](42)`
/// 2. Inferred generic calls: `identity(42)` where T is inferred from argument
pub struct CallSiteAnalyzer<'a> {
    module: &'a Module,
    /// Generic function definitions
    generic_functions: HashMap<String, &'a FunctionDef>,
    /// Collected call sites: (function_name, inferred_type_args)
    call_sites: Vec<(String, Vec<ConcreteType>)>,
    /// Current type context for inference
    type_context: HashMap<String, ConcreteType>,
}

impl<'a> CallSiteAnalyzer<'a> {
    pub fn new(module: &'a Module) -> Self {
        let mut generic_functions = HashMap::new();

        // Collect generic function definitions
        for node in &module.items {
            if let Node::Function(f) = node {
                if !f.generic_params.is_empty() {
                    generic_functions.insert(f.name.clone(), f);
                }
            }
        }

        Self {
            module,
            generic_functions,
            call_sites: Vec::new(),
            type_context: HashMap::new(),
        }
    }

    /// Analyze the module and return all collected call sites.
    pub fn analyze(mut self) -> Vec<(String, Vec<ConcreteType>)> {
        for node in &self.module.items {
            self.analyze_node(node);
        }
        self.call_sites
    }

    fn analyze_node(&mut self, node: &Node) {
        match node {
            Node::Function(f) => {
                // Skip generic function bodies until they're instantiated
                if f.generic_params.is_empty() {
                    self.analyze_block(&f.body);
                }
            }
            Node::Let(let_stmt) => {
                if let Some(value) = &let_stmt.value {
                    // Track variable types for inference
                    if let Some(ty) = &let_stmt.ty {
                        let concrete = ast_type_to_concrete(ty, &HashMap::new());
                        // Extract identifier name from pattern
                        if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                            self.type_context.insert(name.clone(), concrete);
                        }
                    }
                    self.analyze_expr(value);
                }
            }
            Node::Expression(expr) => self.analyze_expr(expr),
            Node::Return(ret) => {
                if let Some(value) = &ret.value {
                    self.analyze_expr(value);
                }
            }
            Node::If(if_stmt) => {
                self.analyze_expr(&if_stmt.condition);
                self.analyze_block(&if_stmt.then_block);
                for (cond, block) in &if_stmt.elif_branches {
                    self.analyze_expr(cond);
                    self.analyze_block(block);
                }
                if let Some(else_block) = &if_stmt.else_block {
                    self.analyze_block(else_block);
                }
            }
            Node::While(w) => {
                self.analyze_expr(&w.condition);
                self.analyze_block(&w.body);
            }
            Node::For(f) => {
                self.analyze_expr(&f.iterable);
                self.analyze_block(&f.body);
            }
            Node::Class(c) => {
                for method in &c.methods {
                    if method.generic_params.is_empty() {
                        self.analyze_block(&method.body);
                    }
                }
            }
            Node::Assignment(assign) => {
                // Handle module-level assignments like `main = identity(42)`
                self.analyze_expr(&assign.value);
            }
            _ => {}
        }
    }

    fn analyze_block(&mut self, block: &Block) {
        for node in &block.statements {
            self.analyze_node(node);
        }
    }

    fn analyze_expr(&mut self, expr: &Expr) {
        match expr {
            // Check for generic function calls
            Expr::Call { callee, args } => {
                // Check if this is a call to a generic function
                if let Expr::Identifier(name) = callee.as_ref() {
                    if let Some(func) = self.generic_functions.get(name) {
                        // Try to infer type arguments from arguments
                        if let Some(type_args) = self.infer_type_args(func, args) {
                            self.call_sites.push((name.clone(), type_args));
                        }
                    }
                }
                // Also check for Index expression: identity[Int](42)
                else if let Expr::Index { receiver, index } = callee.as_ref() {
                    if let Expr::Identifier(name) = receiver.as_ref() {
                        if self.generic_functions.contains_key(name) {
                            // The index should be a type - for now, try to parse it
                            if let Some(type_arg) = self.expr_to_type(index) {
                                self.call_sites.push((name.clone(), vec![type_arg]));
                            }
                        }
                    }
                }

                // Analyze arguments recursively
                for arg in args {
                    self.analyze_expr(&arg.value);
                }
            }
            // Recursively analyze sub-expressions
            Expr::Binary { left, right, .. } => {
                self.analyze_expr(left);
                self.analyze_expr(right);
            }
            Expr::Unary { operand, .. } => {
                self.analyze_expr(operand);
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.analyze_expr(receiver);
                for arg in args {
                    self.analyze_expr(&arg.value);
                }
            }
            Expr::FieldAccess { receiver, .. } => {
                self.analyze_expr(receiver);
            }
            Expr::Index { receiver, index } => {
                self.analyze_expr(receiver);
                self.analyze_expr(index);
            }
            Expr::Array(elems) => {
                for elem in elems {
                    self.analyze_expr(elem);
                }
            }
            Expr::Tuple(elems) => {
                for elem in elems {
                    self.analyze_expr(elem);
                }
            }
            Expr::Dict(pairs) => {
                for (k, v) in pairs {
                    self.analyze_expr(k);
                    self.analyze_expr(v);
                }
            }
            Expr::Lambda { body, .. } => {
                self.analyze_expr(body);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.analyze_expr(condition);
                self.analyze_expr(then_branch);
                if let Some(else_expr) = else_branch {
                    self.analyze_expr(else_expr);
                }
            }
            Expr::Match { subject, arms } => {
                self.analyze_expr(subject);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.analyze_expr(guard);
                    }
                    self.analyze_block(&arm.body);
                }
            }
            _ => {}
        }
    }

    /// Try to infer type arguments from function call arguments.
    fn infer_type_args(
        &self,
        func: &FunctionDef,
        args: &[simple_parser::ast::Argument],
    ) -> Option<Vec<ConcreteType>> {
        let mut type_args = Vec::new();

        for type_param in &func.generic_params {
            // Find which parameter uses this type param
            for (i, param) in func.params.iter().enumerate() {
                if let Some(ty) = &param.ty {
                    if type_uses_param(ty, type_param) {
                        // Get the actual argument value
                        if let Some(arg) = args.get(i) {
                            if let Some(concrete) =
                                infer_concrete_type(&arg.value, &self.type_context)
                            {
                                type_args.push(concrete);
                                break;
                            }
                        }
                    }
                }
            }
        }

        if type_args.len() == func.generic_params.len() {
            Some(type_args)
        } else {
            None
        }
    }

    /// Infer the concrete type of an expression (extended version with Tuple support).
    fn infer_concrete_type(&self, expr: &Expr) -> Option<ConcreteType> {
        // Try the shared utility first
        if let Some(ty) = infer_concrete_type(expr, &self.type_context) {
            return Some(ty);
        }

        // Handle additional cases not in shared util
        match expr {
            Expr::Tuple(elems) => {
                let elem_types: Option<Vec<_>> =
                    elems.iter().map(|e| self.infer_concrete_type(e)).collect();
                elem_types.map(ConcreteType::Tuple)
            }
            _ => None,
        }
    }

    /// Try to convert an expression to a ConcreteType (for explicit type args).
    fn expr_to_type(&self, expr: &Expr) -> Option<ConcreteType> {
        match expr {
            Expr::Identifier(name) => {
                // Common type names
                match name.as_str() {
                    "Int" | "i32" | "i64" => Some(ConcreteType::Int),
                    "Float" | "f32" | "f64" => Some(ConcreteType::Float),
                    "Bool" => Some(ConcreteType::Bool),
                    "String" | "str" => Some(ConcreteType::String),
                    _ => Some(ConcreteType::Named(name.clone())),
                }
            }
            _ => None,
        }
    }
}
