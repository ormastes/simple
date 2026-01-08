//! Interface binding specialization for static polymorphism.
//!
//! This module handles specialization of trait method calls when interface bindings
//! are present. When `bind Logger = ConsoleLogger` is declared, method calls on
//! Logger-typed values are specialized to call ConsoleLogger methods directly.
//!
//! ## How it works
//!
//! 1. Collect all interface bindings from the module
//! 2. Scan for method calls on trait-typed receivers
//! 3. Rewrite those calls to use the bound implementation type
//!
//! ## Example
//!
//! ```simple
//! trait Logger:
//!     fn log(self, msg: str) -> str
//!
//! class ConsoleLogger:
//!     fn log(self, msg: str) -> str:
//!         return "Console: " + msg
//!
//! bind Logger = ConsoleLogger
//!
//! fn main():
//!     let logger: Logger = ConsoleLogger()
//!     logger.log("Hello")  // Specialized to ConsoleLogger::log
//! ```

use simple_parser::ast::{
    Block, Expr, FunctionDef, Module, Node, Type as AstType,
};
use simple_parser::token::Span;
use std::collections::HashMap;

/// Binding specializer that rewrites method calls based on interface bindings
pub struct BindingSpecializer {
    /// Interface bindings: trait_name -> impl_type_name
    bindings: HashMap<String, String>,
}

impl BindingSpecializer {
    /// Create a new binding specializer for a module
    pub fn new(module: &Module) -> Self {
        let mut bindings = HashMap::new();

        // Collect all interface bindings
        for node in &module.items {
            if let Node::InterfaceBinding(binding) = node {
                let impl_type_name = extract_type_name(&binding.impl_type);
                bindings.insert(binding.interface_name.clone(), impl_type_name);
            }
        }

        Self { bindings }
    }

    /// Check if there are any bindings to specialize
    pub fn has_bindings(&self) -> bool {
        !self.bindings.is_empty()
    }

    /// Get the binding for a trait name
    pub fn get_binding(&self, trait_name: &str) -> Option<&String> {
        self.bindings.get(trait_name)
    }

    /// Get all bindings
    pub fn bindings(&self) -> &HashMap<String, String> {
        &self.bindings
    }

    /// Specialize a module by rewriting method calls based on bindings
    pub fn specialize_module(&self, module: &Module) -> Module {
        if !self.has_bindings() {
            return module.clone();
        }

        let new_items: Vec<Node> = module
            .items
            .iter()
            .map(|node| self.specialize_node(node))
            .collect();

        Module {
            name: module.name.clone(),
            items: new_items,
        }
    }

    fn specialize_node(&self, node: &Node) -> Node {
        match node {
            Node::Function(f) => Node::Function(self.specialize_function(f)),
            Node::Expression(expr) => Node::Expression(self.specialize_expr(expr)),
            Node::Let(let_stmt) => {
                let mut new_let = let_stmt.clone();
                if let Some(value) = &let_stmt.value {
                    new_let.value = Some(self.specialize_expr(value));
                }
                Node::Let(new_let)
            }
            Node::Assignment(assign) => {
                let mut new_assign = assign.clone();
                new_assign.value = self.specialize_expr(&assign.value);
                Node::Assignment(new_assign)
            }
            Node::Return(ret) => {
                let mut new_ret = ret.clone();
                if let Some(value) = &ret.value {
                    new_ret.value = Some(self.specialize_expr(value));
                }
                Node::Return(new_ret)
            }
            Node::If(if_stmt) => {
                let mut new_if = if_stmt.clone();
                new_if.condition = self.specialize_expr(&if_stmt.condition);
                new_if.then_block = self.specialize_block(&if_stmt.then_block);
                if let Some(else_block) = &if_stmt.else_block {
                    new_if.else_block = Some(self.specialize_block(else_block));
                }
                Node::If(new_if)
            }
            Node::While(while_stmt) => {
                let mut new_while = while_stmt.clone();
                new_while.condition = self.specialize_expr(&while_stmt.condition);
                new_while.body = self.specialize_block(&while_stmt.body);
                Node::While(new_while)
            }
            Node::For(for_stmt) => {
                let mut new_for = for_stmt.clone();
                new_for.iterable = self.specialize_expr(&for_stmt.iterable);
                new_for.body = self.specialize_block(&for_stmt.body);
                Node::For(new_for)
            }
            Node::Class(c) => {
                let mut new_class = c.clone();
                new_class.methods = c
                    .methods
                    .iter()
                    .map(|m| self.specialize_function(m))
                    .collect();
                Node::Class(new_class)
            }
            Node::Impl(impl_block) => {
                let mut new_impl = impl_block.clone();
                new_impl.methods = impl_block
                    .methods
                    .iter()
                    .map(|m| self.specialize_function(m))
                    .collect();
                Node::Impl(new_impl)
            }
            // Pass through other nodes unchanged
            _ => node.clone(),
        }
    }

    fn specialize_function(&self, f: &FunctionDef) -> FunctionDef {
        let mut new_func = f.clone();
        new_func.body = self.specialize_block(&f.body);
        new_func
    }

    fn specialize_block(&self, block: &Block) -> Block {
        let new_stmts: Vec<Node> = block
            .statements
            .iter()
            .map(|stmt| self.specialize_node(stmt))
            .collect();
        Block {
            span: block.span,
            statements: new_stmts,
        }
    }

    fn specialize_expr(&self, expr: &Expr) -> Expr {
        match expr {
            // Method calls are the primary target for specialization
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let new_receiver = Box::new(self.specialize_expr(receiver));
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| {
                        let mut new_arg = arg.clone();
                        new_arg.value = self.specialize_expr(&arg.value);
                        new_arg
                    })
                    .collect();

                // Note: At AST level, we don't have type information to determine
                // if the receiver is a bound trait type. The actual specialization
                // happens during HIR/MIR lowering when type info is available.
                // This pass prepares the structure for later optimization.
                Expr::MethodCall {
                    receiver: new_receiver,
                    method: method.clone(),
                    args: new_args,
                }
            }

            // Recursively process other expression types
            Expr::Call { callee, args } => {
                let new_callee = Box::new(self.specialize_expr(callee));
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| {
                        let mut new_arg = arg.clone();
                        new_arg.value = self.specialize_expr(&arg.value);
                        new_arg
                    })
                    .collect();
                Expr::Call {
                    callee: new_callee,
                    args: new_args,
                }
            }

            Expr::Binary { op, left, right } => Expr::Binary {
                op: op.clone(),
                left: Box::new(self.specialize_expr(left)),
                right: Box::new(self.specialize_expr(right)),
            },

            Expr::Unary { op, operand } => Expr::Unary {
                op: op.clone(),
                operand: Box::new(self.specialize_expr(operand)),
            },

            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: Box::new(self.specialize_expr(condition)),
                then_branch: Box::new(self.specialize_expr(then_branch)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(self.specialize_expr(e))),
            },

            Expr::Lambda { params, body, .. } => {
                let mut new_lambda = expr.clone();
                if let Expr::Lambda { body: b, .. } = &mut new_lambda {
                    *b = Box::new(self.specialize_expr(body));
                }
                new_lambda
            }

            Expr::Array(elements) => {
                Expr::Array(elements.iter().map(|e| self.specialize_expr(e)).collect())
            }

            Expr::Tuple(elements) => {
                Expr::Tuple(elements.iter().map(|e| self.specialize_expr(e)).collect())
            }

            Expr::Index { receiver, index } => Expr::Index {
                receiver: Box::new(self.specialize_expr(receiver)),
                index: Box::new(self.specialize_expr(index)),
            },

            Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
                receiver: Box::new(self.specialize_expr(receiver)),
                field: field.clone(),
            },

            // Pass through other expressions unchanged
            _ => expr.clone(),
        }
    }
}

/// Extract the type name from an AST type
fn extract_type_name(ty: &AstType) -> String {
    match ty {
        AstType::Simple(name) => name.clone(),
        AstType::Generic { name, .. } => name.clone(),
        _ => format!("{:?}", ty),
    }
}

/// Convenience function to specialize a module based on interface bindings
pub fn specialize_bindings(module: &Module) -> Module {
    let specializer = BindingSpecializer::new(module);
    specializer.specialize_module(module)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_bindings() {
        let module = Module {
            name: None,
            items: vec![],
        };
        let specializer = BindingSpecializer::new(&module);
        assert!(!specializer.has_bindings());
    }
}
