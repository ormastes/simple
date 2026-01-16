//! Module rewriter for applying monomorphization.

use super::analyzer::CallSiteAnalyzer;
use super::engine::Monomorphizer;
use super::types::ConcreteType;
use super::util::{infer_concrete_type, type_uses_param};
use simple_parser::ast::{Block, Expr, FunctionDef, Module, Node};
use std::collections::HashMap;

/// Convenience function to analyze a module and run monomorphization.
///
/// Returns a new module with all generic functions specialized.
pub fn monomorphize_module(module: &Module) -> Module {
    // Step 1: Collect call sites
    let analyzer = CallSiteAnalyzer::new(module);
    let call_sites = analyzer.analyze();

    // If no generic calls found, return original module unchanged
    if call_sites.is_empty() {
        return module.clone();
    }

    // Step 2: Create monomorphizer and request specializations
    let mut mono = Monomorphizer::new(module);

    // Build a mapping from (name, type_args) to mangled name for rewriting
    let mut call_rewrites: HashMap<String, Vec<(Vec<ConcreteType>, String)>> = HashMap::new();

    for (name, type_args) in call_sites {
        if let Some(mangled) = mono.specialize_function_call(&name, type_args.clone()) {
            call_rewrites.entry(name).or_default().push((type_args, mangled));
        }
    }

    // Step 3: Process all pending specializations
    mono.process_pending();

    // Step 4: Create new module with rewritten calls and specialized functions
    let rewriter = CallSiteRewriter::new(&mono.generic_functions, &call_rewrites);
    let mut new_items = Vec::new();

    // Add all non-generic items from original module with rewritten calls
    for item in &module.items {
        match item {
            Node::Function(f) if !f.generic_params.is_empty() => {
                // Skip generic function definitions (they're replaced by specializations)
            }
            _ => new_items.push(rewriter.rewrite_node(item)),
        }
    }

    // Add all specialized functions
    for (_key, func) in mono.table().specialized_functions() {
        new_items.push(Node::Function(func.clone()));
    }

    Module {
        name: module.name.clone(),
        items: new_items,
    }
}

/// Rewrites call sites to use mangled names for specialized generic functions.
struct CallSiteRewriter<'a> {
    /// Generic function definitions (name -> def) for looking up param info
    generic_functions: &'a HashMap<String, FunctionDef>,
    /// Mapping from function name to list of (type_args, mangled_name)
    call_rewrites: &'a HashMap<String, Vec<(Vec<ConcreteType>, String)>>,
}

impl<'a> CallSiteRewriter<'a> {
    fn new(
        generic_functions: &'a HashMap<String, FunctionDef>,
        call_rewrites: &'a HashMap<String, Vec<(Vec<ConcreteType>, String)>>,
    ) -> Self {
        Self {
            generic_functions,
            call_rewrites,
        }
    }

    fn rewrite_node(&self, node: &Node) -> Node {
        match node {
            Node::Assignment(assign) => {
                let mut new_assign = assign.clone();
                new_assign.value = self.rewrite_expr(&assign.value);
                Node::Assignment(new_assign)
            }
            Node::Let(let_stmt) => {
                let mut new_let = let_stmt.clone();
                if let Some(value) = &let_stmt.value {
                    new_let.value = Some(self.rewrite_expr(value));
                }
                Node::Let(new_let)
            }
            Node::Expression(expr) => Node::Expression(self.rewrite_expr(expr)),
            Node::Return(ret) => {
                let mut new_ret = ret.clone();
                if let Some(value) = &ret.value {
                    new_ret.value = Some(self.rewrite_expr(value));
                }
                Node::Return(new_ret)
            }
            Node::If(if_stmt) => {
                let mut new_if = if_stmt.clone();
                new_if.condition = self.rewrite_expr(&if_stmt.condition);
                new_if.then_block = self.rewrite_block(&if_stmt.then_block);
                new_if.elif_branches = if_stmt
                    .elif_branches
                    .iter()
                    .map(|(cond, block)| (self.rewrite_expr(cond), self.rewrite_block(block)))
                    .collect();
                new_if.else_block = if_stmt.else_block.as_ref().map(|b| self.rewrite_block(b));
                Node::If(new_if)
            }
            Node::While(while_stmt) => {
                let mut new_while = while_stmt.clone();
                new_while.condition = self.rewrite_expr(&while_stmt.condition);
                new_while.body = self.rewrite_block(&while_stmt.body);
                Node::While(new_while)
            }
            Node::For(for_stmt) => {
                let mut new_for = for_stmt.clone();
                new_for.iterable = self.rewrite_expr(&for_stmt.iterable);
                new_for.body = self.rewrite_block(&for_stmt.body);
                Node::For(new_for)
            }
            Node::Function(f) if f.generic_params.is_empty() => {
                let mut new_func = f.clone();
                new_func.body = self.rewrite_block(&f.body);
                Node::Function(new_func)
            }
            _ => node.clone(),
        }
    }

    fn rewrite_block(&self, block: &Block) -> Block {
        Block {
            span: block.span,
            statements: block.statements.iter().map(|n| self.rewrite_node(n)).collect(),
        }
    }

    fn rewrite_expr(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Call { callee, args } => {
                // Check if this is a call to a generic function
                if let Expr::Identifier(name) = callee.as_ref() {
                    if let Some(rewrites) = self.call_rewrites.get(name) {
                        if let Some(func_def) = self.generic_functions.get(name) {
                            // Infer the type arguments from the call arguments
                            if let Some(type_args) = self.infer_type_args(func_def, args) {
                                // Find matching mangled name
                                for (expected_args, mangled) in rewrites {
                                    if &type_args == expected_args {
                                        // Rewrite call to use mangled name
                                        return Expr::Call {
                                            callee: Box::new(Expr::Identifier(mangled.clone())),
                                            args: args
                                                .iter()
                                                .map(|a| simple_parser::ast::Argument {
                                                    name: a.name.clone(),
                                                    value: self.rewrite_expr(&a.value),
                                                })
                                                .collect(),
                                        };
                                    }
                                }
                            }
                        }
                    }
                }
                // Not a generic call or couldn't rewrite, just recurse
                Expr::Call {
                    callee: Box::new(self.rewrite_expr(callee)),
                    args: args
                        .iter()
                        .map(|a| simple_parser::ast::Argument {
                            name: a.name.clone(),
                            value: self.rewrite_expr(&a.value),
                        })
                        .collect(),
                }
            }
            // Recursively rewrite sub-expressions
            Expr::Binary { op, left, right } => Expr::Binary {
                op: *op,
                left: Box::new(self.rewrite_expr(left)),
                right: Box::new(self.rewrite_expr(right)),
            },
            Expr::Unary { op, operand } => Expr::Unary {
                op: *op,
                operand: Box::new(self.rewrite_expr(operand)),
            },
            Expr::MethodCall { receiver, method, args } => Expr::MethodCall {
                receiver: Box::new(self.rewrite_expr(receiver)),
                method: method.clone(),
                args: args
                    .iter()
                    .map(|a| simple_parser::ast::Argument {
                        name: a.name.clone(),
                        value: self.rewrite_expr(&a.value),
                    })
                    .collect(),
            },
            Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
                receiver: Box::new(self.rewrite_expr(receiver)),
                field: field.clone(),
            },
            Expr::Index { receiver, index } => Expr::Index {
                receiver: Box::new(self.rewrite_expr(receiver)),
                index: Box::new(self.rewrite_expr(index)),
            },
            Expr::Array(elems) => Expr::Array(elems.iter().map(|e| self.rewrite_expr(e)).collect()),
            Expr::Tuple(elems) => Expr::Tuple(elems.iter().map(|e| self.rewrite_expr(e)).collect()),
            Expr::Dict(pairs) => Expr::Dict(
                pairs
                    .iter()
                    .map(|(k, v)| (self.rewrite_expr(k), self.rewrite_expr(v)))
                    .collect(),
            ),
            Expr::Lambda {
                params,
                body,
                move_mode,
                capture_all,
            } => Expr::Lambda {
                params: params.clone(),
                body: Box::new(self.rewrite_expr(body)),
                move_mode: *move_mode,
                capture_all: *capture_all,
            },
            Expr::If {
                let_pattern,
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                let_pattern: let_pattern.clone(),
                condition: Box::new(self.rewrite_expr(condition)),
                then_branch: Box::new(self.rewrite_expr(then_branch)),
                else_branch: else_branch.as_ref().map(|e| Box::new(self.rewrite_expr(e))),
            },
            // Literals and identifiers don't need rewriting
            _ => expr.clone(),
        }
    }

    /// Infer type arguments from call arguments (same logic as CallSiteAnalyzer).
    fn infer_type_args(&self, func: &FunctionDef, args: &[simple_parser::ast::Argument]) -> Option<Vec<ConcreteType>> {
        let mut type_args = Vec::new();

        for type_param in &func.generic_params {
            for (i, param) in func.params.iter().enumerate() {
                if let Some(ty) = &param.ty {
                    if type_uses_param(ty, type_param) {
                        if let Some(arg) = args.get(i) {
                            // Rewriter doesn't have type context, use empty map
                            if let Some(concrete) = infer_concrete_type(&arg.value, &HashMap::new()) {
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
}
