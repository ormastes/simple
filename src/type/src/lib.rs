use std::collections::HashMap;
use simple_parser::ast::{Node, Expr, BinOp, Pattern};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Str,
    Float,
    Nil,
    Var(usize),
    Function { params: Vec<Type>, ret: Box<Type> },
    Array(Box<Type>),
}

#[derive(Debug)]
pub enum TypeError {
    Mismatch { expected: Type, found: Type },
    Undefined(String),
    Other(String),
}

pub struct TypeChecker {
    env: HashMap<String, Type>,
    next_var: usize,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
            next_var: 0,
        }
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    pub fn check_items(&mut self, items: &[Node]) -> Result<(), TypeError> {
        // Register built-in functions
        let range_ty = self.fresh_var();
        self.env.insert("range".to_string(), range_ty);
        let print_ty = self.fresh_var();
        self.env.insert("print".to_string(), print_ty);
        let len_ty = self.fresh_var();
        self.env.insert("len".to_string(), len_ty);

        // First pass: register all function, class, struct names
        for item in items {
            match item {
                Node::Function(func) => {
                    let ty = self.fresh_var();
                    self.env.insert(func.name.clone(), ty);
                }
                Node::Class(class) => {
                    let ty = self.fresh_var();
                    self.env.insert(class.name.clone(), ty);
                }
                Node::Struct(s) => {
                    let ty = self.fresh_var();
                    self.env.insert(s.name.clone(), ty);
                }
                Node::Enum(e) => {
                    let ty = self.fresh_var();
                    self.env.insert(e.name.clone(), ty);
                }
                _ => {}
            }
        }
        // Second pass: check all nodes
        for item in items {
            self.check_node(item)?;
        }
        Ok(())
    }

    fn check_node(&mut self, node: &Node) -> Result<(), TypeError> {
        match node {
            Node::Let(let_stmt) => {
                if let Some(expr) = &let_stmt.value {
                    let ty = self.infer_expr(expr)?;
                    if let Pattern::Identifier(name) = &let_stmt.pattern {
                        self.env.insert(name.clone(), ty);
                    }
                }
                Ok(())
            }
            Node::Assignment(assign) => {
                let _ = self.infer_expr(&assign.value)?;
                Ok(())
            }
            Node::Function(func) => {
                let old_env = self.env.clone();
                for param in &func.params {
                    let ty = self.fresh_var();
                    self.env.insert(param.name.clone(), ty);
                }
                for stmt in &func.body.statements {
                    self.check_node(stmt)?;
                }
                self.env = old_env;
                Ok(())
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(())
            }
            Node::Expression(expr) => {
                let _ = self.infer_expr(expr)?;
                Ok(())
            }
            Node::If(if_stmt) => {
                let _ = self.infer_expr(&if_stmt.condition)?;
                for stmt in &if_stmt.then_block.statements {
                    self.check_node(stmt)?;
                }
                for (cond, block) in &if_stmt.elif_branches {
                    let _ = self.infer_expr(cond)?;
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                if let Some(block) = &if_stmt.else_block {
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(())
            }
            Node::While(while_stmt) => {
                let _ = self.infer_expr(&while_stmt.condition)?;
                for stmt in &while_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::For(for_stmt) => {
                let _ = self.infer_expr(&for_stmt.iterable)?;
                if let Pattern::Identifier(name) = &for_stmt.pattern {
                    let ty = self.fresh_var();
                    self.env.insert(name.clone(), ty);
                }
                for stmt in &for_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::Loop(loop_stmt) => {
                for stmt in &loop_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::Match(match_stmt) => {
                let _ = self.infer_expr(&match_stmt.subject)?;
                for arm in &match_stmt.arms {
                    self.bind_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        let _ = self.infer_expr(guard)?;
                    }
                    for stmt in &arm.body.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Identifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::MutIdentifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::Tuple(patterns) | Pattern::Array(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Struct { fields, .. } => {
                for (_, p) in fields {
                    self.bind_pattern(p);
                }
            }
            Pattern::Enum { payload, .. } => {
                if let Some(patterns) = payload {
                    for p in patterns {
                        self.bind_pattern(p);
                    }
                }
            }
            Pattern::Or(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Typed { pattern, .. } => {
                self.bind_pattern(pattern);
            }
            _ => {}
        }
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Integer(_) => Ok(Type::Int),
            Expr::Float(_) => Ok(Type::Float),
            Expr::String(_) => Ok(Type::Str),
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Nil => Ok(Type::Nil),
            Expr::Identifier(name) => {
                self.env.get(name).cloned().ok_or_else(|| {
                    TypeError::Undefined(format!("undefined identifier: {}", name))
                })
            }
            Expr::Binary { left, right, .. } => {
                let _ = self.infer_expr(left)?;
                let _ = self.infer_expr(right)?;
                Ok(self.fresh_var())
            }
            Expr::Unary { operand, .. } => self.infer_expr(operand),
            Expr::Call { callee, args } => {
                let _ = self.infer_expr(callee)?;
                for arg in args {
                    let _ = self.infer_expr(&arg.value)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Array(items) => {
                for item in items {
                    let _ = self.infer_expr(item)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Index { receiver, index } => {
                let _ = self.infer_expr(receiver)?;
                let _ = self.infer_expr(index)?;
                Ok(self.fresh_var())
            }
            Expr::If { condition, then_branch, else_branch } => {
                let _ = self.infer_expr(condition)?;
                let then_ty = self.infer_expr(then_branch)?;
                if let Some(else_b) = else_branch {
                    let _ = self.infer_expr(else_b)?;
                }
                Ok(then_ty)
            }
            Expr::Match { subject, arms } => {
                let _ = self.infer_expr(subject)?;
                let result_ty = self.fresh_var();
                for arm in arms {
                    self.bind_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        let _ = self.infer_expr(guard)?;
                    }
                    for stmt in &arm.body.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(result_ty)
            }
            Expr::FieldAccess { receiver, .. } => {
                let _ = self.infer_expr(receiver)?;
                Ok(self.fresh_var())
            }
            Expr::MethodCall { receiver, args, .. } => {
                let _ = self.infer_expr(receiver)?;
                for arg in args {
                    let _ = self.infer_expr(&arg.value)?;
                }
                Ok(self.fresh_var())
            }
            Expr::StructInit { fields, .. } => {
                for (_, expr) in fields {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Path(_) => Ok(self.fresh_var()),
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    let _ = self.infer_expr(s)?;
                }
                if let Some(e) = end {
                    let _ = self.infer_expr(e)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Dict(entries) => {
                for (k, v) in entries {
                    let _ = self.infer_expr(k)?;
                    let _ = self.infer_expr(v)?;
                }
                Ok(self.fresh_var())
            }
            _ => Ok(self.fresh_var()),
        }
    }
}

/// Check a list of AST nodes for type errors
pub fn check(items: &[Node]) -> Result<(), TypeError> {
    let mut checker = TypeChecker::new();
    checker.check_items(items)
}
