//! Monomorphization engine implementation.

use super::table::MonomorphizationTable;
use super::types::{ConcreteType, SpecializationKey};
use super::util::{ast_type_to_concrete, concrete_to_ast_type};
use simple_parser::ast::{
    Block, ClassDef, Expr, Field, FunctionDef, Module, Node, StructDef, Type as AstType,
};
use std::collections::HashMap;

/// Trait for types that have fields and methods (StructDef and ClassDef)
trait HasFieldsAndMethods {
    fn fields_mut(&mut self) -> &mut Vec<Field>;
    fn methods_mut(&mut self) -> &mut Vec<FunctionDef>;
}

impl HasFieldsAndMethods for StructDef {
    fn fields_mut(&mut self) -> &mut Vec<Field> {
        &mut self.fields
    }
    fn methods_mut(&mut self) -> &mut Vec<FunctionDef> {
        &mut self.methods
    }
}

impl HasFieldsAndMethods for ClassDef {
    fn fields_mut(&mut self) -> &mut Vec<Field> {
        &mut self.fields
    }
    fn methods_mut(&mut self) -> &mut Vec<FunctionDef> {
        &mut self.methods
    }
}

pub struct Monomorphizer<'a> {
    /// The module being processed
    #[allow(dead_code)]
    module: &'a Module,

    /// Generic function definitions (name -> def)
    pub(super) generic_functions: HashMap<String, FunctionDef>,

    /// Generic struct definitions
    pub(super) generic_structs: HashMap<String, StructDef>,

    /// Generic class definitions
    pub(super) generic_classes: HashMap<String, ClassDef>,

    /// The specialization table
    table: MonomorphizationTable,
}

impl<'a> Monomorphizer<'a> {
    /// Create a new monomorphizer for a module.
    pub fn new(module: &'a Module) -> Self {
        let mut generic_functions = HashMap::new();
        let mut generic_structs = HashMap::new();
        let mut generic_classes = HashMap::new();

        // Collect all generic definitions
        for node in &module.items {
            match node {
                Node::Function(f) if !f.generic_params.is_empty() => {
                    generic_functions.insert(f.name.clone(), f.clone());
                }
                Node::Struct(s) if !s.generic_params.is_empty() => {
                    generic_structs.insert(s.name.clone(), s.clone());
                }
                Node::Class(c) if !c.generic_params.is_empty() => {
                    generic_classes.insert(c.name.clone(), c.clone());
                }
                _ => {}
            }
        }

        Self {
            module,
            generic_functions,
            generic_structs,
            generic_classes,
            table: MonomorphizationTable::new(),
        }
    }

    /// Get the specialization table.
    pub fn table(&self) -> &MonomorphizationTable {
        &self.table
    }

    /// Get mutable access to the specialization table.
    pub fn table_mut(&mut self) -> &mut MonomorphizationTable {
        &mut self.table
    }

    /// Check if a function is generic.
    pub fn is_generic_function(&self, name: &str) -> bool {
        self.generic_functions.contains_key(name)
    }

    /// Check if a struct is generic.
    pub fn is_generic_struct(&self, name: &str) -> bool {
        self.generic_structs.contains_key(name)
    }

    /// Check if a class is generic.
    pub fn is_generic_class(&self, name: &str) -> bool {
        self.generic_classes.contains_key(name)
    }

    /// Get a generic function definition.
    pub fn get_generic_function(&self, name: &str) -> Option<&FunctionDef> {
        self.generic_functions.get(name)
    }

    /// Request specialization of a generic function call.
    ///
    /// Returns the mangled name of the specialized function.
    pub fn specialize_function_call(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
    ) -> Option<String> {
        let func = self.generic_functions.get(name)?.clone();
        Some(self.table.request_function(name, type_args, &func))
    }

    /// Process all pending specializations.
    ///
    /// This iteratively generates specialized versions until no more are needed.
    pub fn process_pending(&mut self) {
        while self.table.has_pending() {
            // Process pending functions
            while let Some((key, func)) = self.table.pop_pending_function() {
                if self.table.processed.contains(&key) {
                    continue;
                }

                let specialized = self.specialize_function(&func, &key);
                self.table.mark_processed(&key);
                self.table.add_specialized_function(key, specialized);
            }

            // Process pending structs
            while let Some((key, s)) = self.table.pop_pending_struct() {
                if self.table.processed.contains(&key) {
                    continue;
                }

                let specialized = self.specialize_struct(&s, &key);
                self.table.mark_processed(&key);
                self.table.add_specialized_struct(key, specialized);
            }

            // Process pending classes
            while let Some((key, c)) = self.table.pop_pending_class() {
                if self.table.processed.contains(&key) {
                    continue;
                }

                let specialized = self.specialize_class(&c, &key);
                self.table.mark_processed(&key);
                self.table.add_specialized_class(key, specialized);
            }
        }
    }

    /// Specialize a generic function with concrete type arguments.
    fn specialize_function(&mut self, func: &FunctionDef, key: &SpecializationKey) -> FunctionDef {
        // Build type bindings: T -> Int, U -> String, etc.
        let bindings = self.build_bindings(&func.generic_params, &key.type_args);

        // TODO: [compiler][P3] Check where clause bounds against concrete types
        // For now, where clauses are parsed but not validated during monomorphization

        // Create specialized function with mangled name
        let mut specialized = func.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear(); // No longer generic
        specialized.where_clause.clear(); // Where clause no longer needed

        // Substitute types in parameters
        for param in &mut specialized.params {
            if let Some(ty) = &param.ty {
                param.ty = Some(self.substitute_ast_type(ty, &bindings));
            }
        }

        // Substitute return type
        if let Some(ret) = &specialized.return_type {
            specialized.return_type = Some(self.substitute_ast_type(ret, &bindings));
        }

        // Substitute types in body expressions
        specialized.body = self.substitute_in_block(&specialized.body, &bindings);

        specialized
    }

    /// Substitute type parameters in a block.
    fn substitute_in_block(
        &mut self,
        block: &Block,
        bindings: &HashMap<String, ConcreteType>,
    ) -> Block {
        Block {
            span: block.span,
            statements: self.substitute_in_nodes(&block.statements, bindings),
        }
    }

    /// Helper to substitute types in fields and methods
    fn substitute_in_fields_and_methods<T>(
        &mut self,
        item: &mut T,
        bindings: &HashMap<String, ConcreteType>,
    ) where
        T: HasFieldsAndMethods,
    {
        // Substitute types in fields
        for field in item.fields_mut() {
            field.ty = self.substitute_ast_type(&field.ty, bindings);
        }

        // Substitute types in methods
        for method in item.methods_mut() {
            for param in &mut method.params {
                if let Some(ty) = &param.ty {
                    param.ty = Some(self.substitute_ast_type(ty, bindings));
                }
            }
            if let Some(ret) = &method.return_type {
                method.return_type = Some(self.substitute_ast_type(ret, bindings));
            }
        }
    }

    /// Specialize a generic struct.
    fn specialize_struct(&mut self, s: &StructDef, key: &SpecializationKey) -> StructDef {
        let bindings = self.build_bindings(&s.generic_params, &key.type_args);

        let mut specialized = s.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear();
        specialized.where_clause.clear();

        self.substitute_in_fields_and_methods(&mut specialized, &bindings);

        specialized
    }

    /// Specialize a generic class.
    fn specialize_class(&mut self, c: &ClassDef, key: &SpecializationKey) -> ClassDef {
        let bindings = self.build_bindings(&c.generic_params, &key.type_args);

        let mut specialized = c.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear();
        specialized.where_clause.clear();

        self.substitute_in_fields_and_methods(&mut specialized, &bindings);

        // Class methods need body substitution too
        for method in &mut specialized.methods {
            method.body = self.substitute_in_block(&method.body, &bindings);
        }

        specialized
    }

    /// Build type bindings from generic params and concrete args.
    fn build_bindings(
        &self,
        params: &[String],
        args: &[ConcreteType],
    ) -> HashMap<String, ConcreteType> {
        params
            .iter()
            .zip(args.iter())
            .map(|(p, a)| (p.clone(), a.clone()))
            .collect()
    }

    /// Substitute type parameters in an AST type.
    fn substitute_ast_type(
        &mut self,
        ty: &AstType,
        bindings: &HashMap<String, ConcreteType>,
    ) -> AstType {
        match ty {
            AstType::Simple(name) => {
                if let Some(concrete) = bindings.get(name) {
                    concrete_to_ast_type(concrete)
                } else {
                    ty.clone()
                }
            }
            AstType::Generic { name, args } => {
                // If this is a type parameter, substitute it
                if let Some(concrete) = bindings.get(name) {
                    return concrete_to_ast_type(concrete);
                }

                // Otherwise, substitute in the arguments
                let new_args = args
                    .iter()
                    .map(|a| self.substitute_ast_type(a, bindings))
                    .collect();

                // Check if this is a generic type that needs specialization
                if self.is_generic_struct(name) || self.is_generic_class(name) {
                    let concrete_args: Vec<ConcreteType> = args
                        .iter()
                        .map(|a| ast_type_to_concrete(a, bindings))
                        .collect();

                    // Request specialization
                    if self.is_generic_struct(name) {
                        if let Some(s) = self.generic_structs.get(name).cloned() {
                            self.table.request_struct(name, concrete_args.clone(), &s);
                        }
                    } else if let Some(c) = self.generic_classes.get(name).cloned() {
                        self.table.request_class(name, concrete_args.clone(), &c);
                    }

                    // Return the mangled name
                    let key = SpecializationKey::new(name, concrete_args);
                    AstType::Simple(key.mangled_name())
                } else {
                    AstType::Generic {
                        name: name.clone(),
                        args: new_args,
                    }
                }
            }
            AstType::Tuple(elems) => AstType::Tuple(
                elems
                    .iter()
                    .map(|e| self.substitute_ast_type(e, bindings))
                    .collect(),
            ),
            AstType::Array { element, size } => AstType::Array {
                element: Box::new(self.substitute_ast_type(element, bindings)),
                size: size.clone(),
            },
            AstType::Function { params, ret } => AstType::Function {
                params: params
                    .iter()
                    .map(|p| self.substitute_ast_type(p, bindings))
                    .collect(),
                ret: ret
                    .as_ref()
                    .map(|r| Box::new(self.substitute_ast_type(r, bindings))),
            },
            AstType::Pointer { kind, inner } => AstType::Pointer {
                kind: *kind,
                inner: Box::new(self.substitute_ast_type(inner, bindings)),
            },
            AstType::Optional(inner) => {
                AstType::Optional(Box::new(self.substitute_ast_type(inner, bindings)))
            }
            AstType::Union(types) => AstType::Union(
                types
                    .iter()
                    .map(|t| self.substitute_ast_type(t, bindings))
                    .collect(),
            ),
            AstType::Constructor { target, args } => AstType::Constructor {
                target: Box::new(self.substitute_ast_type(target, bindings)),
                args: args.as_ref().map(|a| {
                    a.iter()
                        .map(|t| self.substitute_ast_type(t, bindings))
                        .collect()
                }),
            },
            AstType::Simd { lanes, element } => AstType::Simd {
                lanes: *lanes,
                element: Box::new(self.substitute_ast_type(element, bindings)),
            },
            AstType::Capability { capability, inner } => AstType::Capability {
                capability: *capability,
                inner: Box::new(self.substitute_ast_type(inner, bindings)),
            },
            // dyn Trait doesn't have type parameters to substitute
            AstType::DynTrait(trait_name) => AstType::DynTrait(trait_name.clone()),
            // Unit with repr doesn't have type parameters to substitute
            AstType::UnitWithRepr {
                name,
                repr,
                constraints,
            } => AstType::UnitWithRepr {
                name: name.clone(),
                repr: repr.clone(),
                constraints: constraints.clone(),
            },
        }
    }

    /// Substitute type parameters in AST nodes.
    fn substitute_in_nodes(
        &mut self,
        nodes: &[Node],
        bindings: &HashMap<String, ConcreteType>,
    ) -> Vec<Node> {
        nodes
            .iter()
            .map(|n| self.substitute_in_node(n, bindings))
            .collect()
    }

    /// Substitute type parameters in a single node.
    fn substitute_in_node(
        &mut self,
        node: &Node,
        bindings: &HashMap<String, ConcreteType>,
    ) -> Node {
        match node {
            Node::Let(let_stmt) => {
                let mut new_let = let_stmt.clone();
                if let Some(ty) = &let_stmt.ty {
                    new_let.ty = Some(self.substitute_ast_type(ty, bindings));
                }
                if let Some(value) = &let_stmt.value {
                    new_let.value = Some(self.substitute_in_expr(value, bindings));
                }
                Node::Let(new_let)
            }
            Node::Expression(expr) => Node::Expression(self.substitute_in_expr(expr, bindings)),
            Node::Return(ret) => {
                let mut new_ret = ret.clone();
                if let Some(val) = &ret.value {
                    new_ret.value = Some(self.substitute_in_expr(val, bindings));
                }
                Node::Return(new_ret)
            }
            Node::If(if_stmt) => {
                let mut new_if = if_stmt.clone();
                new_if.condition = self.substitute_in_expr(&if_stmt.condition, bindings);
                new_if.then_block = self.substitute_in_block(&if_stmt.then_block, bindings);
                new_if.elif_branches = if_stmt
                    .elif_branches
                    .iter()
                    .map(|(cond, block)| {
                        (
                            self.substitute_in_expr(cond, bindings),
                            self.substitute_in_block(block, bindings),
                        )
                    })
                    .collect();
                new_if.else_block = if_stmt
                    .else_block
                    .as_ref()
                    .map(|b| self.substitute_in_block(b, bindings));
                Node::If(new_if)
            }
            Node::While(while_stmt) => {
                let mut new_while = while_stmt.clone();
                new_while.condition = self.substitute_in_expr(&while_stmt.condition, bindings);
                new_while.body = self.substitute_in_block(&while_stmt.body, bindings);
                Node::While(new_while)
            }
            Node::For(for_stmt) => {
                let mut new_for = for_stmt.clone();
                new_for.iterable = self.substitute_in_expr(&for_stmt.iterable, bindings);
                new_for.body = self.substitute_in_block(&for_stmt.body, bindings);
                Node::For(new_for)
            }
            // Pass through other nodes
            _ => node.clone(),
        }
    }

    /// Substitute type parameters in an expression.
    ///
    /// This recursively traverses the expression tree and replaces type parameters
    /// with their concrete types. For calls to generic functions, it requests
    /// specialization and rewrites the call to use the mangled name.
    fn substitute_in_expr(
        &mut self,
        expr: &Expr,
        bindings: &HashMap<String, ConcreteType>,
    ) -> Expr {
        match expr {
            // Function calls - check for generic function calls
            Expr::Call { callee, args } => {
                // Substitute in the callee and arguments
                Expr::Call {
                    callee: Box::new(self.substitute_in_expr(callee, bindings)),
                    args: args
                        .iter()
                        .map(|a| simple_parser::ast::Argument {
                            name: a.name.clone(),
                            value: self.substitute_in_expr(&a.value, bindings),
                        })
                        .collect(),
                }
            }
            // Binary operations
            Expr::Binary { op, left, right } => Expr::Binary {
                op: *op,
                left: Box::new(self.substitute_in_expr(left, bindings)),
                right: Box::new(self.substitute_in_expr(right, bindings)),
            },
            // Unary operations
            Expr::Unary { op, operand } => Expr::Unary {
                op: *op,
                operand: Box::new(self.substitute_in_expr(operand, bindings)),
            },
            // Method calls
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => Expr::MethodCall {
                receiver: Box::new(self.substitute_in_expr(receiver, bindings)),
                method: method.clone(),
                args: args
                    .iter()
                    .map(|a| simple_parser::ast::Argument {
                        name: a.name.clone(),
                        value: self.substitute_in_expr(&a.value, bindings),
                    })
                    .collect(),
            },
            // Field access
            Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
                receiver: Box::new(self.substitute_in_expr(receiver, bindings)),
                field: field.clone(),
            },
            // Index access
            Expr::Index { receiver, index } => Expr::Index {
                receiver: Box::new(self.substitute_in_expr(receiver, bindings)),
                index: Box::new(self.substitute_in_expr(index, bindings)),
            },
            // Array literal
            Expr::Array(elems) => Expr::Array(
                elems
                    .iter()
                    .map(|e| self.substitute_in_expr(e, bindings))
                    .collect(),
            ),
            // Tuple literal
            Expr::Tuple(elems) => Expr::Tuple(
                elems
                    .iter()
                    .map(|e| self.substitute_in_expr(e, bindings))
                    .collect(),
            ),
            // Dict literal
            Expr::Dict(pairs) => Expr::Dict(
                pairs
                    .iter()
                    .map(|(k, v)| {
                        (
                            self.substitute_in_expr(k, bindings),
                            self.substitute_in_expr(v, bindings),
                        )
                    })
                    .collect(),
            ),
            // Lambda expression
            Expr::Lambda {
                params,
                body,
                move_mode,
            } => {
                let new_params: Vec<simple_parser::ast::LambdaParam> = params
                    .iter()
                    .map(|p| simple_parser::ast::LambdaParam {
                        name: p.name.clone(),
                        ty: p.ty.as_ref().map(|t| self.substitute_ast_type(t, bindings)),
                    })
                    .collect();

                Expr::Lambda {
                    params: new_params,
                    body: Box::new(self.substitute_in_expr(body, bindings)),
                    move_mode: *move_mode,
                }
            }
            // If expression
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: Box::new(self.substitute_in_expr(condition, bindings)),
                then_branch: Box::new(self.substitute_in_expr(then_branch, bindings)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(self.substitute_in_expr(e, bindings))),
            },
            // Match expression
            Expr::Match { subject, arms } => Expr::Match {
                subject: Box::new(self.substitute_in_expr(subject, bindings)),
                arms: arms
                    .iter()
                    .map(|arm| simple_parser::ast::MatchArm {
                        span: arm.span,
                        pattern: arm.pattern.clone(),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|g| self.substitute_in_expr(g, bindings)),
                        body: self.substitute_in_block(&arm.body, bindings),
                    })
                    .collect(),
            },
            // Literals and identifiers don't need substitution
            _ => expr.clone(),
        }
    }
}
