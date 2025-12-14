//! Monomorphization engine for generic functions and types.
//!
//! This module handles the specialization of generic code by creating
//! concrete instances for each unique combination of type arguments.
//!
//! ## How it works
//!
//! 1. During type checking, generic function/struct calls are recorded
//! 2. The monomorphization pass generates specialized versions
//! 3. HIR/MIR lowering uses the specialized versions
//!
//! ## Example
//!
//! ```simple
//! fn identity[T](x: T) -> T:
//!     return x
//!
//! main = identity[Int](42)  // Generates identity_Int
//! ```

use simple_parser::ast::{
    Block, ClassDef, Expr, FunctionDef, Module, Node, StructDef, Type as AstType,
};
#[cfg(test)]
use simple_parser::Span;
use std::collections::{HashMap, HashSet, VecDeque};

/// A unique key for a specialization.
///
/// Combines the original name with the concrete type arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpecializationKey {
    /// Original generic function/struct name
    pub name: String,
    /// Concrete type arguments (e.g., [Int, String])
    pub type_args: Vec<ConcreteType>,
}

impl SpecializationKey {
    pub fn new(name: impl Into<String>, type_args: Vec<ConcreteType>) -> Self {
        Self {
            name: name.into(),
            type_args,
        }
    }

    /// Generate a mangled name for the specialization.
    ///
    /// Example: `identity` with `[Int]` -> `identity$Int`
    pub fn mangled_name(&self) -> String {
        if self.type_args.is_empty() {
            self.name.clone()
        } else {
            let args_str = self
                .type_args
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join("_");
            format!("{}${}", self.name, args_str)
        }
    }
}

/// A concrete (non-generic) type.
///
/// This represents types after type parameters have been substituted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConcreteType {
    /// Primitive types
    Int,
    Float,
    Bool,
    String,
    Nil,

    /// Named type (struct, class, enum)
    Named(String),

    /// Array of element type
    Array(Box<ConcreteType>),

    /// Tuple of types
    Tuple(Vec<ConcreteType>),

    /// Dictionary
    Dict {
        key: Box<ConcreteType>,
        value: Box<ConcreteType>,
    },

    /// Function type
    Function {
        params: Vec<ConcreteType>,
        ret: Box<ConcreteType>,
    },

    /// Optional type
    Optional(Box<ConcreteType>),

    /// Pointer types
    Pointer {
        kind: PointerKind,
        inner: Box<ConcreteType>,
    },

    /// Specialized generic (after substitution)
    /// e.g., List[Int] becomes Specialized { name: "List", args: [Int] }
    Specialized {
        name: String,
        args: Vec<ConcreteType>,
    },
}

/// Pointer kinds for memory management.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerKind {
    Unique,
    Shared,
    Weak,
    Handle,
    Borrow,
    BorrowMut,
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteType::Int => write!(f, "Int"),
            ConcreteType::Float => write!(f, "Float"),
            ConcreteType::Bool => write!(f, "Bool"),
            ConcreteType::String => write!(f, "String"),
            ConcreteType::Nil => write!(f, "Nil"),
            ConcreteType::Named(name) => write!(f, "{}", name),
            ConcreteType::Array(elem) => write!(f, "Array_{}", elem),
            ConcreteType::Tuple(elems) => {
                let s = elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join("_");
                write!(f, "Tuple_{}", s)
            }
            ConcreteType::Dict { key, value } => write!(f, "Dict_{}_{}", key, value),
            ConcreteType::Function { params, ret } => {
                let p = params
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join("_");
                write!(f, "Fn_{}_{}", p, ret)
            }
            ConcreteType::Optional(inner) => write!(f, "Opt_{}", inner),
            ConcreteType::Pointer { kind, inner } => {
                let k = match kind {
                    PointerKind::Unique => "Unique",
                    PointerKind::Shared => "Shared",
                    PointerKind::Weak => "Weak",
                    PointerKind::Handle => "Handle",
                    PointerKind::Borrow => "Borrow",
                    PointerKind::BorrowMut => "BorrowMut",
                };
                write!(f, "{}_{}", k, inner)
            }
            ConcreteType::Specialized { name, args } => {
                let a = args
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join("_");
                write!(f, "{}_{}", name, a)
            }
        }
    }
}

/// Type bindings: maps type parameter names to concrete types.
pub type TypeBindings = HashMap<String, ConcreteType>;

/// Tracks specializations needed and generated.
#[derive(Debug, Default)]
pub struct MonomorphizationTable {
    /// Functions that need to be specialized
    pending_functions: VecDeque<(SpecializationKey, FunctionDef)>,

    /// Structs that need to be specialized
    pending_structs: VecDeque<(SpecializationKey, StructDef)>,

    /// Classes that need to be specialized
    pending_classes: VecDeque<(SpecializationKey, ClassDef)>,

    /// Already specialized functions (key -> specialized def)
    specialized_functions: HashMap<SpecializationKey, FunctionDef>,

    /// Already specialized structs
    specialized_structs: HashMap<SpecializationKey, StructDef>,

    /// Already specialized classes
    specialized_classes: HashMap<SpecializationKey, ClassDef>,

    /// Keys that have been processed (to avoid infinite loops)
    processed: HashSet<SpecializationKey>,
}

impl MonomorphizationTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Request a function specialization.
    ///
    /// Returns the mangled name for the specialization.
    pub fn request_function(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &FunctionDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_functions.contains_key(&key) {
            self.pending_functions
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Request a struct specialization.
    pub fn request_struct(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &StructDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_structs.contains_key(&key) {
            self.pending_structs
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Request a class specialization.
    pub fn request_class(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &ClassDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_classes.contains_key(&key) {
            self.pending_classes
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Check if there are pending specializations.
    pub fn has_pending(&self) -> bool {
        !self.pending_functions.is_empty()
            || !self.pending_structs.is_empty()
            || !self.pending_classes.is_empty()
    }

    /// Get the next pending function to specialize.
    pub fn pop_pending_function(&mut self) -> Option<(SpecializationKey, FunctionDef)> {
        self.pending_functions.pop_front()
    }

    /// Get the next pending struct to specialize.
    pub fn pop_pending_struct(&mut self) -> Option<(SpecializationKey, StructDef)> {
        self.pending_structs.pop_front()
    }

    /// Get the next pending class to specialize.
    pub fn pop_pending_class(&mut self) -> Option<(SpecializationKey, ClassDef)> {
        self.pending_classes.pop_front()
    }

    /// Mark a key as processed.
    pub fn mark_processed(&mut self, key: &SpecializationKey) {
        self.processed.insert(key.clone());
    }

    /// Add a specialized function.
    pub fn add_specialized_function(&mut self, key: SpecializationKey, func: FunctionDef) {
        self.specialized_functions.insert(key, func);
    }

    /// Add a specialized struct.
    pub fn add_specialized_struct(&mut self, key: SpecializationKey, s: StructDef) {
        self.specialized_structs.insert(key, s);
    }

    /// Add a specialized class.
    pub fn add_specialized_class(&mut self, key: SpecializationKey, c: ClassDef) {
        self.specialized_classes.insert(key, c);
    }

    /// Get a specialized function by key.
    pub fn get_specialized_function(&self, key: &SpecializationKey) -> Option<&FunctionDef> {
        self.specialized_functions.get(key)
    }

    /// Get all specialized functions.
    pub fn specialized_functions(
        &self,
    ) -> impl Iterator<Item = (&SpecializationKey, &FunctionDef)> {
        self.specialized_functions.iter()
    }

    /// Get all specialized structs.
    pub fn specialized_structs(&self) -> impl Iterator<Item = (&SpecializationKey, &StructDef)> {
        self.specialized_structs.iter()
    }

    /// Get all specialized classes.
    pub fn specialized_classes(&self) -> impl Iterator<Item = (&SpecializationKey, &ClassDef)> {
        self.specialized_classes.iter()
    }
}

/// The monomorphization engine.
///
/// Processes generic definitions and generates specialized versions.
pub struct Monomorphizer<'a> {
    /// The module being processed
    #[allow(dead_code)]
    module: &'a Module,

    /// Generic function definitions (name -> def)
    generic_functions: HashMap<String, FunctionDef>,

    /// Generic struct definitions
    generic_structs: HashMap<String, StructDef>,

    /// Generic class definitions
    generic_classes: HashMap<String, ClassDef>,

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

        // Create specialized function with mangled name
        let mut specialized = func.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear(); // No longer generic

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

    /// Specialize a generic struct.
    fn specialize_struct(&mut self, s: &StructDef, key: &SpecializationKey) -> StructDef {
        let bindings = self.build_bindings(&s.generic_params, &key.type_args);

        let mut specialized = s.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear();

        // Substitute types in fields
        for field in &mut specialized.fields {
            field.ty = self.substitute_ast_type(&field.ty, &bindings);
        }

        specialized
    }

    /// Specialize a generic class.
    fn specialize_class(&mut self, c: &ClassDef, key: &SpecializationKey) -> ClassDef {
        let bindings = self.build_bindings(&c.generic_params, &key.type_args);

        let mut specialized = c.clone();
        specialized.name = key.mangled_name();
        specialized.generic_params.clear();

        // Substitute types in fields
        for field in &mut specialized.fields {
            field.ty = self.substitute_ast_type(&field.ty, &bindings);
        }

        // Substitute types in methods
        for method in &mut specialized.methods {
            for param in &mut method.params {
                if let Some(ty) = &param.ty {
                    param.ty = Some(self.substitute_ast_type(ty, &bindings));
                }
            }
            if let Some(ret) = &method.return_type {
                method.return_type = Some(self.substitute_ast_type(ret, &bindings));
            }
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

//=============================================================================
// Call-Site Analysis
//=============================================================================

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
                    if self.type_uses_param(ty, type_param) {
                        // Get the actual argument value
                        if let Some(arg) = args.get(i) {
                            if let Some(concrete) = self.infer_concrete_type(&arg.value) {
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

    /// Check if a type directly uses a type parameter.
    fn type_uses_param(&self, ty: &AstType, param: &str) -> bool {
        match ty {
            AstType::Simple(name) => name == param,
            AstType::Generic { name, args } => {
                name == param || args.iter().any(|a| self.type_uses_param(a, param))
            }
            AstType::Array { element, .. } => self.type_uses_param(element, param),
            AstType::Tuple(elems) => elems.iter().any(|e| self.type_uses_param(e, param)),
            AstType::Function { params, ret } => {
                params.iter().any(|p| self.type_uses_param(p, param))
                    || ret
                        .as_ref()
                        .map_or(false, |r| self.type_uses_param(r, param))
            }
            AstType::Optional(inner) => self.type_uses_param(inner, param),
            AstType::Pointer { inner, .. } => self.type_uses_param(inner, param),
            _ => false,
        }
    }

    /// Infer the concrete type of an expression.
    fn infer_concrete_type(&self, expr: &Expr) -> Option<ConcreteType> {
        match expr {
            Expr::Integer(_) | Expr::TypedInteger(_, _) => Some(ConcreteType::Int),
            Expr::Float(_) | Expr::TypedFloat(_, _) => Some(ConcreteType::Float),
            Expr::Bool(_) => Some(ConcreteType::Bool),
            Expr::String(_) | Expr::TypedString(_, _) | Expr::FString(_) => {
                Some(ConcreteType::String)
            }
            Expr::Nil => Some(ConcreteType::Nil),
            Expr::Identifier(name) => self.type_context.get(name).cloned(),
            Expr::Array(elems) => {
                if let Some(first) = elems.first() {
                    Some(ConcreteType::Array(Box::new(
                        self.infer_concrete_type(first)?,
                    )))
                } else {
                    None
                }
            }
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
            call_rewrites
                .entry(name)
                .or_default()
                .push((type_args, mangled));
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
            statements: block
                .statements
                .iter()
                .map(|n| self.rewrite_node(n))
                .collect(),
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
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => Expr::MethodCall {
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
            } => Expr::Lambda {
                params: params.clone(),
                body: Box::new(self.rewrite_expr(body)),
                move_mode: *move_mode,
            },
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: Box::new(self.rewrite_expr(condition)),
                then_branch: Box::new(self.rewrite_expr(then_branch)),
                else_branch: else_branch.as_ref().map(|e| Box::new(self.rewrite_expr(e))),
            },
            // Literals and identifiers don't need rewriting
            _ => expr.clone(),
        }
    }

    /// Infer type arguments from call arguments (same logic as CallSiteAnalyzer).
    fn infer_type_args(
        &self,
        func: &FunctionDef,
        args: &[simple_parser::ast::Argument],
    ) -> Option<Vec<ConcreteType>> {
        let mut type_args = Vec::new();

        for type_param in &func.generic_params {
            for (i, param) in func.params.iter().enumerate() {
                if let Some(ty) = &param.ty {
                    if self.type_uses_param(ty, type_param) {
                        if let Some(arg) = args.get(i) {
                            if let Some(concrete) = self.infer_concrete_type(&arg.value) {
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

    fn type_uses_param(&self, ty: &AstType, param: &str) -> bool {
        match ty {
            AstType::Simple(name) => name == param,
            AstType::Generic { name, args } => {
                name == param || args.iter().any(|a| self.type_uses_param(a, param))
            }
            AstType::Array { element, .. } => self.type_uses_param(element, param),
            AstType::Tuple(elems) => elems.iter().any(|e| self.type_uses_param(e, param)),
            AstType::Function { params, ret } => {
                params.iter().any(|p| self.type_uses_param(p, param))
                    || ret
                        .as_ref()
                        .map_or(false, |r| self.type_uses_param(r, param))
            }
            AstType::Optional(inner) => self.type_uses_param(inner, param),
            AstType::Pointer { inner, .. } => self.type_uses_param(inner, param),
            _ => false,
        }
    }

    fn infer_concrete_type(&self, expr: &Expr) -> Option<ConcreteType> {
        match expr {
            Expr::Integer(_) | Expr::TypedInteger(_, _) => Some(ConcreteType::Int),
            Expr::Float(_) | Expr::TypedFloat(_, _) => Some(ConcreteType::Float),
            Expr::Bool(_) => Some(ConcreteType::Bool),
            Expr::String(_) | Expr::TypedString(_, _) | Expr::FString(_) => {
                Some(ConcreteType::String)
            }
            Expr::Nil => Some(ConcreteType::Nil),
            Expr::Array(elems) => {
                if let Some(first) = elems.first() {
                    Some(ConcreteType::Array(Box::new(
                        self.infer_concrete_type(first)?,
                    )))
                } else {
                    None
                }
            }
            Expr::Tuple(elems) => {
                let elem_types: Option<Vec<_>> =
                    elems.iter().map(|e| self.infer_concrete_type(e)).collect();
                elem_types.map(ConcreteType::Tuple)
            }
            _ => None,
        }
    }
}

/// Convert a ConcreteType to an AST Type.
fn concrete_to_ast_type(concrete: &ConcreteType) -> AstType {
    match concrete {
        ConcreteType::Int => AstType::Simple("Int".to_string()),
        ConcreteType::Float => AstType::Simple("Float".to_string()),
        ConcreteType::Bool => AstType::Simple("Bool".to_string()),
        ConcreteType::String => AstType::Simple("String".to_string()),
        ConcreteType::Nil => AstType::Simple("Nil".to_string()),
        ConcreteType::Named(name) => AstType::Simple(name.clone()),
        ConcreteType::Array(elem) => AstType::Array {
            element: Box::new(concrete_to_ast_type(elem)),
            size: None,
        },
        ConcreteType::Tuple(elems) => {
            AstType::Tuple(elems.iter().map(concrete_to_ast_type).collect())
        }
        ConcreteType::Dict { key, value } => {
            // Dict is represented as Generic Dict[K, V] in AST
            AstType::Generic {
                name: "Dict".to_string(),
                args: vec![concrete_to_ast_type(key), concrete_to_ast_type(value)],
            }
        }
        ConcreteType::Function { params, ret } => AstType::Function {
            params: params.iter().map(concrete_to_ast_type).collect(),
            ret: Some(Box::new(concrete_to_ast_type(ret))),
        },
        ConcreteType::Optional(inner) => AstType::Optional(Box::new(concrete_to_ast_type(inner))),
        ConcreteType::Pointer { kind, inner } => {
            let ast_kind = match kind {
                PointerKind::Unique => simple_parser::ast::PointerKind::Unique,
                PointerKind::Shared => simple_parser::ast::PointerKind::Shared,
                PointerKind::Weak => simple_parser::ast::PointerKind::Weak,
                PointerKind::Handle => simple_parser::ast::PointerKind::Handle,
                PointerKind::Borrow => simple_parser::ast::PointerKind::Borrow,
                PointerKind::BorrowMut => simple_parser::ast::PointerKind::BorrowMut,
            };
            AstType::Pointer {
                kind: ast_kind,
                inner: Box::new(concrete_to_ast_type(inner)),
            }
        }
        ConcreteType::Specialized { name, args: _ } => {
            // Specialized types are already mangled, return as simple
            AstType::Simple(name.clone())
        }
    }
}

/// Convert an AST Type to a ConcreteType.
///
/// Uses bindings to resolve type parameters.
pub fn ast_type_to_concrete(
    ty: &AstType,
    bindings: &HashMap<String, ConcreteType>,
) -> ConcreteType {
    match ty {
        AstType::Simple(name) => {
            // Check if it's a type parameter
            if let Some(concrete) = bindings.get(name) {
                return concrete.clone();
            }

            // Check for primitive types
            match name.as_str() {
                "Int" | "i32" | "i64" | "i8" | "i16" => ConcreteType::Int,
                "Float" | "f32" | "f64" => ConcreteType::Float,
                "Bool" | "bool" => ConcreteType::Bool,
                "String" | "str" => ConcreteType::String,
                "Nil" | "nil" | "()" => ConcreteType::Nil,
                _ => ConcreteType::Named(name.clone()),
            }
        }
        AstType::Generic { name, args } => {
            // Check if the name itself is a type parameter
            if let Some(concrete) = bindings.get(name) {
                return concrete.clone();
            }

            let concrete_args: Vec<ConcreteType> = args
                .iter()
                .map(|a| ast_type_to_concrete(a, bindings))
                .collect();

            ConcreteType::Specialized {
                name: name.clone(),
                args: concrete_args,
            }
        }
        AstType::Tuple(elems) => ConcreteType::Tuple(
            elems
                .iter()
                .map(|e| ast_type_to_concrete(e, bindings))
                .collect(),
        ),
        AstType::Array { element, size: _ } => {
            ConcreteType::Array(Box::new(ast_type_to_concrete(element, bindings)))
        }
        AstType::Function { params, ret } => ConcreteType::Function {
            params: params
                .iter()
                .map(|p| ast_type_to_concrete(p, bindings))
                .collect(),
            ret: Box::new(
                ret.as_ref()
                    .map(|r| ast_type_to_concrete(r, bindings))
                    .unwrap_or(ConcreteType::Nil),
            ),
        },
        AstType::Optional(inner) => {
            ConcreteType::Optional(Box::new(ast_type_to_concrete(inner, bindings)))
        }
        AstType::Pointer { kind, inner } => {
            let pk = match kind {
                simple_parser::ast::PointerKind::Unique => PointerKind::Unique,
                simple_parser::ast::PointerKind::Shared => PointerKind::Shared,
                simple_parser::ast::PointerKind::Weak => PointerKind::Weak,
                simple_parser::ast::PointerKind::Handle => PointerKind::Handle,
                simple_parser::ast::PointerKind::Borrow => PointerKind::Borrow,
                simple_parser::ast::PointerKind::BorrowMut => PointerKind::BorrowMut,
            };
            ConcreteType::Pointer {
                kind: pk,
                inner: Box::new(ast_type_to_concrete(inner, bindings)),
            }
        }
        AstType::Union(types) => {
            // For unions, we take the first type for now
            // A more complete implementation would create a union concrete type
            if let Some(first) = types.first() {
                ast_type_to_concrete(first, bindings)
            } else {
                ConcreteType::Nil
            }
        }
        AstType::Constructor { target, args: _ } => {
            // Constructor types are used for factory patterns
            // We extract the target type
            ast_type_to_concrete(target, bindings)
        }
        AstType::Simd { lanes: _, element } => {
            // SIMD types are specialized arrays
            ConcreteType::Array(Box::new(ast_type_to_concrete(element, bindings)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_specialization_key() {
        let key = SpecializationKey::new("identity", vec![ConcreteType::Int]);
        assert_eq!(key.mangled_name(), "identity$Int");

        let key2 = SpecializationKey::new("swap", vec![ConcreteType::Int, ConcreteType::String]);
        assert_eq!(key2.mangled_name(), "swap$Int_String");
    }

    #[test]
    fn test_concrete_type_display() {
        assert_eq!(ConcreteType::Int.to_string(), "Int");
        assert_eq!(
            ConcreteType::Array(Box::new(ConcreteType::Int)).to_string(),
            "Array_Int"
        );
        assert_eq!(
            ConcreteType::Specialized {
                name: "List".to_string(),
                args: vec![ConcreteType::String],
            }
            .to_string(),
            "List_String"
        );
    }

    #[test]
    fn test_monomorphization_table() {
        let mut table = MonomorphizationTable::new();

        let func = FunctionDef {
            span: Span::new(0, 0, 1, 1),
            name: "identity".to_string(),
            generic_params: vec!["T".to_string()],
            params: vec![],
            return_type: None,
            body: Block {
                span: Span::new(0, 0, 1, 1),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effect: None,
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
        };

        let mangled = table.request_function("identity", vec![ConcreteType::Int], &func);
        assert_eq!(mangled, "identity$Int");
        assert!(table.has_pending());

        let (key, _) = table.pop_pending_function().unwrap();
        assert_eq!(key.name, "identity");
        assert!(!table.has_pending());
    }

    #[test]
    fn test_ast_type_to_concrete() {
        let bindings: HashMap<String, ConcreteType> = HashMap::new();

        let int_ty = AstType::Simple("Int".to_string());
        assert_eq!(ast_type_to_concrete(&int_ty, &bindings), ConcreteType::Int);

        let array_ty = AstType::Array {
            element: Box::new(AstType::Simple("String".to_string())),
            size: None,
        };
        assert_eq!(
            ast_type_to_concrete(&array_ty, &bindings),
            ConcreteType::Array(Box::new(ConcreteType::String))
        );
    }

    #[test]
    fn test_type_parameter_substitution() {
        let mut bindings = HashMap::new();
        bindings.insert("T".to_string(), ConcreteType::Int);

        let param_ty = AstType::Simple("T".to_string());
        assert_eq!(
            ast_type_to_concrete(&param_ty, &bindings),
            ConcreteType::Int
        );

        let generic_ty = AstType::Generic {
            name: "List".to_string(),
            args: vec![AstType::Simple("T".to_string())],
        };
        assert_eq!(
            ast_type_to_concrete(&generic_ty, &bindings),
            ConcreteType::Specialized {
                name: "List".to_string(),
                args: vec![ConcreteType::Int],
            }
        );
    }

    #[test]
    fn test_monomorphize_identity_function() {
        let code = r#"
fn identity<T>(x: T) -> T:
    return x

main = identity(42)
"#;
        let mut parser = simple_parser::Parser::new(code);
        let module = parser.parse().expect("parse ok");
        let mono_module = monomorphize_module(&module);

        // Verify we have the specialized function
        let has_specialized = mono_module
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(f) if f.name == "identity$Int"));
        assert!(has_specialized, "Should have identity$Int function");

        // Check that generic identity was removed
        let has_generic = mono_module.items.iter().any(|item| {
            matches!(item, Node::Function(f) if f.name == "identity" && !f.generic_params.is_empty())
        });
        assert!(!has_generic, "Generic identity function should be removed");

        // Check that the call site was rewritten
        let call_rewritten = mono_module.items.iter().any(|item| {
            if let Node::Assignment(a) = item {
                if let Expr::Call { callee, .. } = &a.value {
                    return matches!(callee.as_ref(), Expr::Identifier(name) if name == "identity$Int");
                }
            }
            false
        });
        assert!(
            call_rewritten,
            "Call site should be rewritten to identity$Int"
        );
    }
}
