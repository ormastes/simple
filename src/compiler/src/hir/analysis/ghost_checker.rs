//! Ghost code purity checking (VER-001)
//!
//! Verifies that ghost code adheres to purity requirements:
//! - Ghost functions only call other ghost functions (or pure functions)
//! - Ghost code has no side effects
//! - Non-ghost code doesn't call ghost functions (except in contracts)

use crate::hir::types::{HirExpr, HirExprKind, HirFunction, HirModule, HirStmt};
use crate::CompileError;
use std::collections::HashSet;

/// Ghost code analysis result
#[derive(Debug, Default)]
pub struct GhostAnalysisResult {
    /// Ghost functions that were analyzed
    pub ghost_functions: Vec<String>,
    /// Errors found during analysis
    pub errors: Vec<GhostError>,
    /// Warnings found during analysis
    pub warnings: Vec<GhostWarning>,
}

/// Ghost code error
#[derive(Debug, Clone)]
pub struct GhostError {
    /// Function where the error occurred
    pub function: String,
    /// Error message
    pub message: String,
    /// Kind of error
    pub kind: GhostErrorKind,
}

/// Kinds of ghost errors
#[derive(Debug, Clone, PartialEq)]
pub enum GhostErrorKind {
    /// Ghost function calls non-ghost, non-pure function
    GhostCallsNonGhost,
    /// Ghost function has side effects
    GhostHasSideEffects,
    /// Non-ghost function calls ghost function outside contract
    NonGhostCallsGhost,
}

/// Ghost code warning
#[derive(Debug, Clone)]
pub struct GhostWarning {
    /// Function where the warning occurred
    pub function: String,
    /// Warning message
    pub message: String,
}

/// Ghost code checker
pub struct GhostChecker<'a> {
    module: &'a HirModule,
    /// Set of ghost function names
    ghost_functions: HashSet<String>,
    /// Set of pure function names
    pure_functions: HashSet<String>,
    /// Current analysis results
    result: GhostAnalysisResult,
}

impl<'a> GhostChecker<'a> {
    /// Create a new ghost checker for a module
    pub fn new(module: &'a HirModule) -> Self {
        let mut ghost_functions = HashSet::new();
        let mut pure_functions = HashSet::new();

        // Collect ghost and pure functions
        for func in &module.functions {
            if func.is_ghost {
                ghost_functions.insert(func.name.clone());
            }
            if func.is_pure {
                pure_functions.insert(func.name.clone());
            }
        }

        Self {
            module,
            ghost_functions,
            pure_functions,
            result: GhostAnalysisResult::default(),
        }
    }

    /// Run ghost analysis on the module
    pub fn analyze(mut self) -> GhostAnalysisResult {
        for func in &self.module.functions {
            if func.is_ghost {
                self.analyze_ghost_function(func);
            } else {
                self.analyze_non_ghost_function(func);
            }
        }
        self.result
    }

    /// Analyze a ghost function for purity violations
    fn analyze_ghost_function(&mut self, func: &HirFunction) {
        self.result.ghost_functions.push(func.name.clone());

        // Check all statements in the function body
        for stmt in &func.body {
            self.check_ghost_stmt(stmt, &func.name);
        }
    }

    /// Analyze a non-ghost function for ghost calls outside contracts
    fn analyze_non_ghost_function(&mut self, func: &HirFunction) {
        // Check body for ghost calls
        for stmt in &func.body {
            self.check_non_ghost_stmt(stmt, &func.name, false);
        }

        // Ghost calls in contracts are allowed
        if let Some(ref contract) = func.contract {
            // Preconditions, postconditions, and invariants can call ghost functions
            // This is intentional - ghost functions are for verification
        }
    }

    /// Check a statement in ghost context for purity
    fn check_ghost_stmt(&mut self, stmt: &HirStmt, func_name: &str) {
        match stmt {
            HirStmt::Let { value, .. } => {
                if let Some(expr) = value {
                    self.check_ghost_expr(expr, func_name);
                }
            }
            HirStmt::Assign { value, .. } => {
                // Assignment in ghost code is allowed (ghost state)
                self.check_ghost_expr(value, func_name);
            }
            HirStmt::Return(Some(expr)) => {
                self.check_ghost_expr(expr, func_name);
            }
            HirStmt::Expr(expr) => {
                self.check_ghost_expr(expr, func_name);
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                self.check_ghost_expr(condition, func_name);
                for stmt in then_block {
                    self.check_ghost_stmt(stmt, func_name);
                }
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.check_ghost_stmt(stmt, func_name);
                    }
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.check_ghost_expr(condition, func_name);
                for stmt in body {
                    self.check_ghost_stmt(stmt, func_name);
                }
            }
            HirStmt::For { iterable, body, .. } => {
                self.check_ghost_expr(iterable, func_name);
                for stmt in body {
                    self.check_ghost_stmt(stmt, func_name);
                }
            }
            HirStmt::Loop { body } => {
                for stmt in body {
                    self.check_ghost_stmt(stmt, func_name);
                }
            }
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => {
                self.check_ghost_expr(condition, func_name);
            }
            HirStmt::Break | HirStmt::Continue | HirStmt::Return(None) => {}
        }
    }

    /// Check an expression in ghost context for purity
    fn check_ghost_expr(&mut self, expr: &HirExpr, func_name: &str) {
        match &expr.kind {
            // Function calls: must be ghost or pure
            HirExprKind::Call { func, args } => {
                if let HirExprKind::Global(name) = &func.kind {
                    if !self.ghost_functions.contains(name) && !self.pure_functions.contains(name) {
                        self.result.errors.push(GhostError {
                            function: func_name.to_string(),
                            message: format!(
                                "Ghost function '{}' calls non-ghost, non-pure function '{}'",
                                func_name, name
                            ),
                            kind: GhostErrorKind::GhostCallsNonGhost,
                        });
                    }
                }
                self.check_ghost_expr(func, func_name);
                for arg in args {
                    self.check_ghost_expr(arg, func_name);
                }
            }

            // Side effect expressions: not allowed in ghost
            HirExprKind::Yield(_) | HirExprKind::Await(_) => {
                self.result.errors.push(GhostError {
                    function: func_name.to_string(),
                    message: format!("Ghost function '{}' has async side effects (yield/await)", func_name),
                    kind: GhostErrorKind::GhostHasSideEffects,
                });
            }

            // Actor spawn: not allowed
            HirExprKind::ActorSpawn { .. } => {
                self.result.errors.push(GhostError {
                    function: func_name.to_string(),
                    message: format!("Ghost function '{}' spawns actors", func_name),
                    kind: GhostErrorKind::GhostHasSideEffects,
                });
            }

            // Recursively check sub-expressions
            HirExprKind::Binary { left, right, .. } => {
                self.check_ghost_expr(left, func_name);
                self.check_ghost_expr(right, func_name);
            }
            HirExprKind::Unary { operand, .. } => {
                self.check_ghost_expr(operand, func_name);
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.check_ghost_expr(condition, func_name);
                self.check_ghost_expr(then_branch, func_name);
                if let Some(else_expr) = else_branch {
                    self.check_ghost_expr(else_expr, func_name);
                }
            }
            HirExprKind::MethodCall { receiver, args, .. } => {
                self.check_ghost_expr(receiver, func_name);
                for arg in args {
                    self.check_ghost_expr(arg, func_name);
                }
            }
            HirExprKind::FieldAccess { receiver, .. } => {
                self.check_ghost_expr(receiver, func_name);
            }
            HirExprKind::Index { receiver, index } => {
                self.check_ghost_expr(receiver, func_name);
                self.check_ghost_expr(index, func_name);
            }
            HirExprKind::Array(elements) | HirExprKind::VecLiteral(elements) | HirExprKind::Tuple(elements) => {
                for elem in elements {
                    self.check_ghost_expr(elem, func_name);
                }
            }
            HirExprKind::Lambda { body, .. } => {
                self.check_ghost_expr(body, func_name);
            }

            // Simple expressions: always allowed
            HirExprKind::Integer(_)
            | HirExprKind::Float(_)
            | HirExprKind::Bool(_)
            | HirExprKind::String(_)
            | HirExprKind::Local(_)
            | HirExprKind::Global(_)
            | HirExprKind::Nil
            | HirExprKind::ContractResult
            | HirExprKind::ContractOld(_) => {}

            // Other expressions: recursively check
            _ => {}
        }
    }

    /// Check a statement in non-ghost context for ghost calls
    fn check_non_ghost_stmt(&mut self, stmt: &HirStmt, func_name: &str, in_contract: bool) {
        match stmt {
            HirStmt::Let { value, .. } => {
                if let Some(expr) = value {
                    self.check_non_ghost_expr(expr, func_name, in_contract);
                }
            }
            HirStmt::Assign { value, .. } => {
                self.check_non_ghost_expr(value, func_name, in_contract);
            }
            HirStmt::Return(Some(expr)) => {
                self.check_non_ghost_expr(expr, func_name, in_contract);
            }
            HirStmt::Expr(expr) => {
                self.check_non_ghost_expr(expr, func_name, in_contract);
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                self.check_non_ghost_expr(condition, func_name, in_contract);
                for stmt in then_block {
                    self.check_non_ghost_stmt(stmt, func_name, in_contract);
                }
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.check_non_ghost_stmt(stmt, func_name, in_contract);
                    }
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.check_non_ghost_expr(condition, func_name, in_contract);
                for stmt in body {
                    self.check_non_ghost_stmt(stmt, func_name, in_contract);
                }
            }
            HirStmt::For { iterable, body, .. } => {
                self.check_non_ghost_expr(iterable, func_name, in_contract);
                for stmt in body {
                    self.check_non_ghost_stmt(stmt, func_name, in_contract);
                }
            }
            HirStmt::Loop { body } => {
                for stmt in body {
                    self.check_non_ghost_stmt(stmt, func_name, in_contract);
                }
            }
            // Assert/Assume/Admit are contract-like, ghost calls allowed
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => {
                self.check_non_ghost_expr(condition, func_name, true);
            }
            HirStmt::Break | HirStmt::Continue | HirStmt::Return(None) => {}
        }
    }

    /// Check an expression in non-ghost context for ghost calls
    fn check_non_ghost_expr(&mut self, expr: &HirExpr, func_name: &str, in_contract: bool) {
        match &expr.kind {
            // Function calls: check for ghost
            HirExprKind::Call { func, args } => {
                if let HirExprKind::Global(name) = &func.kind {
                    if self.ghost_functions.contains(name) && !in_contract {
                        self.result.errors.push(GhostError {
                            function: func_name.to_string(),
                            message: format!(
                                "Non-ghost function '{}' calls ghost function '{}' outside contract",
                                func_name, name
                            ),
                            kind: GhostErrorKind::NonGhostCallsGhost,
                        });
                    }
                }
                self.check_non_ghost_expr(func, func_name, in_contract);
                for arg in args {
                    self.check_non_ghost_expr(arg, func_name, in_contract);
                }
            }

            // Recursively check sub-expressions
            HirExprKind::Binary { left, right, .. } => {
                self.check_non_ghost_expr(left, func_name, in_contract);
                self.check_non_ghost_expr(right, func_name, in_contract);
            }
            HirExprKind::Unary { operand, .. } => {
                self.check_non_ghost_expr(operand, func_name, in_contract);
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.check_non_ghost_expr(condition, func_name, in_contract);
                self.check_non_ghost_expr(then_branch, func_name, in_contract);
                if let Some(else_expr) = else_branch {
                    self.check_non_ghost_expr(else_expr, func_name, in_contract);
                }
            }
            HirExprKind::MethodCall { receiver, args, .. } => {
                self.check_non_ghost_expr(receiver, func_name, in_contract);
                for arg in args {
                    self.check_non_ghost_expr(arg, func_name, in_contract);
                }
            }
            HirExprKind::FieldAccess { receiver, .. } => {
                self.check_non_ghost_expr(receiver, func_name, in_contract);
            }
            HirExprKind::Index { receiver, index } => {
                self.check_non_ghost_expr(receiver, func_name, in_contract);
                self.check_non_ghost_expr(index, func_name, in_contract);
            }
            HirExprKind::Array(elements) | HirExprKind::VecLiteral(elements) | HirExprKind::Tuple(elements) => {
                for elem in elements {
                    self.check_non_ghost_expr(elem, func_name, in_contract);
                }
            }
            HirExprKind::Lambda { body, .. } => {
                self.check_non_ghost_expr(body, func_name, in_contract);
            }

            // Simple expressions: always allowed
            _ => {}
        }
    }
}

/// Convert ghost analysis result to compile errors
impl GhostAnalysisResult {
    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Convert to compile errors
    pub fn to_compile_errors(&self) -> Vec<CompileError> {
        self.errors
            .iter()
            .map(|e| CompileError::GhostError(e.message.clone()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::types::*;
    use simple_parser::ast::{Mutability, Visibility};

    fn create_test_module() -> HirModule {
        HirModule::new()
    }

    #[test]
    fn test_ghost_checker_empty_module() {
        let module = create_test_module();
        let checker = GhostChecker::new(&module);
        let result = checker.analyze();

        assert!(result.ghost_functions.is_empty());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_ghost_function_pure_call_allowed() {
        let mut module = create_test_module();

        // Add a pure function
        module.functions.push(HirFunction {
            name: "pure_fn".to_string(),
            span: None,
            params: vec![],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![],
            visibility: Visibility::Public,
            contract: None,
            is_pure: true,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: false,
            is_sync: false,
            has_suspension: false,
        });

        // Add a ghost function that calls pure_fn
        module.functions.push(HirFunction {
            name: "ghost_fn".to_string(),
            span: None,
            params: vec![],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![HirStmt::Return(Some(HirExpr {
                kind: HirExprKind::Call {
                    func: Box::new(HirExpr {
                        kind: HirExprKind::Global("pure_fn".to_string()),
                        ty: TypeId::I64,
                    }),
                    args: vec![],
                },
                ty: TypeId::I64,
            }))],
            visibility: Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: true,
            is_sync: false,
            has_suspension: false,
        });

        let checker = GhostChecker::new(&module);
        let result = checker.analyze();

        assert_eq!(result.ghost_functions.len(), 1);
        assert!(result.errors.is_empty());
    }
}
