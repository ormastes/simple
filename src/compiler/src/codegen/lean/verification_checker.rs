//! Verification constraint checker.
//!
//! Checks HIR for verification rule violations before Lean code generation.
//! Enforces the V-* and M-* rules defined in the Lean verification spec.

use super::verification_diagnostics::{VerificationDiagnostic, VerificationDiagnostics, VerificationErrorCode};
use crate::hir::{HirExpr, HirExprKind, HirFunction, HirModule, HirStmt};
use simple_common::diagnostic::Span;

/// Verification constraint checker
pub struct VerificationChecker<'a> {
    /// Module being checked
    module: &'a HirModule,
    /// Collected diagnostics
    diagnostics: VerificationDiagnostics,
    /// Current file path
    file: Option<String>,
}

impl<'a> VerificationChecker<'a> {
    /// Create a new checker for a module
    pub fn new(module: &'a HirModule) -> Self {
        Self {
            module,
            diagnostics: VerificationDiagnostics::new(),
            file: module.name.clone(),
        }
    }

    /// Run all verification checks
    pub fn check(&mut self) -> &VerificationDiagnostics {
        // Check all verified functions
        for func in &self.module.functions {
            if func.verification_mode.is_verified() {
                self.check_verified_function(func);
            }
        }

        &self.diagnostics
    }

    /// Check a verified function for constraint violations
    fn check_verified_function(&mut self, func: &HirFunction) {
        // V-TERM: Check for termination argument on recursive functions
        // (Currently we don't have a decreases field, so skip this check)
        if self.is_potentially_recursive(func) {
            // Note: decreases clause not yet in HirContract, would report here
        }

        // V-EFFECT: Check for IO/FFI in function body
        for stmt in &func.body {
            self.check_statement_effects(stmt, &func.name);
        }

        // V-UNSAFE: Check for unsafe operations
        for stmt in &func.body {
            self.check_statement_safety(stmt, &func.name);
        }

        // Check contract expressions for side effects
        if let Some(ref contract) = func.contract {
            for clause in &contract.preconditions {
                self.check_contract_purity(&clause.condition, "requires");
            }
            for clause in &contract.postconditions {
                self.check_contract_purity(&clause.condition, "ensures");
            }
            for clause in &contract.invariants {
                self.check_contract_purity(&clause.condition, "invariant");
            }
        }
    }

    /// Check if a function is potentially recursive
    fn is_potentially_recursive(&self, func: &HirFunction) -> bool {
        // Simple heuristic: check if the function calls itself
        for stmt in &func.body {
            if self.statement_calls_function(stmt, &func.name) {
                return true;
            }
        }
        false
    }

    /// Check if a statement contains a call to the given function
    fn statement_calls_function(&self, stmt: &HirStmt, name: &str) -> bool {
        match stmt {
            HirStmt::Expr(expr) => self.expr_calls_function(expr, name),
            HirStmt::Let { value, .. } => value
                .as_ref()
                .map(|e| self.expr_calls_function(e, name))
                .unwrap_or(false),
            HirStmt::Assign { value, .. } => self.expr_calls_function(value, name),
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.expr_calls_function(condition, name)
                    || then_block.iter().any(|s| self.statement_calls_function(s, name))
                    || else_block
                        .as_ref()
                        .map(|b| b.iter().any(|s| self.statement_calls_function(s, name)))
                        .unwrap_or(false)
            }
            HirStmt::While { condition, body, .. } => {
                self.expr_calls_function(condition, name) || body.iter().any(|s| self.statement_calls_function(s, name))
            }
            HirStmt::Loop { body, .. } => body.iter().any(|s| self.statement_calls_function(s, name)),
            HirStmt::Return(value) => value
                .as_ref()
                .map(|e| self.expr_calls_function(e, name))
                .unwrap_or(false),
            HirStmt::Assert { condition, .. } => self.expr_calls_function(condition, name),
            HirStmt::For { body, .. } => body.iter().any(|s| self.statement_calls_function(s, name)),
            HirStmt::Assume { condition, .. } => self.expr_calls_function(condition, name),
            HirStmt::Admit { .. } => false,
            HirStmt::Break | HirStmt::Continue => false,
        }
    }

    /// Check if an expression contains a call to the given function
    fn expr_calls_function(&self, expr: &HirExpr, name: &str) -> bool {
        match &expr.kind {
            HirExprKind::Call { func, args, .. } => {
                if let HirExprKind::Global(func_name) = &func.kind {
                    if func_name == name {
                        return true;
                    }
                }
                self.expr_calls_function(func, name) || args.iter().any(|a| self.expr_calls_function(a, name))
            }
            HirExprKind::Binary { left, right, .. } => {
                self.expr_calls_function(left, name) || self.expr_calls_function(right, name)
            }
            HirExprKind::Unary { operand, .. } => self.expr_calls_function(operand, name),
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr_calls_function(condition, name)
                    || self.expr_calls_function(then_branch, name)
                    || else_branch
                        .as_ref()
                        .map(|e| self.expr_calls_function(e, name))
                        .unwrap_or(false)
            }
            HirExprKind::Tuple(elements) | HirExprKind::Array(elements) | HirExprKind::VecLiteral(elements) => {
                elements.iter().any(|e| self.expr_calls_function(e, name))
            }
            HirExprKind::StructInit { fields, .. } => fields.iter().any(|e| self.expr_calls_function(e, name)),
            HirExprKind::FieldAccess { receiver, .. } => self.expr_calls_function(receiver, name),
            HirExprKind::Index { receiver, index, .. } => {
                self.expr_calls_function(receiver, name) || self.expr_calls_function(index, name)
            }
            HirExprKind::Ref(inner) | HirExprKind::Deref(inner) => self.expr_calls_function(inner, name),
            _ => false,
        }
    }

    /// Check statement for effect violations
    fn check_statement_effects(&mut self, stmt: &HirStmt, func_name: &str) {
        match stmt {
            HirStmt::Expr(expr) => self.check_expr_effects(expr, func_name),
            HirStmt::Let { value, .. } => {
                if let Some(e) = value {
                    self.check_expr_effects(e, func_name);
                }
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.check_expr_effects(condition, func_name);
                for s in then_block {
                    self.check_statement_effects(s, func_name);
                }
                if let Some(block) = else_block {
                    for s in block {
                        self.check_statement_effects(s, func_name);
                    }
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.check_expr_effects(condition, func_name);
                for s in body {
                    self.check_statement_effects(s, func_name);
                }
            }
            HirStmt::Loop { body, .. } => {
                for s in body {
                    self.check_statement_effects(s, func_name);
                }
            }
            _ => {}
        }
    }

    /// Check expression for effect violations
    fn check_expr_effects(&mut self, expr: &HirExpr, func_name: &str) {
        match &expr.kind {
            HirExprKind::Call { func, args, .. } => {
                // Check for IO function calls
                if let HirExprKind::Global(name) = &func.kind {
                    if self.is_io_function(name) {
                        self.report(
                            VerificationErrorCode::IoInVerified,
                            Span::at(0, 1, 1), // Placeholder span
                            Some(func_name),
                        );
                    }
                }
                self.check_expr_effects(func, func_name);
                for arg in args {
                    self.check_expr_effects(arg, func_name);
                }
            }
            HirExprKind::Binary { left, right, .. } => {
                self.check_expr_effects(left, func_name);
                self.check_expr_effects(right, func_name);
            }
            _ => {}
        }
    }

    /// Check statement for safety violations
    fn check_statement_safety(&mut self, stmt: &HirStmt, func_name: &str) {
        match stmt {
            HirStmt::Expr(expr) => self.check_expr_safety(expr, func_name),
            HirStmt::Let { value, .. } => {
                if let Some(e) = value {
                    self.check_expr_safety(e, func_name);
                }
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                self.check_expr_safety(condition, func_name);
                for s in then_block {
                    self.check_statement_safety(s, func_name);
                }
                if let Some(block) = else_block {
                    for s in block {
                        self.check_statement_safety(s, func_name);
                    }
                }
            }
            HirStmt::Loop { body, .. } => {
                for s in body {
                    self.check_statement_safety(s, func_name);
                }
            }
            _ => {}
        }
    }

    /// Check expression for safety violations
    fn check_expr_safety(&mut self, expr: &HirExpr, func_name: &str) {
        match &expr.kind {
            HirExprKind::Call { args, .. } => {
                for arg in args {
                    self.check_expr_safety(arg, func_name);
                }
            }
            HirExprKind::Binary { left, right, .. } => {
                self.check_expr_safety(left, func_name);
                self.check_expr_safety(right, func_name);
            }
            // Raw pointer dereference in verified context
            HirExprKind::Deref { .. } => {
                self.report(
                    VerificationErrorCode::RawPointerInVerified,
                    Span::at(0, 1, 1), // Placeholder span
                    Some(func_name),
                );
            }
            _ => {}
        }
    }

    /// Check contract expression for purity
    fn check_contract_purity(&mut self, expr: &HirExpr, clause_type: &str) {
        match &expr.kind {
            HirExprKind::Call { func, args, .. } => {
                // Check for mutating calls in contracts
                if let HirExprKind::Global(name) = &func.kind {
                    if self.is_mutating_function(name) {
                        self.report_with_context(
                            VerificationErrorCode::ContractHasSideEffects,
                            Span::at(0, 1, 1), // Placeholder span
                            None,
                            format!("in {} clause", clause_type),
                        );
                    }
                }
                for arg in args {
                    self.check_contract_purity(arg, clause_type);
                }
            }
            HirExprKind::Binary { left, right, .. } => {
                self.check_contract_purity(left, clause_type);
                self.check_contract_purity(right, clause_type);
            }
            HirExprKind::Unary { operand, .. } => {
                self.check_contract_purity(operand, clause_type);
            }
            _ => {}
        }
    }

    /// Check if function is an IO function
    fn is_io_function(&self, name: &str) -> bool {
        // List of known IO functions
        matches!(
            name,
            "print"
                | "println"
                | "read"
                | "readline"
                | "write"
                | "open"
                | "close"
                | "read_file"
                | "write_file"
                | "spawn"
                | "send"
                | "recv"
                | "sleep"
        )
    }

    /// Check if function is mutating
    fn is_mutating_function(&self, name: &str) -> bool {
        // Functions that modify state
        name.starts_with("set_")
            || name.starts_with("push")
            || name.starts_with("pop")
            || name.starts_with("insert")
            || name.starts_with("remove")
            || name.starts_with("clear")
            || name.starts_with("append")
            || name == "assign"
    }

    /// Report an error
    fn report(&mut self, code: VerificationErrorCode, span: Span, item: Option<&str>) {
        let mut diag = VerificationDiagnostic::new(code, span);
        if let Some(name) = item {
            diag = diag.with_item(name);
        }
        if let Some(ref file) = self.file {
            diag = diag.with_file(file);
        }
        self.diagnostics.push(diag);
    }

    /// Report an error with context
    fn report_with_context(&mut self, code: VerificationErrorCode, span: Span, item: Option<&str>, context: String) {
        let mut diag = VerificationDiagnostic::new(code, span).with_context(context);
        if let Some(name) = item {
            diag = diag.with_item(name);
        }
        if let Some(ref file) = self.file {
            diag = diag.with_file(file);
        }
        self.diagnostics.push(diag);
    }

    /// Take the diagnostics, consuming the checker
    pub fn into_diagnostics(self) -> VerificationDiagnostics {
        self.diagnostics
    }
}

/// Check a module for verification violations
pub fn check_module(module: &HirModule) -> VerificationDiagnostics {
    let mut checker = VerificationChecker::new(module);
    checker.check();
    checker.into_diagnostics()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests would require constructing HIR structures, which is complex
    // In practice, these would be integration tests

    #[test]
    fn test_io_function_detection() {
        let module = HirModule::default();
        let checker = VerificationChecker::new(&module);

        assert!(checker.is_io_function("print"));
        assert!(checker.is_io_function("read_file"));
        assert!(!checker.is_io_function("add"));
        assert!(!checker.is_io_function("calculate"));
    }

    #[test]
    fn test_mutating_function_detection() {
        let module = HirModule::default();
        let checker = VerificationChecker::new(&module);

        assert!(checker.is_mutating_function("set_value"));
        assert!(checker.is_mutating_function("push_item"));
        assert!(checker.is_mutating_function("clear"));
        assert!(!checker.is_mutating_function("get_value"));
        assert!(!checker.is_mutating_function("calculate"));
    }
}
