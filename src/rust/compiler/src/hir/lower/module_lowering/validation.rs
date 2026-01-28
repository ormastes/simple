use std::collections::HashMap;

use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirExpr, HirExprKind, HirStmt};

impl Lowerer {
    /// Validate that sync functions do not call async functions (design decision #3).
    ///
    /// This implements async validation by checking that sync functions
    /// never call functions that have suspension operators.
    pub(super) fn validate_sync_async_calls(&self) -> LowerResult<()> {
        // Build a map of function names to their suspension status
        let mut function_suspension: HashMap<String, bool> = HashMap::new();
        for func in &self.module.functions {
            function_suspension.insert(func.name.clone(), func.has_suspension);
        }

        // Check each sync function for calls to async functions
        for func in &self.module.functions {
            if func.is_sync {
                // Walk the function body looking for calls to async functions
                for stmt in &func.body {
                    self.check_stmt_for_async_calls(stmt, &func.name, &function_suspension)?;
                }
            }
        }

        Ok(())
    }

    /// Check a statement for async function calls from sync functions.
    pub(super) fn check_stmt_for_async_calls(
        &self,
        stmt: &HirStmt,
        caller_name: &str,
        function_suspension: &HashMap<String, bool>,
    ) -> LowerResult<()> {
        match stmt {
            HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => {
                self.check_expr_for_async_calls(expr, caller_name, function_suspension)?;
            }
            HirStmt::Let { value: Some(expr), .. } => {
                self.check_expr_for_async_calls(expr, caller_name, function_suspension)?;
            }
            HirStmt::Assign { value, .. } => {
                self.check_expr_for_async_calls(value, caller_name, function_suspension)?;
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                self.check_expr_for_async_calls(condition, caller_name, function_suspension)?;
                for s in then_block {
                    self.check_stmt_for_async_calls(s, caller_name, function_suspension)?;
                }
                if let Some(else_stmts) = else_block {
                    for s in else_stmts {
                        self.check_stmt_for_async_calls(s, caller_name, function_suspension)?;
                    }
                }
            }
            HirStmt::While { condition, body, .. } => {
                self.check_expr_for_async_calls(condition, caller_name, function_suspension)?;
                for s in body {
                    self.check_stmt_for_async_calls(s, caller_name, function_suspension)?;
                }
            }
            HirStmt::For { iterable, body, .. } => {
                self.check_expr_for_async_calls(iterable, caller_name, function_suspension)?;
                for s in body {
                    self.check_stmt_for_async_calls(s, caller_name, function_suspension)?;
                }
            }
            HirStmt::Loop { body } => {
                for s in body {
                    self.check_stmt_for_async_calls(s, caller_name, function_suspension)?;
                }
            }
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => {
                self.check_expr_for_async_calls(condition, caller_name, function_suspension)?;
            }
            HirStmt::ProofHint { .. } => {
                // Proof hints contain no async calls
            }
            HirStmt::Calc { steps } => {
                // Check each calc step expression for async calls
                for step in steps {
                    self.check_expr_for_async_calls(&step.expr, caller_name, function_suspension)?;
                }
            }
            HirStmt::Let { value: None, .. } | HirStmt::Return(None) | HirStmt::Break | HirStmt::Continue => {}
        }
        Ok(())
    }

    /// Check an expression for async function calls from sync functions.
    pub(super) fn check_expr_for_async_calls(
        &self,
        expr: &HirExpr,
        caller_name: &str,
        function_suspension: &HashMap<String, bool>,
    ) -> LowerResult<()> {
        match &expr.kind {
            HirExprKind::Call { func, args } => {
                // Check if this is a call to an async function
                if let HirExprKind::Global(callee_name) = &func.kind {
                    if let Some(&has_suspension) = function_suspension.get(callee_name) {
                        if has_suspension {
                            return Err(LowerError::Unsupported(format!(
                                "Sync function '{}' cannot call async function '{}'.\n\
                                 Function '{}' uses suspension operators (~=, if~, while~, for~) and is async.\n\
                                 \n\
                                 To fix:\n\
                                 - Remove the 'sync' keyword from '{}' to allow async behavior, OR\n\
                                 - Replace the call to '{}' with a non-suspending alternative",
                                caller_name, callee_name, callee_name, caller_name, callee_name
                            )));
                        }
                    }
                }
                // Check arguments
                for arg in args {
                    self.check_expr_for_async_calls(arg, caller_name, function_suspension)?;
                }
            }
            HirExprKind::Binary { left, right, .. } => {
                self.check_expr_for_async_calls(left, caller_name, function_suspension)?;
                self.check_expr_for_async_calls(right, caller_name, function_suspension)?;
            }
            HirExprKind::Unary { operand, .. } => {
                self.check_expr_for_async_calls(operand, caller_name, function_suspension)?;
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.check_expr_for_async_calls(condition, caller_name, function_suspension)?;
                self.check_expr_for_async_calls(then_branch, caller_name, function_suspension)?;
                if let Some(else_expr) = else_branch {
                    self.check_expr_for_async_calls(else_expr, caller_name, function_suspension)?;
                }
            }
            HirExprKind::Lambda { body, .. } => {
                self.check_expr_for_async_calls(body, caller_name, function_suspension)?;
            }
            HirExprKind::Tuple(exprs) | HirExprKind::Array(exprs) | HirExprKind::VecLiteral(exprs) => {
                for e in exprs {
                    self.check_expr_for_async_calls(e, caller_name, function_suspension)?;
                }
            }
            HirExprKind::ArrayRepeat { value, count } => {
                self.check_expr_for_async_calls(value, caller_name, function_suspension)?;
                self.check_expr_for_async_calls(count, caller_name, function_suspension)?;
            }
            HirExprKind::FieldAccess { receiver, .. } => {
                self.check_expr_for_async_calls(receiver, caller_name, function_suspension)?;
            }
            HirExprKind::Index { receiver, index } => {
                self.check_expr_for_async_calls(receiver, caller_name, function_suspension)?;
                self.check_expr_for_async_calls(index, caller_name, function_suspension)?;
            }
            HirExprKind::StructInit { fields, .. } => {
                for e in fields {
                    self.check_expr_for_async_calls(e, caller_name, function_suspension)?;
                }
            }
            HirExprKind::PointerNew { value, .. } => {
                self.check_expr_for_async_calls(value, caller_name, function_suspension)?;
            }
            HirExprKind::MethodCall { receiver, args, .. } => {
                self.check_expr_for_async_calls(receiver, caller_name, function_suspension)?;
                for arg in args {
                    self.check_expr_for_async_calls(arg, caller_name, function_suspension)?;
                }
            }
            HirExprKind::GeneratorCreate { body } | HirExprKind::FutureCreate { body } | HirExprKind::Await(body) => {
                self.check_expr_for_async_calls(body, caller_name, function_suspension)?;
            }
            HirExprKind::ActorSpawn { body } => {
                self.check_expr_for_async_calls(body, caller_name, function_suspension)?;
            }
            HirExprKind::BuiltinCall { args, .. } => {
                for arg in args {
                    self.check_expr_for_async_calls(arg, caller_name, function_suspension)?;
                }
            }
            HirExprKind::Cast { expr, .. } => {
                self.check_expr_for_async_calls(expr, caller_name, function_suspension)?;
            }
            HirExprKind::Ref(expr) | HirExprKind::Deref(expr) => {
                self.check_expr_for_async_calls(expr, caller_name, function_suspension)?;
            }
            HirExprKind::Yield(expr) | HirExprKind::ContractOld(expr) => {
                self.check_expr_for_async_calls(expr, caller_name, function_suspension)?;
            }
            HirExprKind::GpuIntrinsic { args, .. } => {
                for arg in args {
                    self.check_expr_for_async_calls(arg, caller_name, function_suspension)?;
                }
            }
            HirExprKind::NeighborAccess { array, .. } => {
                self.check_expr_for_async_calls(array, caller_name, function_suspension)?;
            }
            HirExprKind::Dict(entries) => {
                for (key, value) in entries {
                    self.check_expr_for_async_calls(key, caller_name, function_suspension)?;
                    self.check_expr_for_async_calls(value, caller_name, function_suspension)?;
                }
            }
            // Leaf expressions - no recursive calls needed
            HirExprKind::Integer(_)
            | HirExprKind::Float(_)
            | HirExprKind::Bool(_)
            | HirExprKind::String(_)
            | HirExprKind::Nil
            | HirExprKind::Local(_)
            | HirExprKind::Global(_)
            | HirExprKind::ContractResult => {}
        }
        Ok(())
    }
}
