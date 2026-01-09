//! Contract expression lowering
//!
//! This module contains expression lowering logic for contract expressions:
//! result (return value access in postconditions) and old (value capture in preconditions).

use simple_parser::Expr;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a `result` contract expression to HIR
    ///
    /// Used in postconditions (out:, out_err:) to refer to the function's return value.
    /// Type is taken from the function context's return type.
    pub(super) fn lower_contract_result(&self, ctx: &FunctionContext) -> LowerResult<HirExpr> {
        Ok(HirExpr {
            kind: HirExprKind::ContractResult,
            ty: ctx.return_type,
        })
    }

    /// Lower an `old(expr)` contract expression to HIR
    ///
    /// Used in postconditions to capture the value of an expression at function entry.
    /// The expression's type must be snapshot-safe (i.e., can be safely captured).
    pub(super) fn lower_contract_old(
        &mut self,
        inner: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let inner_hir = Box::new(self.lower_expr(inner, ctx)?);
        let ty = inner_hir.ty;

        // CTR-060-062: Check that the type is snapshot-safe
        if !self.module.types.is_snapshot_safe(ty) {
            return Err(LowerError::NotSnapshotSafe);
        }

        Ok(HirExpr {
            kind: HirExprKind::ContractOld(inner_hir),
            ty,
        })
    }
}
