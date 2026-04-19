//! Pointer/reference expression lowering: PointerNew, Ref, Deref, ContractOld, NeighborAccess, GpuIntrinsic dispatch.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, NeighborDirection, PointerKind};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_pointer_new_expr(
        &mut self,
        kind: PointerKind,
        value: &HirExpr,
    ) -> MirLowerResult<VReg> {
        let value_reg = self.lower_expr(value)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::PointerNew {
                dest,
                kind,
                value: value_reg,
            });
            dest
        })
    }

    pub(super) fn lower_ref_expr(&mut self, inner: &HirExpr) -> MirLowerResult<VReg> {
        let source_reg = self.lower_expr(inner)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::PointerRef {
                dest,
                kind: PointerKind::Borrow,
                source: source_reg,
            });
            dest
        })
    }

    pub(super) fn lower_deref_expr(&mut self, inner: &HirExpr) -> MirLowerResult<VReg> {
        let pointer_reg = self.lower_expr(inner)?;
        // Determine pointer kind from the inner expression's type
        // For now, default to Borrow
        let kind = PointerKind::Borrow;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::PointerDeref {
                dest,
                pointer: pointer_reg,
                kind,
            });
            dest
        })
    }

    pub(super) fn lower_contract_old_expr(&mut self, inner: &HirExpr) -> MirLowerResult<VReg> {
        // Look up the captured VReg for this old() expression
        // During emit_entry_contracts(), we stored: index -> (VReg, HirExpr)
        // Now we need to find which index corresponds to this inner expression

        let ctx = self.try_contract_ctx()?;

        // Search through old_expr_map to find matching expression
        for (idx, captured_expr) in &ctx.old_expr_map {
            if captured_expr == inner.as_ref() {
                // Found matching expression, return the captured VReg
                if let Some(&vreg) = ctx.old_captures.get(idx) {
                    return Ok(vreg);
                }
            }
        }

        // If we reach here, the old() expression wasn't found in captures
        // This shouldn't happen with proper HIR lowering
        Err(MirLowerError::Unsupported(format!(
            "old() expression not found in captures: {:?}",
            inner
        )))
    }

    pub(super) fn lower_neighbor_access_expr(
        &mut self,
        array: &HirExpr,
        direction: &crate::hir::NeighborDirection,
    ) -> MirLowerResult<VReg> {
        let array_reg = self.lower_expr(array)?;
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::NeighborLoad {
                dest,
                array: array_reg,
                direction: *direction,
            });
            dest
        })
    }
}
