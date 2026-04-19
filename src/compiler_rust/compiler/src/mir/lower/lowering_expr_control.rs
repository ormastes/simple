//! Control flow expression lowering: If, LetIn.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_if_expr(
        &mut self,
        condition: &HirExpr,
        then_branch: &HirExpr,
        else_branch: &Option<Box<HirExpr>>,
        expr_ty: TypeId,
    ) -> MirLowerResult<VReg> {
        use crate::hir::TypeId;
        use crate::mir::effects::LocalKind;
        use crate::mir::function::MirLocal;

        // Lower condition
        let cond_reg = self.lower_expr(condition)?;

        // Create temporary local for result BEFORE branching
        let temp_local_index = self.with_func(|func, _| {
            let index = func.params.len() + func.locals.len();
            func.locals.push(MirLocal {
                name: format!("$if_merge_{}", index),
                ty: expr_ty,
                kind: LocalKind::Local,
                is_ghost: false,
            });
            index
        })?;

        // Get address of temp local
        let temp_addr = self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            addr
        })?;

        // Create basic blocks
        let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
            let then_id = func.new_block();
            let else_id = func.new_block();
            let merge_id = func.new_block();

            // Set branch terminator
            let block = func.block_mut(current_block).unwrap();
            block.terminator = crate::mir::Terminator::Branch {
                cond: cond_reg,
                then_block: then_id,
                else_block: else_id,
            };
            (then_id, else_id, merge_id)
        })?;

        // Lower then branch
        self.set_current_block(then_id)?;
        let then_value = self.lower_expr(then_branch)?;
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Store {
                addr: temp_addr,
                value: then_value,
                ty: expr_ty,
            });
        })?;
        self.finalize_block_jump(merge_id)?;

        // Lower else branch
        self.set_current_block(else_id)?;
        let else_value = if let Some(else_expr) = else_branch {
            self.lower_expr(else_expr)?
        } else {
            // No else branch - use nil (0)
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                dest
            })?
        };
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Store {
                addr: temp_addr,
                value: else_value,
                ty: expr_ty,
            });
        })?;
        self.finalize_block_jump(merge_id)?;

        // Load merged value in merge block
        self.set_current_block(merge_id)?;
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Load {
                dest,
                addr: temp_addr,
                ty: expr_ty,
            });
            dest
        })
    }

    pub(super) fn lower_let_in_expr(
        &mut self,
        local_idx: usize,
        value: &HirExpr,
        body: &HirExpr,
    ) -> MirLowerResult<VReg> {
        // Store the value into the local variable, then evaluate body
        let val_reg = self.lower_expr(value)?;
        let value_ty = value.ty;
        self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: local_idx,
            });
            block.instructions.push(MirInst::Store {
                addr,
                value: val_reg,
                ty: value_ty,
            });
        })?;
        self.lower_expr(body)
    }
}
