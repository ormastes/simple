//! Operator expression lowering: Binary, Unary, Cast.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirExpr, TypeId, UnaryOp};
#[allow(unused_imports)]
use crate::mir::instructions::MirInst;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_binary_expr(
        &mut self,
        op: BinOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> MirLowerResult<VReg> {
        // For compound boolean expressions (And, Or), emit condition probes
        // to track each sub-condition for condition/MC-DC coverage (#674)
        if self.coverage_enabled && matches!(op, BinOp::And | BinOp::Or) {
            // Create a decision ID for this compound expression
            let decision_id = self.next_decision_id();

            // Lower left operand and emit condition probe
            let left_reg = self.lower_expr(left)?;
            self.emit_condition_probe(decision_id, left_reg, 0, 0)?;

            // Lower right operand and emit condition probe
            let right_reg = self.lower_expr(right)?;
            self.emit_condition_probe(decision_id, right_reg, 0, 0)?;

            // Compute the final result
            let dest = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::BinOp {
                    dest,
                    op,
                    left: left_reg,
                    right: right_reg,
                });
                dest
            })?;

            // Emit decision probe for the overall result
            self.emit_decision_probe(dest, 0, 0)?;

            Ok(dest)
        } else {
            // Non-coverage path or non-boolean operations
            let left_reg = self.lower_expr(left)?;
            let right_reg = self.lower_expr(right)?;

            // String concatenation: if either side is text/string and op is Add,
            // emit rt_string_concat call instead of iadd
            let is_string_add = op == BinOp::Add
                && (left.ty == TypeId::STRING
                    || right.ty == TypeId::STRING
                    || left.ty == TypeId::ANY
                    || right.ty == TypeId::ANY);
            if is_string_add {
                // Convert non-string side to string via rt_to_string if needed
                let left_str = if left.ty != TypeId::STRING && left.ty != TypeId::ANY {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: crate::mir::CallTarget::from_name("rt_to_string"),
                            args: vec![left_reg],
                        });
                        dest
                    })?
                } else {
                    left_reg
                };
                let right_str = if right.ty != TypeId::STRING && right.ty != TypeId::ANY {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: crate::mir::CallTarget::from_name("rt_to_string"),
                            args: vec![right_reg],
                        });
                        dest
                    })?
                } else {
                    right_reg
                };
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_string_concat"),
                        args: vec![left_str, right_str],
                    });
                    dest
                })
            } else {
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::BinOp {
                        dest,
                        op,
                        left: left_reg,
                        right: right_reg,
                    });
                    dest
                })
            }
        }
    }

    pub(super) fn lower_unary_expr(&mut self, op: UnaryOp, operand: &HirExpr) -> MirLowerResult<VReg> {
        let operand_reg = self.lower_expr(operand)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::UnaryOp {
                dest,
                op,
                operand: operand_reg,
            });
            dest
        })
    }

    pub(super) fn lower_cast_expr(
        &mut self,
        inner: &HirExpr,
        target: TypeId,
    ) -> MirLowerResult<VReg> {
        let source_reg = self.lower_expr(inner)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Cast {
                dest,
                source: source_reg,
                from_ty: inner.ty,
                to_ty: target,
            });
            dest
        })
    }
}
