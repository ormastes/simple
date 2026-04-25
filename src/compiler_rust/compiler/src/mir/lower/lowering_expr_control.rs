//! Control flow expression lowering: If, LetIn.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{BinOp, HirExpr, HirExprKind, TypeId};
use crate::mir::instructions::{MirInst, VReg};

/// B5 (compiler_bugs_for_crypto_2026-04-25.md): minimum dense int-match arm
/// count and maximum key span for Switch lowering. Below these thresholds the
/// MIR lowerer keeps the existing nested If chain (cheaper than a jump table
/// for small/sparse switches).
const SWITCH_MIN_ARMS: usize = 4;
const SWITCH_MAX_SPAN: i64 = 1024;

/// Try to peel a nested HIR If chain whose conditions all test
/// `Local(local_idx) == Integer(k)` against a constant. Returns the collected
/// `(key, arm_body)` pairs and the final `else_branch` (the default arm).
///
/// Returns `None` if any node in the chain doesn't match the pattern, so the
/// caller falls back to the existing `lower_expr` path.
fn try_collect_int_match<'a>(
    body: &'a HirExpr,
    local_idx: usize,
) -> Option<(Vec<(i64, &'a HirExpr)>, &'a HirExpr)> {
    let mut cases: Vec<(i64, &'a HirExpr)> = Vec::new();
    let mut node = body;
    loop {
        let HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } = &node.kind
        else {
            // End of chain — current node is the default arm.
            return if cases.is_empty() {
                None
            } else {
                Some((cases, node))
            };
        };
        let Some(else_b) = else_branch.as_ref() else {
            return None;
        };
        let HirExprKind::Binary { op: BinOp::Eq, left, right } = &condition.kind else {
            return None;
        };
        // Accept Local(idx) == Integer(k) in either operand order.
        let key = match (&left.kind, &right.kind) {
            (HirExprKind::Local(n), HirExprKind::Integer(k)) if *n == local_idx => *k,
            (HirExprKind::Integer(k), HirExprKind::Local(n)) if *n == local_idx => *k,
            _ => return None,
        };
        cases.push((key, then_branch.as_ref()));
        node = else_b.as_ref();
    }
}

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

        // B5: detect dense integer match (lowered as LetIn { ... If chain })
        // and emit a Switch terminator so Cranelift produces br_table.
        if value_ty == TypeId::I64 {
            if let Some((cases, default)) = try_collect_int_match(body, local_idx) {
                let span = cases
                    .iter()
                    .map(|(k, _)| *k)
                    .fold((i64::MAX, i64::MIN), |(lo, hi), k| (lo.min(k), hi.max(k)));
                let key_span = span.1.saturating_sub(span.0);
                if cases.len() >= SWITCH_MIN_ARMS && key_span >= 0 && key_span <= SWITCH_MAX_SPAN {
                    return self.lower_int_switch(val_reg, body.ty, cases, default);
                }
            }
        }

        self.lower_expr(body)
    }

    /// Lower a dense integer match as a Switch terminator with one block per
    /// arm and a default block. Each arm stores its result into a temp local
    /// then jumps to a merge block; the merge block loads and returns it.
    fn lower_int_switch(
        &mut self,
        discriminant: VReg,
        result_ty: TypeId,
        cases: Vec<(i64, &HirExpr)>,
        default: &HirExpr,
    ) -> MirLowerResult<VReg> {
        use crate::mir::effects::LocalKind;
        use crate::mir::function::MirLocal;

        // Temp local for merged result.
        let temp_local_index = self.with_func(|func, _| {
            let index = func.params.len() + func.locals.len();
            func.locals.push(MirLocal {
                name: format!("$switch_merge_{}", index),
                ty: result_ty,
                kind: LocalKind::Local,
                is_ghost: false,
            });
            index
        })?;
        let temp_addr = self.with_func(|func, current_block| {
            let addr = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr,
                local_index: temp_local_index,
            });
            addr
        })?;

        // Allocate one block per case + default + merge, and seal the current
        // block with a Switch terminator.
        let merge_id = self.with_func(|func, _| func.new_block())?;
        let default_id = self.with_func(|func, _| func.new_block())?;
        let case_blocks: Vec<_> = cases
            .iter()
            .map(|(k, _)| {
                self.with_func(|func, _| func.new_block())
                    .map(|b| (*k, b))
            })
            .collect::<MirLowerResult<Vec<_>>>()?;
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.terminator = crate::mir::Terminator::Switch {
                discriminant,
                cases: case_blocks.iter().map(|(k, b)| (*k, *b)).collect(),
                default: default_id,
            };
        })?;

        // Lower each arm body into its block, store result, jump to merge.
        for ((_, arm_body), (_, arm_block)) in cases.iter().zip(case_blocks.iter()) {
            self.set_current_block(*arm_block)?;
            let v = self.lower_expr(arm_body)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: temp_addr,
                    value: v,
                    ty: result_ty,
                });
            })?;
            self.finalize_block_jump(merge_id)?;
        }

        // Default arm.
        self.set_current_block(default_id)?;
        let v = self.lower_expr(default)?;
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Store {
                addr: temp_addr,
                value: v,
                ty: result_ty,
            });
        })?;
        self.finalize_block_jump(merge_id)?;

        // Merge block: load the result and return it.
        self.set_current_block(merge_id)?;
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Load {
                dest,
                addr: temp_addr,
                ty: result_ty,
            });
            dest
        })
    }
}
