//! Async/closure expression lowering: Lambda, Yield, GeneratorCreate, FutureCreate, Await, ActorSpawn.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::{HirExpr, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_lambda_expr(&mut self, body: &HirExpr, captures: &[usize]) -> MirLowerResult<VReg> {
        // Save current block
        let original_block = self.with_func(|_, current_block| current_block)?;

        // Create body block and switch to it (like generators/futures)
        let body_block = self.with_func(|func, _| func.new_block())?;
        self.set_current_block(body_block)?;

        // Lower the lambda body INTO the body block
        let body_reg = self.lower_expr(body)?;

        // Add return terminator to body block
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.terminator = crate::mir::Terminator::Return(Some(body_reg));
        })?;

        // Switch back to original block
        self.set_current_block(original_block)?;

        // Each capture is 8 bytes (pointer-sized)
        let closure_size = 8 + (captures.len() as u32 * 8);
        let capture_offsets: Vec<u32> = (0..captures.len()).map(|i| 8 + (i as u32 * 8)).collect();
        let capture_types: Vec<TypeId> = captures.iter().map(|_| TypeId::I64).collect();

        // Load captured variables
        let mut capture_regs = Vec::new();
        for &local_idx in captures.iter() {
            let reg = self.with_func(|func, current_block| {
                let addr_reg = func.new_vreg();
                let val_reg = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::LocalAddr {
                    dest: addr_reg,
                    local_index: local_idx,
                });
                block.instructions.push(MirInst::Load {
                    dest: val_reg,
                    addr: addr_reg,
                    ty: TypeId::I64,
                });
                val_reg
            })?;
            capture_regs.push(reg);
        }

        // Generate function name matching expand_with_outlined convention
        let parent_name = self
            .try_contract_ctx()
            .map(|ctx| ctx.func_name.clone())
            .unwrap_or_else(|_| "anonymous".to_string());
        let func_name = format!("{}_outlined_{}", parent_name, body_block.0);

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ClosureCreate {
                dest,
                func_name,
                closure_size,
                capture_offsets,
                capture_types,
                captures: capture_regs,
                body_block: Some(body_block),
            });
            dest
        })
    }

    pub(super) fn lower_yield_expr(&mut self, value: &HirExpr) -> MirLowerResult<VReg> {
        let value_reg = self.lower_expr(value)?;

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Yield { value: value_reg });
            // Yield doesn't have a meaningful result, return the value register
            value_reg
        })
    }

    pub(super) fn lower_generator_create_expr(&mut self, body: &HirExpr) -> MirLowerResult<VReg> {
        // Save current block
        let original_block = self.with_func(|_, current_block| current_block)?;

        // Create body block and switch to it
        let body_block = self.with_func(|func, _| func.new_block())?;
        self.set_current_block(body_block)?;

        // Lower body expression INTO the body_block
        let body_reg = self.lower_expr(body)?;

        // Add return terminator to body_block
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.terminator = crate::mir::Terminator::Return(Some(body_reg));
        })?;

        // Switch back to original block
        self.set_current_block(original_block)?;

        // Emit GeneratorCreate in original block
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::GeneratorCreate { dest, body_block });
            dest
        })
    }

    pub(super) fn lower_future_create_expr(&mut self, body: &HirExpr) -> MirLowerResult<VReg> {
        // Save current block
        let original_block = self.with_func(|_, current_block| current_block)?;

        // Create body block and switch to it
        let body_block = self.with_func(|func, _| func.new_block())?;
        self.set_current_block(body_block)?;

        // Lower body expression INTO the body_block
        let body_reg = self.lower_expr(body)?;

        // Add return terminator to body_block
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.terminator = crate::mir::Terminator::Return(Some(body_reg));
        })?;

        // Switch back to original block
        self.set_current_block(original_block)?;

        // Emit FutureCreate in original block
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::FutureCreate { dest, body_block });
            dest
        })
    }

    pub(super) fn lower_await_expr(&mut self, future: &HirExpr) -> MirLowerResult<VReg> {
        let future_reg = self.lower_expr(future)?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Await {
                dest,
                future: future_reg,
            });
            dest
        })
    }

    pub(super) fn lower_actor_spawn_expr(&mut self, body: &HirExpr) -> MirLowerResult<VReg> {
        // Lower the body expression first
        let _body_reg = self.lower_expr(body)?;

        // Create a new block for the actor body
        let body_block = self.with_func(|func, _| func.new_block())?;

        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ActorSpawn { dest, body_block });
            dest
        })
    }
}
