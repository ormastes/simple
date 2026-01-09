//! Contract emission methods for MIR lowering
//!
//! This module contains methods for emitting contract checks (preconditions,
//! postconditions, invariants, and error contracts) during MIR lowering.

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::hir::HirContract;
use crate::mir::instructions::{ContractKind, MirInst, VReg};

impl<'a> MirLowerer<'a> {
    /// Emit entry contract checks: preconditions, old() captures, invariants at entry
    pub(super) fn emit_entry_contracts(&mut self, contract: &HirContract) -> MirLowerResult<()> {
        let func_name = self.try_contract_ctx()?.func_name.clone();

        // 1. Check preconditions
        for clause in &contract.preconditions {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::Precondition,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        // 2. Capture old() values
        for (idx, expr) in &contract.old_values {
            let value_reg = self.lower_expr(expr)?;
            let dest = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractOldCapture {
                    dest,
                    value: value_reg,
                });
                dest
            })?;
            let ctx = self.try_contract_ctx_mut()?;
            ctx.old_captures.insert(*idx, dest);
            // Store mapping from index to expression for reverse lookup during ContractOld lowering
            ctx.old_expr_map.insert(*idx, expr.clone());
        }

        // 3. Check invariants at entry
        for clause in &contract.invariants {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::InvariantEntry,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        Ok(())
    }

    /// Emit exit contract checks: invariants, postconditions (for successful returns)
    pub(super) fn emit_exit_contracts(
        &mut self,
        contract: &HirContract,
        return_value: Option<VReg>,
    ) -> MirLowerResult<()> {
        let func_name = self.try_contract_ctx()?.func_name.clone();

        // Store return value in contract context for ContractResult expressions
        if return_value.is_some() {
            self.try_contract_ctx_mut()?.return_value = return_value;
        }

        // 1. Check invariants at exit
        for clause in &contract.invariants {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::InvariantExit,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        // 2. Check postconditions (only for successful returns)
        for clause in &contract.postconditions {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::Postcondition,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        Ok(())
    }

    /// Emit error contract checks: error postconditions (for error returns)
    pub(super) fn emit_error_contracts(
        &mut self,
        contract: &HirContract,
        error_value: VReg,
    ) -> MirLowerResult<()> {
        let func_name = self.try_contract_ctx()?.func_name.clone();

        // Store error value in contract context for error postcondition expressions
        // Use the error binding name if specified, otherwise "err"
        self.try_contract_ctx_mut()?.return_value = Some(error_value);

        // Check error postconditions (only for error returns)
        for clause in &contract.error_postconditions {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::ErrorPostcondition,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        Ok(())
    }
}
