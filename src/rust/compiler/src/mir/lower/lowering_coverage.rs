//! Coverage instrumentation for MIR lowering

use super::lowering_core::{MirLowerResult, MirLowerer};
use crate::mir::instructions::MirInst;

impl<'a> MirLowerer<'a> {
    /// Generate a unique decision ID
    pub(super) fn next_decision_id(&mut self) -> u32 {
        let id = self.decision_counter;
        self.decision_counter += 1;
        id
    }

    /// Emit a decision probe instruction if coverage is enabled
    pub(super) fn emit_decision_probe(
        &mut self,
        cond_reg: crate::mir::instructions::VReg,
        line: u32,
        column: u32,
    ) -> MirLowerResult<()> {
        if !self.coverage_enabled {
            return Ok(());
        }

        let decision_id = self.next_decision_id();
        let file = self.current_file.clone().unwrap_or_default();

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::DecisionProbe {
                decision_id,
                result: cond_reg,
                file,
                line,
                column,
            });
        })?;

        Ok(())
    }

    /// Emit a path probe instruction if coverage is enabled
    #[allow(dead_code)]
    pub(super) fn emit_path_probe(&mut self, path_id: u32, block_id: u32) -> MirLowerResult<()> {
        if !self.coverage_enabled {
            return Ok(());
        }

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::PathProbe { path_id, block_id });
        })?;

        Ok(())
    }

    /// Generate a unique condition ID within a decision
    pub(super) fn next_condition_id(&mut self, decision_id: u32) -> u32 {
        let key = decision_id;
        let counter = self.condition_counters.entry(key).or_insert(0);
        let id = *counter;
        *counter += 1;
        id
    }

    /// Emit a condition probe instruction if coverage is enabled.
    /// Tracks individual conditions within compound boolean expressions (&&, ||).
    pub(super) fn emit_condition_probe(
        &mut self,
        decision_id: u32,
        cond_reg: crate::mir::instructions::VReg,
        line: u32,
        column: u32,
    ) -> MirLowerResult<()> {
        if !self.coverage_enabled {
            return Ok(());
        }

        let condition_id = self.next_condition_id(decision_id);
        let file = self.current_file.clone().unwrap_or_default();

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::ConditionProbe {
                decision_id,
                condition_id,
                result: cond_reg,
                file,
                line,
                column,
            });
        })?;

        Ok(())
    }

    /// Generate a unique path ID for function entry coverage
    pub(super) fn next_path_id(&mut self) -> u32 {
        let id = self.path_counter;
        self.path_counter += 1;
        id
    }

    /// Emit a function entry path probe if coverage is enabled.
    /// Tracks which functions are executed for function-level coverage.
    pub(super) fn emit_function_entry_probe(&mut self) -> MirLowerResult<()> {
        if !self.coverage_enabled {
            return Ok(());
        }

        let path_id = self.next_path_id();
        // Block ID 0 indicates function entry
        let block_id = 0;

        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::PathProbe { path_id, block_id });
        })?;

        Ok(())
    }
}
