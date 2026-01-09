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
            block
                .instructions
                .push(MirInst::PathProbe { path_id, block_id });
        })?;

        Ok(())
    }
}
