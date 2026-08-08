//! Weaving execution logic for inserting advice calls into MIR.

use super::diagnostics::{DiagnosticLevel, WeavingDiagnostic};
use super::matcher::Weaver;
use super::types::*;
use crate::mir::{BlockId, CallTarget, MirBlock, MirFunction, MirInst, VReg};
use crate::security::SecurityAdviceStep;
use std::collections::HashMap;

impl Weaver {
    /// Weave advice into a MIR function.
    pub fn weave_function(&self, function: &mut MirFunction) -> WeavingResult {
        if !self.config.enabled {
            return WeavingResult::default();
        }

        let join_points = self.detect_join_points(function);
        let mut result = WeavingResult::default();

        // Track which advice rules were used
        let mut used_advice_rules: std::collections::HashSet<String> = std::collections::HashSet::new();

        // Group join points by block for efficient insertion
        let mut insertions: HashMap<BlockId, Vec<(usize, JoinPointKind, Vec<MatchedAdvice>)>> = HashMap::new();

        for join_point in join_points {
            let (advices, diagnostics) = self.match_advice(&join_point);

            // Collect diagnostics
            for diagnostic in diagnostics {
                result.add_diagnostic(diagnostic);
            }

            if !advices.is_empty() {
                result.join_points_woven += 1;
                result.advices_inserted += advices.len();

                // Record for debugging
                for advice in &advices {
                    result
                        .advice_calls
                        .push((join_point.kind.clone(), advice.advice_function.clone()));

                    // Track used advice rules
                    used_advice_rules.insert(advice.advice_function.clone());
                }

                // Group by block
                insertions.entry(join_point.block_id).or_default().push((
                    join_point.instruction_index,
                    join_point.kind,
                    advices,
                ));
            }
        }

        // Check for unused advice rules
        for rule in self.config.all_advices() {
            if !used_advice_rules.contains(&rule.advice_function) {
                result.add_diagnostic(
                    WeavingDiagnostic::warning(format!(
                        "Advice '{}' was never applied (predicate may be too specific or never matches)",
                        rule.advice_function
                    ))
                    .with_predicate(rule.predicate_text.clone())
                    .with_location(function.name.clone()),
                );
            }
        }

        // Add informational diagnostic about weaving summary
        if result.join_points_woven > 0 {
            result.add_diagnostic(
                WeavingDiagnostic::info(format!(
                    "Woven {} advice calls at {} join points",
                    result.advices_inserted, result.join_points_woven
                ))
                .with_location(function.name.clone()),
            );
        }

        // Insert advice calls into blocks
        // Process blocks in reverse order of instruction indices to avoid offset issues
        for (block_id, mut block_insertions) in insertions {
            // Sort by instruction index in descending order
            block_insertions.sort_by(|a, b| b.0.cmp(&a.0));

            if let Some(block_index) = function.blocks.iter().position(|b| b.id == block_id) {
                for (instruction_index, join_point_kind, advices) in block_insertions {
                    self.insert_advice_calls(function, block_index, instruction_index, &join_point_kind, &advices);
                }
            }
        }

        result
    }

    /// Create a MIR instruction for calling an advice function.
    fn create_advice_call(&self, advice_function: &str, args: Vec<VReg>) -> MirInst {
        MirInst::Call {
            dest: None,                                          // Advice functions don't return values (for now)
            target: CallTarget::Io(advice_function.to_string()), // Use Io effect by default
            args,
        }
    }

    fn create_security_advice_insts(&self, function: &mut MirFunction, step: &SecurityAdviceStep) -> Vec<MirInst> {
        let (name, ids): (&str, Vec<u64>) = match step {
            SecurityAdviceStep::EnterGate { gate_id, .. } => ("rt_security_enter_gate", vec![*gate_id]),
            SecurityAdviceStep::RequirePolicy { policy_id, .. } => ("rt_security_require_policy", vec![*policy_id]),
            SecurityAdviceStep::EnterSandbox { sandbox_id, .. } => ("rt_security_enter_sandbox", vec![*sandbox_id]),
            SecurityAdviceStep::AuditStart { gate_id, audit_id, .. } => {
                ("rt_security_audit_start", vec![*gate_id, *audit_id])
            }
            SecurityAdviceStep::Proceed => return Vec::new(),
            SecurityAdviceStep::AuditSuccess { gate_id, .. } => ("rt_security_audit_success", vec![*gate_id]),
            SecurityAdviceStep::AuditFailure { gate_id, .. } => ("rt_security_audit_failure", vec![*gate_id]),
            SecurityAdviceStep::ExitSandbox { sandbox_id } => ("rt_security_exit_sandbox", vec![*sandbox_id]),
            SecurityAdviceStep::ExitGate { gate_id } => ("rt_security_exit_gate", vec![*gate_id]),
        };
        let mut insts = Vec::new();
        let mut args = Vec::new();
        for id in ids {
            let dest = function.new_vreg();
            insts.push(MirInst::ConstInt { dest, value: id as i64 });
            args.push(dest);
        }
        insts.push(self.create_advice_call(name, args));
        insts
    }

    /// Insert advice calls into a block at a specific instruction index.
    /// Returns the number of instructions inserted.
    fn insert_advice_calls(
        &self,
        function: &mut MirFunction,
        block_index: usize,
        instruction_index: usize,
        join_point_kind: &JoinPointKind,
        advices: &[MatchedAdvice],
    ) -> usize {
        let mut inserted = 0;

        // Separate advices by form
        let before_advices: Vec<_> = advices.iter().filter(|a| a.form == AdviceForm::Before).collect();
        let after_success_advices: Vec<_> = advices.iter().filter(|a| a.form == AdviceForm::AfterSuccess).collect();
        let after_error_advices: Vec<_> = advices.iter().filter(|a| a.form == AdviceForm::AfterError).collect();

        // Insert Before advices before the join point instruction
        for (i, advice) in before_advices.iter().enumerate() {
            let call_inst = self.create_advice_call(&advice.advice_function, Vec::new());
            function.blocks[block_index]
                .instructions
                .insert(instruction_index + i, call_inst);
            inserted += 1;
        }

        // Insert AfterSuccess advices after the join point instruction
        // For execution join points (index 0 with no actual instruction),
        // insert at the current end of the block
        let after_index = if instruction_index == 0 && function.blocks[block_index].instructions.len() <= inserted {
            // Execution join point - append after all before advices
            instruction_index + inserted
        } else {
            // Regular join point - insert after the actual instruction
            instruction_index + inserted + 1
        };

        for (i, advice) in after_success_advices.iter().enumerate() {
            let call_inst = self.create_advice_call(&advice.advice_function, Vec::new());
            function.blocks[block_index]
                .instructions
                .insert(after_index + i, call_inst);
            inserted += 1;
        }

        // Insert AfterError advices at error handling points
        // For error join points (ResultErr, TryUnwrap), insert immediately after
        if !after_error_advices.is_empty() {
            let error_index = if instruction_index == 0 && function.blocks[block_index].instructions.len() <= inserted {
                // Execution join point - append after all other advices
                instruction_index + inserted
            } else {
                // Error join point - insert after the error instruction
                instruction_index + inserted + 1
            };

            for (i, advice) in after_error_advices.iter().enumerate() {
                let call_inst = self.create_advice_call(&advice.advice_function, Vec::new());
                function.blocks[block_index]
                    .instructions
                    .insert(error_index + i, call_inst);
                inserted += 1;
            }
        }

        // Handle Around advices
        // Note: Around advice uses the runtime proceed mechanism (rt_aop_invoke_around)
        // True compile-time around would require extracting the join point into a continuation,
        // which needs complex MIR transformations. For now, we document this limitation.
        let around_advices: Vec<_> = advices.iter().filter(|a| a.form == AdviceForm::Around).collect();

        if !around_advices.is_empty() {
            for advice in around_advices {
                let Some(plan) = &advice.security_plan else {
                    continue;
                };
                let is_error_join_point = matches!(join_point_kind, JoinPointKind::Error { .. });
                let security_insert_index = if is_error_join_point {
                    if instruction_index == 0 && function.blocks[block_index].instructions.len() <= inserted {
                        instruction_index + inserted
                    } else {
                        instruction_index + inserted + 1
                    }
                } else {
                    instruction_index + inserted
                };
                let mut offset = 0;
                for step in &plan.steps {
                    let should_materialize = if is_error_join_point {
                        matches!(
                            step,
                            SecurityAdviceStep::AuditFailure { .. }
                                | SecurityAdviceStep::ExitSandbox { .. }
                                | SecurityAdviceStep::ExitGate { .. }
                        )
                    } else {
                        !matches!(step, SecurityAdviceStep::AuditFailure { .. })
                    };
                    if !should_materialize {
                        continue;
                    }
                    let insts = self.create_security_advice_insts(function, step);
                    for inst in insts {
                        let insert_at =
                            (security_insert_index + offset).min(function.blocks[block_index].instructions.len());
                        function.blocks[block_index].instructions.insert(insert_at, inst);
                        offset += 1;
                    }
                }
                inserted += offset;
            }

            // Around advice requires wrapping the join point in a continuation
            // This is complex and requires MIR function extraction/closure creation
            // For now, around advice only works via the interpreter's runtime support
            //
            // Future implementation would:
            // 1. Extract instructions from join point to a new internal function (continuation)
            // 2. Insert call to rt_aop_invoke_around with:
            //    - target: pointer to continuation function
            //    - advices: array of advice function pointers
            //    - advice_len: number of advices
            //    - argc/argv: original function arguments
            // 3. Replace join point with the invoke_around call
            //
            // Limitation documented in doc/status/aop_implementation_status.md
        }

        inserted
    }
}
