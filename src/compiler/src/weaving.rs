//! Compile-time AOP weaving infrastructure.
//!
//! This module provides compile-time weaving of aspects into the MIR.
//! It detects join points (execution, decision, condition) and inserts
//! advice calls (before, after_success, after_error, around).
//!
//! See doc/research/aop.md for the complete specification.

use crate::aop_config::AopConfig;
use crate::hir::BinOp;
use crate::mir::{BlockId, CallTarget, MirBlock, MirFunction, MirInst, VReg};
use crate::predicate::{MatchContext, PredicateContext, Selector};
use std::collections::HashMap;

/// Advice form determines when and how advice is executed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdviceForm {
    /// Execute before the join point
    Before,
    /// Execute after successful completion
    AfterSuccess,
    /// Execute after error
    AfterError,
    /// Wrap the join point (can control execution via proceed)
    Around,
}

/// Join point types in the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JoinPointKind {
    /// Function execution
    Execution {
        function_name: String,
        signature: String,
    },
    /// Decision point (if/match condition)
    Decision {
        location: String,
    },
    /// Condition evaluation
    Condition {
        location: String,
    },
}

/// A detected join point in the MIR.
#[derive(Debug, Clone)]
pub struct JoinPoint {
    /// Kind of join point
    pub kind: JoinPointKind,
    /// Block ID where the join point occurs
    pub block_id: BlockId,
    /// Instruction index within the block
    pub instruction_index: usize,
    /// Match context for predicate evaluation
    pub context: JoinPointContext,
}

/// Context information for join point matching.
#[derive(Debug, Clone)]
pub struct JoinPointContext {
    pub function_name: String,
    pub module_path: String,
    pub signature: String,
    pub attributes: Vec<String>,
    pub effects: Vec<String>,
}

impl JoinPointContext {
    /// Create a match context for predicate evaluation.
    pub fn to_match_context(&self) -> MatchContext<'_> {
        MatchContext::new()
            .with_type_name(&self.function_name)
            .with_module_path(&self.module_path)
            .with_signature(&self.signature)
            .with_attrs(&self.attributes)
            .with_effects(&self.effects)
    }
}

/// Matched advice for a join point.
#[derive(Debug, Clone)]
pub struct MatchedAdvice {
    pub advice_function: String,
    pub form: AdviceForm,
    pub priority: i64,
    pub specificity: i32,
}

/// Weaving configuration loaded from TOML.
#[derive(Debug, Clone)]
pub struct WeavingConfig {
    pub enabled: bool,
    pub before_advices: Vec<WeavingRule>,
    pub after_success_advices: Vec<WeavingRule>,
    pub after_error_advices: Vec<WeavingRule>,
    pub around_advices: Vec<WeavingRule>,
}

#[derive(Debug, Clone)]
pub struct WeavingRule {
    pub predicate_text: String,
    pub advice_function: String,
    pub form: AdviceForm,
    pub priority: i64,
}

impl AdviceForm {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "before" => Some(AdviceForm::Before),
            "after_success" | "after-success" => Some(AdviceForm::AfterSuccess),
            "after_error" | "after-error" => Some(AdviceForm::AfterError),
            "around" => Some(AdviceForm::Around),
            _ => None,
        }
    }
}

impl WeavingConfig {
    /// Create an empty configuration (weaving disabled).
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            before_advices: Vec::new(),
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        }
    }

    /// Load from AOP configuration.
    pub fn from_aop_config(aop_config: &AopConfig) -> Self {
        // For now, treat runtime around as compile-time around
        // In the future, we'll have separate compile-time config
        let around_advices = aop_config
            .around
            .iter()
            .map(|rule| WeavingRule {
                predicate_text: rule.raw_predicate.clone(),
                advice_function: rule.advice.clone(),
                form: AdviceForm::Around,
                priority: rule.priority,
            })
            .collect();

        Self {
            enabled: aop_config.runtime_enabled,
            before_advices: Vec::new(),
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices,
        }
    }

    /// Get all advice rules.
    fn all_advices(&self) -> impl Iterator<Item = &WeavingRule> {
        self.before_advices
            .iter()
            .chain(self.after_success_advices.iter())
            .chain(self.after_error_advices.iter())
            .chain(self.around_advices.iter())
    }
}

/// Main weaving engine.
pub struct Weaver {
    config: WeavingConfig,
}

impl Weaver {
    /// Create a new weaver with the given configuration.
    pub fn new(config: WeavingConfig) -> Self {
        Self { config }
    }

    /// Detect join points in a MIR function.
    pub fn detect_join_points(&self, function: &MirFunction) -> Vec<JoinPoint> {
        if !self.config.enabled {
            return Vec::new();
        }

        let mut join_points = Vec::new();

        // Detect function execution join point (at entry)
        let context = JoinPointContext {
            function_name: function.name.clone(),
            module_path: String::new(), // TODO: Get from function metadata
            signature: self.build_signature(function),
            attributes: Vec::new(), // TODO: Get from function metadata
            effects: Vec::new(),    // TODO: Get from function effects
        };

        join_points.push(JoinPoint {
            kind: JoinPointKind::Execution {
                function_name: function.name.clone(),
                signature: context.signature.clone(),
            },
            block_id: function.entry_block,
            instruction_index: 0,
            context: context.clone(),
        });

        // Detect decision/condition join points by scanning instructions
        for block in &function.blocks {
            for (idx, inst) in block.instructions.iter().enumerate() {
                match inst {
                    MirInst::BinOp { dest: _, op, left: _, right: _ } => {
                        // Condition evaluation (comparison operators)
                        match op {
                            BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                                join_points.push(JoinPoint {
                                    kind: JoinPointKind::Condition {
                                        location: format!("{}:block{:?}:inst{}",
                                            function.name, block.id, idx),
                                    },
                                    block_id: block.id,
                                    instruction_index: idx,
                                    context: context.clone(),
                                });
                            }
                            _ => {}
                        }
                    }
                    _ => {
                        // Check for decision points (branches)
                        if self.is_decision_instruction(inst) {
                            join_points.push(JoinPoint {
                                kind: JoinPointKind::Decision {
                                    location: format!("{}:block{:?}:inst{}",
                                        function.name, block.id, idx),
                                },
                                block_id: block.id,
                                instruction_index: idx,
                                context: context.clone(),
                            });
                        }
                    }
                }
            }
        }

        join_points
    }

    /// Check if an instruction represents a decision point.
    fn is_decision_instruction(&self, inst: &MirInst) -> bool {
        matches!(inst,
            MirInst::PatternTest { .. } |
            MirInst::EnumDiscriminant { .. } |
            MirInst::TryUnwrap { .. }  // Result/Option unwrapping is a decision point
        )
    }

    /// Match advice to join points.
    pub fn match_advice(&self, join_point: &JoinPoint) -> Vec<MatchedAdvice> {
        if !self.config.enabled {
            return Vec::new();
        }

        let match_ctx = join_point.context.to_match_context();
        let mut matched = Vec::new();

        for rule in self.config.all_advices() {
            // Parse predicate and check if it matches
            if let Ok(predicate) = crate::predicate_parser::parse_predicate(&rule.predicate_text) {
                // Validate for weaving context
                if predicate
                    .validate(PredicateContext::Weaving)
                    .is_ok()
                {
                    if predicate.matches(&match_ctx) {
                        matched.push(MatchedAdvice {
                            advice_function: rule.advice_function.clone(),
                            form: rule.form,
                            priority: rule.priority,
                            specificity: predicate.specificity(),
                        });
                    }
                }
            }
        }

        // Sort by priority (higher first), then specificity, then stable order
        matched.sort_by(|a, b| {
            b.priority
                .cmp(&a.priority)
                .then_with(|| b.specificity.cmp(&a.specificity))
        });

        matched
    }

    /// Weave advice into a MIR function.
    pub fn weave_function(&self, function: &mut MirFunction) -> WeavingResult {
        if !self.config.enabled {
            return WeavingResult::default();
        }

        let join_points = self.detect_join_points(function);
        let mut result = WeavingResult::default();

        // Group join points by block for efficient insertion
        let mut insertions: HashMap<BlockId, Vec<(usize, Vec<MatchedAdvice>)>> = HashMap::new();

        for join_point in join_points {
            let advices = self.match_advice(&join_point);
            if !advices.is_empty() {
                result.join_points_woven += 1;
                result.advices_inserted += advices.len();

                // Record for debugging
                for advice in &advices {
                    result
                        .advice_calls
                        .push((join_point.kind.clone(), advice.advice_function.clone()));
                }

                // Group by block
                insertions
                    .entry(join_point.block_id)
                    .or_insert_with(Vec::new)
                    .push((join_point.instruction_index, advices));
            }
        }

        // Insert advice calls into blocks
        // Process blocks in reverse order of instruction indices to avoid offset issues
        for (block_id, mut block_insertions) in insertions {
            // Sort by instruction index in descending order
            block_insertions.sort_by(|a, b| b.0.cmp(&a.0));

            if let Some(block) = function.blocks.iter_mut().find(|b| b.id == block_id) {
                for (instruction_index, advices) in block_insertions {
                    self.insert_advice_calls(block, instruction_index, &advices);
                }
            }
        }

        result
    }

    /// Build a signature string for a function.
    fn build_signature(&self, function: &MirFunction) -> String {
        // Simple signature: return_type name(param_types...)
        // TODO: Use proper type names instead of TypeId debug format
        // For now, just use simple format that matches predicate patterns
        let param_types = function
            .params
            .iter()
            .map(|_| "Any".to_string())  // Simplified for now
            .collect::<Vec<_>>()
            .join(", ");

        // Use "*" for return type to match any
        format!("* {}({})", function.name, param_types)
    }

    /// Create a MIR instruction for calling an advice function.
    fn create_advice_call(&self, advice_function: &str, args: Vec<VReg>) -> MirInst {
        MirInst::Call {
            dest: None, // Advice functions don't return values (for now)
            target: CallTarget::Io(advice_function.to_string()), // Use Io effect by default
            args,
        }
    }

    /// Insert advice calls into a block at a specific instruction index.
    /// Returns the number of instructions inserted.
    fn insert_advice_calls(
        &self,
        block: &mut MirBlock,
        instruction_index: usize,
        advices: &[MatchedAdvice],
    ) -> usize {
        let mut inserted = 0;

        // Separate advices by form
        let before_advices: Vec<_> = advices
            .iter()
            .filter(|a| a.form == AdviceForm::Before)
            .collect();
        let after_success_advices: Vec<_> = advices
            .iter()
            .filter(|a| a.form == AdviceForm::AfterSuccess)
            .collect();

        // Insert Before advices before the join point instruction
        for (i, advice) in before_advices.iter().enumerate() {
            let call_inst = self.create_advice_call(&advice.advice_function, Vec::new());
            block
                .instructions
                .insert(instruction_index + i, call_inst);
            inserted += 1;
        }

        // Insert AfterSuccess advices after the join point instruction
        // For execution join points (index 0 with no actual instruction),
        // insert at the current end of the block
        let after_index = if instruction_index == 0 && block.instructions.len() <= inserted {
            // Execution join point - append after all before advices
            instruction_index + inserted
        } else {
            // Regular join point - insert after the actual instruction
            instruction_index + inserted + 1
        };

        for (i, advice) in after_success_advices.iter().enumerate() {
            let call_inst = self.create_advice_call(&advice.advice_function, Vec::new());
            block
                .instructions
                .insert(after_index + i, call_inst);
            inserted += 1;
        }

        // TODO: Implement AfterError advices (requires error handling infrastructure)
        // TODO: Implement Around advices (requires wrapping the join point)

        inserted
    }
}

/// Result of weaving a function.
#[derive(Debug, Clone, Default)]
pub struct WeavingResult {
    /// Number of join points that had advice woven
    pub join_points_woven: usize,
    /// Total number of advice calls inserted
    pub advices_inserted: usize,
    /// List of (join point, advice) pairs for debugging
    pub advice_calls: Vec<(JoinPointKind, String)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aop_config::{AopAroundRule, AopConfig};
    use crate::hir::TypeId;
    use crate::mir::{LocalKind, MirBlock, MirLocal};
    use crate::predicate::Predicate;
    use simple_parser::Visibility;

    #[test]
    fn test_weaver_disabled() {
        let config = WeavingConfig::disabled();
        let weaver = Weaver::new(config);

        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        assert_eq!(result.join_points_woven, 0);
        assert_eq!(result.advices_inserted, 0);
    }

    #[test]
    fn test_detect_execution_join_point() {
        let config = WeavingConfig {
            enabled: true,
            before_advices: Vec::new(),
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };
        let weaver = Weaver::new(config);

        let func = create_test_function("my_function");
        let join_points = weaver.detect_join_points(&func);

        assert_eq!(join_points.len(), 1);
        match &join_points[0].kind {
            JoinPointKind::Execution { function_name, .. } => {
                assert_eq!(function_name, "my_function");
            }
            _ => panic!("Expected execution join point"),
        }
    }

    #[test]
    fn test_match_advice_to_join_point() {
        // Use init() selector which matches on type_name (function_name in our case)
        let predicate = crate::predicate_parser::parse_predicate("pc{ init(my_function) }")
            .unwrap();

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![AopAroundRule {
                predicate,
                advice: "log_advice".to_string(),
                priority: 10,
                order: 0,
                raw_predicate: "pc{ init(my_function) }".to_string(),
            }],
        };

        let config = WeavingConfig::from_aop_config(&aop_config);
        let weaver = Weaver::new(config);

        let func = create_test_function("my_function");
        let join_points = weaver.detect_join_points(&func);
        let advices = weaver.match_advice(&join_points[0]);

        assert_eq!(advices.len(), 1);
        assert_eq!(advices[0].advice_function, "log_advice");
    }

    #[test]
    fn test_match_execution_selector() {
        // Test execution() selector with proper signature matching
        let predicate = crate::predicate_parser::parse_predicate("pc{ execution(* my_function(..)) }")
            .unwrap();

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![AopAroundRule {
                predicate,
                advice: "trace_fn".to_string(),
                priority: 5,
                order: 0,
                raw_predicate: "pc{ execution(* my_function(..)) }".to_string(),
            }],
        };

        let config = WeavingConfig::from_aop_config(&aop_config);
        let weaver = Weaver::new(config);

        let func = create_test_function("my_function");
        let join_points = weaver.detect_join_points(&func);

        // Debug: print the signature
        eprintln!("Signature: {}", join_points[0].context.signature);

        let advices = weaver.match_advice(&join_points[0]);

        // For now, since signature format might be complex, just check that matching works
        // We'll fix the signature format issue separately
        assert_eq!(advices.len(), 1, "Expected 1 advice but got {}", advices.len());
        assert_eq!(advices[0].advice_function, "trace_fn");
    }

    fn create_test_function(name: &str) -> MirFunction {
        let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        func.entry_block = BlockId(0);
        func.blocks.push(MirBlock::new(BlockId(0)));
        func
    }

    #[test]
    fn test_multiple_advices_priority_ordering() {
        // Create multiple advices with different priorities
        let pred1 = crate::predicate_parser::parse_predicate("pc{ init(test_fn) }").unwrap();
        let pred2 = crate::predicate_parser::parse_predicate("pc{ init(test_fn) }").unwrap();
        let pred3 = crate::predicate_parser::parse_predicate("pc{ init(test_fn) }").unwrap();

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![
                AopAroundRule {
                    predicate: pred1,
                    advice: "advice_low".to_string(),
                    priority: 5,
                    order: 0,
                    raw_predicate: "pc{ init(test_fn) }".to_string(),
                },
                AopAroundRule {
                    predicate: pred2,
                    advice: "advice_high".to_string(),
                    priority: 20,
                    order: 0,
                    raw_predicate: "pc{ init(test_fn) }".to_string(),
                },
                AopAroundRule {
                    predicate: pred3,
                    advice: "advice_medium".to_string(),
                    priority: 10,
                    order: 0,
                    raw_predicate: "pc{ init(test_fn) }".to_string(),
                },
            ],
        };

        let config = WeavingConfig::from_aop_config(&aop_config);
        let weaver = Weaver::new(config);

        let func = create_test_function("test_fn");
        let join_points = weaver.detect_join_points(&func);
        let advices = weaver.match_advice(&join_points[0]);

        // Should be sorted by priority: high (20), medium (10), low (5)
        assert_eq!(advices.len(), 3);
        assert_eq!(advices[0].advice_function, "advice_high");
        assert_eq!(advices[0].priority, 20);
        assert_eq!(advices[1].advice_function, "advice_medium");
        assert_eq!(advices[1].priority, 10);
        assert_eq!(advices[2].advice_function, "advice_low");
        assert_eq!(advices[2].priority, 5);
    }

    #[test]
    fn test_weave_function_inserts_instructions() {
        // Create a Before advice
        let predicate = crate::predicate_parser::parse_predicate("pc{ init(test_fn) }").unwrap();

        let before_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "before_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![before_rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");

        // Record original instruction count
        let original_count = func.blocks[0].instructions.len();

        // Weave the function
        let result = weaver.weave_function(&mut func);

        // Should have detected 1 join point and inserted 1 advice
        assert_eq!(result.join_points_woven, 1);
        assert_eq!(result.advices_inserted, 1);

        // Should have inserted 1 instruction
        assert_eq!(func.blocks[0].instructions.len(), original_count + 1);

        // The inserted instruction should be a Call
        match &func.blocks[0].instructions[0] {
            MirInst::Call { target, .. } => {
                match target {
                    CallTarget::Io(name) => assert_eq!(name, "before_advice"),
                    _ => panic!("Expected Io call target"),
                }
            }
            _ => panic!("Expected Call instruction"),
        }
    }

    #[test]
    fn test_before_and_after_success_ordering() {
        let before_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "before_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let after_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "after_advice".to_string(),
            form: AdviceForm::AfterSuccess,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![before_rule],
            after_success_advices: vec![after_rule],
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");

        let result = weaver.weave_function(&mut func);

        assert_eq!(result.advices_inserted, 2);

        // Should have 2 Call instructions inserted
        assert_eq!(func.blocks[0].instructions.len(), 2);

        // First should be before_advice
        match &func.blocks[0].instructions[0] {
            MirInst::Call { target: CallTarget::Io(name), .. } => {
                assert_eq!(name, "before_advice");
            }
            _ => panic!("Expected before_advice call"),
        }

        // Second should be after_advice
        match &func.blocks[0].instructions[1] {
            MirInst::Call { target: CallTarget::Io(name), .. } => {
                assert_eq!(name, "after_advice");
            }
            _ => panic!("Expected after_advice call"),
        }
    }

    #[test]
    fn test_condition_join_point_detection() {
        // Create a function with a comparison operation
        let mut func = MirFunction::new("test_fn".to_string(), TypeId::I64, Visibility::Public);
        func.entry_block = BlockId(0);
        let mut block = MirBlock::new(BlockId(0));

        // Add a comparison instruction (condition join point)
        block.instructions.push(MirInst::BinOp {
            dest: VReg(0),
            op: BinOp::Eq,
            left: VReg(1),
            right: VReg(2),
        });

        func.blocks.push(block);

        let config = WeavingConfig {
            enabled: true,
            before_advices: Vec::new(),
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let join_points = weaver.detect_join_points(&func);

        // Should detect execution join point + condition join point
        assert_eq!(join_points.len(), 2);

        // Check that one is a condition join point
        let has_condition = join_points.iter().any(|jp| {
            matches!(jp.kind, JoinPointKind::Condition { .. })
        });
        assert!(has_condition, "Should detect condition join point");
    }

    #[test]
    fn test_wildcard_pattern_matching() {
        // Test that wildcard patterns match correctly
        let predicate = crate::predicate_parser::parse_predicate("pc{ init(test_*) }").unwrap();

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![AopAroundRule {
                predicate,
                advice: "wildcard_advice".to_string(),
                priority: 10,
                order: 0,
                raw_predicate: "pc{ init(test_*) }".to_string(),
            }],
        };

        let config = WeavingConfig::from_aop_config(&aop_config);
        let weaver = Weaver::new(config);

        // Should match test_fn
        let func1 = create_test_function("test_fn");
        let jp1 = weaver.detect_join_points(&func1);
        let advices1 = weaver.match_advice(&jp1[0]);
        assert_eq!(advices1.len(), 1);

        // Should match test_something
        let func2 = create_test_function("test_something");
        let jp2 = weaver.detect_join_points(&func2);
        let advices2 = weaver.match_advice(&jp2[0]);
        assert_eq!(advices2.len(), 1);

        // Should not match other_fn
        let func3 = create_test_function("other_fn");
        let jp3 = weaver.detect_join_points(&func3);
        let advices3 = weaver.match_advice(&jp3[0]);
        assert_eq!(advices3.len(), 0);
    }
}
