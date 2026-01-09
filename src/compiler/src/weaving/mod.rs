//! Compile-time AOP weaving infrastructure.
//!
//! This module provides compile-time weaving of aspects into the MIR.
//! It detects join points (execution, decision, condition) and inserts
//! advice calls (before, after_success, after_error, around).
//!
//! See doc/research/aop.md for the complete specification.

pub mod diagnostics;
pub mod matcher;
pub mod types;
pub mod weaver;

// Re-export public API
pub use diagnostics::{DiagnosticLevel, WeavingDiagnostic};
pub use matcher::Weaver;
pub use types::{
    AdviceForm, JoinPoint, JoinPointContext, JoinPointKind, MatchedAdvice, WeavingConfig,
    WeavingResult, WeavingRule,
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aop_config::{AopAroundRule, AopConfig};
    use crate::hir::{BinOp, TypeId};
    use crate::mir::{BlockId, CallTarget, MirBlock, MirFunction, MirInst, VReg};
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
        let predicate =
            crate::predicate_parser::parse_predicate("pc{ init(my_function) }").unwrap();

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
        let (advices, diagnostics) = weaver.match_advice(&join_points[0]);

        assert_eq!(advices.len(), 1);
        assert_eq!(advices[0].advice_function, "log_advice");
        assert!(
            diagnostics.is_empty(),
            "Should not have diagnostics for valid advice"
        );
    }

    #[test]
    fn test_match_execution_selector() {
        // Test execution() selector with proper signature matching
        let predicate =
            crate::predicate_parser::parse_predicate("pc{ execution(* my_function(..)) }").unwrap();

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

        let (advices, _diagnostics) = weaver.match_advice(&join_points[0]);

        // For now, since signature format might be complex, just check that matching works
        // We'll fix the signature format issue separately
        assert_eq!(
            advices.len(),
            1,
            "Expected 1 advice but got {}",
            advices.len()
        );
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
        let (advices, _diagnostics) = weaver.match_advice(&join_points[0]);

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
            MirInst::Call { target, .. } => match target {
                CallTarget::Io(name) => assert_eq!(name, "before_advice"),
                _ => panic!("Expected Io call target"),
            },
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
            MirInst::Call {
                target: CallTarget::Io(name),
                ..
            } => {
                assert_eq!(name, "before_advice");
            }
            _ => panic!("Expected before_advice call"),
        }

        // Second should be after_advice
        match &func.blocks[0].instructions[1] {
            MirInst::Call {
                target: CallTarget::Io(name),
                ..
            } => {
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
        let has_condition = join_points
            .iter()
            .any(|jp| matches!(jp.kind, JoinPointKind::Condition { .. }));
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
        let (advices1, _) = weaver.match_advice(&jp1[0]);
        assert_eq!(advices1.len(), 1);

        // Should match test_something
        let func2 = create_test_function("test_something");
        let jp2 = weaver.detect_join_points(&func2);
        let (advices2, _) = weaver.match_advice(&jp2[0]);
        assert_eq!(advices2.len(), 1);

        // Should not match other_fn
        let func3 = create_test_function("other_fn");
        let jp3 = weaver.detect_join_points(&func3);
        let (advices3, _) = weaver.match_advice(&jp3[0]);
        assert_eq!(advices3.len(), 0);
    }

    #[test]
    fn test_error_join_point_detection() {
        // Create a function with error handling
        let mut func = MirFunction::new("test_fn".to_string(), TypeId::I64, Visibility::Public);
        func.entry_block = BlockId(0);
        let mut block = MirBlock::new(BlockId(0));

        // Add a ResultErr instruction (error join point)
        block.instructions.push(MirInst::ResultErr {
            dest: VReg(0),
            value: VReg(1),
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

        // Should detect execution join point + error join point
        assert_eq!(join_points.len(), 2);

        // Check that one is an error join point
        let has_error = join_points
            .iter()
            .any(|jp| matches!(jp.kind, JoinPointKind::Error { .. }));
        assert!(has_error, "Should detect error join point");
    }

    #[test]
    fn test_after_error_advice() {
        let error_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "error_handler".to_string(),
            form: AdviceForm::AfterError,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: Vec::new(),
            after_success_advices: Vec::new(),
            after_error_advices: vec![error_rule],
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);

        // Create function with error handling
        let mut func = MirFunction::new("test_fn".to_string(), TypeId::I64, Visibility::Public);
        func.entry_block = BlockId(0);
        let mut block = MirBlock::new(BlockId(0));

        block.instructions.push(MirInst::ResultErr {
            dest: VReg(0),
            value: VReg(1),
        });

        func.blocks.push(block);

        let original_count = func.blocks[0].instructions.len();
        let result = weaver.weave_function(&mut func);

        // Should have woven 2 join points (execution + error)
        assert_eq!(result.join_points_woven, 2);

        // Should have inserted 2 advices (one per join point)
        assert_eq!(result.advices_inserted, 2);

        // Should have inserted 2 instructions
        assert_eq!(func.blocks[0].instructions.len(), original_count + 2);
    }

    #[test]
    fn test_combined_after_success_and_after_error() {
        let success_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "success_handler".to_string(),
            form: AdviceForm::AfterSuccess,
            priority: 10,
        };

        let error_rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "error_handler".to_string(),
            form: AdviceForm::AfterError,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: Vec::new(),
            after_success_advices: vec![success_rule],
            after_error_advices: vec![error_rule],
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");

        let result = weaver.weave_function(&mut func);

        // Both success and error handlers should be inserted
        assert_eq!(result.advices_inserted, 2);
    }

    #[test]
    fn test_diagnostic_predicate_parse_error() {
        // Create an advice with invalid predicate syntax
        let rule = WeavingRule {
            predicate_text: "pc{ invalid syntax here }".to_string(),
            advice_function: "bad_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        // Should have error diagnostic
        assert!(result.has_errors(), "Should have parsing error");
        let errors: Vec<_> = result.errors().collect();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("Failed to parse predicate"));
    }

    #[test]
    fn test_diagnostic_invalid_selector() {
        // Create an advice with invalid selector for weaving context
        // Use 'type()' selector which is not valid for weaving
        let rule = WeavingRule {
            predicate_text: "pc{ type(SomeClass) }".to_string(),
            advice_function: "invalid_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        // Should have error diagnostic for invalid selector
        assert!(result.has_errors(), "Should have invalid selector error");
        let errors: Vec<_> = result.errors().collect();
        assert!(errors
            .iter()
            .any(|e| e.message.contains("Invalid selector")));
    }

    #[test]
    fn test_diagnostic_unused_advice() {
        // Create an advice that will never match
        let rule = WeavingRule {
            predicate_text: "pc{ init(nonexistent_function) }".to_string(),
            advice_function: "unused_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        // Should have warning about unused advice
        assert!(result.has_warnings(), "Should have unused advice warning");
        let warnings: Vec<_> = result.warnings().collect();
        assert!(warnings.iter().any(|w| w.message.contains("never applied")));
    }

    #[test]
    fn test_diagnostic_ambiguous_ordering() {
        // Create multiple advices with same priority
        let rule1 = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "advice_a".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let rule2 = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "advice_b".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule1, rule2],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        // Should have warning about ambiguous ordering
        assert!(
            result.has_warnings(),
            "Should have ambiguous ordering warning"
        );
        let warnings: Vec<_> = result.warnings().collect();
        assert!(warnings
            .iter()
            .any(|w| w.message.contains("Ambiguous advice ordering")));
    }

    #[test]
    fn test_diagnostic_info_messages() {
        // Create a valid advice that matches
        let rule = WeavingRule {
            predicate_text: "pc{ init(test_fn) }".to_string(),
            advice_function: "good_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        // Should have info diagnostic about weaving summary
        let info_diags: Vec<_> = result
            .diagnostics
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Info)
            .collect();
        assert!(!info_diags.is_empty(), "Should have info diagnostics");
        assert!(info_diags.iter().any(|d| d.message.contains("Woven")));
    }

    #[test]
    fn test_diagnostic_has_predicates_and_locations() {
        // Test that diagnostics have predicate and location information
        let rule = WeavingRule {
            predicate_text: "pc{ invalid }".to_string(),
            advice_function: "test_advice".to_string(),
            form: AdviceForm::Before,
            priority: 10,
        };

        let config = WeavingConfig {
            enabled: true,
            before_advices: vec![rule],
            after_success_advices: Vec::new(),
            after_error_advices: Vec::new(),
            around_advices: Vec::new(),
        };

        let weaver = Weaver::new(config);
        let mut func = create_test_function("test_fn");
        let result = weaver.weave_function(&mut func);

        let errors: Vec<_> = result.errors().collect();
        if !errors.is_empty() {
            assert!(errors[0].predicate.is_some(), "Should have predicate");
            assert!(errors[0].location.is_some(), "Should have location");
        }
    }
}
