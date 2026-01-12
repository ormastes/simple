//! Advice matching logic for AOP weaving.

use super::diagnostics::{DiagnosticLevel, WeavingDiagnostic};
use super::types::*;
use crate::hir::BinOp;
use crate::mir::{MirFunction, MirInst};
use crate::predicate::PredicateContext;

/// Main weaving engine.
pub struct Weaver {
    pub(super) config: WeavingConfig,
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
            module_path: function.module_path.clone(),
            signature: self.build_signature(function),
            attributes: function.attributes.clone(),
            effects: function.effects.clone(),
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
                    MirInst::BinOp {
                        dest: _,
                        op,
                        left: _,
                        right: _,
                    } => {
                        // Condition evaluation (comparison operators)
                        match op {
                            BinOp::Eq
                            | BinOp::NotEq
                            | BinOp::Lt
                            | BinOp::LtEq
                            | BinOp::Gt
                            | BinOp::GtEq => {
                                join_points.push(JoinPoint {
                                    kind: JoinPointKind::Condition {
                                        location: format!(
                                            "{}:block{:?}:inst{}",
                                            function.name, block.id, idx
                                        ),
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
                                    location: format!(
                                        "{}:block{:?}:inst{}",
                                        function.name, block.id, idx
                                    ),
                                },
                                block_id: block.id,
                                instruction_index: idx,
                                context: context.clone(),
                            });
                        }

                        // Check for error handling points
                        if self.is_error_instruction(inst) {
                            join_points.push(JoinPoint {
                                kind: JoinPointKind::Error {
                                    location: format!(
                                        "{}:block{:?}:inst{}",
                                        function.name, block.id, idx
                                    ),
                                    error_type: "Result".to_string(),
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
        matches!(
            inst,
            MirInst::PatternTest { .. }
                | MirInst::EnumDiscriminant { .. }
                | MirInst::TryUnwrap { .. } // Result/Option unwrapping is a decision point
        )
    }

    /// Check if an instruction represents an error handling point.
    fn is_error_instruction(&self, inst: &MirInst) -> bool {
        matches!(
            inst,
            MirInst::ResultErr { .. } |  // Creating Result::Err
            MirInst::TryUnwrap { .. } // ? operator (unwrap or propagate error)
        )
    }

    /// Match advice to join points.
    /// Returns (matched advices, diagnostics).
    pub fn match_advice(
        &self,
        join_point: &JoinPoint,
    ) -> (Vec<MatchedAdvice>, Vec<WeavingDiagnostic>) {
        if !self.config.enabled {
            return (Vec::new(), Vec::new());
        }

        let match_ctx = join_point.context.to_match_context();
        let mut matched = Vec::new();
        let mut diagnostics = Vec::new();

        for rule in self.config.all_advices() {
            // Parse predicate and check if it matches
            match crate::predicate_parser::parse_predicate(&rule.predicate_text) {
                Ok(predicate) => {
                    // Validate for weaving context
                    match predicate.validate(PredicateContext::Weaving) {
                        Ok(()) => {
                            if predicate.matches(&match_ctx) {
                                matched.push(MatchedAdvice {
                                    advice_function: rule.advice_function.clone(),
                                    form: rule.form,
                                    priority: rule.priority,
                                    specificity: predicate.specificity(),
                                });
                            }
                        }
                        Err(invalid_selector) => {
                            // Invalid selector for weaving context
                            diagnostics.push(
                                WeavingDiagnostic::error(format!(
                                    "Invalid selector '{}' for weaving context in advice '{}'",
                                    invalid_selector, rule.advice_function
                                ))
                                .with_predicate(rule.predicate_text.clone())
                                .with_location(join_point.context.function_name.clone()),
                            );
                        }
                    }
                }
                Err(err) => {
                    // Predicate parsing failed
                    diagnostics.push(
                        WeavingDiagnostic::error(format!(
                            "Failed to parse predicate for advice '{}': {}",
                            rule.advice_function, err
                        ))
                        .with_predicate(rule.predicate_text.clone())
                        .with_location(join_point.context.function_name.clone()),
                    );
                }
            }
        }

        // Check for ambiguous ordering (same priority, different advice)
        if matched.len() > 1 {
            let same_priority_groups: Vec<Vec<&MatchedAdvice>> = {
                let mut groups = Vec::new();
                let mut current_group = Vec::new();
                let mut last_priority = None;

                for advice in &matched {
                    if last_priority == Some(advice.priority) {
                        current_group.push(advice);
                    } else {
                        if current_group.len() > 1 {
                            groups.push(current_group.clone());
                        }
                        current_group.clear();
                        current_group.push(advice);
                        last_priority = Some(advice.priority);
                    }
                }
                if current_group.len() > 1 {
                    groups.push(current_group);
                }
                groups
            };

            for group in same_priority_groups {
                if group.len() > 1 && group.iter().any(|a| a.specificity == group[0].specificity) {
                    let advice_names: Vec<String> =
                        group.iter().map(|a| a.advice_function.clone()).collect();
                    diagnostics.push(
                        WeavingDiagnostic::warning(format!(
                            "Ambiguous advice ordering at priority {}: [{}]. Consider adjusting priorities.",
                            group[0].priority,
                            advice_names.join(", ")
                        ))
                        .with_location(join_point.context.function_name.clone()),
                    );
                }
            }
        }

        // Sort by priority (higher first), then specificity, then stable order
        matched.sort_by(|a, b| {
            b.priority
                .cmp(&a.priority)
                .then_with(|| b.specificity.cmp(&a.specificity))
        });

        (matched, diagnostics)
    }

    /// Build a signature string for a function.
    ///
    /// Currently uses simplified type matching ("*" and "Any") because proper type name
    /// resolution requires a type registry. Future improvement would pass a TypeRegistry
    /// reference to resolve TypeIds to actual type names (e.g., "i32", "String", "MyStruct").
    pub(super) fn build_signature(&self, function: &MirFunction) -> String {
        // Use simplified matching for now - this is sufficient for most AOP use cases
        // since predicates often match by function name and attributes rather than exact types
        let param_types = function
            .params
            .iter()
            .map(|_| "Any".to_string())
            .collect::<Vec<_>>()
            .join(", ");

        format!("* {}({})", function.name, param_types)
    }
}
