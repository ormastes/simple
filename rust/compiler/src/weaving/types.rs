//! Type definitions for AOP weaving.

use crate::mir::BlockId;
use crate::predicate::MatchContext;

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

/// Join point types in the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JoinPointKind {
    /// Function execution
    Execution { function_name: String, signature: String },
    /// Decision point (if/match condition)
    Decision { location: String },
    /// Condition evaluation
    Condition { location: String },
    /// Error handling point (Result::Err, TryUnwrap)
    Error { location: String, error_type: String },
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
    pub fn from_aop_config(aop_config: &crate::aop_config::AopConfig) -> Self {
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

    /// Load from HIR AOP advices (parsed from Simple source code).
    pub fn from_hir_advices(advices: &[crate::hir::HirAopAdvice]) -> Self {
        let mut before_advices = Vec::new();
        let mut after_success_advices = Vec::new();
        let mut after_error_advices = Vec::new();
        let mut around_advices = Vec::new();

        for advice in advices {
            let form = AdviceForm::from_str(&advice.form).unwrap_or(AdviceForm::Before);
            let rule = WeavingRule {
                predicate_text: advice.predicate_text.clone(),
                advice_function: advice.advice_function.clone(),
                form,
                priority: advice.priority,
            };

            match form {
                AdviceForm::Before => before_advices.push(rule),
                AdviceForm::AfterSuccess => after_success_advices.push(rule),
                AdviceForm::AfterError => after_error_advices.push(rule),
                AdviceForm::Around => around_advices.push(rule),
            }
        }

        Self {
            enabled: !advices.is_empty(),
            before_advices,
            after_success_advices,
            after_error_advices,
            around_advices,
        }
    }

    /// Get all advice rules.
    pub(super) fn all_advices(&self) -> impl Iterator<Item = &WeavingRule> {
        self.before_advices
            .iter()
            .chain(self.after_success_advices.iter())
            .chain(self.after_error_advices.iter())
            .chain(self.around_advices.iter())
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
    /// Diagnostic messages generated during weaving
    pub diagnostics: Vec<super::diagnostics::WeavingDiagnostic>,
}

impl WeavingResult {
    /// Add a diagnostic message.
    pub fn add_diagnostic(&mut self, diagnostic: super::diagnostics::WeavingDiagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.level == super::diagnostics::DiagnosticLevel::Error)
    }

    /// Check if there are any warnings.
    pub fn has_warnings(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.level == super::diagnostics::DiagnosticLevel::Warning)
    }

    /// Get all errors.
    pub fn errors(&self) -> impl Iterator<Item = &super::diagnostics::WeavingDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.level == super::diagnostics::DiagnosticLevel::Error)
    }

    /// Get all warnings.
    pub fn warnings(&self) -> impl Iterator<Item = &super::diagnostics::WeavingDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.level == super::diagnostics::DiagnosticLevel::Warning)
    }
}
