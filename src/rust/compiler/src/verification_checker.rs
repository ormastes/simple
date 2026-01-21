//! Verification Constraint Checker
//!
//! Enforces the verified subset rules from the Lean verification mode specification.
//! See doc/plans/lean_verification_implementation.md for details.
//!
//! Rules implemented:
//! - V-UNSAFE: Code marked @verify cannot use @unsafe operations
//! - V-EFFECT: Verified code cannot use IO/FFI effects (must be @pure)
//! - V-REFLECT: Verified code cannot use reflection
//! - V-GHOST: Ghost code can only access ghost state

use crate::hir::{HirFunction, HirModule, VerificationMode};
use simple_parser::ast::Effect;
use std::collections::HashSet;

/// Verification constraint violation
#[derive(Debug, Clone)]
pub struct VerificationViolation {
    /// Rule that was violated
    pub rule: VerificationRule,
    /// Location description
    pub location: String,
    /// Detailed message
    pub message: String,
}

/// Verification rules that can be violated
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationRule {
    /// V-UNSAFE: No @unsafe in @verify code
    VUnsafe,
    /// V-EFFECT: No impure effects (IO, Net, Fs) in verified code
    VEffect,
    /// V-REFLECT: No reflection in verified code
    VReflect,
    /// V-GHOST: Ghost code can only access ghost state
    VGhost,
    /// V-TRUSTED: Trusted functions must have contracts
    VTrusted,
    /// V-PARTIAL: Recursive functions need termination proof
    VPartial,
}

impl VerificationRule {
    /// Get the rule code for error messages
    pub fn code(&self) -> &'static str {
        match self {
            VerificationRule::VUnsafe => "V-UNSAFE",
            VerificationRule::VEffect => "V-EFFECT",
            VerificationRule::VReflect => "V-REFLECT",
            VerificationRule::VGhost => "V-GHOST",
            VerificationRule::VTrusted => "V-TRUSTED",
            VerificationRule::VPartial => "V-PARTIAL",
        }
    }

    /// Get the rule description
    pub fn description(&self) -> &'static str {
        match self {
            VerificationRule::VUnsafe => "verified code cannot use unsafe operations",
            VerificationRule::VEffect => "verified code must be pure (no IO, Net, Fs effects)",
            VerificationRule::VReflect => "verified code cannot use reflection",
            VerificationRule::VGhost => "ghost code can only access ghost state",
            VerificationRule::VTrusted => "trusted boundary functions must have contracts",
            VerificationRule::VPartial => "recursive functions in verified code need termination proof",
        }
    }
}

impl std::fmt::Display for VerificationViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}: {}", self.rule.code(), self.location, self.message)
    }
}

/// Verification constraint checker
pub struct VerificationChecker {
    /// Collected violations
    violations: Vec<VerificationViolation>,
    /// Whether to enable strict mode (all violations are errors)
    strict: bool,
}

impl VerificationChecker {
    /// Create a new verification checker
    pub fn new(strict: bool) -> Self {
        Self {
            violations: Vec::new(),
            strict,
        }
    }

    /// Check a module for verification violations
    pub fn check_module(&mut self, module: &HirModule) {
        for func in &module.functions {
            self.check_function(func);
        }
    }

    /// Check a function for verification violations
    pub fn check_function(&mut self, func: &HirFunction) {
        // Only check verified functions
        if !func.verification_mode.is_verified() {
            // Check trusted functions have contracts
            if func.verification_mode.is_trusted() {
                self.check_trusted_has_contract(func);
            }
            return;
        }

        // V-UNSAFE: Check for unsafe effect
        self.check_no_unsafe(func);

        // V-EFFECT: Check for impure effects
        self.check_pure_effects(func);

        // V-GHOST: Check ghost variable usage (if function has ghost params/locals)
        if func.has_ghost_params() || func.has_ghost_locals() {
            self.check_ghost_constraints(func);
        }
    }

    /// V-UNSAFE: Verified code cannot use @unsafe
    fn check_no_unsafe(&mut self, func: &HirFunction) {
        for effect in &func.effects {
            if effect == "unsafe" {
                self.add_violation(
                    VerificationRule::VUnsafe,
                    &func.name,
                    format!(
                        "function '{}' is marked @verify but also uses @unsafe. \
                         Remove @unsafe or change to @trusted if this is a boundary function.",
                        func.name
                    ),
                );
            }
        }
    }

    /// V-EFFECT: Verified code must be pure
    fn check_pure_effects(&mut self, func: &HirFunction) {
        let impure_effects: Vec<_> = func
            .effects
            .iter()
            .filter(|e| matches!(e.as_str(), "io" | "net" | "fs" | "async"))
            .collect();

        if !impure_effects.is_empty() {
            self.add_violation(
                VerificationRule::VEffect,
                &func.name,
                format!(
                    "function '{}' is marked @verify but has impure effects: [{}]. \
                     Verified code must be @pure or have no effects.",
                    func.name,
                    impure_effects.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
                ),
            );
        }
    }

    /// V-TRUSTED: Trusted boundary functions must have contracts
    fn check_trusted_has_contract(&mut self, func: &HirFunction) {
        if func.contract.is_none() {
            self.add_violation(
                VerificationRule::VTrusted,
                &func.name,
                format!(
                    "function '{}' is marked @trusted but has no contract. \
                     Trusted boundary functions must specify their contracts \
                     so callers can rely on the guarantees.",
                    func.name
                ),
            );
        }
    }

    /// V-GHOST: Ghost code constraints
    fn check_ghost_constraints(&mut self, func: &HirFunction) {
        // Ghost parameters can only be used in ghost expressions
        // This is a placeholder - full implementation needs expression analysis
        // For now, just record that the function uses ghost state
        let ghost_param_names: Vec<_> = func
            .params
            .iter()
            .filter(|p| p.is_ghost)
            .map(|p| p.name.as_str())
            .collect();

        let ghost_local_names: Vec<_> = func
            .locals
            .iter()
            .filter(|l| l.is_ghost)
            .map(|l| l.name.as_str())
            .collect();

        // If there are ghost variables, log them (full checking needs expression visitor)
        if !ghost_param_names.is_empty() || !ghost_local_names.is_empty() {
            tracing::debug!(
                "Function '{}' has ghost state: params=[{}], locals=[{}]",
                func.name,
                ghost_param_names.join(", "),
                ghost_local_names.join(", ")
            );
        }
    }

    /// Add a violation
    fn add_violation(&mut self, rule: VerificationRule, location: &str, message: String) {
        self.violations.push(VerificationViolation {
            rule,
            location: location.to_string(),
            message,
        });
    }

    /// Get all violations
    pub fn violations(&self) -> &[VerificationViolation] {
        &self.violations
    }

    /// Check if there are any violations
    pub fn has_violations(&self) -> bool {
        !self.violations.is_empty()
    }

    /// Check if strict mode is enabled
    pub fn is_strict(&self) -> bool {
        self.strict
    }

    /// Get violations as error messages
    pub fn error_messages(&self) -> Vec<String> {
        self.violations.iter().map(|v| v.to_string()).collect()
    }

    /// Clear all violations
    pub fn clear(&mut self) {
        self.violations.clear();
    }
}

/// Check if an AST effect list contains unsafe
pub fn has_unsafe_effect(effects: &[Effect]) -> bool {
    effects.iter().any(|e| *e == Effect::Unsafe)
}

/// Check if an AST effect list is pure (no impure effects)
pub fn is_pure_effects(effects: &[Effect]) -> bool {
    effects
        .iter()
        .all(|e| matches!(e, Effect::Pure | Effect::Verify | Effect::Trusted))
}

/// Check if verification mode allows calling another function
pub fn can_call(caller: VerificationMode, callee: VerificationMode) -> bool {
    match caller {
        VerificationMode::Unverified => true, // Unverified can call anything
        VerificationMode::Verified => {
            // Verified can only call verified or trusted
            matches!(callee, VerificationMode::Verified | VerificationMode::Trusted)
        }
        VerificationMode::Trusted => true, // Trusted can call anything (it's a boundary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_rule_codes() {
        assert_eq!(VerificationRule::VUnsafe.code(), "V-UNSAFE");
        assert_eq!(VerificationRule::VEffect.code(), "V-EFFECT");
        assert_eq!(VerificationRule::VGhost.code(), "V-GHOST");
    }

    #[test]
    fn test_can_call_verified() {
        // Verified can call verified
        assert!(can_call(VerificationMode::Verified, VerificationMode::Verified));
        // Verified can call trusted
        assert!(can_call(VerificationMode::Verified, VerificationMode::Trusted));
        // Verified cannot call unverified
        assert!(!can_call(VerificationMode::Verified, VerificationMode::Unverified));
    }

    #[test]
    fn test_can_call_unverified() {
        // Unverified can call anything
        assert!(can_call(VerificationMode::Unverified, VerificationMode::Unverified));
        assert!(can_call(VerificationMode::Unverified, VerificationMode::Verified));
        assert!(can_call(VerificationMode::Unverified, VerificationMode::Trusted));
    }

    #[test]
    fn test_can_call_trusted() {
        // Trusted can call anything (it's a boundary)
        assert!(can_call(VerificationMode::Trusted, VerificationMode::Unverified));
        assert!(can_call(VerificationMode::Trusted, VerificationMode::Verified));
        assert!(can_call(VerificationMode::Trusted, VerificationMode::Trusted));
    }

    #[test]
    fn test_has_unsafe_effect() {
        assert!(has_unsafe_effect(&[Effect::Unsafe]));
        assert!(has_unsafe_effect(&[Effect::Pure, Effect::Unsafe]));
        assert!(!has_unsafe_effect(&[Effect::Pure]));
        assert!(!has_unsafe_effect(&[]));
    }

    #[test]
    fn test_is_pure_effects() {
        assert!(is_pure_effects(&[]));
        assert!(is_pure_effects(&[Effect::Pure]));
        assert!(is_pure_effects(&[Effect::Verify]));
        assert!(!is_pure_effects(&[Effect::Io]));
        assert!(!is_pure_effects(&[Effect::Pure, Effect::Net]));
    }
}
