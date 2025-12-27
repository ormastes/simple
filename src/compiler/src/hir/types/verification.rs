//! Verification mode types for Lean proof generation integration.
//!
//! This module defines the verification context that propagates through
//! the HIR, enabling formal verification with Lean 4.
//!
//! See doc/plans/lean_verification_implementation.md for the full specification.

/// Verification mode for a function, module, or declaration.
///
/// Verification mode determines whether code is subject to formal verification
/// constraints and Lean proof generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VerificationMode {
    /// No verification constraints - code is not formally verified.
    /// This is the default for all code not marked with @verify.
    #[default]
    Unverified,

    /// Code is subject to formal verification constraints.
    /// Must follow the verified subset:
    /// - No @unsafe operations
    /// - No reflection or dynamic code
    /// - Must be pure or have explicit effect annotations
    /// - Contracts are exported to Lean propositions
    Verified,

    /// Trusted boundary between verified and unverified code.
    /// The function's contracts are assumed without proof.
    /// Used for FFI, runtime primitives, or verified-elsewhere code.
    Trusted,
}

impl VerificationMode {
    /// Check if this mode enables verification constraints.
    pub fn is_verified(&self) -> bool {
        matches!(self, VerificationMode::Verified)
    }

    /// Check if this mode is a trusted boundary.
    pub fn is_trusted(&self) -> bool {
        matches!(self, VerificationMode::Trusted)
    }

    /// Check if code in this mode can call unverified code.
    /// Only trusted boundaries can call unverified code from verified context.
    pub fn can_call_unverified(&self) -> bool {
        !matches!(self, VerificationMode::Verified)
    }

    /// Get the verification mode from AST effects.
    pub fn from_effects(effects: &[simple_parser::ast::Effect]) -> Self {
        use simple_parser::ast::Effect;

        for effect in effects {
            if *effect == Effect::Verify {
                return VerificationMode::Verified;
            }
            if *effect == Effect::Trusted {
                return VerificationMode::Trusted;
            }
        }
        VerificationMode::Unverified
    }
}

/// Verification context that propagates through the HIR.
///
/// Implements the V-SCOPE and V-INHERIT rules from the specification:
/// - V-SCOPE: Verified mode propagates to nested scopes
/// - V-INHERIT: Child declarations inherit parent's verification mode
#[derive(Debug, Clone, Default)]
pub struct VerificationContext {
    /// Current verification mode (verified, trusted, or unverified)
    pub mode: VerificationMode,

    /// Path of verified ancestors (for error reporting)
    pub verified_path: Vec<String>,

    /// Whether ghost code is allowed in this context
    pub ghost_allowed: bool,

    /// Whether we're inside a ghost block
    pub in_ghost: bool,
}

impl VerificationContext {
    /// Create a new unverified context.
    pub fn unverified() -> Self {
        Self::default()
    }

    /// Create a verified context.
    pub fn verified() -> Self {
        Self {
            mode: VerificationMode::Verified,
            ghost_allowed: true,
            ..Default::default()
        }
    }

    /// Create a trusted context.
    pub fn trusted() -> Self {
        Self {
            mode: VerificationMode::Trusted,
            ghost_allowed: true,
            ..Default::default()
        }
    }

    /// Enter a child scope, inheriting verification mode (V-INHERIT).
    pub fn enter_scope(&self, name: &str) -> Self {
        let mut path = self.verified_path.clone();
        if self.mode.is_verified() {
            path.push(name.to_string());
        }
        Self {
            mode: self.mode,
            verified_path: path,
            ghost_allowed: self.ghost_allowed,
            in_ghost: self.in_ghost,
        }
    }

    /// Enter a ghost block.
    pub fn enter_ghost(&self) -> Self {
        Self {
            in_ghost: true,
            ..self.clone()
        }
    }

    /// Check if an unsafe operation is allowed in this context.
    pub fn unsafe_allowed(&self) -> bool {
        !self.mode.is_verified()
    }

    /// Check if ghost declarations are allowed.
    pub fn ghost_declarations_allowed(&self) -> bool {
        self.ghost_allowed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_mode_default() {
        let mode = VerificationMode::default();
        assert!(!mode.is_verified());
        assert!(!mode.is_trusted());
        assert!(mode.can_call_unverified());
    }

    #[test]
    fn test_verified_mode() {
        let mode = VerificationMode::Verified;
        assert!(mode.is_verified());
        assert!(!mode.is_trusted());
        assert!(!mode.can_call_unverified());
    }

    #[test]
    fn test_trusted_mode() {
        let mode = VerificationMode::Trusted;
        assert!(!mode.is_verified());
        assert!(mode.is_trusted());
        assert!(mode.can_call_unverified());
    }

    #[test]
    fn test_context_scope_inheritance() {
        let ctx = VerificationContext::verified();
        let child = ctx.enter_scope("foo");

        assert!(child.mode.is_verified());
        assert_eq!(child.verified_path, vec!["foo"]);
    }

    #[test]
    fn test_context_ghost() {
        let ctx = VerificationContext::verified();
        assert!(!ctx.in_ghost);

        let ghost_ctx = ctx.enter_ghost();
        assert!(ghost_ctx.in_ghost);
    }
}
