//! Verification diagnostics and error codes.
//!
//! Defines error codes for Lean verification mode violations:
//! - V-AOP-xxx: AOP constraint violations
//! - V-MACRO-xxx: Macro constraint violations
//! - V-TERM-xxx: Termination requirement violations
//! - V-UNSAFE-xxx: Unsafe code in verified context
//! - V-DEP-xxx: Dependency boundary violations
//! - V-INHERIT-xxx: Verification inheritance violations
//! - M-INTRO-xxx: Macro introduction contract violations

use simple_common::diagnostic::{Diagnostic, Severity, Span};

/// Verification error codes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationErrorCode {
    // AOP constraint violations
    /// Non-ghost aspect targets verified join point
    AopNonGhostTargetsVerified,
    /// Verified pointcut uses wildcard
    AopWildcardInVerified,
    /// Aspect introduces runtime member in verified context
    AopIntroducesRuntime,

    // Macro constraint violations
    /// Undeclared macro introduction
    MacroUndeclaredIntroduction,
    /// Macro introduces public item in verified context
    MacroIntroducesPub,
    /// Macro introduces global in verified context
    MacroIntroducesGlobal,
    /// Macro introduces runtime code in verified context
    MacroIntroducesRuntime,
    /// Macro-generated AOP violates verification rules
    MacroAopViolation,

    // Termination requirements
    /// Missing termination argument for recursive function
    MissingTermination,
    /// Termination argument is not well-founded
    InvalidTermination,

    // Unsafe code violations
    /// Unsafe primitive used in verified context
    UnsafeInVerified,
    /// Raw pointer operation in verified context
    RawPointerInVerified,
    /// FFI call in verified context
    FfiInVerified,

    // Dependency violations
    /// Verified code depends on unverified code without @trusted
    MissingTrustedBoundary,
    /// Circular dependency in verification context
    CircularVerifiedDep,

    // Inheritance violations
    /// Opt-out from verified parent without explicit @unsafe
    VerifiedInheritanceOptOut,
    /// Verified class extends unverified class
    VerifiedExtendsUnverified,

    // Effect violations
    /// IO effect in verified context
    IoInVerified,
    /// Reflection in verified context
    ReflectionInVerified,

    // Contract violations
    /// Ghost code accesses non-ghost state
    GhostAccessesNonGhost,
    /// Contract expression has side effects
    ContractHasSideEffects,
}

impl VerificationErrorCode {
    /// Get the string code (e.g., "V-AOP-001")
    pub fn code(&self) -> &'static str {
        match self {
            // AOP
            Self::AopNonGhostTargetsVerified => "V-AOP-001",
            Self::AopWildcardInVerified => "V-AOP-002",
            Self::AopIntroducesRuntime => "V-AOP-003",

            // Macro
            Self::MacroUndeclaredIntroduction => "M-INTRO-001",
            Self::MacroIntroducesPub => "V-MACRO-001",
            Self::MacroIntroducesGlobal => "V-MACRO-002",
            Self::MacroIntroducesRuntime => "V-MACRO-003",
            Self::MacroAopViolation => "V-MACRO-004",

            // Termination
            Self::MissingTermination => "V-TERM-001",
            Self::InvalidTermination => "V-TERM-002",

            // Unsafe
            Self::UnsafeInVerified => "V-UNSAFE-001",
            Self::RawPointerInVerified => "V-UNSAFE-002",
            Self::FfiInVerified => "V-UNSAFE-003",

            // Dependency
            Self::MissingTrustedBoundary => "V-DEP-001",
            Self::CircularVerifiedDep => "V-DEP-002",

            // Inheritance
            Self::VerifiedInheritanceOptOut => "V-INHERIT-001",
            Self::VerifiedExtendsUnverified => "V-INHERIT-002",

            // Effects
            Self::IoInVerified => "V-EFFECT-001",
            Self::ReflectionInVerified => "V-EFFECT-002",

            // Contracts
            Self::GhostAccessesNonGhost => "V-GHOST-001",
            Self::ContractHasSideEffects => "V-CONTRACT-001",
        }
    }

    /// Get the default message for this error
    pub fn message(&self) -> &'static str {
        match self {
            Self::AopNonGhostTargetsVerified => "non-ghost aspect targets verified join point",
            Self::AopWildcardInVerified => "verified pointcut uses wildcard pattern",
            Self::AopIntroducesRuntime => "aspect introduces runtime member in verified context",

            Self::MacroUndeclaredIntroduction => "macro introduces symbols not declared in `introduces:` clause",
            Self::MacroIntroducesPub => "macro introduces public item in verified context",
            Self::MacroIntroducesGlobal => "macro introduces global variable in verified context",
            Self::MacroIntroducesRuntime => "macro introduces runtime code in verified context",
            Self::MacroAopViolation => "macro-generated aspect violates verification rules",

            Self::MissingTermination => "recursive function missing `decreases:` clause",
            Self::InvalidTermination => "termination argument is not well-founded",

            Self::UnsafeInVerified => "unsafe operation in verified context",
            Self::RawPointerInVerified => "raw pointer operation in verified context",
            Self::FfiInVerified => "FFI call in verified context",

            Self::MissingTrustedBoundary => "verified code depends on unverified code without @trusted boundary",
            Self::CircularVerifiedDep => "circular dependency in verification context",

            Self::VerifiedInheritanceOptOut => "opt-out from verified parent requires explicit @unsafe",
            Self::VerifiedExtendsUnverified => "verified class cannot extend unverified class",

            Self::IoInVerified => "IO effect not allowed in verified context",
            Self::ReflectionInVerified => "reflection not allowed in verified context",

            Self::GhostAccessesNonGhost => "ghost code cannot access non-ghost state",
            Self::ContractHasSideEffects => "contract expression must be pure (no side effects)",
        }
    }

    /// Get the help text for this error
    pub fn help(&self) -> &'static str {
        match self {
            Self::AopNonGhostTargetsVerified => "mark the aspect with `ghost` to allow it in verified context",
            Self::AopWildcardInVerified => "use explicit pointcuts instead of wildcards for verified code",
            Self::AopIntroducesRuntime => "only ghost introductions are allowed in verified context",

            Self::MacroUndeclaredIntroduction => "add all introduced symbols to the `introduces:` clause",
            Self::MacroIntroducesPub => "macros in verified context can only introduce private items",
            Self::MacroIntroducesGlobal => "use local variables instead of global state",
            Self::MacroIntroducesRuntime => "macros in verified context can only introduce ghost code",
            Self::MacroAopViolation => "ensure macro-generated aspects are marked ghost",

            Self::MissingTermination => "add `decreases: <expr>` to prove termination",
            Self::InvalidTermination => "ensure the decreases expression decreases on each recursive call",

            Self::UnsafeInVerified => "remove unsafe operations or move to @trusted function",
            Self::RawPointerInVerified => "use references instead of raw pointers",
            Self::FfiInVerified => "wrap FFI calls in @trusted functions",

            Self::MissingTrustedBoundary => "add @trusted annotation to the dependency or verify the dependency",
            Self::CircularVerifiedDep => "break the circular dependency using @trusted annotations",

            Self::VerifiedInheritanceOptOut => "add @unsafe to explicitly opt out of verification",
            Self::VerifiedExtendsUnverified => "verify the parent class or use composition instead",

            Self::IoInVerified => "move IO operations to @trusted functions",
            Self::ReflectionInVerified => "use explicit types instead of reflection",

            Self::GhostAccessesNonGhost => "only access ghost variables and parameters in ghost code",
            Self::ContractHasSideEffects => "ensure contract expressions only read state, don't modify it",
        }
    }

    /// Get the severity for this error
    pub fn severity(&self) -> Severity {
        // All verification errors are hard errors
        Severity::Error
    }
}

/// A verification diagnostic with full context
#[derive(Debug, Clone)]
pub struct VerificationDiagnostic {
    /// The error code
    pub code: VerificationErrorCode,
    /// Source span
    pub span: Span,
    /// Additional context message
    pub context: Option<String>,
    /// File path
    pub file: Option<String>,
    /// Name of the problematic item
    pub item_name: Option<String>,
}

impl VerificationDiagnostic {
    /// Create a new verification diagnostic
    pub fn new(code: VerificationErrorCode, span: Span) -> Self {
        Self {
            code,
            span,
            context: None,
            file: None,
            item_name: None,
        }
    }

    /// Add context message
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Add file path
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Add item name
    pub fn with_item(mut self, name: impl Into<String>) -> Self {
        self.item_name = Some(name.into());
        self
    }

    /// Convert to common Diagnostic format
    pub fn to_diagnostic(&self) -> Diagnostic {
        let message = if let Some(ref item) = self.item_name {
            format!("{}: `{}`", self.code.message(), item)
        } else {
            self.code.message().to_string()
        };

        let mut diag = Diagnostic::new(self.code.severity(), message)
            .with_code(self.code.code())
            .with_label(self.span, self.code.message())
            .with_help(self.code.help());

        if let Some(ref file) = self.file {
            diag = diag.with_file(file);
        }

        if let Some(ref context) = self.context {
            diag = diag.with_note(context);
        }

        diag
    }
}

/// Collector for verification diagnostics
#[derive(Debug, Default)]
pub struct VerificationDiagnostics {
    diagnostics: Vec<VerificationDiagnostic>,
}

impl VerificationDiagnostics {
    /// Create a new collector
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a diagnostic
    pub fn push(&mut self, diag: VerificationDiagnostic) {
        self.diagnostics.push(diag);
    }

    /// Report an error
    pub fn error(&mut self, code: VerificationErrorCode, span: Span) -> &mut VerificationDiagnostic {
        self.diagnostics.push(VerificationDiagnostic::new(code, span));
        self.diagnostics.last_mut().unwrap()
    }

    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// Get the number of errors
    pub fn error_count(&self) -> usize {
        self.diagnostics.len()
    }

    /// Convert all diagnostics to common format
    pub fn to_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.iter().map(|d| d.to_diagnostic()).collect()
    }

    /// Iterate over diagnostics
    pub fn iter(&self) -> impl Iterator<Item = &VerificationDiagnostic> {
        self.diagnostics.iter()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_codes() {
        assert_eq!(VerificationErrorCode::AopNonGhostTargetsVerified.code(), "V-AOP-001");
        assert_eq!(VerificationErrorCode::MacroUndeclaredIntroduction.code(), "M-INTRO-001");
        assert_eq!(VerificationErrorCode::MissingTermination.code(), "V-TERM-001");
        assert_eq!(VerificationErrorCode::UnsafeInVerified.code(), "V-UNSAFE-001");
    }

    #[test]
    fn test_diagnostic_creation() {
        let span = Span::new(10, 20, 5, 3);
        let diag = VerificationDiagnostic::new(VerificationErrorCode::MissingTermination, span)
            .with_item("factorial")
            .with_file("math.spl");

        let common = diag.to_diagnostic();
        assert!(common.message.contains("factorial"));
        assert_eq!(common.code, Some("V-TERM-001".to_string()));
        assert_eq!(common.file, Some("math.spl".to_string()));
    }

    #[test]
    fn test_diagnostics_collector() {
        let mut collector = VerificationDiagnostics::new();

        let span = Span::new(0, 10, 1, 1);
        collector.error(VerificationErrorCode::IoInVerified, span);
        collector.diagnostics.last_mut().unwrap().item_name = Some("read_file".to_string());
        collector.error(VerificationErrorCode::FfiInVerified, span);
        collector.diagnostics.last_mut().unwrap().item_name = Some("call_c_function".to_string());

        assert!(collector.has_errors());
        assert_eq!(collector.error_count(), 2);

        let diags = collector.to_diagnostics();
        assert_eq!(diags.len(), 2);
    }
}
