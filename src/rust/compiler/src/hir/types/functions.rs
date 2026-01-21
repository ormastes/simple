use super::*;
use simple_parser::ast::Visibility;
use simple_parser::Span;

/// HIR function definition
#[derive(Debug, Clone)]
pub struct HirFunction {
    pub name: String,
    /// Source location span for error reporting and architecture rules
    pub span: Option<Span>,
    pub params: Vec<LocalVar>,
    pub locals: Vec<LocalVar>,
    pub return_type: TypeId,
    pub body: Vec<HirStmt>,
    pub visibility: Visibility,
    /// Function contract (preconditions, postconditions, invariants)
    pub contract: Option<HirContract>,
    /// Whether this function is marked as pure (no side effects)
    /// Pure functions can be called from contract expressions (CTR-030-032)
    pub is_pure: bool,
    /// Whether this function uses DI constructor injection
    pub inject: bool,
    /// Concurrency mode for this function (actor, lock_base, unsafe)
    pub concurrency_mode: ConcurrencyMode,
    /// Module path where this function is defined (for AOP predicate matching)
    pub module_path: String,
    /// Compile-time attributes (e.g., "inline", "deprecated") for AOP matching
    pub attributes: Vec<String>,
    /// Effect decorators (e.g., "async", "pure", "io") for AOP effect() selector
    pub effects: Vec<String>,
    /// Code layout hint for 4KB page locality optimization.
    /// Specifies the execution phase (startup, first_frame, steady, cold)
    /// and optional anchor designation (event_loop).
    pub layout_hint: Option<FunctionLayoutHint>,
    /// Verification mode for Lean proof generation (#1840-#1879)
    /// Determines if this function is subject to formal verification constraints.
    pub verification_mode: VerificationMode,
    /// Whether this function is marked as ghost (@ghost effect).
    /// Ghost functions exist only for verification and are completely erased at runtime.
    /// They are included in Lean output but not in compiled code.
    pub is_ghost: bool,
    /// Whether this function is explicitly marked as sync (non-suspending).
    /// sync fn = cannot contain suspension operators (~=, if~, while~, for~)
    /// Default (false) = async-by-default, may suspend
    pub is_sync: bool,
    /// Whether this function contains suspension operators (inferred via effect_inference).
    /// If true, the function is async and should return Promise<T> (not enforced yet)
    pub has_suspension: bool,
}

impl HirFunction {
    /// Check if this function is public (helper for backwards compatibility)
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }

    /// Get the layout phase for this function.
    /// Returns `Steady` (default) if no layout hint is specified.
    pub fn layout_phase(&self) -> LayoutPhase {
        self.layout_hint.as_ref().map(|h| h.phase).unwrap_or_default()
    }

    /// Check if this function is marked as an event loop anchor.
    pub fn is_event_loop_anchor(&self) -> bool {
        self.layout_hint.as_ref().map(|h| h.is_event_loop()).unwrap_or(false)
    }

    /// Check if this function's layout is pinned (should not be moved by optimizer).
    pub fn is_layout_pinned(&self) -> bool {
        self.layout_hint.as_ref().map(|h| h.pinned).unwrap_or(false)
    }

    /// Get the ELF section suffix for this function based on its layout phase.
    pub fn layout_section_suffix(&self) -> &'static str {
        self.layout_phase().section_suffix()
    }

    /// Check if this function is subject to formal verification.
    pub fn is_verified(&self) -> bool {
        self.verification_mode.is_verified()
    }

    /// Check if this function is a trusted boundary.
    pub fn is_trusted(&self) -> bool {
        self.verification_mode.is_trusted()
    }

    /// Check if this function has any ghost parameters.
    pub fn has_ghost_params(&self) -> bool {
        self.params.iter().any(|p| p.is_ghost)
    }

    /// Check if this function has any ghost locals.
    pub fn has_ghost_locals(&self) -> bool {
        self.locals.iter().any(|l| l.is_ghost)
    }
}
