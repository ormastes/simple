use super::*;
use simple_parser::ast::Visibility;

/// HIR function definition
#[derive(Debug, Clone)]
pub struct HirFunction {
    pub name: String,
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
}

impl HirFunction {
    /// Check if this function is public (helper for backwards compatibility)
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }
}
