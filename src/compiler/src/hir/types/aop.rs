// === AOP & Unified Predicates (#1000-1050) ===

/// HIR representation of an AOP advice declaration.
#[derive(Debug, Clone)]
pub struct HirAopAdvice {
    pub predicate_text: String,
    pub advice_function: String,
    pub form: String, // "before", "after_success", "after_error", "around"
    pub priority: i64,
}

/// HIR representation of a DI binding.
#[derive(Debug, Clone)]
pub struct HirDiBinding {
    pub predicate_text: String,
    pub implementation: String,
    pub scope: Option<String>, // "singleton", "transient", "scoped"
    pub priority: i64,
}

/// HIR representation of an architecture rule.
#[derive(Debug, Clone)]
pub struct HirArchRule {
    pub rule_type: String, // "forbid" or "allow"
    pub predicate_text: String,
    pub message: Option<String>,
    pub priority: i64,
}

/// HIR representation of a mock declaration.
#[derive(Debug, Clone)]
pub struct HirMockDecl {
    pub name: String,
    pub trait_name: String,
    pub expectations: Vec<String>,
}
