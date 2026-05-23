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

/// HIR representation of a first-class DI graph declaration.
#[derive(Debug, Clone)]
pub struct HirInjectGraph {
    pub name: String,
    pub mode: Option<String>,
    pub items: Vec<HirInjectItem>,
}

#[derive(Debug, Clone)]
pub enum HirInjectItem {
    Root {
        type_ref: String,
    },
    Scan {
        pattern: String,
    },
    Load {
        path: String,
    },
    Bind {
        service: String,
        target: String,
        lifetime: Option<String>,
        configurable: bool,
        final_binding: bool,
    },
    Slot {
        service: String,
        qualifier: Option<String>,
        default_target: Option<String>,
    },
    Profile {
        name: String,
        items: Vec<HirInjectItem>,
    },
}

#[derive(Debug, Clone)]
pub struct HirSecurityPolicy {
    pub name: String,
    pub conventions_enabled: bool,
    pub items: Vec<HirSecurityItem>,
}

#[derive(Debug, Clone)]
pub enum HirSecurityItem {
    Root {
        path: String,
    },
    Default {
        action: String,
    },
    Dimension {
        name: String,
        rules: Vec<String>,
    },
    Allow {
        from: String,
        to: String,
        through: Option<String>,
        configurable: bool,
        final_rule: bool,
    },
    Deny {
        from: String,
        to: String,
        except: Option<String>,
        direct: bool,
        configurable: bool,
        final_rule: bool,
    },
    Gate(HirSecurityGate),
    Raw {
        text: String,
    },
}

#[derive(Debug, Clone)]
pub struct HirSecurityGate {
    pub name: String,
    pub from: Option<String>,
    pub to: Option<String>,
    pub policy: Option<String>,
    pub audit: Option<String>,
    pub sandbox: Option<String>,
    pub grants: Vec<String>,
    pub body: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct HirSandboxPolicy {
    pub name: String,
    pub items: Vec<HirSandboxItem>,
}

#[derive(Debug, Clone)]
pub enum HirSandboxItem {
    Backend { name: String },
    Rule { key: String, value: String },
}

#[derive(Debug, Clone)]
pub struct HirCapabilityPolicy {
    pub name: String,
    pub items: Vec<HirCapabilityItem>,
}

#[derive(Debug, Clone)]
pub enum HirCapabilityItem {
    Rule { key: String, value: String },
}

/// HIR representation of an architecture rule.
#[derive(Debug, Clone)]
pub struct HirArchRule {
    pub rule_type: String, // "forbid" or "allow"
    pub predicate_text: String,
    pub message: Option<String>,
    pub priority: i64,
}

/// HIR representation of a mock expectation.
#[derive(Debug, Clone)]
pub struct HirMockExpectation {
    pub method_name: String,
    pub params: Vec<super::LocalVar>,
    pub return_type: crate::hir::TypeId,
    pub body: Vec<super::HirStmt>,
}

/// HIR representation of a mock declaration.
#[derive(Debug, Clone)]
pub struct HirMockDecl {
    pub name: String,
    pub trait_name: String,
    pub expectations: Vec<HirMockExpectation>,
}
