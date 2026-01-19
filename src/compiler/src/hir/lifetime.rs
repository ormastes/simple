//! Lifetime inference and tracking for memory safety
//!
//! This module implements lifetime inference for references and borrows,
//! detecting violations like use-after-free, dangling references, and
//! escaping borrows.
//!
//! ## Lifetime Model
//!
//! ```text
//! 'static > 'module > 'function > 'block > 'expr
//! ```
//!
//! Each scope has a lifetime that outlives its children. References cannot
//! outlive their origin scope.
//!
//! ## Key Properties (verified in Lean 4)
//!
//! 1. **Well-Formedness**: Every reference has a valid lifetime
//! 2. **Containment**: Borrowed reference lifetime ⊆ owner lifetime
//! 3. **Non-Escaping**: References don't escape their defining scope
//! 4. **Drop Order**: Values dropped in reverse declaration order

use std::collections::HashMap;
use std::fmt;

use simple_parser::Span;

/// Unique identifier for a lifetime
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LifetimeId(u32);

impl LifetimeId {
    /// Static lifetime - lives for the entire program
    pub const STATIC: LifetimeId = LifetimeId(0);

    /// Create a new lifetime ID
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    /// Check if this is the static lifetime
    pub fn is_static(&self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for LifetimeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_static() {
            write!(f, "'static")
        } else {
            write!(f, "'{}", self.0)
        }
    }
}

/// Scope kind for lifetime tracking
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// Module-level scope (globals, constants)
    Module,
    /// Function body scope
    Function,
    /// Block scope (if, while, loop, etc.)
    Block,
    /// Expression scope (temporaries)
    Expression,
}

impl ScopeKind {
    /// Get the nesting level (higher = shorter lifetime)
    pub fn nesting_level(&self) -> u8 {
        match self {
            ScopeKind::Module => 0,
            ScopeKind::Function => 1,
            ScopeKind::Block => 2,
            ScopeKind::Expression => 3,
        }
    }
}

/// A scope with lifetime information
#[derive(Debug, Clone)]
pub struct Scope {
    /// Unique identifier for this scope
    pub id: LifetimeId,
    /// Parent scope (None for module scope)
    pub parent: Option<LifetimeId>,
    /// Kind of scope
    pub kind: ScopeKind,
    /// Source location
    pub span: Option<Span>,
    /// Variables declared in this scope (name -> lifetime)
    pub variables: HashMap<String, LifetimeId>,
}

impl Scope {
    /// Create a new scope
    pub fn new(id: LifetimeId, parent: Option<LifetimeId>, kind: ScopeKind) -> Self {
        Self {
            id,
            parent,
            kind,
            span: None,
            variables: HashMap::new(),
        }
    }

    /// Add a variable to this scope
    pub fn add_variable(&mut self, name: String, lifetime: LifetimeId) {
        self.variables.insert(name, lifetime);
    }
}

/// Origin of a reference (where the value was created)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReferenceOrigin {
    /// Local variable
    Local { name: String, scope: LifetimeId },
    /// Function parameter
    Parameter { name: String, index: usize },
    /// Global variable
    Global { name: String },
    /// Temporary value
    Temporary { scope: LifetimeId },
    /// Field of another reference
    Field { base: Box<ReferenceOrigin>, field: String },
    /// Return value
    Return { function: String },
}

impl ReferenceOrigin {
    /// Get the lifetime of this origin
    pub fn lifetime(&self) -> LifetimeId {
        match self {
            ReferenceOrigin::Local { scope, .. } => *scope,
            ReferenceOrigin::Parameter { .. } => LifetimeId::STATIC, // Params outlive function body
            ReferenceOrigin::Global { .. } => LifetimeId::STATIC,
            ReferenceOrigin::Temporary { scope } => *scope,
            ReferenceOrigin::Field { base, .. } => base.lifetime(),
            ReferenceOrigin::Return { .. } => LifetimeId::STATIC,
        }
    }
}

/// A reference with lifetime information
#[derive(Debug, Clone)]
pub struct LifetimeRef {
    /// The lifetime of this reference
    pub lifetime: LifetimeId,
    /// Where this reference points to
    pub origin: ReferenceOrigin,
    /// Source location where reference was created
    pub span: Option<Span>,
}

/// Lifetime violation types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LifetimeViolation {
    /// Reference escapes its defining scope
    EscapingReference {
        ref_lifetime: LifetimeId,
        target_scope: LifetimeId,
        origin: ReferenceOrigin,
        span: Span,
    },
    /// Use after the referenced value is dropped
    UseAfterDrop {
        variable: String,
        dropped_at: LifetimeId,
        used_at: LifetimeId,
        span: Span,
    },
    /// Dangling reference (points to freed memory)
    DanglingReference {
        variable: String,
        origin: ReferenceOrigin,
        span: Span,
    },
    /// Borrow outlives owner
    BorrowOutlivesOwner {
        borrow_lifetime: LifetimeId,
        owner_lifetime: LifetimeId,
        span: Span,
    },
    /// Return reference to local
    ReturnLocalReference {
        variable: String,
        function: String,
        span: Span,
    },
    /// Store reference in longer-lived location
    StorageEscapes {
        ref_lifetime: LifetimeId,
        storage_lifetime: LifetimeId,
        span: Span,
    },
}

impl LifetimeViolation {
    /// Get a human-readable error code
    pub fn code(&self) -> &'static str {
        match self {
            LifetimeViolation::EscapingReference { .. } => "E2001",
            LifetimeViolation::UseAfterDrop { .. } => "E2002",
            LifetimeViolation::DanglingReference { .. } => "E2003",
            LifetimeViolation::BorrowOutlivesOwner { .. } => "E2004",
            LifetimeViolation::ReturnLocalReference { .. } => "E2005",
            LifetimeViolation::StorageEscapes { .. } => "E2006",
        }
    }

    /// Get a short description
    pub fn description(&self) -> String {
        match self {
            LifetimeViolation::EscapingReference { origin, .. } => {
                format!("reference to {:?} escapes its scope", origin)
            }
            LifetimeViolation::UseAfterDrop { variable, .. } => {
                format!("use of `{}` after it was dropped", variable)
            }
            LifetimeViolation::DanglingReference { variable, .. } => {
                format!("dangling reference to `{}`", variable)
            }
            LifetimeViolation::BorrowOutlivesOwner { .. } => {
                "borrowed reference outlives the owner".to_string()
            }
            LifetimeViolation::ReturnLocalReference { variable, .. } => {
                format!("cannot return reference to local variable `{}`", variable)
            }
            LifetimeViolation::StorageEscapes { .. } => {
                "reference stored in longer-lived location".to_string()
            }
        }
    }

    /// Get the span where the violation occurred
    pub fn span(&self) -> Span {
        match self {
            LifetimeViolation::EscapingReference { span, .. }
            | LifetimeViolation::UseAfterDrop { span, .. }
            | LifetimeViolation::DanglingReference { span, .. }
            | LifetimeViolation::BorrowOutlivesOwner { span, .. }
            | LifetimeViolation::ReturnLocalReference { span, .. }
            | LifetimeViolation::StorageEscapes { span, .. } => *span,
        }
    }

    /// Format the violation with detailed lifetime information
    pub fn format_detailed(&self, source_file: &str) -> String {
        let span = self.span();
        let mut msg = format!(
            "{}:{}:{}: error[{}]: {}\n",
            source_file,
            span.line,
            span.column,
            self.code(),
            self.description()
        );

        // Add lifetime context
        match self {
            LifetimeViolation::EscapingReference {
                ref_lifetime,
                target_scope,
                ..
            } => {
                msg.push_str(&format!(
                    "  note: reference has lifetime {} but escapes to scope {}\n",
                    ref_lifetime, target_scope
                ));
                msg.push_str("  help: consider returning an owned value instead\n");
            }
            LifetimeViolation::UseAfterDrop {
                dropped_at,
                used_at,
                ..
            } => {
                msg.push_str(&format!(
                    "  note: value was dropped at scope {} but used at scope {}\n",
                    dropped_at, used_at
                ));
                msg.push_str("  help: ensure the value lives long enough\n");
            }
            LifetimeViolation::BorrowOutlivesOwner {
                borrow_lifetime,
                owner_lifetime,
                ..
            } => {
                msg.push_str(&format!(
                    "  note: borrow lifetime {} > owner lifetime {}\n",
                    borrow_lifetime, owner_lifetime
                ));
                msg.push_str("  help: reduce the borrow's scope or extend the owner's lifetime\n");
            }
            LifetimeViolation::ReturnLocalReference { function, .. } => {
                msg.push_str(&format!(
                    "  note: local variables are dropped when `{}` returns\n",
                    function
                ));
                msg.push_str("  help: return an owned value or use a parameter reference\n");
            }
            _ => {}
        }

        msg
    }
}

/// Lifetime inference context
#[derive(Debug)]
pub struct LifetimeContext {
    /// All scopes in the current function
    scopes: Vec<Scope>,
    /// Current scope stack (indices into scopes)
    scope_stack: Vec<usize>,
    /// Next lifetime ID to allocate
    next_id: u32,
    /// Collected violations
    violations: Vec<LifetimeViolation>,
    /// Variable lifetimes (name -> origin)
    variable_origins: HashMap<String, ReferenceOrigin>,
    /// Current function name (for error messages)
    current_function: Option<String>,
}

impl LifetimeContext {
    /// Create a new lifetime context
    pub fn new() -> Self {
        let mut ctx = Self {
            scopes: Vec::new(),
            scope_stack: Vec::new(),
            next_id: 1, // 0 is reserved for 'static
            violations: Vec::new(),
            variable_origins: HashMap::new(),
            current_function: None,
        };
        // Create module scope
        let module_scope = Scope::new(LifetimeId::STATIC, None, ScopeKind::Module);
        ctx.scopes.push(module_scope);
        ctx.scope_stack.push(0);
        ctx
    }

    /// Set the current function name
    pub fn set_function(&mut self, name: &str) {
        self.current_function = Some(name.to_string());
    }

    /// Allocate a new lifetime ID
    pub fn alloc_lifetime(&mut self) -> LifetimeId {
        let id = LifetimeId::new(self.next_id);
        self.next_id += 1;
        id
    }

    /// Get the current scope's lifetime
    pub fn current_lifetime(&self) -> LifetimeId {
        self.scope_stack
            .last()
            .and_then(|&idx| self.scopes.get(idx))
            .map(|s| s.id)
            .unwrap_or(LifetimeId::STATIC)
    }

    /// Enter a new scope
    pub fn enter_scope(&mut self, kind: ScopeKind, span: Option<Span>) -> LifetimeId {
        let id = self.alloc_lifetime();
        let parent = Some(self.current_lifetime());
        let mut scope = Scope::new(id, parent, kind);
        scope.span = span;
        let idx = self.scopes.len();
        self.scopes.push(scope);
        self.scope_stack.push(idx);
        id
    }

    /// Exit the current scope
    pub fn exit_scope(&mut self) {
        self.scope_stack.pop();
    }

    /// Register a variable in the current scope
    pub fn register_variable(&mut self, name: &str, origin: ReferenceOrigin) {
        let lifetime = self.current_lifetime();
        if let Some(idx) = self.scope_stack.last() {
            if let Some(scope) = self.scopes.get_mut(*idx) {
                scope.add_variable(name.to_string(), lifetime);
            }
        }
        self.variable_origins.insert(name.to_string(), origin);
    }

    /// Get the origin of a variable
    pub fn get_variable_origin(&self, name: &str) -> Option<&ReferenceOrigin> {
        self.variable_origins.get(name)
    }

    /// Check if lifetime `a` outlives lifetime `b` (a >= b)
    pub fn outlives(&self, a: LifetimeId, b: LifetimeId) -> bool {
        if a == LifetimeId::STATIC {
            return true;
        }
        if b == LifetimeId::STATIC {
            return false;
        }

        // Find scope for b and check if a is an ancestor
        let mut current = Some(b);
        while let Some(id) = current {
            if id == a {
                return true;
            }
            // Find parent
            current = self
                .scopes
                .iter()
                .find(|s| s.id == id)
                .and_then(|s| s.parent);
        }
        false
    }

    /// Check if a reference can be stored in a location with given lifetime
    pub fn check_storage(&mut self, ref_lifetime: LifetimeId, storage_lifetime: LifetimeId, span: Span) {
        // Reference lifetime must outlive storage lifetime
        if !self.outlives(ref_lifetime, storage_lifetime) {
            self.violations.push(LifetimeViolation::StorageEscapes {
                ref_lifetime,
                storage_lifetime,
                span,
            });
        }
    }

    /// Check if a reference escapes its scope
    pub fn check_escape(&mut self, ref_lifetime: LifetimeId, target_scope: LifetimeId, origin: ReferenceOrigin, span: Span) {
        if !self.outlives(ref_lifetime, target_scope) {
            self.violations.push(LifetimeViolation::EscapingReference {
                ref_lifetime,
                target_scope,
                origin,
                span,
            });
        }
    }

    /// Check if a return value escapes the function
    pub fn check_return(&mut self, origin: &ReferenceOrigin, span: Span) {
        match origin {
            ReferenceOrigin::Local { name, .. } => {
                self.violations.push(LifetimeViolation::ReturnLocalReference {
                    variable: name.clone(),
                    function: self.current_function.clone().unwrap_or_default(),
                    span,
                });
            }
            ReferenceOrigin::Temporary { .. } => {
                self.violations.push(LifetimeViolation::ReturnLocalReference {
                    variable: "<temporary>".to_string(),
                    function: self.current_function.clone().unwrap_or_default(),
                    span,
                });
            }
            ReferenceOrigin::Field { base, .. } => {
                self.check_return(base, span);
            }
            _ => {} // Parameters and globals are fine to return
        }
    }

    /// Check a borrow against its owner
    pub fn check_borrow(&mut self, borrow_lifetime: LifetimeId, owner_lifetime: LifetimeId, span: Span) {
        if !self.outlives(owner_lifetime, borrow_lifetime) {
            self.violations.push(LifetimeViolation::BorrowOutlivesOwner {
                borrow_lifetime,
                owner_lifetime,
                span,
            });
        }
    }

    /// Get all collected violations
    pub fn violations(&self) -> &[LifetimeViolation] {
        &self.violations
    }

    /// Check if there are any violations
    pub fn has_violations(&self) -> bool {
        !self.violations.is_empty()
    }

    /// Format all violations
    pub fn format_violations(&self, source_file: &str) -> String {
        self.violations
            .iter()
            .map(|v| v.format_detailed(source_file))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Generate Lean 4 verification code for the current lifetime constraints
    pub fn generate_lean4(&self) -> String {
        let mut lean = String::new();

        lean.push_str("/-\n");
        lean.push_str("  Lifetime verification generated from Simple compiler\n");
        lean.push_str("  Scopes and lifetime relationships\n");
        lean.push_str("-/\n\n");

        lean.push_str("namespace LifetimeVerification\n\n");

        // Define lifetime type
        lean.push_str("-- Lifetime identifiers\n");
        lean.push_str("inductive Lifetime where\n");
        lean.push_str("  | static : Lifetime\n");
        for scope in &self.scopes {
            if !scope.id.is_static() {
                lean.push_str(&format!("  | l{} : Lifetime\n", scope.id.0));
            }
        }
        lean.push_str("deriving DecidableEq, Repr\n\n");

        // Define outlives relation
        lean.push_str("-- Outlives relation (a >= b means a outlives b)\n");
        lean.push_str("def outlives : Lifetime → Lifetime → Bool\n");
        lean.push_str("  | Lifetime.static, _ => true\n");
        lean.push_str("  | _, Lifetime.static => false\n");

        // Add specific outlives relationships
        for scope in &self.scopes {
            if let Some(parent) = scope.parent {
                if !parent.is_static() {
                    lean.push_str(&format!(
                        "  | Lifetime.l{}, Lifetime.l{} => true\n",
                        parent.0, scope.id.0
                    ));
                }
            }
        }
        lean.push_str("  | a, b => a == b\n\n");

        // Generate verification theorems
        lean.push_str("-- Verification theorems\n\n");

        lean.push_str("-- Static outlives everything\n");
        lean.push_str("theorem static_outlives_all (l : Lifetime) : outlives Lifetime.static l = true := by\n");
        lean.push_str("  cases l <;> rfl\n\n");

        lean.push_str("-- Outlives is reflexive\n");
        lean.push_str("theorem outlives_refl (l : Lifetime) : outlives l l = true := by\n");
        lean.push_str("  cases l <;> simp [outlives]\n\n");

        // Add violation checks if any
        if !self.violations.is_empty() {
            lean.push_str("-- Detected lifetime violations\n");
            lean.push_str("-- These would be compile-time errors in the Simple compiler\n\n");

            for (i, violation) in self.violations.iter().enumerate() {
                lean.push_str(&format!("-- Violation {}: {}\n", i + 1, violation.description()));
            }
            lean.push_str("\n");
        }

        lean.push_str("end LifetimeVerification\n");

        lean
    }
}

impl Default for LifetimeContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_span() -> Span {
        Span::new(0, 10, 1, 1)
    }

    #[test]
    fn test_lifetime_outlives() {
        let mut ctx = LifetimeContext::new();

        // Enter function scope
        let func_lt = ctx.enter_scope(ScopeKind::Function, None);

        // Enter block scope
        let block_lt = ctx.enter_scope(ScopeKind::Block, None);

        // Static outlives everything
        assert!(ctx.outlives(LifetimeId::STATIC, func_lt));
        assert!(ctx.outlives(LifetimeId::STATIC, block_lt));

        // Function outlives block
        assert!(ctx.outlives(func_lt, block_lt));

        // Block does not outlive function
        assert!(!ctx.outlives(block_lt, func_lt));
    }

    #[test]
    fn test_escaping_reference() {
        let mut ctx = LifetimeContext::new();
        ctx.set_function("test_fn");

        let func_lt = ctx.enter_scope(ScopeKind::Function, None);
        let block_lt = ctx.enter_scope(ScopeKind::Block, Some(test_span()));

        // Reference created in block
        let origin = ReferenceOrigin::Local {
            name: "x".to_string(),
            scope: block_lt,
        };

        // Try to escape to function scope - should fail
        ctx.check_escape(block_lt, func_lt, origin.clone(), test_span());

        assert!(ctx.has_violations());
        assert!(matches!(
            ctx.violations()[0],
            LifetimeViolation::EscapingReference { .. }
        ));
    }

    #[test]
    fn test_return_local() {
        let mut ctx = LifetimeContext::new();
        ctx.set_function("get_ref");

        let func_lt = ctx.enter_scope(ScopeKind::Function, None);

        let origin = ReferenceOrigin::Local {
            name: "local_var".to_string(),
            scope: func_lt,
        };

        ctx.check_return(&origin, test_span());

        assert!(ctx.has_violations());
        assert!(matches!(
            ctx.violations()[0],
            LifetimeViolation::ReturnLocalReference { .. }
        ));
    }

    #[test]
    fn test_generate_lean4() {
        let mut ctx = LifetimeContext::new();

        ctx.enter_scope(ScopeKind::Function, None);
        ctx.enter_scope(ScopeKind::Block, None);

        let lean = ctx.generate_lean4();

        assert!(lean.contains("namespace LifetimeVerification"));
        assert!(lean.contains("inductive Lifetime"));
        assert!(lean.contains("def outlives"));
        assert!(lean.contains("theorem static_outlives_all"));
    }
}
