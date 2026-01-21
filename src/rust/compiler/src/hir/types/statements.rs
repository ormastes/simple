use super::contracts::HirContractClause;
use super::*;
use simple_parser::ast::Mutability;

/// HIR statement
#[derive(Debug, Clone, PartialEq)]
pub enum HirStmt {
    Let {
        local_index: usize,
        ty: TypeId,
        value: Option<HirExpr>,
    },
    Assign {
        target: HirExpr,
        value: HirExpr,
    },
    Return(Option<HirExpr>),
    Expr(HirExpr),
    If {
        condition: HirExpr,
        then_block: Vec<HirStmt>,
        else_block: Option<Vec<HirStmt>>,
    },
    While {
        condition: HirExpr,
        body: Vec<HirStmt>,
        /// Loop invariants for verification
        invariants: Vec<HirContractClause>,
    },
    /// For loop (lowered from ForStmt)
    /// Note: for loops can have invariants for verification
    For {
        /// Pattern binding for the loop variable
        pattern: String,
        /// The iterator expression
        iterable: HirExpr,
        /// Loop body
        body: Vec<HirStmt>,
        /// Loop invariants for verification
        invariants: Vec<HirContractClause>,
    },
    Loop {
        body: Vec<HirStmt>,
    },
    Break,
    Continue,
    /// Assert statement for inline contract checks
    /// assert condition, "message"
    Assert {
        condition: HirExpr,
        message: Option<String>,
    },
    /// Assume statement for verification assumptions
    /// assume condition, "message"
    /// In verification: creates hypothesis without proof (axiom-like)
    /// At runtime: behaves like assert (debug) or erased (release)
    Assume {
        condition: HirExpr,
        message: Option<String>,
    },
    /// Admit statement for skipping proofs (tracked)
    /// admit condition, "reason"
    /// In verification: marks as axiom, requires tracking
    /// At runtime: behaves like assert
    Admit {
        condition: HirExpr,
        message: Option<String>,
    },
    /// Proof hint for guiding Lean proof tactics (VER-020)
    /// lean hint: "simp"
    /// In verification: provides tactic hint for Lean prover
    /// At runtime: no-op (erased)
    ProofHint {
        hint: String,
    },
    /// Calculational proof block for step-by-step equational reasoning (VER-021)
    /// calc:
    ///     sum(0..=n)
    ///     == sum(0..n) + n        by: "definition"
    ///     == n * (n + 1) / 2      by: "factor"
    /// In verification: generates Lean calc proof
    /// At runtime: no-op (erased)
    Calc {
        steps: Vec<HirCalcStep>,
    },
}

/// A single step in a calculational proof
#[derive(Debug, Clone, PartialEq)]
pub struct HirCalcStep {
    /// The expression in this step
    pub expr: HirExpr,
    /// Optional justification string (by: "reason")
    pub justification: Option<String>,
}

/// Local variable info
#[derive(Debug, Clone)]
pub struct LocalVar {
    pub name: String,
    pub ty: TypeId,
    pub mutability: Mutability,
    /// Per-parameter DI injection flag (#1013)
    pub inject: bool,
    /// Ghost variable - only exists for verification, erased at runtime
    /// Ghost variables can only be used in verified contexts
    pub is_ghost: bool,
}

impl LocalVar {
    /// Check if this variable is mutable (helper for backwards compatibility)
    pub fn is_mutable(&self) -> bool {
        self.mutability.is_mutable()
    }

    /// Check if this is a ghost variable (verification-only)
    pub fn is_ghost(&self) -> bool {
        self.is_ghost
    }
}
