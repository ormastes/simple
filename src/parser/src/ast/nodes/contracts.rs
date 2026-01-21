//! Contract and invariant AST nodes (preconditions, postconditions, invariants, refinement types)

use super::super::enums::*;
use super::core::*;
use crate::token::Span;

//==============================================================================
// Contract Blocks (LLM-friendly feature #400)
// Spec: doc/spec/invariant.md
//==============================================================================

/// Contract specification for a function.
///
/// Contracts make function behavior explicit and verifiable, which helps
/// catch LLM-generated code errors at runtime (and optionally at compile time).
///
/// New spec syntax (doc/spec/invariant.md):
/// ```simple
/// fn div(a: i64, b: i64) -> (i64 | DivByZero):
///     in:
///         b != 0
///     invariant:
///         true
///
///     if b == 0:
///         return DivByZero(msg: "division by zero")
///     return a / b
///
///     out(ret):
///         ret * b == a
///     out_err(err):
///         old(b) == 0
/// ```
///
/// Legacy syntax (still supported):
/// ```simple
/// fn divide(a: i64, b: i64) -> i64:
///     requires:
///         b != 0
///     ensures:
///         result * b == a
///     return a / b
/// ```
///
/// Termination (for Lean verification):
/// ```simple
/// fn factorial(n: i64) -> i64:
///     requires: n >= 0
///     decreases: n
///     ensures: ret >= 1
///     ...
/// ```
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ContractBlock {
    /// Preconditions (in: block) - must be true at function entry
    /// Legacy: requires: block
    pub preconditions: Vec<ContractClause>,
    /// Routine invariants (invariant: block inside function)
    /// Must be true at entry and all exits
    pub invariants: Vec<ContractClause>,
    /// Postconditions for success (out(ret): block)
    /// Legacy: ensures: block
    /// The binding name for return value (default: "ret")
    pub postconditions: Vec<ContractClause>,
    pub postcondition_binding: Option<String>,
    /// Postconditions for error exit (out_err(err): block)
    /// The binding name for error value (default: "err")
    pub error_postconditions: Vec<ContractClause>,
    pub error_binding: Option<String>,
    /// Termination measure (decreases: block) - for Lean verification
    /// Expression that must decrease on each recursive call
    /// Not checked at runtime, only used for Lean termination_by
    pub decreases: Option<ContractClause>,
    /// Proof reference (proof uses: theorem_name) - for Lean verification (VER-022)
    /// References an existing Lean theorem from lean{} blocks
    /// Example: proof uses: list_sum_pos
    pub proof_uses: Option<String>,
}

impl ContractBlock {
    /// Check if the contract block is empty (no clauses)
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.invariants.is_empty()
            && self.postconditions.is_empty()
            && self.error_postconditions.is_empty()
            && self.decreases.is_none()
            && self.proof_uses.is_none()
    }

    /// Check if this contract has a termination measure
    pub fn has_decreases(&self) -> bool {
        self.decreases.is_some()
    }

    /// Legacy compatibility: get requires clauses
    pub fn requires(&self) -> &[ContractClause] {
        &self.preconditions
    }

    /// Legacy compatibility: get ensures clauses
    pub fn ensures(&self) -> &[ContractClause] {
        &self.postconditions
    }
}

/// A single contract clause (one condition in contract blocks).
#[derive(Debug, Clone, PartialEq)]
pub struct ContractClause {
    pub span: Span,
    /// The boolean expression that must be true
    pub condition: Expr,
    /// Optional message to display on failure
    pub message: Option<String>,
}

/// Class/struct invariant - must be true after constructor and every public method.
///
/// Example:
/// ```simple
/// class BankAccount:
///     balance: i64
///
///     invariant:
///         balance >= 0
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct InvariantBlock {
    pub span: Span,
    /// Conditions that must always be true
    pub conditions: Vec<ContractClause>,
}

/// Refinement type definition (type T = Base where predicate)
///
/// Example:
/// ```simple
/// type PosI64 = i64 where self > 0
/// type NonZero = i64 where self != 0
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementType {
    pub span: Span,
    pub name: String,
    pub base_type: Type,
    /// The predicate expression (uses 'self' to refer to the value)
    pub predicate: Expr,
    pub visibility: Visibility,
}
