use super::*;

/// HIR contract clause - a single condition in a contract block
#[derive(Debug, Clone, PartialEq)]
pub struct HirContractClause {
    /// The boolean condition expression
    pub condition: HirExpr,
    /// Optional error message for contract violation
    pub message: Option<String>,
}

/// HIR contract block for function contracts
#[derive(Debug, Clone, Default)]
pub struct HirContract {
    /// Preconditions (in:/requires:) - checked at function entry
    pub preconditions: Vec<HirContractClause>,
    /// Invariants (invariant:) - checked at entry and exit
    pub invariants: Vec<HirContractClause>,
    /// Postconditions (out(ret):/ensures:) - checked on success exit
    pub postconditions: Vec<HirContractClause>,
    /// Binding name for return value in postconditions (default: "ret")
    pub postcondition_binding: Option<String>,
    /// Error postconditions (out_err(err):) - checked on error exit
    pub error_postconditions: Vec<HirContractClause>,
    /// Binding name for error value in error postconditions (default: "err")
    pub error_binding: Option<String>,
    /// Captured "old" values - (local_index, snapshot_index)
    /// These are expressions evaluated at function entry for use in postconditions
    pub old_values: Vec<(usize, HirExpr)>,
    /// Termination measure (decreases:) - for Lean verification
    /// This is NOT checked at runtime, only used for Lean termination_by generation
    pub decreases: Option<HirContractClause>,
}

impl HirContract {
    /// Check if this contract block has any clauses
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.invariants.is_empty()
            && self.postconditions.is_empty()
            && self.error_postconditions.is_empty()
            && self.decreases.is_none()
    }

    /// Check if this contract has a termination measure
    pub fn has_decreases(&self) -> bool {
        self.decreases.is_some()
    }
}

/// Type invariant for struct/class types
#[derive(Debug, Clone, Default)]
pub struct HirTypeInvariant {
    /// Invariant conditions (using 'self' to refer to the instance)
    pub conditions: Vec<HirContractClause>,
}

/// Refined type definition (CTR-020)
///
/// A refined type is a type alias with a predicate that constrains values.
/// Example: `type PosI64 = i64 where self > 0`
#[derive(Debug, Clone)]
pub struct HirRefinedType {
    /// Name of the refined type
    pub name: String,
    /// Base type that is being refined
    pub base_type: TypeId,
    /// Refinement predicate (using 'self' to refer to the value)
    pub predicate: HirExpr,
}

/// CTR-021: Subtype relationship result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubtypeResult {
    /// Types are the same - no coercion needed
    Same,
    /// Source is a subtype of target - no runtime check needed (widening)
    /// Example: PosI64 -> i64 (refined to base)
    Subtype,
    /// Target is a subtype of source - runtime check needed (narrowing)
    /// Example: i64 -> PosI64 (base to refined)
    NeedsCheck,
    /// Types are incompatible
    Incompatible,
}

impl HirRefinedType {
    /// CTR-022: Attempt to evaluate a constant predicate at compile time
    ///
    /// Returns Some(true) if the predicate is definitely satisfied,
    /// Some(false) if it's definitely violated, or None if we can't determine.
    pub fn try_const_eval(&self, value: &HirExpr) -> Option<bool> {
        // Simple constant folding for common cases
        match (&self.predicate.kind, &value.kind) {
            // For predicates like `self > 0` with integer constants
            (HirExprKind::Binary { op, left, right }, HirExprKind::Integer(val)) => {
                // Check if predicate is in form: self <op> <const>
                if let (HirExprKind::Local(0), HirExprKind::Integer(bound)) =
                    (&left.kind, &right.kind)
                {
                    match op {
                        BinOp::Gt => return Some(*val > *bound),
                        BinOp::GtEq => return Some(*val >= *bound),
                        BinOp::Lt => return Some(*val < *bound),
                        BinOp::LtEq => return Some(*val <= *bound),
                        BinOp::Eq => return Some(*val == *bound),
                        BinOp::NotEq => return Some(*val != *bound),
                        _ => {}
                    }
                }
                // Check reversed: <const> <op> self
                if let (HirExprKind::Integer(bound), HirExprKind::Local(0)) =
                    (&left.kind, &right.kind)
                {
                    match op {
                        BinOp::Gt => return Some(*bound > *val),
                        BinOp::GtEq => return Some(*bound >= *val),
                        BinOp::Lt => return Some(*bound < *val),
                        BinOp::LtEq => return Some(*bound <= *val),
                        BinOp::Eq => return Some(*bound == *val),
                        BinOp::NotEq => return Some(*bound != *val),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        None
    }
}
