//==============================================================================
// Visibility and Mutability (for formal verification)
//==============================================================================
// These enums replace boolean flags to make the semantics explicit.
// This simplifies formal verification by making invalid states unrepresentable.

/// Visibility of a declaration.
///
/// Lean equivalent:
/// ```lean
/// inductive Visibility
///   | public
///   | private
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    /// Publicly accessible
    Public,
    /// Private to the module (default)
    #[default]
    Private,
}

impl Visibility {
    /// Check if this is public visibility
    pub fn is_public(&self) -> bool {
        matches!(self, Visibility::Public)
    }
}

/// Mutability of a binding or field.
///
/// Lean equivalent:
/// ```lean
/// inductive Mutability
///   | mutable
///   | immutable
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mutability {
    /// Can be modified
    Mutable,
    /// Cannot be modified (default)
    #[default]
    Immutable,
}

impl Mutability {
    /// Check if this is mutable
    pub fn is_mutable(&self) -> bool {
        matches!(self, Mutability::Mutable)
    }
}

/// Range bound type - whether the end bound is inclusive or exclusive.
///
/// Lean equivalent:
/// ```lean
/// inductive RangeBound
///   | inclusive  -- a..=b includes b
///   | exclusive  -- a..b excludes b
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RangeBound {
    /// Inclusive bound (a..=b includes b)
    Inclusive,
    /// Exclusive bound (a..b excludes b, default)
    #[default]
    Exclusive,
}

impl RangeBound {
    /// Check if this is inclusive
    pub fn is_inclusive(&self) -> bool {
        matches!(self, RangeBound::Inclusive)
    }

    /// Check if this is exclusive
    pub fn is_exclusive(&self) -> bool {
        matches!(self, RangeBound::Exclusive)
    }
}

/// Self-binding mode for method calls.
/// Distinguishes whether `self` should be explicitly bound in parameter evaluation.
///
/// Lean equivalent:
/// ```lean
/// inductive SelfMode
///   | includeSelf  -- bind self from parameters
///   | skipSelf     -- self is already bound
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SelfMode {
    /// Include self in parameter binding (for constructors, free functions)
    #[default]
    IncludeSelf,
    /// Skip self in parameter binding (self already bound to receiver)
    SkipSelf,
}

impl SelfMode {
    /// Check if self should be skipped
    pub fn should_skip_self(&self) -> bool {
        matches!(self, SelfMode::SkipSelf)
    }
}

/// Capture mode for lambdas/closures.
/// Distinguishes between move semantics (captures by value) and borrow semantics.
///
/// Lean equivalent:
/// ```lean
/// inductive MoveMode
///   | move  -- captures environment by value
///   | copy  -- captures environment by reference (default)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MoveMode {
    /// Move closure: captures environment by value (move|x: expr)
    Move,
    /// Copy/borrow closure: captures environment by reference (|x: expr, default)
    #[default]
    Copy,
}

impl MoveMode {
    /// Check if this is a move closure
    pub fn is_move(&self) -> bool {
        matches!(self, MoveMode::Move)
    }
}

