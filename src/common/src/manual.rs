use std::sync::Mutex;

//==============================================================================
// Nat - Non-negative integer (matches Lean's Nat)
//==============================================================================
// Lean's Nat type is always non-negative. This newtype provides the same
// guarantee in Rust and matches Lean semantics for pred (saturating at 0).

/// Non-negative integer matching Lean's Nat type.
/// Invariant: value is always >= 0 (guaranteed by usize).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Nat(pub usize);

impl Nat {
    pub const ZERO: Nat = Nat(0);

    /// Create a new Nat from a usize.
    pub fn new(n: usize) -> Self {
        Nat(n)
    }

    /// Get the inner value.
    pub fn get(self) -> usize {
        self.0
    }

    /// Predecessor function matching Lean's Nat.pred.
    /// Returns 0 if self is 0 (saturating subtraction).
    pub fn pred(self) -> Nat {
        Nat(self.0.saturating_sub(1))
    }

    /// Successor function.
    pub fn succ(self) -> Nat {
        Nat(self.0.saturating_add(1))
    }

    /// Check if zero.
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }
}

impl From<usize> for Nat {
    fn from(n: usize) -> Self {
        Nat(n)
    }
}

impl From<Nat> for usize {
    fn from(n: Nat) -> Self {
        n.0
    }
}

//==============================================================================
// Standalone Validity Predicates (matches Lean style)
//==============================================================================
// These standalone functions mirror Lean's predicate style exactly.
// They can be used for verification and property testing.

/// Lean: def valid (s : BorrowState) : Prop := if s.exclusive then s.shared = 0 else True
///
/// Check the borrow state validity invariant.
/// Valid states either have no exclusive borrow, or have exclusive with zero shared.
pub fn borrow_state_valid(s: &BorrowState) -> bool {
    if s.exclusive {
        s.shared.is_zero()
    } else {
        true
    }
}

/// Lean: def safe (s : GcState) : Prop := ∀ id, id ∈ s.borrowed → id ∈ s.live
///
/// Check the GC state safety invariant.
/// All borrowed objects must be in the live set.
pub fn gc_state_safe(s: &GcState) -> bool {
    s.borrowed.iter().all(|id| s.live.contains(id))
}

/// Lean: def safe (s : GcStateVerify) : Prop := ∀ id, id ∈ s.borrowed → id ∈ s.live
///
/// Check the GC state safety invariant (verification variant).
pub fn gc_state_verify_safe(s: &GcStateVerify) -> bool {
    s.borrowed.iter().all(|id| s.live.contains(id))
}

//==============================================================================
// Borrow Tracking (for formal verification)
//==============================================================================
// This module provides explicit borrow tracking that maps directly to the
// Lean 4 formal verification model in `verification/manual_pointer_borrow/`.
//
// The Lean model is:
//   structure BorrowState where
//     exclusive : Bool := false
//     shared : Nat := 0
//   def valid (s : BorrowState) : Prop :=
//     if s.exclusive then s.shared = 0 else True
//
// Invariant: No mixing of exclusive and shared borrows.
//
// We provide TWO representations:
// 1. `BorrowState` - dynamic validation (original Lean model)
// 2. `ValidBorrowState` - type-safe encoding (invariant in the type)

/// Explicit borrow state for a single allocation.
/// Maps directly to the Lean `BorrowState` structure.
/// NOTE: This type can represent invalid states - use `is_valid()` or `borrow_state_valid()`.
///
/// Lean equivalent:
/// ```lean
/// structure BorrowState where
///   exclusive : Bool := false
///   shared : Nat := 0
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BorrowState {
    /// True if an exclusive (mutable) borrow is active
    pub exclusive: bool,
    /// Count of active shared (immutable) borrows (Nat - always >= 0)
    pub shared: Nat,
}

impl BorrowState {
    /// Create a new unborrowed state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Check the validity invariant: exclusive implies shared = 0
    /// Corresponds to Lean's `valid` predicate.
    /// Prefer standalone `borrow_state_valid()` for Lean-style code.
    pub fn is_valid(&self) -> bool {
        borrow_state_valid(self)
    }

    /// Convert to type-safe representation if valid.
    pub fn to_valid(&self) -> Option<ValidBorrowState> {
        ValidBorrowState::from_state(self)
    }

    /// Attempt to take an exclusive borrow (mutating version).
    /// Corresponds to Lean's `takeExclusive`.
    pub fn take_exclusive(&mut self) -> bool {
        if self.shared.is_zero() {
            self.exclusive = true;
            true
        } else {
            false
        }
    }

    /// Attempt to take a shared borrow (mutating version).
    /// Corresponds to Lean's `takeShared`.
    pub fn take_shared(&mut self) -> bool {
        if self.exclusive {
            false
        } else {
            self.shared = self.shared.succ();
            true
        }
    }

    /// Release an exclusive borrow (mutating version).
    /// Corresponds to Lean's `releaseExclusive`.
    pub fn release_exclusive(&mut self) {
        self.exclusive = false;
    }

    /// Release a shared borrow (mutating version).
    /// Corresponds to Lean's `releaseShared`.
    pub fn release_shared(&mut self) {
        self.shared = self.shared.pred();
    }
}

//==============================================================================
// Pure BorrowState Operations (matches Lean exactly)
//==============================================================================
// These functions take ownership and return new state, matching Lean's pure
// functional style. No mutation occurs.

/// Lean: def takeExclusive (s : BorrowState) : BorrowState :=
///   if s.shared = 0 then { s with exclusive := true } else s
pub fn take_exclusive(s: BorrowState) -> BorrowState {
    if s.shared.is_zero() {
        BorrowState {
            exclusive: true,
            ..s
        }
    } else {
        s
    }
}

/// Lean: def takeShared (s : BorrowState) : BorrowState :=
///   if s.exclusive then s else { s with shared := s.shared + 1 }
pub fn take_shared(s: BorrowState) -> BorrowState {
    if s.exclusive {
        s
    } else {
        BorrowState {
            shared: s.shared.succ(),
            ..s
        }
    }
}

/// Lean: def releaseShared (s : BorrowState) : BorrowState :=
///   { s with shared := s.shared.pred }
pub fn release_shared(s: BorrowState) -> BorrowState {
    BorrowState {
        shared: s.shared.pred(),
        ..s
    }
}

/// Lean: def releaseExclusive (s : BorrowState) : BorrowState :=
///   { s with exclusive := false }
pub fn release_exclusive(s: BorrowState) -> BorrowState {
    BorrowState {
        exclusive: false,
        ..s
    }
}

//==============================================================================
// Type-Safe Borrow State (invariant encoded in the type)
//==============================================================================
// This representation makes invalid states unrepresentable.
// The invariant "exclusive → shared = 0" is encoded in the enum structure.
//
// Lean equivalent:
//   inductive ValidBorrowState
//     | unborrowed                           -- no borrows
//     | exclusive                            -- one exclusive borrow
//     | shared (count : Nat) (h : count > 0) -- one or more shared borrows

/// Type-safe borrow state where the invariant is encoded in the type.
/// Invalid states (exclusive AND shared) are unrepresentable.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum ValidBorrowState {
    /// No active borrows
    #[default]
    Unborrowed,
    /// One exclusive (mutable) borrow - cannot coexist with shared
    Exclusive,
    /// One or more shared (immutable) borrows - count is always >= 1
    Shared(std::num::NonZeroUsize),
}

impl ValidBorrowState {
    /// Create from dynamic BorrowState if valid.
    pub fn from_state(state: &BorrowState) -> Option<Self> {
        match (state.exclusive, state.shared.get()) {
            (false, 0) => Some(ValidBorrowState::Unborrowed),
            (true, 0) => Some(ValidBorrowState::Exclusive),
            // Explicit: shared borrows (exclusive=false, shared>0)
            (false, n) => Some(ValidBorrowState::Shared(
                std::num::NonZeroUsize::new(n).expect("n > 0 after matching 0"),
            )),
            // Explicit: invalid state - exclusive AND shared (exclusive=true, shared>0)
            (true, _) => None,
        }
    }

    /// Convert to dynamic BorrowState for interop.
    pub fn to_state(&self) -> BorrowState {
        match self {
            ValidBorrowState::Unborrowed => BorrowState {
                exclusive: false,
                shared: Nat::ZERO,
            },
            ValidBorrowState::Exclusive => BorrowState {
                exclusive: true,
                shared: Nat::ZERO,
            },
            ValidBorrowState::Shared(n) => BorrowState {
                exclusive: false,
                shared: Nat::new(n.get()),
            },
        }
    }

    /// Try to take an exclusive borrow. Returns new state if successful.
    /// Corresponds to Lean's `takeExclusive`.
    pub fn take_exclusive(self) -> Option<ValidBorrowState> {
        match self {
            ValidBorrowState::Unborrowed => Some(ValidBorrowState::Exclusive),
            _ => None, // Cannot take exclusive if already borrowed
        }
    }

    /// Take a shared borrow. Always succeeds unless exclusive.
    /// Corresponds to Lean's `takeShared`.
    pub fn take_shared(self) -> Option<ValidBorrowState> {
        match self {
            ValidBorrowState::Unborrowed => Some(ValidBorrowState::Shared(
                std::num::NonZeroUsize::new(1).unwrap(),
            )),
            ValidBorrowState::Shared(n) => Some(ValidBorrowState::Shared(
                std::num::NonZeroUsize::new(n.get() + 1).unwrap(),
            )),
            ValidBorrowState::Exclusive => None,
        }
    }

    /// Release an exclusive borrow.
    /// Corresponds to Lean's `releaseExclusive`.
    pub fn release_exclusive(self) -> ValidBorrowState {
        match self {
            ValidBorrowState::Exclusive => ValidBorrowState::Unborrowed,
            other => other, // No-op if not exclusive
        }
    }

    /// Release a shared borrow.
    /// Corresponds to Lean's `releaseShared`.
    pub fn release_shared(self) -> ValidBorrowState {
        match self {
            ValidBorrowState::Shared(n) if n.get() == 1 => ValidBorrowState::Unborrowed,
            ValidBorrowState::Shared(n) => {
                ValidBorrowState::Shared(std::num::NonZeroUsize::new(n.get() - 1).unwrap())
            }
            other => other, // No-op if not shared
        }
    }

    /// Check if unborrowed.
    pub fn is_unborrowed(&self) -> bool {
        matches!(self, ValidBorrowState::Unborrowed)
    }

    /// Check if exclusively borrowed.
    pub fn is_exclusive(&self) -> bool {
        matches!(self, ValidBorrowState::Exclusive)
    }

    /// Check if shared borrowed.
    pub fn is_shared(&self) -> bool {
        matches!(self, ValidBorrowState::Shared(_))
    }

    /// Get shared count (0 if not shared).
    pub fn shared_count(&self) -> usize {
        match self {
            ValidBorrowState::Shared(n) => n.get(),
            // Explicit: unborrowed and exclusive have no shared borrows
            ValidBorrowState::Unborrowed | ValidBorrowState::Exclusive => 0,
        }
    }
}

//==============================================================================
// GC State Tracking (for formal verification)
//==============================================================================
// This module provides explicit GC state tracking that maps directly to the
// Lean 4 formal verification model in `verification/gc_manual_borrow/`.
//
// The Lean model is:
//   structure GcState where
//     live : List Nat := []
//     borrowed : List Nat := []
//   def safe (s : GcState) : Prop :=
//     ∀ id, id ∈ s.borrowed → id ∈ s.live
//
// Invariant: Every borrowed object must still be live.

/// Explicit GC state tracking for verification.
/// Maps directly to the Lean `GcState` structure.
#[derive(Debug, Default)]
pub struct GcState {
    /// Set of live allocation IDs
    live: std::collections::HashSet<usize>,
    /// Set of borrowed allocation IDs
    borrowed: std::collections::HashSet<usize>,
    /// Next allocation ID
    next_id: usize,
}

impl GcState {
    pub fn new() -> Self {
        Self::default()
    }

    /// Check the safety invariant: borrowed ⊆ live
    /// Corresponds to Lean's `safe` predicate.
    pub fn is_safe(&self) -> bool {
        self.borrowed.iter().all(|id| self.live.contains(id))
    }

    /// Allocate a new object, returning its ID.
    /// Corresponds to Lean's `allocate`.
    pub fn allocate(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.live.insert(id);
        id
    }

    /// Borrow an object (add to borrowed set if live).
    /// Corresponds to Lean's `borrow`.
    pub fn borrow(&mut self, id: usize) -> bool {
        if self.live.contains(&id) {
            self.borrowed.insert(id);
            true
        } else {
            false
        }
    }

    /// Release a borrow.
    /// Corresponds to Lean's `release`.
    pub fn release(&mut self, id: usize) {
        self.borrowed.remove(&id);
    }

    /// Safely collect an object (only if not borrowed).
    /// Corresponds to Lean's `collectSafe`.
    pub fn collect_safe(&mut self, id: usize) -> bool {
        if self.borrowed.contains(&id) {
            false
        } else {
            self.live.remove(&id);
            true
        }
    }

    /// Get counts for debugging/verification.
    pub fn counts(&self) -> (usize, usize) {
        (self.live.len(), self.borrowed.len())
    }

    /// Get live set for inspection.
    pub fn live(&self) -> &std::collections::HashSet<usize> {
        &self.live
    }

    /// Get borrowed set for inspection.
    pub fn borrowed(&self) -> &std::collections::HashSet<usize> {
        &self.borrowed
    }
}

//==============================================================================
// GcStateVerify - Vec-based variant for exact Lean correspondence
//==============================================================================
// This variant uses Vec instead of HashSet to match Lean's List semantics exactly.
// Use this for verification and property testing where order/duplicates matter.
//
// Lean equivalent:
// ```lean
// structure GcState where
//   live : List Nat := []
//   borrowed : List Nat := []
// ```

/// GC state using Vec (List) semantics for exact Lean correspondence.
/// Prefer `GcState` for production use (O(1) operations).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GcStateVerify {
    /// List of live allocation IDs (matches Lean's `live : List Nat`)
    pub live: Vec<usize>,
    /// List of borrowed allocation IDs (matches Lean's `borrowed : List Nat`)
    pub borrowed: Vec<usize>,
}

impl GcStateVerify {
    /// Create a new empty state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Check the safety invariant: borrowed ⊆ live
    /// Corresponds to Lean's `safe` predicate.
    /// Prefer standalone `gc_state_verify_safe()` for Lean-style code.
    pub fn is_safe(&self) -> bool {
        gc_state_verify_safe(self)
    }

    /// Allocate a new object, returning its ID.
    /// Lean: def allocate (s : GcState) (id : Nat) : GcState :=
    ///   { s with live := id :: s.live }
    pub fn allocate(&mut self, id: usize) -> &mut Self {
        self.live.insert(0, id); // Prepend like Lean's cons
        self
    }

    /// Borrow an object (add to borrowed set if live).
    /// Lean: def borrow (s : GcState) (id : Nat) : GcState :=
    ///   if h : id ∈ s.live then { s with borrowed := id :: s.borrowed } else s
    pub fn borrow(&mut self, id: usize) -> bool {
        if self.live.contains(&id) {
            self.borrowed.insert(0, id); // Prepend like Lean's cons
            true
        } else {
            false
        }
    }

    /// Release a borrow.
    /// Lean: def release (s : GcState) (id : Nat) : GcState :=
    ///   { s with borrowed := s.borrowed.erase id }
    pub fn release(&mut self, id: usize) {
        if let Some(pos) = self.borrowed.iter().position(|&x| x == id) {
            self.borrowed.remove(pos);
        }
    }

    /// Safely collect an object (only if not borrowed).
    /// Lean: def collectSafe (s : GcState) (id : Nat) : GcState :=
    ///   if h : id ∈ s.borrowed then s else { s with live := s.live.erase id }
    pub fn collect_safe(&mut self, id: usize) -> bool {
        if self.borrowed.contains(&id) {
            false
        } else {
            if let Some(pos) = self.live.iter().position(|&x| x == id) {
                self.live.remove(pos);
            }
            true
        }
    }
}

//==============================================================================
// Pure GcState Operations (matches Lean exactly)
//==============================================================================
// These functions take ownership and return new state, matching Lean's pure
// functional style. No mutation occurs.

/// Lean: def allocate (s : GcState) (id : Nat) : GcState :=
///   { s with live := id :: s.live }
pub fn gc_allocate(mut s: GcStateVerify, id: usize) -> GcStateVerify {
    s.live.insert(0, id);
    s
}

/// Lean: def borrow (s : GcState) (id : Nat) : GcState :=
///   if h : id ∈ s.live then { s with borrowed := id :: s.borrowed } else s
pub fn gc_borrow(mut s: GcStateVerify, id: usize) -> GcStateVerify {
    if s.live.contains(&id) {
        s.borrowed.insert(0, id);
    }
    s
}

/// Lean: def release (s : GcState) (id : Nat) : GcState :=
///   { s with borrowed := s.borrowed.erase id }
pub fn gc_release(mut s: GcStateVerify, id: usize) -> GcStateVerify {
    if let Some(pos) = s.borrowed.iter().position(|&x| x == id) {
        s.borrowed.remove(pos);
    }
    s
}

/// Lean: def collectSafe (s : GcState) (id : Nat) : GcState :=
///   if h : id ∈ s.borrowed then s else { s with live := s.live.erase id }
pub fn gc_collect_safe(mut s: GcStateVerify, id: usize) -> GcStateVerify {
    if !s.borrowed.contains(&id) {
        if let Some(pos) = s.live.iter().position(|&x| x == id) {
            s.live.remove(pos);
        }
    }
    s
}

/// Thread-safe GC state tracker.
#[derive(Debug, Default)]
pub struct GcStateTracker {
    state: Mutex<GcState>,
}

impl GcStateTracker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_safe(&self) -> bool {
        self.state.lock().unwrap().is_safe()
    }

    pub fn allocate(&self) -> usize {
        self.state.lock().unwrap().allocate()
    }

    pub fn borrow(&self, id: usize) -> bool {
        self.state.lock().unwrap().borrow(id)
    }

    pub fn release(&self, id: usize) {
        self.state.lock().unwrap().release(id)
    }

    pub fn collect_safe(&self, id: usize) -> bool {
        self.state.lock().unwrap().collect_safe(id)
    }

    pub fn counts(&self) -> (usize, usize) {
        self.state.lock().unwrap().counts()
    }
}

// Manual memory management types moved to manual_mem.rs
