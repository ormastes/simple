namespace ManualPointerBorrow

/-- A tiny borrow checker for manual pointers: `exclusive` tracks a unique borrow,
    `shared` counts active shared borrows. -/
structure BorrowState where
  exclusive : Bool := false
  shared : Nat := 0
deriving Repr

/-- Type-safe borrow state where invalid states are unrepresentable.
    The invariant "exclusive → shared = 0" is encoded in the inductive structure.
    This is an alternative representation to BorrowState that provides
    correctness by construction rather than runtime validation. -/
inductive ValidBorrowState
  | unborrowed                              -- no borrows active
  | exclusive                               -- one exclusive (mutable) borrow
  | shared (count : Nat) (h : count > 0)    -- one or more shared (immutable) borrows
deriving Repr

/-- Valid states disallow mixing an exclusive borrow with any shared borrows. -/
def valid (s : BorrowState) : Prop :=
  if s.exclusive then s.shared = 0 else True

/-- Convert ValidBorrowState to BorrowState. Always produces a valid state. -/
def ValidBorrowState.toState : ValidBorrowState → BorrowState
  | .unborrowed => { exclusive := false, shared := 0 }
  | .exclusive => { exclusive := true, shared := 0 }
  | .shared count _ => { exclusive := false, shared := count }

/-- Convert BorrowState to ValidBorrowState if valid.
    Returns none for invalid states (exclusive AND shared). -/
def BorrowState.toValid (s : BorrowState) : Option ValidBorrowState :=
  match s.exclusive, s.shared with
  | false, 0 => some .unborrowed
  | true, 0 => some .exclusive
  | false, n + 1 => some (.shared (n + 1) (Nat.succ_pos n))
  | true, _ + 1 => none  -- invalid: exclusive with shared

/-- Key theorem: ValidBorrowState always converts to a valid BorrowState.
    This is the benefit of the type-safe representation. -/
theorem validState_always_valid (vs : ValidBorrowState) : valid vs.toState := by
  cases vs with
  | unborrowed => simp [ValidBorrowState.toState, valid]
  | exclusive => simp [ValidBorrowState.toState, valid]
  | shared count h => simp [ValidBorrowState.toState, valid]

/-- Round-trip: toValid ∘ toState = some for valid states -/
theorem toValid_toState (vs : ValidBorrowState) :
    vs.toState.toValid = some vs := by
  cases vs with
  | unborrowed => simp [ValidBorrowState.toState, BorrowState.toValid]
  | exclusive => simp [ValidBorrowState.toState, BorrowState.toValid]
  | shared count h =>
    simp [ValidBorrowState.toState, BorrowState.toValid]
    cases count with
    | zero => exact absurd rfl (Nat.ne_of_gt h)
    | succ n => rfl

def takeExclusive (s : BorrowState) : BorrowState :=
  if s.shared = 0 then { s with exclusive := true } else s

def takeShared (s : BorrowState) : BorrowState :=
  if s.exclusive then s else { s with shared := s.shared + 1 }

def releaseShared (s : BorrowState) : BorrowState :=
  { s with shared := s.shared.pred }

def releaseExclusive (s : BorrowState) : BorrowState :=
  { s with exclusive := false }

-- Type-safe operations on ValidBorrowState.
-- These operations preserve validity by construction - no runtime checks needed.

-- Try to take exclusive borrow. Returns some only if currently unborrowed.
def ValidBorrowState.takeExclusive : ValidBorrowState → Option ValidBorrowState
  | .unborrowed => some .exclusive
  -- Explicit: cannot take exclusive if already borrowed
  | .exclusive => none
  | .shared _ _ => none

-- Try to take shared borrow. Returns some unless already exclusive.
def ValidBorrowState.takeShared : ValidBorrowState → Option ValidBorrowState
  | .unborrowed => some (.shared 1 (Nat.one_pos))
  | .shared n _ => some (.shared (n + 1) (Nat.succ_pos n))
  | .exclusive => none  -- Cannot take shared if exclusive

-- Release exclusive borrow. No-op if not exclusive.
def ValidBorrowState.releaseExclusive : ValidBorrowState → ValidBorrowState
  | .exclusive => .unborrowed
  | other => other

-- Release shared borrow. Decrements count or returns unborrowed.
def ValidBorrowState.releaseShared : ValidBorrowState → ValidBorrowState
  | .shared 1 _ => .unborrowed
  | .shared (n + 2) _ => .shared (n + 1) (Nat.succ_pos n)
  | other => other

-- Type-safe operations always preserve validity (trivially true by construction).
theorem validState_takeExclusive_valid (vs : ValidBorrowState) :
    ∀ vs', vs.takeExclusive = some vs' → valid vs'.toState := by
  intro vs' h
  exact validState_always_valid vs'

theorem validState_takeShared_valid (vs : ValidBorrowState) :
    ∀ vs', vs.takeShared = some vs' → valid vs'.toState := by
  intro vs' h
  exact validState_always_valid vs'

theorem exclusive_ok (s : BorrowState) (hv : valid s) :
    valid (takeExclusive s) := by
  unfold takeExclusive valid at *
  split
  · -- Case: shared = 0, so we set exclusive := true
    assumption
  · -- Case: shared ≠ 0, state unchanged
    exact hv

theorem shared_ok (s : BorrowState) (hv : valid s) :
    valid (takeShared s) := by
  unfold takeShared valid at *
  split
  · -- Case: exclusive = true, state unchanged
    split at hv
    · exact hv
    · trivial
  · -- Case: exclusive = false, we add a shared borrow
    simp

theorem release_ok (s : BorrowState) (hv : valid s) :
    valid (releaseShared s) ∧ valid (releaseExclusive s) := by
  unfold releaseShared releaseExclusive valid at *
  constructor
  · -- releaseShared preserves validity
    split
    case isTrue hex =>
      -- exclusive = true means shared = 0 by validity
      split at hv
      case isTrue =>
        -- hv says shared = 0, so shared.pred = 0
        simp_all
      case isFalse h => exact absurd hex h
    case isFalse =>
      -- exclusive = false, trivially valid
      trivial
  · -- releaseExclusive: setting exclusive := false makes it trivially valid
    simp

end ManualPointerBorrow
