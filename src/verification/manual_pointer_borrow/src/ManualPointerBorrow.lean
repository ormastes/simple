namespace ManualPointerBorrow
-- A tiny borrow checker for manual pointers: `exclusive` tracks a unique borrow,
--     `shared` counts active shared borrows.
-- Type-safe borrow state where invalid states are unrepresentable.
--     Shared borrows are encoded as `n + 1`, so the shared case is always positive.
-- Convert ValidBorrowState to BorrowState. Always produces a valid state.
inductive ValidBorrowState
  | unborrowed
  | exclusive
  | shared : Nat → ValidBorrowState
deriving Repr

structure BorrowState where
  exclusive : Bool
  shared : Nat

def ValidBorrowState.toState : ValidBorrowState → BorrowState
  | .unborrowed => { exclusive := false, shared := 0 }
  | .exclusive => { exclusive := true, shared := 0 }
  | .shared count => { exclusive := false, shared := count + 1 }

-- Convert BorrowState to ValidBorrowState if valid.
def BorrowState.toValid (s : BorrowState) : Option ValidBorrowState :=
  match s.exclusive, s.shared with
  | false, 0 => some .unborrowed
  | true, 0 => some .exclusive
  | false, n + 1 => some (.shared n)
  | true, _ + 1 => none

def valid (s : BorrowState) : Prop :=
  if s.exclusive then s.shared = 0 else True

theorem valid_exclusive_has_no_shared (s : BorrowState)
    (hv : valid s) (hex : s.exclusive = true) :
    s.shared = 0 := by
  unfold valid at hv
  rw [hex] at hv
  exact hv

def takeExclusive (s : BorrowState) : BorrowState :=
  if s.shared = 0 then { s with exclusive := true } else s

def takeShared (s : BorrowState) : BorrowState :=
  if s.exclusive then s else { s with shared := s.shared + 1 }

def releaseShared (s : BorrowState) : BorrowState :=
  { s with shared := s.shared.pred }

def releaseExclusive (s : BorrowState) : BorrowState :=
  { s with exclusive := false }

theorem validState_always_valid (vs : ValidBorrowState) :
  valid vs.toState := by
  cases vs with
  | unborrowed => simp [ValidBorrowState.toState, valid]
  | exclusive => simp [ValidBorrowState.toState, valid]
  | shared count => simp [ValidBorrowState.toState, valid]

theorem toValid_toState (vs : ValidBorrowState) :
  vs.toState.toValid = some vs := by
  cases vs with
  | unborrowed => simp [ValidBorrowState.toState, BorrowState.toValid]
  | exclusive => simp [ValidBorrowState.toState, BorrowState.toValid]
  | shared count => simp [ValidBorrowState.toState, BorrowState.toValid]

theorem exclusive_ok (s : BorrowState) (hv : valid s) :
  valid (takeExclusive s) := by
  unfold takeExclusive valid at *
  split
  · assumption
  · exact hv

theorem shared_ok (s : BorrowState) (hv : valid s) :
  valid (takeShared s) := by
  unfold takeShared valid at *
  split
  · split at hv
    · exact hv
    · trivial
  · simp

theorem take_shared_exclusive_noop (s : BorrowState)
    (hex : s.exclusive = true) :
    takeShared s = s := by
  simp [takeShared, hex]

theorem take_shared_increments_when_not_exclusive (s : BorrowState)
    (hex : s.exclusive = false) :
    (takeShared s).shared = s.shared + 1 := by
  simp [takeShared, hex]

theorem take_shared_preserves_exclusive (s : BorrowState) :
    (takeShared s).exclusive = s.exclusive := by
  cases s with
  | mk exclusive shared =>
      cases exclusive <;> simp [takeShared]

theorem take_exclusive_shared_noop (s : BorrowState)
    (hshared : s.shared ≠ 0) :
    takeExclusive s = s := by
  simp [takeExclusive, hshared]

theorem take_exclusive_sets_flag_when_no_shared (s : BorrowState)
    (hshared : s.shared = 0) :
    (takeExclusive s).exclusive = true := by
  simp [takeExclusive, hshared]

theorem take_exclusive_no_shared_eq_exclusive (s : BorrowState)
    (hshared : s.shared = 0) :
    takeExclusive s = { exclusive := true, shared := 0 } := by
  cases s with
  | mk exclusive shared =>
      simp at hshared
      cases hshared
      simp [takeExclusive]

theorem take_exclusive_preserves_shared (s : BorrowState) :
    (takeExclusive s).shared = s.shared := by
  by_cases hshared : s.shared = 0
  · simp [takeExclusive, hshared]
  · simp [takeExclusive, hshared]

theorem release_exclusive_clears (s : BorrowState) :
    (releaseExclusive s).exclusive = false := by
  simp [releaseExclusive]

theorem release_exclusive_preserves_shared (s : BorrowState) :
    (releaseExclusive s).shared = s.shared := by
  simp [releaseExclusive]

theorem release_exclusive_false_noop (s : BorrowState)
    (hex : s.exclusive = false) :
    releaseExclusive s = s := by
  cases s with
  | mk exclusive shared =>
      simp at hex
      simp [releaseExclusive, hex]

theorem take_exclusive_then_release_no_shared (s : BorrowState)
    (hshared : s.shared = 0) :
    releaseExclusive (takeExclusive s) = { exclusive := false, shared := 0 } := by
  rw [take_exclusive_no_shared_eq_exclusive s hshared]
  simp [releaseExclusive]

theorem release_shared_preserves_exclusive (s : BorrowState) :
    (releaseShared s).exclusive = s.exclusive := by
  simp [releaseShared]

theorem release_shared_zero_noop (s : BorrowState)
    (hshared : s.shared = 0) :
    (releaseShared s).shared = 0 := by
  simp [releaseShared, hshared]

theorem release_shared_decreases_when_present (s : BorrowState)
    (hshared : s.shared ≠ 0) :
    (releaseShared s).shared < s.shared := by
  cases s with
  | mk exclusive shared =>
      cases shared with
      | zero => exact False.elim (hshared rfl)
      | succ n => simp [releaseShared]

theorem release_ok (s : BorrowState) (hv : valid s) :
  valid (releaseShared s) ∧ valid (releaseExclusive s) := by
  unfold releaseShared releaseExclusive valid at *
  constructor
  · split
    case isTrue hex =>
      split at hv
      case isTrue => simp_all
      case isFalse h => exact absurd hex h
    case isFalse => trivial
  · simp

end ManualPointerBorrow
