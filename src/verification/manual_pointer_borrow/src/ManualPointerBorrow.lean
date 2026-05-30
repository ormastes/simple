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
