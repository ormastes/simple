namespace ManualPointerBorrow

/-- A tiny borrow checker for manual pointers: `exclusive` tracks a unique borrow,
    `shared` counts active shared borrows. -/
structure BorrowState where
  exclusive : Bool := false
  shared : Nat := 0
deriving Repr

/-- Valid states disallow mixing an exclusive borrow with any shared borrows. -/
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
