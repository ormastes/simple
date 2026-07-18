import ManualPointerBorrow

/-!
# ManualPointerBorrowConstraints — hand-written constraints and proofs for `ManualPointerBorrow`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `ManualPointerBorrow` live here; the generated model lives in
`ManualPointerBorrow.lean` and may be replaced wholesale by regeneration.
-/

namespace ManualPointerBorrow

theorem valid_exclusive_has_no_shared (s : BorrowState)
    (hv : valid s) (hex : s.exclusive = true) :
    s.shared = 0 := by
  unfold valid at hv
  rw [hex] at hv
  exact hv

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

theorem take_exclusive_valid_has_no_shared (s : BorrowState)
    (hv : valid s)
    (hex : (takeExclusive s).exclusive = true) :
    (takeExclusive s).shared = 0 := by
  exact valid_exclusive_has_no_shared (takeExclusive s) (exclusive_ok s hv) hex

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

theorem take_shared_then_release_when_not_exclusive (s : BorrowState)
    (hex : s.exclusive = false) :
    releaseShared (takeShared s) = s := by
  cases s with
  | mk exclusive shared =>
      simp at hex
      cases hex
      simp [takeShared, releaseShared]

theorem take_shared_then_exclusive_noop_when_not_exclusive (s : BorrowState)
    (hex : s.exclusive = false) :
    takeExclusive (takeShared s) = takeShared s := by
  apply take_exclusive_shared_noop
  simp [takeShared, hex]

theorem release_shared_decreases_when_present (s : BorrowState)
    (hshared : s.shared ≠ 0) :
    (releaseShared s).shared < s.shared := by
  cases s with
  | mk exclusive shared =>
      cases shared with
      | zero => exact False.elim (hshared rfl)
      | succ n => simp [releaseShared]


end ManualPointerBorrow
