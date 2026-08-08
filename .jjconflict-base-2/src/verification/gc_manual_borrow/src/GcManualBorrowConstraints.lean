import GcManualBorrow

/-!
# GcManualBorrowConstraints — hand-written constraints and proofs for `GcManualBorrow`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `GcManualBorrow` live here; the generated model lives in
`GcManualBorrow.lean` and may be replaced wholesale by regeneration.
-/

namespace GcManualBorrow

theorem collect_borrowed_noop (s : GcState) (id : Nat)
    (hborrowed : id ∈ s.borrowed) :
    collectSafe s id = s := by
  simp [collectSafe, hborrowed]

theorem collect_unborrowed_decrements_live_count (s : GcState) (id : Nat)
    (hborrowed : id ∉ s.borrowed) :
  List.count id (collectSafe s id).live = List.count id s.live - 1 := by
  simp [collectSafe, hborrowed]

theorem collect_preserves_borrowed_list (s : GcState) (id : Nat) :
  (collectSafe s id).borrowed = s.borrowed := by
  by_cases hborrowed : id ∈ s.borrowed
  · simp [collectSafe, hborrowed]
  · simp [collectSafe, hborrowed]

theorem allocate_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (allocate s id) := by
  intro x hx
  simp only [allocate]
  exact List.mem_cons_of_mem id (hs x hx)

theorem allocate_makes_live (s : GcState) (id : Nat) :
  id ∈ (allocate s id).live := by
  simp [allocate]

theorem allocate_unborrowed_then_collect_decrements_live_count (s : GcState) (id : Nat)
    (hborrowed : id ∉ s.borrowed) :
  List.count id (collectSafe (allocate s id) id).live =
    List.count id (allocate s id).live - 1 := by
  exact collect_unborrowed_decrements_live_count (allocate s id) id hborrowed

theorem allocate_then_borrow_records_pin (s : GcState) (id : Nat) :
  id ∈ (borrow (allocate s id) id).borrowed := by
  simp [borrow, allocate]

theorem borrow_live_records_pin (s : GcState) (id : Nat)
    (hlive : id ∈ s.live) :
  id ∈ (borrow s id).borrowed := by
  simp [borrow, hlive]

theorem borrow_nonlive_noop (s : GcState) (id : Nat)
    (hlive : id ∉ s.live) :
  borrow s id = s := by
  simp [borrow, hlive]

theorem borrow_live_then_collect_noop (s : GcState) (id : Nat)
    (hlive : id ∈ s.live) :
  collectSafe (borrow s id) id = borrow s id := by
  exact collect_borrowed_noop (borrow s id) id (borrow_live_records_pin s id hlive)

theorem release_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (release s id) := by
  intro x hx
  simp only [release] at hx
  exact hs x (List.mem_of_mem_erase hx)

theorem release_decrements_borrow_count (s : GcState) (id : Nat) :
  List.count id (release s id).borrowed = List.count id s.borrowed - 1 := by
  simp [release]

theorem release_zero_count_stays_zero (s : GcState) (id : Nat)
    (hcount : List.count id s.borrowed = 0) :
  List.count id (release s id).borrowed = 0 := by
  simp [release, hcount]

theorem collect_keeps_borrowed_live (s : GcState) (id borrowedId : Nat)
    (hs : safe s)
    (hborrowed : borrowedId ∈ s.borrowed) :
  borrowedId ∈ (collectSafe s id).live := by
  have hstillBorrowed : borrowedId ∈ (collectSafe s id).borrowed := by
    rw [collect_preserves_borrowed_list s id]
    exact hborrowed
  exact collect_preserves s id hs borrowedId hstillBorrowed

theorem release_then_collect_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (collectSafe (release s id) id) :=
  collect_preserves (release s id) id (release_preserves s id hs)


end GcManualBorrow
