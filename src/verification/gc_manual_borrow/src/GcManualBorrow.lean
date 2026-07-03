namespace GcManualBorrow
-- A tiny GC + manual-pointer state: `live` holds objects managed by the GC,
--     `borrowed` tracks outstanding borrows (manual pins) that must stay live.
-- Safety invariant: every borrowed object must still be live.
-- GC may drop a live object only when it is not borrowed.
structure GcState where
  live : List Nat
  borrowed : List Nat

def safe (s : GcState) : Prop :=
  ∀ id, id ∈ s.borrowed → id ∈ s.live

def allocate (s : GcState) (id : Nat) : GcState :=
  { s with live := id :: s.live }

def borrow (s : GcState) (id : Nat) : GcState :=
  if _h : id ∈ s.live then { s with borrowed := id :: s.borrowed } else s

def release (s : GcState) (id : Nat) : GcState :=
  { s with borrowed := s.borrowed.erase id }

def collectSafe (s : GcState) (id : Nat) : GcState :=
  if _h : id ∈ s.borrowed then s else { s with live := s.live.erase id }

theorem collect_borrowed_noop (s : GcState) (id : Nat)
    (hborrowed : id ∈ s.borrowed) :
    collectSafe s id = s := by
  simp [collectSafe, hborrowed]

theorem allocate_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (allocate s id) := by
  intro x hx
  simp only [allocate]
  exact List.mem_cons_of_mem id (hs x hx)

theorem borrow_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (borrow s id) := by
  intro x hx
  simp only [borrow] at hx ⊢
  by_cases hlive : id ∈ s.live
  · simp only [hlive, ↓reduceDIte] at hx ⊢
    cases hx with
    | head => exact hlive
    | tail _ htail => exact hs x htail
  · simp only [hlive, ↓reduceDIte] at hx ⊢
    exact hs x hx

theorem release_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (release s id) := by
  intro x hx
  simp only [release] at hx
  exact hs x (List.mem_of_mem_erase hx)

theorem collect_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (collectSafe s id) := by
  intro x hx
  simp only [collectSafe] at hx ⊢
  by_cases hborrowed : id ∈ s.borrowed
  · simp only [hborrowed, ↓reduceDIte] at hx ⊢
    exact hs x hx
  · simp only [hborrowed, ↓reduceDIte] at hx ⊢
    have hlive := hs x hx
    have hne : x ≠ id := fun heq => hborrowed (heq ▸ hx)
    exact List.mem_erase_of_ne hne |>.mpr hlive

theorem release_then_collect_preserves (s : GcState) (id : Nat) (hs : safe s) :
  safe (collectSafe (release s id) id) :=
  collect_preserves (release s id) id (release_preserves s id hs)

end GcManualBorrow
