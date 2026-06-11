/-
  UiCompositor.Theorems — Six provable theorems about the UI compositor model.

  All theorems proved without `sorry`.

  T1  merge_covers_left         — merged rect contains left input (no lost damage)
  T2  merge_covers_right        — merged rect contains right input (no lost damage)
  T3  clip_inside_left          — clip result (when Some) is inside left input rect
  T4  clip_inside_right         — clip result (when Some) is inside right input rect
  T5  insertSorted_is_perm      — insertSorted is a permutation operation (WindowEntry)
  T6  sortStackingContexts_perm — sort produces a permutation of the input list

  IMPLEMENTATION FIDELITY NOTES:
  ──────────────────────────────
  T1/T2: merged rect covers both inputs → no pixel of input escapes → no stale damage.
  T3/T4: clip result is inside both inputs → scissor cannot produce out-of-bounds pixels.
  T5/T6: sort is a permutation → paint order contains each surface exactly once.

  FINDING-U1 (scope gap, not a false theorem):
  ─────────────────────────────────────────────
  `WindowStack.raiseWindow` adjusts the z_order of the named window but does NOT
  re-normalise other windows' z_orders.  After multiple raise/lower cycles,
  z_order values can diverge widely (potentially overflowing Int in the impl's
  i64).  The Simple source in stacking.spl uses the same incrementing pattern
  without wrapping.  A theorem "raise places window strictly above all others"
  would require the precondition that next_z > all existing z_orders — which
  holds by WindowStack.wf invariant but is not checked at the callsite.
  Recommendation: add an assertion in WindowStack.add / raiseWindow that
  next_z > max(windows.map(_.z_order)).

  FINDING-U2 (flatten approximation):
  ─────────────────────────────────────
  The Lean model flattens only one level of children (StackingCtx has a flat
  display_items list, not a recursive child tree).  The real `flatten_to_paint_order`
  in stacking.spl is recursive.  The permutation property T6 holds for each
  level; the full recursive claim would need a mutual induction on the tree
  structure, which is deferred pending a richer tree model.
-/

import UiCompositor.Basic

namespace UiCompositor

-- ============================================================
-- § A  Rect containment predicate
-- ============================================================

/-- `RectContains outer inner` — every pixel of `inner` is inside `outer`. -/
def RectContains (outer inner : Rect2) : Prop :=
  outer.x ≤ inner.x ∧ inner.right ≤ outer.right ∧
  outer.y ≤ inner.y ∧ inner.bottom ≤ outer.bottom

-- ============================================================
-- § B  T1 — merge_covers_left
-- ============================================================

/-- T1: The merged rect covers the left input.
    Mirrors `merge_rects` / `Rect2.merge` in damage.spl:
    no pixel of rect `a` is outside the merged result, so no damage is lost. -/
theorem merge_covers_left (a b : Rect2) : RectContains (Rect2.merge a b) a := by
  simp only [RectContains, Rect2.merge, Rect2.right, Rect2.bottom]
  -- After simp: goals are pure linear arithmetic over Int
  -- (1) min a.x b.x ≤ a.x
  -- (2) a.x + a.w ≤ min a.x b.x + (max (a.x + a.w) (b.x + b.w) - min a.x b.x)
  -- (3) min a.y b.y ≤ a.y
  -- (4) a.y + a.h ≤ min a.y b.y + (max (a.y + a.h) (b.y + b.h) - min a.y b.y)
  -- omega handles all four
  omega

-- ============================================================
-- § C  T2 — merge_covers_right
-- ============================================================

/-- T2: The merged rect covers the right input.
    Symmetric to T1. -/
theorem merge_covers_right (a b : Rect2) : RectContains (Rect2.merge a b) b := by
  simp only [RectContains, Rect2.merge, Rect2.right, Rect2.bottom]
  omega

-- ============================================================
-- § D  T3 / T4 — clip soundness
-- ============================================================

/-- T3: When clip returns Some r, r is geometrically inside the left rect `a`.
    Soundness: the clip region does not extend beyond the left scissor boundary. -/
theorem clip_inside_left (a b : Rect2) (r : Rect2)
    (h : Rect2.clip a b = some r) : RectContains a r := by
  simp only [Rect2.clip] at h
  -- h is `if (min a.right b.right > max a.x b.x ∧ ...) then some {...} else none = some r`
  by_cases hcond : min a.right b.right > max a.x b.x ∧ min a.bottom b.bottom > max a.y b.y
  · rw [if_pos hcond] at h
    have heq := Option.some.inj h
    subst heq
    simp only [RectContains, Rect2.right, Rect2.bottom]
    omega
  · rw [if_neg hcond] at h
    exact absurd h (by simp)

/-- T4: When clip returns Some r, r is geometrically inside the right rect `b`.
    Soundness: the clip region does not extend beyond the right scissor boundary. -/
theorem clip_inside_right (a b : Rect2) (r : Rect2)
    (h : Rect2.clip a b = some r) : RectContains b r := by
  simp only [Rect2.clip] at h
  by_cases hcond : min a.right b.right > max a.x b.x ∧ min a.bottom b.bottom > max a.y b.y
  · rw [if_pos hcond] at h
    have heq := Option.some.inj h
    subst heq
    simp only [RectContains, Rect2.right, Rect2.bottom]
    omega
  · rw [if_neg hcond] at h
    exact absurd h (by simp)

-- ============================================================
-- § E  T5 — insertSorted is a permutation (WindowEntry)
-- ============================================================

/-- Helper: `insertSorted e xs` is a permutation of `e :: xs`. -/
private theorem insertSorted_perm_aux (e : WindowEntry) :
    ∀ (xs : List WindowEntry), (insertSorted e xs).Perm (e :: xs) := by
  intro xs
  induction xs with
  | nil => simp [insertSorted]
  | cons hd tl ih =>
    simp only [insertSorted]
    by_cases hle : e.z_order ≤ hd.z_order
    · rw [if_pos hle]
    · rw [if_neg hle]
      -- goal: (hd :: insertSorted e tl).Perm (e :: hd :: tl)
      -- List.Perm.swap a b l : (a :: b :: l).Perm (b :: a :: l)
      -- so swap hd e tl : (hd :: e :: tl).Perm (e :: hd :: tl)  ← that's what we want
      exact (List.Perm.cons hd ih).trans (List.Perm.swap e hd tl)

/-- T5: insertSorted (WindowEntry) is a permutation operation.
    Applied iteratively in WindowStack.paintOrder, this guarantees paint_order
    contains exactly the same windows as the original stack — no window is
    dropped or duplicated during z-sort. -/
theorem insertSorted_is_perm (e : WindowEntry) (xs : List WindowEntry) :
    (insertSorted e xs).Perm (e :: xs) :=
  insertSorted_perm_aux e xs

-- ============================================================
-- § F  T6 — sortStackingContexts is a permutation
-- ============================================================

/-- Helper: `insertCtxSorted c xs` is a permutation of `c :: xs`. -/
private theorem insertCtxSorted_perm_aux (c : StackingCtx) :
    ∀ (xs : List StackingCtx), (insertCtxSorted c xs).Perm (c :: xs) := by
  intro xs
  induction xs with
  | nil => simp [insertCtxSorted]
  | cons hd tl ih =>
    simp only [insertCtxSorted]
    by_cases hle : c.z_index ≤ hd.z_index
    · rw [if_pos hle]
    · rw [if_neg hle]
      exact (List.Perm.cons hd ih).trans (List.Perm.swap c hd tl)

/-- Folding insertCtxSorted over xs with accumulator acc yields a
    permutation of acc ++ xs. -/
private theorem foldl_insertCtxSorted_perm :
    ∀ (xs acc : List StackingCtx),
      (xs.foldl (fun a c => insertCtxSorted c a) acc).Perm (acc ++ xs) := by
  intro xs
  induction xs with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have hstep : (insertCtxSorted hd acc).Perm (hd :: acc) :=
      insertCtxSorted_perm_aux hd acc
    have hrec := ih (insertCtxSorted hd acc)
    -- hrec : foldl tl (insertCtxSorted hd acc) .Perm (insertCtxSorted hd acc) ++ tl
    -- hstep: (insertCtxSorted hd acc) .Perm (hd :: acc)
    -- want: result .Perm acc ++ (hd :: tl)
    have hcat : ((insertCtxSorted hd acc) ++ tl).Perm ((hd :: acc) ++ tl) :=
      List.Perm.append_right tl hstep
    -- want: result .Perm (acc ++ hd :: tl)
    -- Chain: result .Perm ((insertCtxSorted hd acc) ++ tl)  [hrec]
    --             .Perm ((hd :: acc) ++ tl)                 [hcat, append_right]
    --             = hd :: (acc ++ tl)
    --             .Perm acc ++ (hd :: tl)                   [hcomm below]
    have hcomm : (hd :: acc ++ tl).Perm (acc ++ hd :: tl) := by
      -- hd :: acc ++ tl = (hd :: acc) ++ tl
      -- acc ++ hd :: tl = acc ++ ([hd] ++ tl) = (acc ++ [hd]) ++ tl
      -- (hd :: acc).Perm (acc ++ [hd]) by perm_append_comm
      have h1 : (hd :: acc).Perm (acc ++ [hd]) :=
        List.perm_append_comm (l₁ := [hd]) (l₂ := acc)
      -- (hd :: acc) ++ tl .Perm (acc ++ [hd]) ++ tl
      have h2 : ((hd :: acc) ++ tl).Perm ((acc ++ [hd]) ++ tl) :=
        List.Perm.append_right tl h1
      -- rewrite (acc ++ [hd]) ++ tl  as  acc ++ ([hd] ++ tl) = acc ++ (hd :: tl)
      rw [List.append_assoc, List.singleton_append] at h2
      exact h2
    exact hrec.trans (hcat.trans hcomm)

/-- T6: `sortStackingContexts` produces a permutation of the input list.
    Mirrors `sort_stacking_contexts` in stacking.spl.
    Consequence: `flattenPaintOrder` contains all display items from all stacking
    contexts exactly once — no surface is silently dropped or duplicated. -/
theorem sortStackingContexts_perm (ctxs : List StackingCtx) :
    (sortStackingContexts ctxs).Perm ctxs := by
  simp only [sortStackingContexts]
  have h := foldl_insertCtxSorted_perm ctxs []
  simp at h
  exact h

end UiCompositor
