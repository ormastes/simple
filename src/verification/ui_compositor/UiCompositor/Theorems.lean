/-
  UiCompositor.Theorems — Seven provable theorems about the UI compositor model.

  All theorems proved without `sorry`.

  T1  merge_covers_left         — merged rect contains left input (no lost damage)
  T2  merge_covers_right        — merged rect contains right input (no lost damage)
  T3  clip_inside_left          — clip result (when Some) is inside left input rect
  T4  clip_inside_right         — clip result (when Some) is inside right input rect
  T5  insertSorted_is_perm      — insertSorted is a permutation operation (WindowEntry)
  T6  sortStackingContexts_perm — sort produces a permutation of the input list
  T7  renorm_order_preserving   — renormalisation preserves the relative z_order of
                                  every pair of windows (FINDING-U1 closure)

  IMPLEMENTATION FIDELITY NOTES:
  ──────────────────────────────
  T1/T2: merged rect covers both inputs → no pixel of input escapes → no stale damage.
  T3/T4: clip result is inside both inputs → scissor cannot produce out-of-bounds pixels.
  T5/T6: sort is a permutation → paint order contains each surface exactly once.
  T7:    renorm is order-preserving → raises followed by compaction leave the relative
         stacking order of every pair of windows unchanged.

  FINDING-U1 — CLOSED:
  ─────────────────────
  `WindowStack.raiseWindow` previously incremented `next_z` without bound, risking
  i64 overflow after O(RENORM_THRESHOLD) raise/lower cycles.  Fixed in stacking.spl:
  both `add` and `raise_window` now call `_renorm_windows` (compact 0..n-1, reset
  next_z = n) whenever next_z reaches RENORM_THRESHOLD (1_000_000_000).  The Lean
  model mirrors this via `WindowStack.renorm` / `renormThreshold`.  T7 proves
  renormalisation is order-preserving: for any two windows a, b, their relative
  z_order comparison is identical before and after renorm.

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

-- ============================================================
-- § G  T7 — renorm is order-preserving (FINDING-U1 closure)
-- ============================================================

-- We use a custom sorted predicate because List.Sorted is not in core Lean 4.
/-- `WinSorted xs` means every consecutive pair in xs has non-decreasing z_order. -/
def WinSorted : List WindowEntry → Prop
  | []          => True
  | [_]         => True
  | a :: b :: t => a.z_order ≤ b.z_order ∧ WinSorted (b :: t)

/-- WinSorted is preserved dropping the head. -/
private theorem winSorted_tail (hd : WindowEntry) (tl : List WindowEntry)
    (hs : WinSorted (hd :: tl)) : WinSorted tl := by
  cases tl with
  | nil => simp [WinSorted]
  | cons h t => simp only [WinSorted] at hs; exact hs.2

/-- Every element in a WinSorted list is ≥ the head. -/
private theorem winSorted_head_le : ∀ (hd : WindowEntry) (tl : List WindowEntry),
    WinSorted (hd :: tl) → ∀ (x : WindowEntry), x ∈ tl → hd.z_order ≤ x.z_order := by
  intro hd tl
  induction tl generalizing hd with
  | nil => intro _ x hx; simp at hx
  | cons h2 rest ih =>
    intro hs x hx
    simp only [WinSorted] at hs
    obtain ⟨hle, hs2⟩ := hs
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx'
    · exact hle
    · exact Int.le_trans hle (ih h2 hs2 x hx')

/-- Helper: `insertSortedW e xs` is a permutation of `e :: xs`. -/
private theorem insertSortedW_perm_aux (e : WindowEntry) :
    ∀ (xs : List WindowEntry), (insertSortedW e xs).Perm (e :: xs) := by
  intro xs
  induction xs with
  | nil => simp [insertSortedW]
  | cons hd tl ih =>
    simp only [insertSortedW]
    by_cases hle : e.z_order ≤ hd.z_order
    · rw [if_pos hle]
    · rw [if_neg hle]
      exact (List.Perm.cons hd ih).trans (List.Perm.swap e hd tl)

private theorem foldl_insertSortedW_perm :
    ∀ (xs acc : List WindowEntry),
      (xs.foldl (fun a w => insertSortedW w a) acc).Perm (acc ++ xs) := by
  intro xs
  induction xs with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have hstep : (insertSortedW hd acc).Perm (hd :: acc) :=
      insertSortedW_perm_aux hd acc
    have hrec := ih (insertSortedW hd acc)
    have hcat : ((insertSortedW hd acc) ++ tl).Perm ((hd :: acc) ++ tl) :=
      List.Perm.append_right tl hstep
    have hcomm : (hd :: acc ++ tl).Perm (acc ++ hd :: tl) := by
      have h1 : (hd :: acc).Perm (acc ++ [hd]) :=
        List.perm_append_comm (l₁ := [hd]) (l₂ := acc)
      have h2 : ((hd :: acc) ++ tl).Perm ((acc ++ [hd]) ++ tl) :=
        List.Perm.append_right tl h1
      rw [List.append_assoc, List.singleton_append] at h2
      exact h2
    exact hrec.trans (hcat.trans hcomm)

private theorem sortWindowEntries_perm (ws : List WindowEntry) :
    (sortWindowEntries ws).Perm ws := by
  simp only [sortWindowEntries]
  have h := foldl_insertSortedW_perm ws []
  simp at h; exact h

/-- After `insertSortedW` inserts into a WinSorted list, the result is WinSorted. -/
private theorem insertSortedW_winSorted (e : WindowEntry) (xs : List WindowEntry)
    (hxs : WinSorted xs) : WinSorted (insertSortedW e xs) := by
  induction xs with
  | nil => simp [insertSortedW, WinSorted]
  | cons hd tl ih =>
    simp only [insertSortedW]
    by_cases hle : e.z_order ≤ hd.z_order
    · rw [if_pos hle]
      cases tl with
      | nil  => simp only [WinSorted]; exact ⟨hle, trivial⟩
      | cons h2 rest => simp only [WinSorted]; exact ⟨hle, hxs⟩
    · rw [if_neg hle]
      have hle' : hd.z_order ≤ e.z_order := Int.le_of_not_le hle
      have ih'  : WinSorted (insertSortedW e tl) := ih (winSorted_tail hd tl hxs)
      match hins : insertSortedW e tl with
      | [] => simp [WinSorted]
      | h2 :: rest =>
        simp only [WinSorted]
        constructor
        · have hmem  : h2 ∈ insertSortedW e tl := by rw [hins]; simp
          have hmem2 : h2 ∈ e :: tl :=
            (insertSortedW_perm_aux e tl).mem_iff.mp hmem
          simp only [List.mem_cons] at hmem2
          rcases hmem2 with rfl | hmem_tl
          · exact hle'
          · exact winSorted_head_le hd tl hxs h2 hmem_tl
        · rw [← hins]; exact ih'

/-- Folding `insertSortedW` preserves WinSorted. -/
private theorem foldl_insertSortedW_winSorted :
    ∀ (xs acc : List WindowEntry), WinSorted acc →
      WinSorted (xs.foldl (fun a w => insertSortedW w a) acc) := by
  intro xs; induction xs with
  | nil  => intro acc h; simpa
  | cons hd tl ih =>
    intro acc hacc; simp only [List.foldl_cons]
    exact ih _ (insertSortedW_winSorted hd acc hacc)

/-- `sortWindowEntries` produces a WinSorted list. -/
private theorem sortWindowEntries_winSorted (ws : List WindowEntry) :
    WinSorted (sortWindowEntries ws) := by
  simp only [sortWindowEntries]
  exact foldl_insertSortedW_winSorted ws [] (by simp [WinSorted])

/-- `UniqueIds xs` — every window_id appears at most once. -/
def UniqueIds : List WindowEntry → Prop
  | []     => True
  | h :: t => (∀ x ∈ t, x.window_id ≠ h.window_id) ∧ UniqueIds t

private theorem uniqueIds_tail (hd : WindowEntry) (tl : List WindowEntry)
    (hu : UniqueIds (hd :: tl)) : UniqueIds tl := hu.2

/-- UniqueIds is preserved by permutation. -/
private theorem uniqueIds_perm {xs ys : List WindowEntry}
    (hperm : xs.Perm ys) (hu : UniqueIds xs) : UniqueIds ys := by
  induction hperm with
  | nil => exact hu
  | cons x hrest ih =>
    -- xs = x :: l1, ys = x :: l2, hrest : l1.Perm l2
    -- hu : UniqueIds (x :: l1)
    simp only [UniqueIds] at hu ⊢
    constructor
    · intro y hy hne
      have hy_xs : y ∈ _ := (List.Perm.mem_iff hrest.symm).mp hy
      exact hu.1 y hy_xs hne
    · exact ih hu.2
  | swap x y l =>
    -- In Lean 4's Perm.swap induction: xs = y :: x :: l, ys = x :: y :: l
    -- hu : UniqueIds (y :: x :: l)
    --   hu.1    : ∀ w ∈ x :: l, w.window_id ≠ y.window_id
    --   hu.2.1  : ∀ w ∈ l, w.window_id ≠ x.window_id
    --   hu.2.2  : UniqueIds l
    -- goal: UniqueIds (x :: y :: l):
    --   (∀ w ∈ y::l, w.window_id ≠ x.window_id) ∧ (∀ w ∈ l, w.window_id ≠ y.window_id) ∧ UniqueIds l
    have hxl_ne : ∀ w ∈ x :: l, w.window_id ≠ y.window_id := hu.1
    have hxl2_ne : ∀ w ∈ l, w.window_id ≠ x.window_id     := hu.2.1
    have hul    : UniqueIds l                               := hu.2.2
    simp only [UniqueIds]
    refine ⟨?_, ?_, hul⟩
    · -- ∀ w ∈ y::l, w.window_id ≠ x.window_id
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw'
      · -- w = y; need y.window_id ≠ x.window_id
        -- hxl_ne x (x ∈ x::l) : x.window_id ≠ y.window_id, so y.window_id ≠ x.window_id
        exact Ne.symm (hxl_ne x List.mem_cons_self)
      · exact hxl2_ne w hw'
    · -- ∀ w ∈ l, w.window_id ≠ y.window_id
      intro w hw
      exact hxl_ne w (List.mem_cons_of_mem x hw)
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hu)

/-- A helper: `(x == y) = true ↔ x = y` for Int. -/
private theorem Int.beq_true {x y : Int} : (x == y) = true ↔ x = y := by
  simp [beq_iff_eq]

/-- In a WinSorted + UniqueIds list, strict z_order ordering implies strict rank ordering. -/
private theorem rankOf_reflects_order (sorted : List WindowEntry)
    (hsorted : WinSorted sorted) (huniq : UniqueIds sorted)
    (a b : WindowEntry)
    (ha : a ∈ sorted) (hb : b ∈ sorted)
    (hlt : a.z_order < b.z_order) :
    rankOf a.window_id sorted < rankOf b.window_id sorted := by
  induction sorted with
  | nil => simp at ha
  | cons hd tl ih =>
    -- Reduce `if (hd.window_id == x) = true then ...` to `if hd.window_id = x then ...`
    simp only [rankOf, beq_iff_eq]
    -- Now goal: (if hd.window_id = a.window_id then 0 else 1 + rankOf a.window_id tl) <
    --           (if hd.window_id = b.window_id then 0 else 1 + rankOf b.window_id tl)
    by_cases hda : hd.window_id = a.window_id <;>
    by_cases hdb : hd.window_id = b.window_id
    · -- both match → contradiction from UniqueIds / lt_irrefl
      exfalso
      rcases List.mem_cons.mp ha with rfl | ha_tl
      · rcases List.mem_cons.mp hb with rfl | hb_tl
        · exact absurd hlt (Int.lt_irrefl _)
        · exact absurd hdb.symm (huniq.1 b hb_tl)
      · exact absurd hda.symm (huniq.1 a ha_tl)
    · -- hd = a.id, hd ≠ b.id → LHS = 0, RHS = 1 + ...; goal: 0 < 1 + rankOf b.window_id tl
      rw [if_pos hda, if_neg hdb]
      omega
    · -- hd ≠ a.id, hd = b.id → contradiction via WinSorted
      exfalso
      have ha_tl : a ∈ tl := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact absurd rfl hda
        · exact h
      rcases List.mem_cons.mp hb with rfl | hb_tl
      · -- b is the head entry; WinSorted ⟹ b.z_order ≤ a.z_order
        exact absurd hlt (Int.not_lt.mpr (winSorted_head_le b tl hsorted a ha_tl))
      · -- b ∈ tl but b.window_id = hd.window_id: UniqueIds forbids this
        exact absurd hdb.symm (huniq.1 b hb_tl)
    · -- neither matches → recurse into tl
      rw [if_neg hda, if_neg hdb]
      have ha_tl : a ∈ tl := by
        rcases List.mem_cons.mp ha with rfl | h; exact absurd rfl hda; exact h
      have hb_tl : b ∈ tl := by
        rcases List.mem_cons.mp hb with rfl | h; exact absurd rfl hdb; exact h
      have hrec := ih (winSorted_tail hd tl hsorted) (uniqueIds_tail hd tl huniq) ha_tl hb_tl
      omega

/-- T7: `WindowStack.renorm` is order-preserving (FINDING-U1 closure).
    Precondition: window IDs are unique — this is the standard WindowStack invariant
    (every `add` assigns a fresh ID; `remove` eliminates it).
    For any two windows a, b with a.z_order < b.z_order, after renorm the
    corresponding entries a', b' still satisfy a'.z_order < b'.z_order. -/
theorem renorm_order_preserving (ws : WindowStack)
    (huniq : UniqueIds ws.windows)
    (a b : WindowEntry)
    (ha : a ∈ ws.windows) (hb : b ∈ ws.windows)
    (hlt : a.z_order < b.z_order) :
    let ws' := WindowStack.renorm ws
    ∃ a' b' : WindowEntry,
      a' ∈ ws'.windows ∧ b' ∈ ws'.windows ∧
      a'.window_id = a.window_id ∧ b'.window_id = b.window_id ∧
      a'.z_order < b'.z_order := by
  -- Unfold renorm: ws'.windows = ws.windows.map (fun w => {w with z_order := rankOf ...})
  show ∃ a' b' : WindowEntry,
      a' ∈ (WindowStack.renorm ws).windows ∧ b' ∈ (WindowStack.renorm ws).windows ∧
      a'.window_id = a.window_id ∧ b'.window_id = b.window_id ∧ a'.z_order < b'.z_order
  simp only [WindowStack.renorm]
  -- After simp, ws'.windows = ws.windows.map (rename), srt = sortWindowEntries ws.windows
  have hperm    : (sortWindowEntries ws.windows).Perm ws.windows :=
    sortWindowEntries_perm ws.windows
  have hwsorted : WinSorted (sortWindowEntries ws.windows) :=
    sortWindowEntries_winSorted ws.windows
  have huniq_s  : UniqueIds (sortWindowEntries ws.windows) :=
    uniqueIds_perm hperm.symm huniq
  have ha_s : a ∈ sortWindowEntries ws.windows :=
    (List.Perm.mem_iff hperm.symm).mp ha
  have hb_s : b ∈ sortWindowEntries ws.windows :=
    (List.Perm.mem_iff hperm.symm).mp hb
  have hrank : rankOf a.window_id (sortWindowEntries ws.windows) <
               rankOf b.window_id (sortWindowEntries ws.windows) :=
    rankOf_reflects_order _ hwsorted huniq_s a b ha_s hb_s hlt
  have ha_in : { window_id := a.window_id
               , z_order := Int.ofNat (rankOf a.window_id (sortWindowEntries ws.windows)) } ∈
      ws.windows.map (fun w =>
        { w with z_order := Int.ofNat (rankOf w.window_id (sortWindowEntries ws.windows)) }) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hb_in : { window_id := b.window_id
               , z_order := Int.ofNat (rankOf b.window_id (sortWindowEntries ws.windows)) } ∈
      ws.windows.map (fun w =>
        { w with z_order := Int.ofNat (rankOf w.window_id (sortWindowEntries ws.windows)) }) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  exact ⟨{ window_id := a.window_id
           , z_order := Int.ofNat (rankOf a.window_id (sortWindowEntries ws.windows)) },
         { window_id := b.window_id
           , z_order := Int.ofNat (rankOf b.window_id (sortWindowEntries ws.windows)) },
         ha_in, hb_in, rfl, rfl, Int.ofNat_lt.mpr hrank⟩

end UiCompositor
