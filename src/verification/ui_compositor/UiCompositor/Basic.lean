/-
  UiCompositor.Basic — Lean 4 formal model of the Simple UI compositor core.

  Source of truth:
    src/lib/nogc_sync_mut/compositor/damage.spl    (DamageTracker, Rect2, merge_rects,
                                                    rects_overlap)
    src/lib/nogc_sync_mut/compositor/stacking.spl  (WindowStack, sort_stacking_contexts,
                                                    flatten_to_paint_order, StackingContext)

  Design
  ======
  The model captures four pure-functional cores:

  § 1  Rect2 — axis-aligned bounding box over integers (mirrors f64 in impl; we
       use Int for exact arithmetic so proofs are clean).

  § 2  Damage — rect union / overlap helpers from damage.spl.

  § 3  WindowStack — z-order management from stacking.spl WindowStack class.

  § 4  StackingContext / paint-order flatten — CSS 2.1 Appendix E ordering from
       stacking.spl sort_stacking_contexts / flatten_to_paint_order.

  IMPLEMENTATION FACTS (not violations):
  ──────────────────────────────────────
  F1. `rects_overlap` in damage.spl uses ≤ (touching edges count as overlap).
      The model mirrors this exactly.
  F2. `merge_rects` delegates to `Rect2.merge` which computes the bounding-box
      union (min of top-lefts, max of bottom-rights).
  F3. `sort_stacking_contexts` uses insertion sort — stable, O(n²).  The Lean
      model uses the same algorithm so permutation proofs are structural.
  F4. `flatten_to_paint_order` recurses on the stacking context tree.  The Lean
      model uses a non-recursive list-based approximation (one level of
      children) sufficient to prove the permutation invariant.
  F5. `WindowStack.paint_order` returns entries sorted ascending by z_order.
      The Lean model mirrors this with insertion sort.
-/

namespace UiCompositor

-- ============================================================
-- § 1  Rect2 — integer axis-aligned bounding box
-- ============================================================

/-- Axis-aligned rectangle.  Uses Int so subtraction stays in Int.
    Mirrors `Rect2` in damage.spl / compositor libs; f64 → Int for proof clarity. -/
structure Rect2 where
  x : Int
  y : Int
  w : Int   -- width  (assumed ≥ 0 in wf)
  h : Int   -- height (assumed ≥ 0 in wf)
  deriving Repr, DecidableEq

/-- Well-formed rectangle: non-negative dimensions. -/
def Rect2.wf (r : Rect2) : Prop := r.w ≥ 0 ∧ r.h ≥ 0

def Rect2.right  (r : Rect2) : Int := r.x + r.w
def Rect2.bottom (r : Rect2) : Int := r.y + r.h

/-- Bounding-box union of two rects.  Mirrors `Rect2.merge` in damage.spl.
    For two wf rects the result is also wf (proved in Theorems). -/
def Rect2.merge (a b : Rect2) : Rect2 :=
  let x1 := min a.x b.x
  let y1 := min a.y b.y
  let x2 := max a.right b.right
  let y2 := max a.bottom b.bottom
  { x := x1, y := y1, w := x2 - x1, h := y2 - y1 }

/-- Clip intersection of two rects (the overlapping sub-rectangle, if any).
    Returns `none` when the rects do not overlap.
    Not present verbatim in damage.spl but implied by any clip/scissor pass. -/
def Rect2.clip (a b : Rect2) : Option Rect2 :=
  let x1 := max a.x b.x
  let y1 := max a.y b.y
  let x2 := min a.right b.right
  let y2 := min a.bottom b.bottom
  if x2 > x1 ∧ y2 > y1 then
    some { x := x1, y := y1, w := x2 - x1, h := y2 - y1 }
  else
    none

-- ============================================================
-- § 2  Damage helpers
-- ============================================================

/-- Whether two rects overlap (including touching edges).
    Mirrors `rects_overlap` in damage.spl. -/
def rectsOverlap (a b : Rect2) : Bool :=
  !(a.right < b.x || b.right < a.x || a.bottom < b.y || b.bottom < a.y)

/-- Merge two rects into their union bounding box.
    Mirrors `merge_rects` in damage.spl. -/
def mergeRects (a b : Rect2) : Rect2 := a.merge b

/-- A damage region is a list of axis-aligned rects.
    Mirrors `DamageTracker.regions` in damage.spl. -/
abbrev DamageRegion := List Rect2

/-- Add a rect to a damage region (no deduplication — mirrors `add_damage`). -/
def DamageRegion.add (r : DamageRegion) (rect : Rect2) : DamageRegion :=
  r ++ [rect]

-- ============================================================
-- § 3  WindowStack — z-order management
-- ============================================================

/-- A single window entry in the z-order stack.
    Mirrors `WindowEntry` in stacking.spl. -/
structure WindowEntry where
  window_id : Int
  z_order   : Int
  deriving Repr, DecidableEq

/-- Z-order stack.  The `next_z` counter always exceeds every assigned z_order.
    Mirrors `WindowStack` in stacking.spl. -/
structure WindowStack where
  windows : List WindowEntry
  next_z  : Int
  deriving Repr

def WindowStack.empty : WindowStack := { windows := [], next_z := 0 }

/-- Add a window at the top of the stack (highest z_order so far). -/
def WindowStack.add (ws : WindowStack) (wid : Int) : WindowStack :=
  { windows := ws.windows ++ [{ window_id := wid, z_order := ws.next_z }]
  , next_z  := ws.next_z + 1 }

/-- Remove a window from the stack. -/
def WindowStack.remove (ws : WindowStack) (wid : Int) : WindowStack :=
  { ws with windows := ws.windows.filter (fun w => w.window_id ≠ wid) }

-- ============================================================
-- § 3b  Renormalisation — FINDING-U1 fix
-- ============================================================

/-- Renormalisation threshold: next_z values reaching this bound trigger a
    compaction.  1_000_000_000 is well below i64 max but far beyond realistic
    operation counts — mirrors RENORM_THRESHOLD in stacking.spl. -/
def renormThreshold : Int := 1000000000

/-- Rank-assignment helper.
    Given a window entry `e` and the sorted list (ascending z_order), return
    the index (0-based) of `e`'s window_id in that list. -/
def rankOf (wid : Int) : List WindowEntry → Nat
  | []      => 0
  | h :: t  => if h.window_id == wid then 0 else 1 + rankOf wid t

/-- Sort a list of WindowEntry ascending by z_order (insertion sort). -/
def insertSortedW (e : WindowEntry) : List WindowEntry → List WindowEntry
  | []      => [e]
  | h :: t  => if e.z_order ≤ h.z_order then e :: h :: t
               else h :: insertSortedW e t

def sortWindowEntries (ws : List WindowEntry) : List WindowEntry :=
  ws.foldl (fun acc w => insertSortedW w acc) []

/-- Renormalise a WindowStack: compact all z_orders to 0..n-1 preserving
    strict relative order and reset next_z = n.
    Mirrors `_renorm_windows` in stacking.spl. -/
def WindowStack.renorm (ws : WindowStack) : WindowStack :=
  let sorted := sortWindowEntries ws.windows
  let new_windows := ws.windows.map (fun w =>
    { w with z_order := Int.ofNat (rankOf w.window_id sorted) })
  { windows := new_windows, next_z := Int.ofNat ws.windows.length }

/-- Raise a window to the top (assigns next_z and increments counter).
    After raising, if next_z ≥ RENORM_THRESHOLD, renormalise. -/
def WindowStack.raiseWindow (ws : WindowStack) (wid : Int) : WindowStack :=
  let nz := ws.next_z
  let ws1 : WindowStack :=
    { windows := ws.windows.map (fun w =>
        if w.window_id == wid then { w with z_order := nz } else w)
    , next_z := nz + 1 }
  if ws1.next_z ≥ renormThreshold then
    WindowStack.renorm ws1
  else
    ws1

/-- Insertion-sort helper: insert one entry into an already-sorted list (ascending). -/
def insertSorted (e : WindowEntry) : List WindowEntry → List WindowEntry
  | []      => [e]
  | h :: t  => if e.z_order ≤ h.z_order then e :: h :: t
               else h :: insertSorted e t

/-- Return the window list sorted ascending by z_order (bottom→top paint order).
    Mirrors `WindowStack.paint_order` insertion sort in stacking.spl. -/
def WindowStack.paintOrder (ws : WindowStack) : List WindowEntry :=
  ws.windows.foldl (fun acc w => insertSorted w acc) []

-- ============================================================
-- § 4  StackingContext / paint-order flatten (simplified)
-- ============================================================

/-- A display entry (opaque id + z_index).
    Mirrors `DisplayEntry` in layer.spl / stacking.spl. -/
structure DisplayEntry where
  node_id : Int
  z_index : Int
  deriving Repr, DecidableEq

/-- A single-level stacking context (children are flat for the model).
    Mirrors `StackingContext` in stacking.spl — we omit the recursive tree
    because the permutation property holds at each level independently. -/
structure StackingCtx where
  z_index      : Int
  display_items : List DisplayEntry
  deriving Repr

/-- Insertion-sort helper for StackingCtx by z_index (ascending). -/
def insertCtxSorted (c : StackingCtx) : List StackingCtx → List StackingCtx
  | []     => [c]
  | h :: t => if c.z_index ≤ h.z_index then c :: h :: t
              else h :: insertCtxSorted c t

/-- Sort a list of stacking contexts by z_index ascending.
    Mirrors `sort_stacking_contexts` (insertion sort) in stacking.spl. -/
def sortStackingContexts (ctxs : List StackingCtx) : List StackingCtx :=
  ctxs.foldl (fun acc c => insertCtxSorted c acc) []

/-- Flatten a list of stacking contexts into paint order.
    Negative z-index first, then zero, then positive (CSS 2.1 Appendix E steps 2/6/7).
    Mirrors `flatten_to_paint_order` in stacking.spl.
    Returns all display items from all contexts in sorted order. -/
def flattenPaintOrder (ctxs : List StackingCtx) : List DisplayEntry :=
  let negative := (ctxs.filter (fun c => c.z_index < 0))
  let zero     := (ctxs.filter (fun c => c.z_index == 0))
  let positive := (ctxs.filter (fun c => c.z_index > 0))
  let neg_sorted := sortStackingContexts negative
  let pos_sorted := sortStackingContexts positive
  let collect (cs : List StackingCtx) : List DisplayEntry :=
        cs.foldl (fun acc c => acc ++ c.display_items) []
  collect neg_sorted ++ collect zero ++ collect pos_sorted

-- ============================================================
-- § 5  Permutation helpers (used by Theorems)
-- ============================================================

/-- `IsPermutation xs ys` — ys is a permutation of xs.
    We use List.Perm from Mathlib-free Lean 4 core. -/
abbrev IsPermutation (α : Type _) (xs ys : List α) : Prop := xs.Perm ys

end UiCompositor
