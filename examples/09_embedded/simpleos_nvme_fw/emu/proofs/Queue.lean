/-
  Queue.lean — ring-buffer (NVMe submission/completion queue) index invariants.

  The host/device queues are fixed-depth rings. The invariant is:
      head, tail ∈ [0, depth)        (valid slot indices)
      len        ∈ [0, depth]        (occupancy, depth means full)
  and advancing a pointer is `(x + 1) % depth`, which must stay a valid slot index.

  Proven (Lean core + omega only, no mathlib):
    * advance_in_range   : for depth > 0 and 0 ≤ x < depth, (x+1) % depth ∈ [0, depth).
    * enqueue_preserves  : a bounded enqueue keeps tail and len in range.
    * dequeue_preserves  : a bounded dequeue keeps head and len in range.
    * wrap_at_top        : the pointer wraps to 0 exactly at the top slot.

  Modulo is by the (variable) `depth`, so the [0, depth) range of `_ % depth`
  comes from the Lean core lemmas `Int.emod_nonneg` / `Int.emod_lt_of_pos`,
  after which `omega` discharges the surrounding linear arithmetic.
-/
set_option linter.unusedVariables false

-- Advancing a ring pointer stays a valid slot index.
theorem advance_in_range (x depth : Int)
    (hd : 0 < depth) (hlo : 0 ≤ x) (hhi : x < depth) :
    0 ≤ (x + 1) % depth ∧ (x + 1) % depth < depth :=
  ⟨Int.emod_nonneg (x + 1) (by omega), Int.emod_lt_of_pos (x + 1) hd⟩

-- Enqueue: from a valid (tail, len) with room (len < depth), the new tail and
-- the new len = len + 1 stay within their invariant ranges.
theorem enqueue_preserves (tail len depth : Int)
    (hd : 0 < depth)
    (htlo : 0 ≤ tail) (hthi : tail < depth)
    (hllo : 0 ≤ len)  (hlhi : len < depth) :
    (0 ≤ (tail + 1) % depth ∧ (tail + 1) % depth < depth) ∧
    (0 ≤ len + 1 ∧ len + 1 ≤ depth) := by
  have h1 : 0 ≤ (tail + 1) % depth := Int.emod_nonneg (tail + 1) (by omega)
  have h2 : (tail + 1) % depth < depth := Int.emod_lt_of_pos (tail + 1) hd
  omega

-- Dequeue: from a valid (head, len) with data (len > 0), the new head and
-- the new len = len - 1 stay within their invariant ranges.
theorem dequeue_preserves (head len depth : Int)
    (hd : 0 < depth)
    (hhlo : 0 ≤ head) (hhhi : head < depth)
    (hllo : 0 < len)  (hlhi : len ≤ depth) :
    (0 ≤ (head + 1) % depth ∧ (head + 1) % depth < depth) ∧
    (0 ≤ len - 1 ∧ len - 1 ≤ depth) := by
  have h1 : 0 ≤ (head + 1) % depth := Int.emod_nonneg (head + 1) (by omega)
  have h2 : (head + 1) % depth < depth := Int.emod_lt_of_pos (head + 1) hd
  omega

-- The ring wraps exactly at the top slot: advancing depth-1 returns 0.
theorem wrap_at_top (depth : Int) (hd : 0 < depth) :
    (depth - 1 + 1) % depth = 0 := by
  have h : depth - 1 + 1 = depth := by omega
  rw [h, Int.emod_self]

-- A ring is empty iff len = 0 and full iff len = depth; these are exclusive when depth > 0.
theorem empty_full_exclusive (len depth : Int)
    (hd : 0 < depth) (hllo : 0 ≤ len) (hlhi : len ≤ depth)
    (hempty : len = 0) : len ≠ depth := by
  omega
