/-
  TypeValueSemantics -- Soundness of Simple's value/reference type discipline.

  Simple enforces `struct` = value type (assignment COPIES) and
  `class` = reference type (assignment SHARES identity). This model proves the
  two observable guarantees that discipline must provide:

    * struct (value):  a copy is an independent snapshot -- mutating the copy
                       (or the source) never affects the other.
    * class (reference): an assignment aliases -- a write through one binding
                       is observable through the other.

  All theorems are proved without `sorry` (std only, no Mathlib).
-/
namespace TypeValueSemantics

-- A stored value payload.
abbrev Payload := Nat

-- A total heap: `cells` maps every id to a payload; `next` is the next fresh id.
-- All ids `< next` are considered allocated.
structure Heap where
  cells : Nat → Payload
  next  : Nat

-- Allocate a fresh cell holding `p`; returns the new id and the grown heap.
def Heap.alloc (h : Heap) (p : Payload) : Nat × Heap :=
  (h.next, { cells := fun i => if i = h.next then p else h.cells i,
             next := h.next + 1 })

def Heap.read (h : Heap) (id : Nat) : Payload := h.cells id

def Heap.write (h : Heap) (id : Nat) (p : Payload) : Heap :=
  { h with cells := fun i => if i = id then p else h.cells i }

theorem read_write_same (h : Heap) (id : Nat) (p : Payload) :
    (h.write id p).read id = p := by
  simp [Heap.write, Heap.read]

theorem read_write_other (h : Heap) (i j : Nat) (p : Payload) (hne : i ≠ j) :
    (h.write j p).read i = h.read i := by
  simp [Heap.write, Heap.read, hne]

-- Two named bindings and the id each currently denotes.
structure Vars where
  xid : Nat
  yid : Nat

/-! ### Reference (class) semantics: assignment shares the object identity. -/

def classAssign (v : Vars) : Vars := { v with yid := v.xid }

-- After a class assignment the two bindings denote the SAME object.
theorem class_shares_identity (v : Vars) :
    (classAssign v).yid = (classAssign v).xid := by
  simp [classAssign]

-- Aliasing: a write through `yid` is observable when reading through `xid`.
theorem class_alias_write_visible (h : Heap) (v : Vars) (p : Payload) :
    (h.write (classAssign v).yid p).read (classAssign v).xid = p := by
  simp [classAssign, read_write_same]

/-! ### Value (struct) semantics: assignment copies into a fresh cell. -/

-- New bindings after a struct copy: `yid` denotes a fresh object.
def structAssignVars (h : Heap) (v : Vars) : Vars := { v with yid := h.next }

-- The heap after a struct copy: a fresh cell holds a snapshot of `xid`.
def structAssignHeap (h : Heap) (v : Vars) : Heap := (h.alloc (h.read v.xid)).2

-- A struct copy produces a DISTINCT object identity (given `xid` was allocated).
theorem struct_distinct_identity (h : Heap) (v : Vars) (hx : v.xid < h.next) :
    (structAssignVars h v).yid ≠ v.xid := by
  simp [structAssignVars]
  exact fun heq => (Nat.ne_of_lt hx) heq.symm

-- The copy is a faithful snapshot: reading the fresh binding yields the
-- source's value at copy time.
theorem struct_copy_snapshot (h : Heap) (v : Vars) :
    (structAssignHeap h v).read (structAssignVars h v).yid = h.read v.xid := by
  simp [structAssignHeap, structAssignVars, Heap.alloc, Heap.read]

-- Independence: mutating the copy (`yid`) never changes the source (`xid`).
theorem struct_copy_independent (h : Heap) (v : Vars) (p : Payload)
    (hx : v.xid < h.next) :
    ((structAssignHeap h v).write (structAssignVars h v).yid p).read v.xid
      = h.read v.xid := by
  have hne : v.xid ≠ (structAssignVars h v).yid := (struct_distinct_identity h v hx).symm
  rw [read_write_other _ _ _ _ hne]
  have hlt : v.xid ≠ h.next := Nat.ne_of_lt hx
  simp [structAssignHeap, Heap.alloc, Heap.read, hlt]

-- Independence, other direction: after the copy, mutating the SOURCE (`xid`)
-- leaves the copy (`yid`) unchanged.
theorem struct_source_mut_preserves_copy (h : Heap) (v : Vars) (p : Payload)
    (hx : v.xid < h.next) :
    ((structAssignHeap h v).write v.xid p).read (structAssignVars h v).yid
      = h.read v.xid := by
  have hne : (structAssignVars h v).yid ≠ v.xid := struct_distinct_identity h v hx
  rw [read_write_other _ _ _ _ hne]
  exact struct_copy_snapshot h v

end TypeValueSemantics
