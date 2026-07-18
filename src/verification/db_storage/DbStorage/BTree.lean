-- DbStorage.BTree -- Formal model of pmap_btree.spl
--
-- Source fidelity (pmap_btree.spl):
--   min_keys  = fanout / 2          (integer division; NOT CLRS t-1)
--   max_keys  = 2 * fanout - 1
--   Leaf split: median index mid = fanout - 1.
--     Left half  keeps keys[0..mid-1].
--     Right half keeps keys[mid+1..].
--     Median key is promoted to parent only (not kept in either half).
--   Internal split: children[0..mid] stay left, [mid+1..] go right.
--   Delete: top-down proactive fix-up (borrow-left, borrow-right, merge-right).
--   Root shrink: root with 0 keys and 1 child -> replace root with child.
--
-- Keys and values are Nat.

namespace DbStorage.BTree

inductive BNode where
  | leaf     : List Nat -> List Nat -> BNode
  | internal : List Nat -> List BNode -> BNode
  deriving Repr

def minKeys (t : Nat) : Nat := t / 2
def maxKeys (t : Nat) : Nat := 2 * t - 1

-- Key ordering (strict, in-order)
def keysOrdered : List Nat -> Prop
  | []              => True
  | [_]             => True
  | k1 :: k2 :: rest => k1 < k2 ∧ keysOrdered (k2 :: rest)

-- Height: leaves = 0, internal = height of first child + 1
def nodeHeight : BNode -> Nat
  | BNode.leaf _ _      => 0
  | BNode.internal _ cs =>
      match cs with
      | []     => 0
      | c :: _ => nodeHeight c + 1

-- Uniform-height predicate for a list of nodes
def uniformHeight : List BNode -> Prop
  | []           => True
  | [_]          => True
  | c1 :: c2 :: rest =>
      nodeHeight c1 = nodeHeight c2 ∧ uniformHeight (c2 :: rest)

-- All elements of a uniform-height list have the same height as each other.
-- We state this as: any two members have equal height.
theorem uniformHeight_pairwise (cs : List BNode) (h : uniformHeight cs) :
    ∀ c d, c ∈ cs -> d ∈ cs -> nodeHeight c = nodeHeight d := by
  induction cs with
  | nil => intro c _ hc; simp at hc
  | cons x xs ih =>
    intro c d hc hd
    cases hc with
    | head =>
      cases hd with
      | head => rfl
      | tail _ hdxs =>
        cases xs with
        | nil => exact nomatch hdxs
        | cons y ys =>
          simp [uniformHeight] at h
          have hyd : nodeHeight y = nodeHeight d := ih h.2 y d (List.Mem.head ys) hdxs
          rw [← hyd]
          exact h.1
    | tail _ hcxs =>
      cases hd with
      | head =>
        cases xs with
        | nil => exact nomatch hcxs
        | cons y ys =>
          simp [uniformHeight] at h
          have hcy : nodeHeight c = nodeHeight y := ih h.2 c y hcxs (List.Mem.head ys)
          rw [hcy]
          exact h.1.symm
      | tail _ hdxs =>
        cases xs with
        | nil => exact nomatch hcxs
        | cons y ys =>
          simp [uniformHeight] at h
          exact ih h.2 c d hcxs hdxs

-- Members of take/drop are members of the original list.
theorem mem_take_of_mem {α} (n : Nat) (l : List α) (x : α) (h : x ∈ l.take n) : x ∈ l :=
  List.mem_of_mem_take h

theorem mem_drop_of_mem {α} (n : Nat) (l : List α) (x : α) (h : x ∈ l.drop n) : x ∈ l :=
  List.mem_of_mem_drop h

-- ===========================================================================
-- T1 -- orderedInsert preserves key ordering
-- ===========================================================================

def orderedInsert (k : Nat) : List Nat -> List Nat
  | []      => [k]
  | x :: xs => if k < x then k :: x :: xs else x :: orderedInsert k xs

-- orderedInsert preserves strict ordering provided k is not already in ks.
-- (Inserting a duplicate would require k < k, which is false.)
theorem orderedInsert_ordered (k : Nat) (ks : List Nat)
    (h : keysOrdered ks)
    (hfresh : ∀ x ∈ ks, k ≠ x) :
    keysOrdered (orderedInsert k ks) := by
  induction ks with
  | nil => simp [orderedInsert, keysOrdered]
  | cons x xs ih =>
    have hkx : k ≠ x := hfresh x (List.Mem.head xs)
    have hfresh' : ∀ y ∈ xs, k ≠ y := fun y hy => hfresh y (List.Mem.tail x hy)
    simp only [orderedInsert]
    by_cases hlt : k < x
    · simp only [hlt, ↓reduceIte]
      -- goal: keysOrdered (k :: x :: xs)
      cases xs with
      | nil =>
        -- keysOrdered [k, x]
        show k < x ∧ True
        exact ⟨hlt, trivial⟩
      | cons y ys =>
        -- keysOrdered (k :: x :: y :: ys)
        -- h : keysOrdered (x :: y :: ys)
        -- goal : k < x ∧ keysOrdered (x :: y :: ys)
        exact ⟨hlt, h⟩
    · -- k > x (since k ≠ x and ¬(k < x))
      have hxk : x < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hkx)
      simp only [hlt, ↓reduceIte]
      -- goal: keysOrdered (x :: orderedInsert k xs)
      cases xs with
      | nil =>
        -- goal: keysOrdered (x :: [k]) = keysOrdered [x, k]
        -- After unfolding: x < k ∧ True
        show x < k ∧ True
        exact ⟨hxk, trivial⟩
      | cons y ys =>
        -- h : keysOrdered (x :: y :: ys), goal: keysOrdered (x :: orderedInsert k (y :: ys))
        -- h gives h.1 : x < y, h.2 : keysOrdered (y :: ys)
        have hxy : x < y := h.1
        have hord : keysOrdered (orderedInsert k (y :: ys)) := ih h.2 hfresh'
        -- goal: x < (head of orderedInsert k (y::ys)) ∧ rest
        -- Case split on whether k < y
        by_cases hky : k < y
        · -- orderedInsert k (y::ys) = k :: y :: ys
          -- goal: keysOrdered (x :: k :: y :: ys) = x < k ∧ k < y ∧ keysOrdered (y :: ys)
          simp only [orderedInsert, hky, ↓reduceIte]
          exact ⟨hxk, hky, h.2⟩
        · -- orderedInsert k (y::ys) = y :: orderedInsert k ys
          -- goal: keysOrdered (x :: y :: orderedInsert k ys) = x < y ∧ keysOrdered (y :: orderedInsert k ys)
          simp only [orderedInsert, hky, ↓reduceIte] at hord ⊢
          exact ⟨hxy, hord⟩

theorem T1_btree_ordered (ks : List Nat) (k : Nat) (h : keysOrdered ks)
    (hfresh : ∀ x ∈ ks, k ≠ x) :
    keysOrdered (orderedInsert k ks) :=
  orderedInsert_ordered k ks h hfresh

theorem orderedInsert_mem (k : Nat) (ks : List Nat) : k ∈ orderedInsert k ks := by
  induction ks with
  | nil => simp [orderedInsert]
  | cons x xs ih =>
    simp only [orderedInsert]
    by_cases hlt : k < x
    · simp [hlt]
    · simp only [hlt, ↓reduceIte, List.mem_cons]
      right; exact ih

-- ===========================================================================
-- T2 -- balanced split: leaf halves both have height 0
-- ===========================================================================

theorem T2_btree_balanced_leaf_split (ks vs : List Nat) (t : Nat) :
    nodeHeight (BNode.leaf (ks.take (t-1)) (vs.take (t-1))) =
    nodeHeight (BNode.leaf (ks.drop t) (vs.drop t)) := by
  simp [nodeHeight]

-- T2 (internal): any two elements of take or drop sub-lists have the same
-- height, because they are all members of the original uniform-height list.
theorem T2_btree_balanced_internal_split
    (cs : List BNode) (t : Nat)
    (huni : uniformHeight cs) :
    (∀ c d, c ∈ cs.take t -> d ∈ cs.take t -> nodeHeight c = nodeHeight d) ∧
    (∀ c d, c ∈ cs.drop t -> d ∈ cs.drop t -> nodeHeight c = nodeHeight d) := by
  constructor
  · intro c d hc hd
    exact uniformHeight_pairwise cs huni c d (mem_take_of_mem t cs c hc) (mem_take_of_mem t cs d hd)
  · intro c d hc hd
    exact uniformHeight_pairwise cs huni c d (mem_drop_of_mem t cs c hc) (mem_drop_of_mem t cs d hd)

-- ===========================================================================
-- T3 -- occupancy bounds after split
-- ===========================================================================

theorem T3_btree_bounds_split (t : Nat) (ht : t >= 2)
    (ks : List Nat) (hfull : ks.length = maxKeys t) :
    minKeys t ≤ t - 1 ∧ t - 1 ≤ maxKeys t ∧
    minKeys t ≤ ks.length - t ∧ ks.length - t ≤ maxKeys t := by
  simp [minKeys, maxKeys] at *; omega

theorem T3_btree_bounds_insert_nonfull (t : Nat) (ks : List Nat)
    (hlt : ks.length < maxKeys t) :
    ks.length + 1 ≤ maxKeys t := by
  omega

end DbStorage.BTree
