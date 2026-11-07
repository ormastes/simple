import Std

/- Source-linked model of ownership_flow.spl and borrow_graph.spl.
   IDs preserve the 64-bit equality domain of Simple i64; this model performs
   no ID arithmetic. Lists model maybe-moved facts, not a heap owner count.
   Native allocation behavior, CFG convergence and HIR extraction are separate
   obligations. See source_bindings.sdn and the refinement plan. -/
namespace OwnershipFlow

abbrev Id := BitVec 64

inductive Base where
  | local (id : Id)
  | static (name : String)
  | promoted (id : Id)
  deriving DecidableEq, Repr

inductive Elem where
  | deref
  | field (id : Id)
  | index (id : Id)
  | constantIndex (id : Id)
  | downcast (id : Id)
  deriving DecidableEq, Repr

structure Place where
  base : Base
  projections : List Elem
  deriving DecidableEq, Repr

def elemOverlap : Elem → Elem → Bool
  | .index _, .index _ => true
  | .index _, .constantIndex _ => true
  | .constantIndex _, .index _ => true
  | a, b => decide (a = b)

def pathOverlap : List Elem → List Elem → Bool
  | [], _ => true
  | _, [] => true
  | a :: as', b :: bs => elemOverlap a b && pathOverlap as' bs

def conflicts (a b : Place) : Bool :=
  decide (a.base = b.base) && pathOverlap a.projections b.projections

def coversPath : List Elem → List Elem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | .index _ :: _, _ :: _ => false
  | a :: as', b :: bs => decide (a = b) && coversPath as' bs

def covers (write moved : Place) : Bool :=
  decide (write.base = moved.base) && coversPath write.projections moved.projections

inductive Event where
  | read (place : Place)
  | move (place : Place)
  | write (place : Place)
  | revive (place : Place)
  deriving DecidableEq, Repr

def transfer (state : List Place) : Event → List Place
  | .read _ => state
  | .write _ => state
  | .move p => if p ∈ state then state else state ++ [p]
  | .revive p => state.filter (fun moved => !(covers p moved))

def rejects (state : List Place) : Event → Bool
  | .read p | .move p => state.any (fun moved => conflicts p moved)
  | .write p => state.any (fun moved =>
      decide (moved.projections.length < p.projections.length) && conflicts p moved)
  | .revive _ => false

/-- Exact membership-deduplicating successor merge from OwnershipFlow.check. -/
def merge (left : List Place) : List Place → List Place
  | [] => left
  | p :: rest => merge (transfer left (.move p)) rest

/-- Terminal predecessors contribute no state. Reachability is supplied by the
    CFG owner; proving that owner's fixed point is a separate obligation. -/
def joinReachable (left right : List Place) (leftLive rightLive : Bool) : List Place :=
  merge (if leftLive then left else []) (if rightLive then right else [])

theorem elem_overlap_refl (e : Elem) : elemOverlap e e = true := by
  cases e <;> simp [elemOverlap]

theorem path_overlap_refl (es : List Elem) : pathOverlap es es = true := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [pathOverlap, elem_overlap_refl, ih]

theorem conflicts_refl (p : Place) : conflicts p p = true := by
  simp [conflicts, path_overlap_refl]

theorem different_base_no_conflict (p q : Place) (h : p.base ≠ q.base) :
    conflicts p q = false := by
  simp [conflicts, h]

theorem move_membership (state : List Place) (p q : Place) :
    q ∈ transfer state (.move p) ↔ q ∈ state ∨ q = p := by
  by_cases h : p ∈ state
  · simp only [transfer, if_pos h]
    constructor
    · exact Or.inl
    · intro hq
      rcases hq with hq | hq
      · exact hq
      · simpa [hq] using h
  · simp [transfer, h]

theorem move_records_operand (state : List Place) (p : Place) :
    p ∈ transfer state (.move p) :=
  (move_membership state p p).mpr (Or.inr rfl)

theorem move_preserves_other_hazard (state : List Place) (p q : Place)
    (h : q ∈ state) : q ∈ transfer state (.move p) :=
  (move_membership state p q).mpr (Or.inl h)

theorem revive_membership (state : List Place) (write moved : Place) :
    moved ∈ transfer state (.revive write) ↔ moved ∈ state ∧ covers write moved = false := by
  simp [transfer]

theorem revive_preserves_uncovered (state : List Place) (write moved : Place)
    (hm : moved ∈ state) (hc : covers write moved = false) :
    moved ∈ transfer state (.revive write) :=
  (revive_membership state write moved).mpr ⟨hm, hc⟩

theorem revive_removes_covered (state : List Place) (write moved : Place)
    (hc : covers write moved = true) :
    moved ∉ transfer state (.revive write) := by
  simp [revive_membership, hc]

theorem whole_place_covers_descendant (base : Base) (path : List Elem) :
    covers ⟨base, []⟩ ⟨base, path⟩ = true := by
  simp [covers, coversPath]

theorem symbolic_write_not_definite (base : Base) (idx : Id)
    (tail target : List Elem) :
    covers ⟨base, .index idx :: tail⟩ ⟨base, target⟩ = false := by
  cases target <;> simp [covers, coversPath]

theorem symbolic_indices_may_conflict (base : Base) (a b : Id) :
    conflicts ⟨base, [.index a]⟩ ⟨base, [.index b]⟩ = true := by
  simp [conflicts, pathOverlap, elemOverlap]

theorem distinct_constant_indices_do_not_conflict (base : Base) (a b : Id)
    (h : a ≠ b) :
    conflicts ⟨base, [.constantIndex a]⟩ ⟨base, [.constantIndex b]⟩ = false := by
  simp [conflicts, pathOverlap, elemOverlap, h]

theorem read_rejects_moved_overlap (state : List Place) (read moved : Place)
    (hm : moved ∈ state) (hc : conflicts read moved = true) :
    rejects state (.read read) = true := by
  exact List.any_eq_true.mpr ⟨moved, hm, hc⟩

theorem move_rejects_moved_overlap (state : List Place) (target moved : Place)
    (hm : moved ∈ state) (hc : conflicts target moved = true) :
    rejects state (.move target) = true := by
  exact List.any_eq_true.mpr ⟨moved, hm, hc⟩

theorem read_after_move_rejected (state : List Place) (p : Place) :
    rejects (transfer state (.move p)) (.read p) = true :=
  read_rejects_moved_overlap _ p p (move_records_operand state p) (conflicts_refl p)

theorem separate_base_read_accepted (read moved : Place)
    (h : read.base ≠ moved.base) : rejects [moved] (.read read) = false := by
  simp [rejects, different_base_no_conflict read moved h]

theorem write_preserves_facts (state : List Place) (target : Place) :
    transfer state (.write target) = state := rfl

theorem write_rejects_moved_strict_ancestor (state : List Place) (target moved : Place)
    (hm : moved ∈ state) (hlen : moved.projections.length < target.projections.length)
    (hc : conflicts target moved = true) : rejects state (.write target) = true := by
  apply List.any_eq_true.mpr
  exact ⟨moved, hm, by simp [hlen, hc]⟩

theorem write_exact_moved_target_allowed (target : Place) :
    rejects [target] (.write target) = false := by
  simp [rejects]

theorem whole_local_write_then_revive (base : Base) :
    transfer (transfer [⟨base, []⟩] (.write ⟨base, []⟩)) (.revive ⟨base, []⟩) = [] := by
  simp [transfer, covers, coversPath]

theorem merge_membership (left right : List Place) (p : Place) :
    p ∈ merge left right ↔ p ∈ left ∨ p ∈ right := by
  induction right generalizing left with
  | nil => simp [merge]
  | cons q rest ih =>
    simp only [merge, ih, move_membership, List.mem_cons]
    simp only [or_assoc, or_left_comm]

theorem merge_order_same_hazards (left right : List Place) (p : Place) :
    p ∈ merge left right ↔ p ∈ merge right left := by
  simp [merge_membership, or_comm]

theorem reachable_join_preserves_left (left right : List Place) (p : Place)
    (h : p ∈ left) (rightLive : Bool) :
    p ∈ joinReachable left right true rightLive := by
  simp [joinReachable, merge_membership, h]

theorem reachable_join_preserves_right (left right : List Place) (p : Place)
    (h : p ∈ right) (leftLive : Bool) :
    p ∈ joinReachable left right leftLive true := by
  simp [joinReachable, merge_membership, h]

theorem terminal_predecessors_contribute_nothing (left right : List Place) :
    joinReachable left right false false = [] := by
  simp [joinReachable, merge]

theorem reachable_join_read_rejects (left right : List Place) (read moved : Place)
    (hm : moved ∈ left) (hc : conflicts read moved = true) (rightLive : Bool) :
    rejects (joinReachable left right true rightLive) (.read read) = true :=
  read_rejects_moved_overlap _ read moved
    (reachable_join_preserves_left left right moved hm rightLive) hc

end OwnershipFlow
